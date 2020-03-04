"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const mir_assembly_1 = require("../../compiler/mir_assembly");
const smttype_emitter_1 = require("./smttype_emitter");
const smtbody_emitter_1 = require("./smtbody_emitter");
const mir_callg_1 = require("../../compiler/mir_callg");
const smt_exp_1 = require("./smt_exp");
class SMTEmitter {
    static emit(assembly, entrypoint, errorcheck) {
        const typeemitter = new smttype_emitter_1.SMTTypeEmitter(assembly);
        typeemitter.initializeConceptSubtypeRelation();
        const bodyemitter = new smtbody_emitter_1.SMTBodyEmitter(assembly, typeemitter);
        let typedecls_fwd = [];
        let typedecls = [];
        let ocons = [];
        let edecls = [];
        assembly.entityDecls.forEach((edecl) => {
            const smtdecl = typeemitter.generateSMTEntity(edecl);
            if (smtdecl !== undefined) {
                typedecls_fwd.push(smtdecl.fwddecl);
                typedecls.push(smtdecl.fulldecl);
                ocons.push(smtdecl.ocons);
                if (smtdecl.emptydecl !== undefined) {
                    edecls.push(smtdecl.emptydecl);
                }
            }
        });
        let doneset = new Set();
        let funcdecls = [];
        let resultdecls_fwd = [];
        let resultdecls = [];
        resultdecls_fwd.push(`(Result@Bool 0)`);
        resultdecls.push(`( (result_success@Bool (result_success_value@Bool Bool)) (result_error@Bool (result_error_code@Bool ErrorCode)) )`);
        const cginfo = mir_callg_1.constructCallGraphInfo(assembly.entryPoints, assembly);
        const rcg = [...cginfo.topologicalOrder].reverse();
        for (let i = 0; i < rcg.length; ++i) {
            const cn = rcg[i];
            if (doneset.has(cn.invoke)) {
                continue;
            }
            const cscc = cginfo.recursive.find((scc) => scc.has(cn.invoke));
            const currentSCC = cscc || new Set();
            let worklist = cscc !== undefined ? [...cscc].sort() : [cn.invoke];
            let gasmax = cscc !== undefined ? Math.max(...worklist.map((bbup) => bodyemitter.getGasForOperation(bbup))) : 1;
            for (let gasctr = 1; gasctr <= gasmax; gasctr++) {
                for (let mi = 0; mi < worklist.length; ++mi) {
                    const ikey = worklist[mi];
                    let gas = undefined;
                    let gasdown = undefined;
                    if (gasctr !== gasmax) {
                        gas = gasctr;
                        gasdown = gasctr - 1;
                    }
                    else {
                        gasdown = gasmax - 1;
                    }
                    const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey));
                    const finfo = bodyemitter.generateSMTInvoke(idcl, currentSCC, gas, gasdown);
                    funcdecls.push(finfo);
                    const rtype = typeemitter.getSMTTypeFor(typeemitter.getMIRType(idcl.resultType));
                    if (!resultdecls_fwd.includes(`(Result@${rtype} 0)`)) {
                        resultdecls_fwd.push(`(Result@${rtype} 0)`);
                        resultdecls.push(`( (result_success@${rtype} (result_success_value@${rtype} ${rtype})) (result_error@${rtype} (result_error_code@${rtype} ErrorCode)) )`);
                    }
                }
                if (cscc !== undefined) {
                    cscc.forEach((v) => doneset.add(v));
                }
            }
        }
        let vfieldaccess = [];
        for (let i = 0; i < bodyemitter.vfieldLookups.length; ++i) {
            const vl = bodyemitter.vfieldLookups[i];
            const opts = [...assembly.entityDecls].filter((edcl) => {
                const etype = typeemitter.getMIRType(edcl[0]);
                return assembly.subtypeOf(etype, vl.infertype) && assembly.subtypeOf(etype, typeemitter.getMIRType(vl.fdecl.enclosingDecl));
            });
            const ttl = assembly.typeMap.get(opts[opts.length - 1][0]);
            const cargl = typeemitter.coerce(new smt_exp_1.SMTValue("$arg$"), vl.infertype, ttl).emit();
            let body = `(${typeemitter.generateEntityAccessor(typeemitter.getEntityEKey(ttl), vl.fdecl.fkey)} ${cargl})`;
            for (let i = opts.length - 2; i >= 0; --i) {
                const tti = assembly.typeMap.get(opts[i][0]);
                const testi = `(= $objtype$ "${typeemitter.mangleStringForSMT(tti.trkey)}")`;
                const cargi = typeemitter.coerce(new smt_exp_1.SMTValue("$arg$"), vl.infertype, tti).emit();
                body = `  (ite ${testi} (${typeemitter.generateEntityAccessor(typeemitter.getEntityEKey(tti), vl.fdecl.fkey)} ${cargi})\n`
                    + `  ${body})`;
            }
            const cdcl = `(define-fun ${typeemitter.mangleStringForSMT(vl.lname)} (($arg$ ${typeemitter.getSMTTypeFor(vl.infertype)})) ${typeemitter.getSMTTypeFor(typeemitter.getMIRType(vl.fdecl.declaredType))}\n`;
            if (opts.length === 1) {
                vfieldaccess.push(cdcl + body + "\n)");
            }
            else {
                body = `(let (($objtype$ (bsqterm_get_nominal_type $arg$)))\n` + body + "\n)";
                vfieldaccess.push(cdcl + body + "\n)");
            }
        }
        const rrtype = typeemitter.getSMTTypeFor(typeemitter.getMIRType(entrypoint.resultType));
        let argscall = [];
        let argsdecls = [];
        for (let i = 0; i < entrypoint.params.length; ++i) {
            const param = entrypoint.params[i];
            const paramtype = typeemitter.getMIRType(param.type);
            argscall.push(`@${param.name}`);
            argsdecls.push(`(declare-const @${param.name} ${typeemitter.getSMTTypeFor(paramtype)})`);
            const tcops = paramtype.options.map((opt) => bodyemitter.generateTypeCheck("@" + param.name, paramtype, paramtype, typeemitter.getMIRType(opt.trkey)));
            if (!tcops.some((tcr) => tcr === "true")) {
                argsdecls.push(`(assert (or ${tcops.join(" ")}))`);
            }
        }
        if (entrypoint.preconditions !== undefined) {
            const params = entrypoint.params.map((param) => `@${param.name}`);
            argsdecls.push("(declare-const @icheck Result@Bool)");
            if (params.length === 0) {
                argsdecls.push(`(assert (= @icheck ${typeemitter.mangleStringForSMT(entrypoint.preconditions)}))`);
            }
            else {
                argsdecls.push(`(assert (= @icheck (${typeemitter.mangleStringForSMT(entrypoint.preconditions)} ${params.join(" ")})))`);
            }
            argsdecls.push("(assert (and (is-result_success@Bool @icheck) (result_success_value@Bool @icheck)))");
        }
        let conceptSubtypes = [];
        typeemitter.conceptSubtypeRelation.forEach((stv, cpt) => {
            const nemums = stv.map((ek) => `"${typeemitter.mangleStringForSMT(ek)}"`).sort();
            if (nemums.length !== 0) {
                const sta = `(declare-const MIRConceptSubtypeArray$${typeemitter.mangleStringForSMT(cpt)} (Array String Bool))`;
                let iv = "mirconceptsubtypearray_empty";
                for (let i = 0; i < nemums.length; ++i) {
                    iv = `(store ${iv} ${nemums[i]} true)`;
                }
                conceptSubtypes.push(sta + "\n" + `(assert (= MIRConceptSubtypeArray$${typeemitter.mangleStringForSMT(cpt)} ${iv}))`);
            }
        });
        const typechecks = [...bodyemitter.subtypeFMap].map(tcp => tcp[1]).sort((tc1, tc2) => tc1.order - tc2.order).map((tc) => tc.decl);
        let nominal_data_kinds = [];
        let special_name_decls = [];
        let ephdecls_fwd = [];
        let ephdecls = [];
        [...typeemitter.assembly.typeMap].forEach((te) => {
            const tt = te[1];
            if (typeemitter.typecheckIsName(tt, /^NSCore::None$/) || typeemitter.typecheckIsName(tt, /^NSCore::Bool$/) || typeemitter.typecheckIsName(tt, /^NSCore::Int$/) || typeemitter.typecheckIsName(tt, /^NSCore::String$/)
                || typeemitter.typecheckIsName(tt, /^NSCore::GUID$/) || typeemitter.typecheckIsName(tt, /^NSCore::LogicalTime$/)
                || typeemitter.typecheckIsName(tt, /^NSCore::DataHash$/) || typeemitter.typecheckIsName(tt, /^NSCore::CryptoHash$/)
                || typeemitter.typecheckIsName(tt, /^NSCore::ISOTime$/) || typeemitter.typecheckIsName(tt, /^NSCore::Regex$/)) {
                special_name_decls.push(`(assert (= MIRNominalTypeEnum_${tt.trkey.substr(8)} "${typeemitter.mangleStringForSMT(tt.trkey)}"))`);
            }
            if (tt.trkey === "NSCore::Tuple" || tt.trkey === "NSCore::Record") {
                special_name_decls.push(`(assert (= MIRNominalTypeEnum_${tt.trkey.substr(8)} "${typeemitter.mangleStringForSMT(tt.trkey)}"))`);
            }
            if (tt.options.length === 1 && (tt.options[0] instanceof mir_assembly_1.MIREntityType)) {
                const ndn = typeemitter.mangleStringForSMT(tt.trkey);
                const dk = typeemitter.generateInitialDataKindFlag(tt);
                nominal_data_kinds.push(`(assert (= (nominalDataKinds "${ndn}") ${dk.toString()}))`);
            }
            if (tt.options.length === 1 && (tt.options[0] instanceof mir_assembly_1.MIREphemeralListType)) {
                const ephdecl = typeemitter.generateSMTEphemeral(tt.options[0]);
                ephdecls_fwd.push(ephdecl.fwddecl);
                ephdecls.push(ephdecl.fulldecl);
            }
        });
        let fulledecls = "";
        if (ephdecls_fwd.length !== 0) {
            fulledecls = "(declare-datatypes (\n"
                + `  ${ephdecls_fwd.sort().join("\n  ")}`
                + "\n) (\n"
                + `  ${ephdecls.sort().join("\n  ")}`
                + "\n))";
        }
        const resv = `(declare-const @smtres@ Result@${rrtype})`;
        const call = argscall.length !== 0 ? `(${bodyemitter.invokenameToSMT(entrypoint.key)} ${argscall.join(" ")})` : bodyemitter.invokenameToSMT(entrypoint.key);
        const cassert = `(assert (= @smtres@ ${call}))`;
        const bmcchk = `(assert (not (and (is-result_error@${rrtype} @smtres@) (is-result_bmc (result_error_code@${rrtype} @smtres@)))))`;
        let chk = errorcheck ? `(assert (is-result_error@${rrtype} @smtres@))` : `(assert (not (is-result_error@${rrtype} @smtres@)))`;
        const callinfo = resv + "\n" + cassert + "\n" + bmcchk + "\n" + chk;
        return {
            NOMINAL_DECLS_FWD: typedecls_fwd.sort().join("\n    "),
            NOMINAL_CONSTRUCTORS: typedecls.sort().join("\n    "),
            NOMINAL_OBJECT_CONSTRUCTORS: ocons.sort().join("\n    "),
            NOMINAL_TYPE_TO_DATA_KIND_ASSERTS: nominal_data_kinds.sort().join("\n"),
            SPECIAL_NAME_BLOCK_ASSERTS: special_name_decls.sort().join("\n"),
            EPHEMERAL_DECLS: fulledecls,
            EMPTY_CONTENT_ARRAY_DECLS: edecls.sort().join("\n"),
            RESULTS_FWD: resultdecls_fwd.sort().join("\n    "),
            RESULTS: resultdecls.sort().join("\n    "),
            CONCEPT_SUBTYPE_RELATION_DECLARE: conceptSubtypes.sort().join("\n"),
            SUBTYPE_DECLS: typechecks.join("\n    "),
            VFIELD_ACCESS: vfieldaccess.join("\n"),
            FUNCTION_DECLS: funcdecls.join("\n"),
            ARG_VALUES: argsdecls.join("\n"),
            INVOKE_ACTION: callinfo
        };
    }
}
exports.SMTEmitter = SMTEmitter;
//# sourceMappingURL=smtdecls_emitter.js.map