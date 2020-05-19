//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRInvokeDecl, MIRInvokeBodyDecl, MIREntityType, MIREphemeralListType } from "../../compiler/mir_assembly";
import { SMTTypeEmitter } from "./smttype_emitter";
import { SMTBodyEmitter } from "./smtbody_emitter";
import { constructCallGraphInfo } from "../../compiler/mir_callg";
import { MIRInvokeKey } from "../../compiler/mir_ops";

type SMTCode = {
    REGEX_DECLS: string,

    NOMINAL_DECLS_FWD: string,
    NOMINAL_CONSTRUCTORS: string,
    NOMINAL_OBJECT_CONSTRUCTORS: string,

    NOMINAL_TYPE_KIND_DECLS: string,
    NOMINAL_TYPE_TO_DATA_KIND_ASSERTS: string,
    SPECIAL_NAME_BLOCK_ASSERTS: string,

    EPHEMERAL_DECLS: string,

    EMPTY_CONTENT_ARRAY_DECLS: string,

    RESULTS_FWD: string,
    RESULTS: string,

    CONCEPT_SUBTYPE_RELATION_DECLARE: string,
    SUBTYPE_DECLS: string,

    VFIELD_ACCESS: string,

    FUNCTION_DECLS: string,
    ARG_VALUES: string,

    INVOKE_ACTION: string
};

class SMTEmitter {
    static emit(assembly: MIRAssembly, entrypoint: MIRInvokeBodyDecl, errorcheck: boolean): SMTCode {
        const typeemitter = new SMTTypeEmitter(assembly);
        typeemitter.initializeConceptSubtypeRelation();

        const bodyemitter = new SMTBodyEmitter(assembly, typeemitter);

        let typedecls_fwd: string[] = [];
        let typedecls: string[] = [];
        let nominaltypeinfo: string[] = [];
        let ocons: string[] = [];
        let edecls: string[] = [];
        [...assembly.entityDecls]
        .sort((a, b) => a[0].localeCompare(b[0]))
        .map((ee) => ee[1])
        .forEach((edecl) => {
            const smtdecl = typeemitter.generateSMTEntity(edecl);
            if (smtdecl !== undefined) {
                typedecls_fwd.push(smtdecl.fwddecl);
                typedecls.push(smtdecl.fulldecl);
                ocons.push(smtdecl.ocons);
                if(smtdecl.emptydecl !== undefined) {
                    edecls.push(smtdecl.emptydecl);
                }
            }

            const decl = `(declare-const MIRNominalTypeEnum_${typeemitter.mangleStringForSMT(edecl.tkey)} Int)`
            const enumv = `(assert (= MIRNominalTypeEnum_${typeemitter.mangleStringForSMT(edecl.tkey)} ${nominaltypeinfo.length + 1}))`;
            nominaltypeinfo.push(decl);
            nominaltypeinfo.push(enumv);
        });

        let concepttypeinfo: string[] = [];
        [...assembly.conceptDecls]
        .sort((a, b) => a[0].localeCompare(b[0]))
        .map((ce) => ce[1])
        .forEach((cdecl) => {
            const decl = `(declare-const MIRNominalTypeEnum_${typeemitter.mangleStringForSMT(cdecl.tkey)} Int)`
            const enumv = `(assert (= MIRNominalTypeEnum_${typeemitter.mangleStringForSMT(cdecl.tkey)} ${concepttypeinfo.length + nominaltypeinfo.length + 1}))`;
            concepttypeinfo.push(decl);
            concepttypeinfo.push(enumv);
        });

        let doneset = new Set<MIRInvokeKey>();
        let funcdecls: string[] = [];
        let resultdecls_fwd: string[] = [];
        let resultdecls: string[] = [];

        resultdecls_fwd.push(`(Result@Bool 0)`);
        resultdecls.push(`( (result_success@Bool (result_success_value@Bool Bool)) (result_error@Bool (result_error_code@Bool ErrorCode)) )`);

        const cginfo = constructCallGraphInfo(assembly.entryPoints, assembly);
        const rcg = [...cginfo.topologicalOrder].reverse();

        for (let i = 0; i < rcg.length; ++i) {
            const cn = rcg[i];
            if(doneset.has(cn.invoke)) {
                continue;
            }

            const cscc = cginfo.recursive.find((scc) => scc.has(cn.invoke));
            const currentSCC = cscc || new Set<string>();
            let worklist = cscc !== undefined ? [...cscc].sort() : [cn.invoke];

            let gasmax: number | undefined = cscc !== undefined ? Math.max(...worklist.map((bbup) => bodyemitter.getGasForOperation(bbup))) : 1;
            for (let gasctr = 1; gasctr <= gasmax; gasctr++) {
                for (let mi = 0; mi < worklist.length; ++mi) {
                    const ikey = worklist[mi];

                    let gas: number | undefined = undefined;
                    let gasdown: number | undefined = undefined;
                    if (gasctr !== gasmax) {
                        gas = gasctr;
                        gasdown = gasctr - 1;
                    }
                    else {
                        gasdown = gasmax - 1;
                    }

                    const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
                    const finfo = bodyemitter.generateSMTInvoke(idcl, currentSCC, gas, gasdown);

                    funcdecls.push(finfo);

                    const rtype = typeemitter.getSMTTypeFor(typeemitter.getMIRType(idcl.resultType));
                    if (!resultdecls_fwd.includes(`(Result@${rtype} 0)`)) {
                        resultdecls_fwd.push(`(Result@${rtype} 0)`);
                        resultdecls.push(`( (result_success@${rtype} (result_success_value@${rtype} ${rtype})) (result_error@${rtype} (result_error_code@${rtype} ErrorCode)) )`);
                    }
                }

                if(cscc !== undefined) {
                    cscc.forEach((v) => doneset.add(v));
                }
            }
        }   

        let vfieldaccess: string[] = [];
        for(let i = 0; i < bodyemitter.vfieldLookups.length; ++i) {
            //
            //TODO: generate vfield switches
            //
        }

        const rrtype = typeemitter.getSMTTypeFor(typeemitter.getMIRType(entrypoint.resultType));

        let argscall: string[] = [];
        let argsdecls: string[] = [];
        for(let i = 0; i < entrypoint.params.length; ++i) {
            const param = entrypoint.params[i];
            const paramtype = typeemitter.getMIRType(param.type);

            argscall.push(`@${param.name}`);
            argsdecls.push(`(declare-const @${param.name} ${typeemitter.getSMTTypeFor(paramtype)})`);
            if(paramtype.options.length !== 1) {
                const tcops = paramtype.options.map((opt) => {
                    if(opt.trkey === "NSCore::None") {
                        return `(= @${param.name} bsqkey_none)`;
                    }
                    else if(opt.trkey === "NSCore::Bool") {
                        return `(is-bsqkey_bool @${param.name})`;
                    }
                    else if(opt.trkey === "NSCore::Int") {
                        return `(is-bsqkey_int @${param.name})`;
                    }
                    else {
                        return `(is-bsqkey_string @${param.name})`;
                    }
                });

                argsdecls.push(`(assert (or ${tcops.join(" ")}))`);
            }
        }

        if(entrypoint.preconditions !== undefined) {
            const params = entrypoint.params.map((param) => `@${param.name}`);
            argsdecls.push("(declare-const @icheck Result@Bool)")
            if(params.length === 0) {
                argsdecls.push(`(assert (= @icheck ${typeemitter.mangleStringForSMT(entrypoint.preconditions)}))`);
            }
            else {
                argsdecls.push(`(assert (= @icheck (${typeemitter.mangleStringForSMT(entrypoint.preconditions)} ${params.join(" ")})))`);
            }
            argsdecls.push("(assert (and (is-result_success@Bool @icheck) (result_success_value@Bool @icheck)))")
        }

        let conceptSubtypes: string[] = [];
        typeemitter.conceptSubtypeRelation.forEach((stv, cpt) => {
            const nemums = stv.map((ek) => `MIRNominalTypeEnum_${typeemitter.mangleStringForSMT(ek)}`).sort();
            if (nemums.length !== 0) {
                const sta = `(declare-const MIRConceptSubtypeArray$${typeemitter.mangleStringForSMT(cpt)} (Array Int Bool))`;
                let iv = "mirconceptsubtypearray_empty";
                for (let i = 0; i < nemums.length; ++i) {
                    iv = `(store ${iv} ${nemums[i]} true)`;
                }

                conceptSubtypes.push(sta + "\n" + `(assert (= MIRConceptSubtypeArray$${typeemitter.mangleStringForSMT(cpt)} ${iv}))`);
            }
        });

        const typechecks = [...bodyemitter.subtypeFMap].map(tcp => tcp[1]).sort((tc1, tc2) => tc1.order - tc2.order).map((tc) => tc.decl);

        let nominal_data_kinds: string[] = [];
        let special_name_decls: string[] = [];
        let ephdecls_fwd: string[] = [];
        let ephdecls: string[] = [];
        [...typeemitter.assembly.typeMap].forEach((te) => {
            const tt = te[1];

            if(typeemitter.typecheckIsName(tt, /^NSCore::None$/) || typeemitter.typecheckIsName(tt, /^NSCore::Bool$/) || typeemitter.typecheckIsName(tt, /^NSCore::Int$/) || typeemitter.typecheckIsName(tt, /^NSCore::BigInt$/) || typeemitter.typecheckIsName(tt, /^NSCore::Float64$/) 
            || typeemitter.typecheckIsName(tt, /^NSCore::String$/) || typeemitter.typecheckIsName(tt, /^NSCore::UUID$/) || typeemitter.typecheckIsName(tt, /^NSCore::LogicalTime$/) || typeemitter.typecheckIsName(tt, /^NSCore::CryptoHash$/) || typeemitter.typecheckIsName(tt, /^NSCore::ByteBuffer$/)
            || typeemitter.typecheckIsName(tt, /^NSCore::ISOTime$/) || typeemitter.typecheckIsName(tt, /^NSCore::Regex$/)) {
                        special_name_decls.push(`(assert (= MIRNominalTypeEnum_${tt.trkey.substr(8)} MIRNominalTypeEnum_${typeemitter.mangleStringForSMT(tt.trkey)}))`);
                    }
            
            if (tt.trkey === "NSCore::Tuple" || tt.trkey === "NSCore::Record") {
                special_name_decls.push(`(assert (= MIRNominalTypeEnum_${tt.trkey.substr(8)} MIRNominalTypeEnum_${typeemitter.mangleStringForSMT(tt.trkey)}))`);
            }

            if(tt.options.length === 1 && (tt.options[0] instanceof MIREntityType)) {
                const ndn = typeemitter.mangleStringForSMT(tt.trkey);
                const dk = typeemitter.generateInitialDataKindFlag(tt);
                nominal_data_kinds.push(`(assert (= (nominalDataKinds MIRNominalTypeEnum_${ndn}) ${dk.toString()}))`);
            }

            if(tt.options.length === 1 && (tt.options[0] instanceof MIREphemeralListType)) {
                const ephdecl = typeemitter.generateSMTEphemeral(tt.options[0] as MIREphemeralListType);
                ephdecls_fwd.push(ephdecl.fwddecl);
                ephdecls.push(ephdecl.fulldecl);
            }
        });

        let fulledecls = "";
        if(ephdecls_fwd.length !== 0) {
            fulledecls = "(declare-datatypes (\n"
            + `  ${ephdecls_fwd.sort().join("\n  ")}`
            + "\n) (\n"
            + `  ${ephdecls.sort().join("\n  ")}`
            + "\n))"
        }

        let constregexs: string[] = [];
        bodyemitter.allConstRegexes.forEach((v, k) => {
            constregexs.push(`;;${k} = ${v}`);
        });

        const resv = `(declare-const @smtres@ Result@${rrtype})`;
        const call = argscall.length !== 0 ? `(${bodyemitter.invokenameToSMT(entrypoint.key)} ${argscall.join(" ")})` : bodyemitter.invokenameToSMT(entrypoint.key);
        const cassert = `(assert (= @smtres@ ${call}))`;

        const bmcchk = `(assert (not (and (is-result_error@${rrtype} @smtres@) (is-result_bmc (result_error_code@${rrtype} @smtres@)))))`

        let chk = errorcheck ? `(assert (is-result_error@${rrtype} @smtres@))` : `(assert (not (is-result_error@${rrtype} @smtres@)))`;

        const callinfo = resv + "\n" + cassert + "\n" + bmcchk + "\n" + chk;

        return {
            NOMINAL_DECLS_FWD: typedecls_fwd.sort().join("\n    "),
            NOMINAL_CONSTRUCTORS: typedecls.sort().join("\n    "),
            NOMINAL_OBJECT_CONSTRUCTORS: ocons.sort().join("\n    "),
        
            NOMINAL_TYPE_KIND_DECLS: [...nominaltypeinfo, ...concepttypeinfo].join("\n"),
            NOMINAL_TYPE_TO_DATA_KIND_ASSERTS: nominal_data_kinds.sort().join("\n"),
            SPECIAL_NAME_BLOCK_ASSERTS: special_name_decls.sort().join("\n"),
        
            EPHEMERAL_DECLS: fulledecls,
        
            EMPTY_CONTENT_ARRAY_DECLS: edecls.sort().join("\n"),
        
            RESULTS_FWD: resultdecls_fwd.sort().join("\n    "),
            RESULTS: resultdecls.sort().join("\n    "),
        
            REGEX_DECLS: constregexs.sort().join("\n    "),

            CONCEPT_SUBTYPE_RELATION_DECLARE: conceptSubtypes.sort().join("\n"),
            SUBTYPE_DECLS: typechecks.join("\n    "),
        
            VFIELD_ACCESS: vfieldaccess.join("\n"),

            FUNCTION_DECLS: funcdecls.join("\n"),
            ARG_VALUES: argsdecls.join("\n"),
        
            INVOKE_ACTION: callinfo
        };
    }
}

export {
    SMTEmitter
};
