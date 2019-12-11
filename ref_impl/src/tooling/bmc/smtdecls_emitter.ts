//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRInvokeDecl, MIRInvokeBodyDecl, MIREntityTypeDecl, MIRConstantDecl, MIRFieldDecl } from "../../compiler/mir_assembly";
import { SMTTypeEmitter } from "./smttype_emitter";
import { SMTBodyEmitter } from "./smtbody_emitter";
import { constructCallGraphInfo } from "../../compiler/mir_callg";
import { extractMirBodyKeyPrefix, extractMirBodyKeyData, MIRInvokeKey, MIRNominalTypeKey, MIRConstantKey, MIRFieldKey, MIRBodyKey } from "../../compiler/mir_ops";

import * as assert from "assert";

type SMTCode = {
    typedecls_fwd: string,
    typedecls: string,
    conceptSubtypeRelation: string,
    typechecks: string,
    fixedtupledecls_fwd: string,
    fixedtupledecls: string,
    fixedrecorddecls_fwd: string,
    fixedrecorddecls: string,
    resultdecls_fwd: string,
    resultdecls: string,
    function_decls: string,
    args_info: string,
    main_info: string
};

const SymbolicArgTypecheckGas = 3;

class SMTEmitter {
    static emit(assembly: MIRAssembly, entrypoint: MIRInvokeBodyDecl, default_gas: number, errorcheck: boolean): SMTCode {
        const typeemitter = new SMTTypeEmitter(assembly);
        typeemitter.initializeConceptSubtypeRelation();

        const bodyemitter = new SMTBodyEmitter(assembly, typeemitter, default_gas);

        const cginfo = constructCallGraphInfo(assembly.entryPoints, assembly);
        const rcg = [...cginfo.topologicalOrder].reverse();

        let typedecls_fwd: string[] = [];
        let typedecls: string[] = [];
        assembly.entityDecls.forEach((edecl) => {
            const smtdecl = typeemitter.generateSMTEntity(edecl);
            if (smtdecl !== undefined) {
                typedecls_fwd.push(smtdecl.fwddecl);
                typedecls.push(smtdecl.fulldecl);
            }
        });

        let fixedtupledecls_fwd: string[] = [];
        let fixedtupledecls: string[] = [];
        let fixedrecorddecls_fwd: string[] = [];
        let fixedrecorddecls: string[] = [];
        assembly.typeMap.forEach((tt) => {
            if (typeemitter.isTupleType(tt) && SMTTypeEmitter.getTupleTypeMaxLength(tt) !== 0) {
                if (!fixedtupledecls_fwd.includes(`(${typeemitter.typeToSMTCategory(tt)} 0)`)) {
                    fixedtupledecls_fwd.push(`(${typeemitter.typeToSMTCategory(tt)} 0)`);

                    const maxlen = SMTTypeEmitter.getTupleTypeMaxLength(tt);
                    let cargs: string[] = [];
                    for (let i = 0; i < maxlen; ++i) {
                        cargs.push(`(${typeemitter.generateTupleAccessor(tt, i)} BTerm)`);
                    }
                    fixedtupledecls.push(`( (${typeemitter.generateTupleConstructor(tt)} ${cargs.join(" ")}) )`);
                }
            }

            if (typeemitter.isRecordType(tt) && SMTTypeEmitter.getRecordTypeMaxPropertySet(tt).length !== 0) {
                if (!fixedrecorddecls_fwd.includes(`(${typeemitter.typeToSMTCategory(tt)} 0)`)) {
                    fixedrecorddecls_fwd.push(`(${typeemitter.typeToSMTCategory(tt)} 0)`);

                    const maxset = SMTTypeEmitter.getRecordTypeMaxPropertySet(tt);
                    let cargs: string[] = [];
                    for (let i = 0; i < maxset.length; ++i) {
                        cargs.push(`(${typeemitter.generateRecordAccessor(tt, maxset[i])} BTerm)`);
                    }
                    fixedrecorddecls.push(`( (${typeemitter.generateRecordConstructor(tt)} ${cargs.join(" ")}) )`);
                }
            }
        });

        let doneset = new Set<MIRBodyKey>();
        let funcdecls: string[] = [];
        let resultdecls_fwd: string[] = [];
        let resultdecls: string[] = [];

        resultdecls_fwd.push(`(Result@Bool 0)`);
        resultdecls.push(`( (result_success@Bool (result_success_value@Bool Bool)) (result_error@Bool (result_error_code@Bool ErrorCode)) )`);

        for (let i = 0; i < rcg.length; ++i) {
            const cn = rcg[i];
            if(doneset.has(cn.invoke)) {
                continue;
            }

            const cscc = cginfo.recursive.find((scc) => scc.has(cn.invoke));
            const currentSCC = cscc !== undefined ? new Set<string>([...cscc].map((cc) => extractMirBodyKeyData(cc))) : new Set<string>();
            let worklist = cscc !== undefined ? [...cscc].sort() : [cn.invoke];

            let gasmax: number | undefined = cscc !== undefined ? Math.max(...worklist.map((bbup) => bodyemitter.getGasForOperation(bbup))) : 1;
            for (let gasctr = 1; gasctr <= gasmax; gasctr++) {
                for (let mi = 0; mi < worklist.length; ++mi) {
                    const bbup = worklist[mi];

                    let gas: number | undefined = undefined;
                    let gasdown: number | undefined = undefined;
                    if(gasctr !== gasmax) {
                        gas = gasctr;
                        gasdown = gasctr - 1;
                    }
                    else {
                        gasdown = gasmax - 1;
                    }

                    const tag = extractMirBodyKeyPrefix(bbup);
                    if (tag === "invoke") {
                        const ikey = extractMirBodyKeyData(bbup) as MIRInvokeKey;
                        const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
                        const finfo = bodyemitter.generateSMTInvoke(idcl, currentSCC, gas, gasdown);

                        funcdecls.push(finfo);

                        const rtype = typeemitter.typeToSMTCategory(typeemitter.getMIRType(idcl.resultType));
                        if (!resultdecls_fwd.includes(`(Result@${rtype} 0)`)) {
                            resultdecls_fwd.push(`(Result@${rtype} 0)`);
                            resultdecls.push(`( (result_success@${rtype} (result_success_value@${rtype} ${rtype})) (result_error@${rtype} (result_error_code@${rtype} ErrorCode)) )`);
                        }
                    }
                    else if (tag === "pre") {
                        const ikey = extractMirBodyKeyData(bbup) as MIRInvokeKey;
                        const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
                        funcdecls.push(bodyemitter.generateSMTPre(bbup, idcl));
                    }
                    else if (tag === "post") {
                        const ikey = extractMirBodyKeyData(bbup) as MIRInvokeKey;
                        const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
                        funcdecls.push(bodyemitter.generateSMTPost(bbup, idcl));
                    }
                    else if (tag === "invariant") {
                        const edcl = assembly.entityDecls.get(extractMirBodyKeyData(bbup) as MIRNominalTypeKey) as MIREntityTypeDecl;
                        funcdecls.push(bodyemitter.generateSMTInv(bbup, edcl));
                    }
                    else if (tag === "const") {
                        const cdcl = assembly.constantDecls.get(extractMirBodyKeyData(bbup) as MIRConstantKey) as MIRConstantDecl;
                        const cdeclemit = bodyemitter.generateSMTConst(bbup, cdcl);
                        if (cdeclemit !== undefined) {
                            funcdecls.push(cdeclemit);

                            const rtype = typeemitter.typeToSMTCategory(typeemitter.getMIRType(cdcl.declaredType));
                            if (!resultdecls_fwd.includes(`(Result@${rtype} 0)`)) {
                                resultdecls_fwd.push(`(Result@${rtype} 0)`);
                                resultdecls.push(`( (result_success@${rtype} (result_success_value@${rtype} ${rtype})) (result_error@${rtype} (result_error_code@${rtype} ErrorCode)) )`);
                            }
                        }

                    }
                    else {
                        assert(tag === "fdefault");

                        const fdcl = assembly.fieldDecls.get(extractMirBodyKeyData(bbup) as MIRFieldKey) as MIRFieldDecl;
                        const fdeclemit = bodyemitter.generateSMTFDefault(bbup, fdcl);
                        if (fdeclemit !== undefined) {
                            funcdecls.push(fdeclemit);

                            const rtype = typeemitter.typeToSMTCategory(typeemitter.getMIRType(fdcl.declaredType));
                            if (!resultdecls_fwd.includes(`(Result@${rtype} 0)`)) {
                                resultdecls_fwd.push(`(Result@${rtype} 0)`);
                                resultdecls.push(`( (result_success@${rtype} (result_success_value@${rtype} ${rtype})) (result_error@${rtype} (result_error_code@${rtype} ErrorCode)) )`);
                            }
                        }
                    }
                }

                if(cscc !== undefined) {
                    cscc.forEach((v) => doneset.add(v));
                }
            }
        }   

        const rrtype = typeemitter.typeToSMTCategory(typeemitter.getMIRType(entrypoint.resultType));

        let argscall: string[] = [];
        let argsdecls: string[] = [];
        for(let i = 0; i < entrypoint.params.length; ++i) {
            const param = entrypoint.params[i];
            const paramtype = typeemitter.getMIRType(param.type);

            argscall.push(`@${param.name}`);
            argsdecls.push(`(declare-const @${param.name} ${typeemitter.typeToSMTCategory(paramtype)})`);
            if(typeemitter.typeToSMTCategory(paramtype) === "BTerm") {
                argsdecls.push(`(assert ${bodyemitter.generateTypeCheck(param.name, typeemitter.anyType, typeemitter.getMIRType(param.type), true, SymbolicArgTypecheckGas)})`)
            }
        }

        let conceptSubtypes: string[] = [];
        typeemitter.conceptSubtypeRelation.forEach((stv, cpt) => {
            const nemums = stv.map((ek) => typeemitter.mangleStringForSMT(ek)).sort();
            const sta = `(declare-const MIRConceptSubtypeArray__${typeemitter.mangleStringForSMT(cpt)} (Array String Bool))`;
            let iv = "mirconceptsubtypearray_empty";
            for (let i = 0; i < nemums.length; ++i) {
                iv = `(store ${iv} ${nemums[i]}, true)`;
            }

            conceptSubtypes.push(sta + "\n" + `(assert (= MIRConceptSubtypeArray__${typeemitter.mangleStringForSMT(cpt)} ${iv}))`);
        });

        const typechecks = [...bodyemitter.subtypeFMap].map(tcp => tcp[1]).sort((tc1, tc2) => tc1.order - tc2.order).map((tc) => tc.decl);

        const resv = `(declare-const @smtres@ Result@${rrtype})`;
        const call = argscall.length !== 0 ? `(${bodyemitter.invokenameToSMT(entrypoint.key)} ${argscall.join(" ")})` : bodyemitter.invokenameToSMT(entrypoint.key);
        const cassert = `(assert (= @smtres@ ${call}))`;

        const bmcchk = `(assert (not (and (is-result_error@${rrtype} @smtres@) (is-result_bmc (result_error_code@${rrtype} @smtres@)))))`

        let chk = errorcheck ? `(assert (is-result_error@${rrtype} @smtres@))` : `(assert (not (is-result_error@${rrtype} @smtres@)))`;

        if(entrypoint.preconditions.length !== 0) {
            const eid = bodyemitter.getErrorIds(entrypoint.sourceLocation)[0];
            const excludepreid = `(= (error_id (result_error_code@${rrtype} @smtres@)) ${eid})`;

            chk = chk + "\n" + `(assert (or (not (is-result_error (result_error_code@${rrtype} @smtres@))) (not ${excludepreid})))`;
        }

        const callinfo = resv + "\n" + cassert + "\n" + bmcchk + "\n" + chk;

        return {
            typedecls_fwd: typedecls_fwd.sort().join("\n    "),
            typedecls: typedecls.sort().join("\n    "),
            conceptSubtypeRelation: conceptSubtypes.sort().join("\n"),
            typechecks: typechecks.join("\n    "),
            fixedtupledecls_fwd: fixedtupledecls_fwd.sort().join("\n    "),
            fixedtupledecls: fixedtupledecls.sort().join("\n    "),
            fixedrecorddecls_fwd: fixedrecorddecls_fwd.sort().join("\n    "),
            fixedrecorddecls: fixedrecorddecls.sort().join("\n    "),
            resultdecls_fwd: resultdecls_fwd.sort().join("\n    "),
            resultdecls: resultdecls.sort().join("\n    "),
            function_decls: funcdecls.join("\n"),
            args_info: argsdecls.join("\n"),
            main_info: callinfo
        };
    }
}

export {
    SMTEmitter
};
