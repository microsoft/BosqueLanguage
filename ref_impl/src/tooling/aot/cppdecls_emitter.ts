//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRRecordType, MIRInvokeDecl, MIRConstantDecl, MIREntityTypeDecl, MIRFieldDecl, MIRInvokeBodyDecl } from "../../compiler/mir_assembly";
import { CPPTypeEmitter } from "./cpptype_emitter";
import { CPPBodyEmitter } from "./cppbody_emitter";
import { constructCallGraphInfo } from "../../compiler/mir_callg";
import { extractMirBodyKeyPrefix, extractMirBodyKeyData, MIRInvokeKey, MIRConstantKey, MIRNominalTypeKey, MIRFieldKey } from "../../compiler/mir_ops";

import * as assert from "assert";

type CPPCode = {
    typedecls_fwd: string,
    typedecls: string,
    nominalenums: string,
    conceptSubtypeRelation: string,
    typechecks: string,
    funcdecls_fwd: string,
    funcdecls: string,
    conststring_declare: string,
    conststring_create: string,
    constint_declare: string,
    constint_create: string,
    propertyenums: string,
    propertynames: string,
    known_property_lists_declare: string,
    vfield_decls: string,
    vmethod_decls: string,
    maincall: string
};

class CPPEmitter {
    static emit(assembly: MIRAssembly, entrypointname: string): CPPCode {
        const typeemitter = new CPPTypeEmitter(assembly);
        typeemitter.initializeConceptSubtypeRelation();

        const bodyemitter = new CPPBodyEmitter(assembly, typeemitter);

        let typedecls_fwd: string[] = [];
        let typedecls: string[] = [];
        let nominalenums: string[] = [];
        assembly.entityDecls.forEach((edecl) => {
            const cppdecl = typeemitter.generateCPPEntity(edecl);
            if (cppdecl !== undefined) {
                typedecls_fwd.push(cppdecl.fwddecl);
                typedecls.push(cppdecl.fulldecl);
            }

            if(!typeemitter.isSpecialRepType(edecl)) {
                nominalenums.push(typeemitter.mangleStringForCpp(edecl.tkey));
            }
        });

        const cginfo = constructCallGraphInfo(assembly.entryPoints, assembly);
        const rcg = [...cginfo.topologicalOrder].reverse();

        let funcdecls_fwd: string[] = [];
        let funcdecls: string[] = [];
        for (let i = 0; i < rcg.length; ++i) {
            const bbup = rcg[i];
            const tag = extractMirBodyKeyPrefix(bbup.invoke);
            //
            //TODO: rec is implmented via stack recusion -- want to add option for bounded stack version
            //

            if (tag === "invoke") {
                const ikey = extractMirBodyKeyData(bbup.invoke) as MIRInvokeKey;
                const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
                const finfo = bodyemitter.generateCPPInvoke(idcl);

                funcdecls_fwd.push(finfo.fwddecl);
                funcdecls.push(finfo.fulldecl);
            }
            else if (tag === "pre") {
                const ikey = extractMirBodyKeyData(bbup.invoke) as MIRInvokeKey;
                const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
                const finfo = bodyemitter.generateCPPPre(bbup.invoke, idcl);

                funcdecls.push(finfo);
            }
            else if (tag === "post") {
                const ikey = extractMirBodyKeyData(bbup.invoke) as MIRInvokeKey;
                const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
                const finfo = bodyemitter.generateCPPPost(bbup.invoke, idcl);

                funcdecls.push(finfo);
            }
            else if (tag === "invariant") {
                const edcl = assembly.entityDecls.get(extractMirBodyKeyData(bbup.invoke) as MIRNominalTypeKey) as MIREntityTypeDecl;
                const finfo = bodyemitter.generateCPPInv(bbup.invoke, edcl);

                funcdecls.push(finfo);
            }
            else if (tag === "const") {
                const cdcl = assembly.constantDecls.get(extractMirBodyKeyData(bbup.invoke) as MIRConstantKey) as MIRConstantDecl;
                const finfo = bodyemitter.generateCPPConst(bbup.invoke, cdcl);

                if (finfo !== undefined) {
                    funcdecls_fwd.push(finfo.fwddecl);
                    funcdecls.push(finfo.fulldecl);
                }
            }
            else {
                assert(tag === "fdefault");
                const fdcl = assembly.fieldDecls.get(extractMirBodyKeyData(bbup.invoke) as MIRFieldKey) as MIRFieldDecl;
                const finfo = bodyemitter.generateCPPFDefault(bbup.invoke, fdcl);

                if (finfo !== undefined) {
                    funcdecls_fwd.push(finfo.fwddecl);
                    funcdecls.push(finfo.fulldecl);
                }
            }
        }

        let conceptSubtypes: string[] = [];
        typeemitter.conceptSubtypeRelation.forEach((stv, cpt) => {
            const nemums = stv.map((ek) => `MIRNominalTypeEnum::${typeemitter.mangleStringForCpp(ek)}`).sort();
            const sta = `constexpr MIRNominalTypeEnum MIRConceptSubtypeArray__${typeemitter.mangleStringForCpp(cpt)}[${nemums.length}] = {${nemums.join(", ")}};`;

            conceptSubtypes.push(sta);
        });

        const typechecks = [...bodyemitter.subtypeFMap].map(tcp => tcp[1]).sort((tc1, tc2) => tc1.order - tc2.order).map((tc) => tc.decl);
        
        let conststring_declare: string[] = [];
        let conststring_create: string[] = [];
        bodyemitter.allConstStrings.forEach((v, k) => {
            conststring_declare.push(`static BSQString ${v};`);
            conststring_create.push(`BSQString Runtime::${v}(${k}, 1);`);
        });

        let constint_declare: string[] = [];
        let constint_create: string[] = [];
        bodyemitter.allConstBigInts.forEach((v, k) => {
            constint_declare.push(`static BSQInt ${v};`);
            constint_create.push(`BSQInt Runtime::${v}(BigInt(${k}));`);
        });

        let propertyenums: Set<string> = new Set<string>();
        let propertynames: Set<string> = new Set<string>();
        let known_property_lists_declare: string[] = [];
        bodyemitter.allPropertyNames.forEach((pname) => {
            propertyenums.add(pname);
            propertynames.add(`"${pname}"`);
        });
        assembly.typeMap.forEach((tt) => {
            tt.options.forEach((topt) => {
                if (topt instanceof MIRRecordType) {
                    topt.entries.forEach((entry) => {
                        propertyenums.add(entry.name);
                        propertynames.add(`"${entry.name}"`);
                    });
                }

                if (typeemitter.isKnownLayoutRecordType(tt)) {
                    const knownrec = CPPTypeEmitter.getKnownLayoutRecordType(tt);
                    const knownenum = knownrec.entries.map((entry) => `MIRPropertyEnum::${entry.name}`);

                    const decl = `constexpr MIRPropertyEnum ${typeemitter.getKnownPropertyRecordArrayName(tt)}[${knownrec.entries.length}] = {${knownenum.join(", ")}};`
                    if (knownrec.entries.length !== 0 && !known_property_lists_declare.includes(decl)) {
                        known_property_lists_declare.push(decl);
                    }
                }
            });
        });

        const entrypoint = assembly.invokeDecls.get(entrypointname) as MIRInvokeBodyDecl;
        const restype = typeemitter.getMIRType(entrypoint.resultType);
        const mainsig = `int main(int argc, char** argv)`;
        const chkarglen = `    if(argc != ${entrypoint.params.length} + 1) { fprintf(stderr, "Expected ${entrypoint.params.length} arguments but got %i\\n", argc - 1); exit(1); }`;
        const convdecl = "    std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;";
        const convargs = entrypoint.params.map((p, i) => {
            if(p.type === "NSCore::Bool") {
                const fchk = `if(std::string(argv[${i}+1]) != "true" && std::string(argv[${i}+1]) != "false") { fprintf(stderr, "Bad argument for ${p.name} -- expected Bool got %s\\n", argv[${i}+1]); exit(1); }`;
                const conv = `bool ${p.name} = std::string(argv[${i}+1]) == "true";`;
                return "    " + fchk + "\n    " + conv;
            }
            else if(p.type === "NSCore::Int") {
                const fchk = `if(!std::regex_match(std::string(argv[${i}+1]), std::regex("^([+]|[-])?[0-9]{1,8}$"))) { fprintf(stderr, "Bad argument for ${p.name} -- expected (small) Int got %s\\n", argv[${i}+1]); exit(1); }`;
                const conv = `BSQInt ${p.name}(std::stoi(std::string(argv[${i}+1])));`;
                return "    \n    " + fchk + "\n    " + conv;
            } 
            else  {
                const conv = `BSQString ${p.name}(argv[${i}+1], 1);`;
                return "    " + conv;
            }
        });

        let scopev = "";
        let callargs = entrypoint.params.map((p) => p.type !== "NSCore::String" ? p.name : `&${p.name}`);
        if(typeemitter.maybeRefableCountableType(restype)) {
            if (typeemitter.maybeRefableCountableType(restype)) {
                if (typeemitter.isTupleType(restype)) {
                    const maxlen = CPPTypeEmitter.getTupleTypeMaxLength(restype);
                    scopev = `BSQRefScope<${maxlen}> __scopes__;`;
                    for (let i = 0; i < maxlen; ++i) {
                        callargs.push(`__scopes__.getCallerSlot<${i}>()`);
                    }
                }
                else if (typeemitter.isRecordType(restype)) {
                    const allprops = CPPTypeEmitter.getRecordTypeMaxPropertySet(restype);
                    scopev = `BSQRefScope<${allprops.length}> __scopes__;`;
                    for (let i = 0; i < allprops.length; ++i) {
                        callargs.push(`__scopes__.getCallerSlot<${i}>()`);                }
                }
                else {
                    scopev = "BSQRefScope<1> __scopes__;";
                    callargs.push("__scopes__.getCallerSlot<0>()");
                }
            }
        }
        
        typeemitter.scopectr = 0;
        const callv = `${bodyemitter.invokenameToCPP(entrypointname)}(${callargs.join(", ")})`;
        const fcall = `std::cout << conv.to_bytes(Runtime::diagnostic_format(${typeemitter.coerce(callv, restype, typeemitter.anyType)})) << "\\n"`;

        if(typeemitter.scopectr !== 0) {
            const scopevar = bodyemitter.varNameToCppName("$scope$");
            const refscope = `BSQRefScope<${typeemitter.scopectr}> ${scopevar};`;

            scopev = scopev + " " + refscope;
        }

        const maincall = `${mainsig} {\n${chkarglen}\n\n${convdecl}\n${convargs.join("\n")}\n\n  try {\n    ${scopev}\n    ${fcall};\n    fflush(stdout);\n    return 0;\n  } catch (BSQAbort& abrt) HANDLE_BSQ_ABORT(abrt) \n}\n`;

        return {
            typedecls_fwd: typedecls_fwd.sort().join("\n"),
            typedecls: typedecls.sort().join("\n"),
            nominalenums: nominalenums.sort().join(",\n    "),
            conceptSubtypeRelation: conceptSubtypes.sort().join("\n"),
            typechecks: typechecks.join("\n"),
            funcdecls_fwd: funcdecls_fwd.join("\n"),
            funcdecls: funcdecls.join("\n"),
            conststring_declare: conststring_declare.sort().join("\n  "),
            conststring_create: conststring_create.sort().join("\n  "),
            constint_declare: constint_declare.sort().join("\n  "),
            constint_create: constint_create.sort().join("\n  "),
            propertyenums: [...propertyenums].sort().join(",\n  "),
            propertynames: [...propertynames].sort().join(",\n  "),
            known_property_lists_declare: known_property_lists_declare.sort().join("\n"),
            vfield_decls: "//NOT IMPLEMENTED YET -- NEED TO UPDATE MIR TO DO EXACT V-FIELD RESOLUTION",
            vmethod_decls: "//NOT IMPLEMENTED YET -- NEED TO UPDATE MIR TO DO EXACT V-METHOD RESOLUTION",
            maincall: maincall
        };
    }
}

export {
    CPPEmitter
};
