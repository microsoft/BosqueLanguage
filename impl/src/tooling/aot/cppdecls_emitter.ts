//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRRecordType, MIRInvokeDecl, MIRInvokeBodyDecl, MIREphemeralListType, MIREntityTypeDecl, MIRType, MIREntityType, MIRConceptType, MIRTupleType, MIRConceptTypeDecl } from "../../compiler/mir_assembly";
import { CPPTypeEmitter } from "./cpptype_emitter";
import { CPPBodyEmitter } from "./cppbody_emitter";
import { constructCallGraphInfo } from "../../compiler/mir_callg";

type CPPCode = {
    STATIC_STRING_DECLARE: string,
    STATIC_STRING_CREATE: string,

    STATIC_INT_DECLARE: string,
    STATIC_INT_CREATE: string,
    
    TYPEDECLS_FWD: string,
    TYPEDECLS: string,
    EPHEMERAL_LIST_DECLARE: string,

    PROPERTY_ENUM_DECLARE: string, 
    NOMINAL_TYPE_ENUM_DECLARE: string,

    PROPERTY_NAMES: string,
    NOMINAL_TYPE_DISPLAY_NAMES: string,

    CONCEPT_SUBTYPE_RELATION_DECLARE: string,
    NOMINAL_TYPE_TO_DATA_KIND: string,

    SPECIAL_NAME_BLOCK_BEGIN: string,

    VFIELD_ACCESS: string,
    
    TYPECHECKS: string,
    FUNC_DECLS_FWD: string,
    FUNC_DECLS: string,

    MAIN_CALL: string
};

function getDepFromType(root: MIRType, tt: MIRType, typeemitter: CPPTypeEmitter, deps: Set<string>) {
    tt.options.map((opt) => {
        if (opt instanceof MIREntityType) {
            const edcl = typeemitter.assembly.entityDecls.get(opt.ekey) as MIREntityTypeDecl;
            edcl.provides.forEach((pv) => getDepFromType(root, typeemitter.getMIRType(pv), typeemitter, deps));
            edcl.terms.forEach((v) => getDepFromType(root, v, typeemitter, deps));
            edcl.fields.forEach((fd) => getDepFromType(root, typeemitter.getMIRType(fd.declaredType), typeemitter, deps));

            if(root.trkey !== opt.trkey) {
                deps.add(opt.trkey);
            }
        }
        else if (opt instanceof MIRConceptType) {
            return opt.ckeys.forEach((cc) => {
                const cpt = typeemitter.assembly.conceptDecls.get(cc) as MIRConceptTypeDecl;
                cpt.provides.forEach((pv) => getDepFromType(root, typeemitter.getMIRType(pv), typeemitter, deps));
                cpt.terms.forEach((v) => getDepFromType(root, v, typeemitter, deps));
            });
        }
        else if (opt instanceof MIRTupleType) {
            return opt.entries.forEach((entry) => getDepFromType(root, entry.type, typeemitter, deps));
        }
        else {
            return (opt as MIRRecordType).entries.forEach((entry) => getDepFromType(root, entry.type, typeemitter, deps));
        }
    });
}

function getDepOn(dcl: MIREntityTypeDecl, typeemitter: CPPTypeEmitter): Set<string> {
    const deps = new Set<string>();
    getDepFromType(typeemitter.getMIRType(dcl.tkey), typeemitter.getMIRType(dcl.tkey), typeemitter, deps);

    return deps;
}

function depOrderSingle(decls: {name: string, decl: string, deps: Set<string>, ops: string[]}[], cdecl: {name: string, decl: string, deps: Set<string>, ops: string[]}, order: {name: string, decl: string,ops: string[]}[]) {
    if(order.find((dc) => dc.name === cdecl.name) !== undefined) {
        return; //already in the order
    }

    //insert all my deps
    cdecl.deps.forEach((dep) => {
        const ddcl = decls.find((dc) => dc.name === dep);
        if(ddcl !== undefined) {
            depOrderSingle(decls, ddcl, order);
        }
    });

    order.push({name: cdecl.name, decl: cdecl.decl, ops: cdecl.ops});
}

function depOrderDecls(alldecls: {name: string, decl: string, deps: Set<string>, ops: string[]}[]): {decl: string, ops: string[]}[] {
    let res: {name: string, decl: string, ops: string[]}[] = [];

    for (let i = 0; i < alldecls.length; ++i) {
        const dcl = alldecls[i];
        depOrderSingle(alldecls, dcl, res);
    }

    return res.map((rr) => { return {decl: rr.decl, ops: rr.ops} });
}

class CPPEmitter {
    static emit(assembly: MIRAssembly, entrypointname: string): CPPCode {
        const typeemitter = new CPPTypeEmitter(assembly);
        typeemitter.initializeConceptSubtypeRelation();

        const bodyemitter = new CPPBodyEmitter(assembly, typeemitter);
        
        let typedecls_fwd: string[] = [];
        let itypedecls: {name: string, decl: string, deps: Set<string>, ops: string[]}[] = [];
        let nominaltypeinfo: {enum: string, display: string, datakind: string}[] = [];
        let vfieldaccesses: string[] = [];
        [...assembly.entityDecls]
        .sort((a, b) => a[0].localeCompare(b[0]))
        .map((ee) => ee[1])
        .forEach((edecl) => {
            const cppdecl: any = typeemitter.generateCPPEntity(edecl);
            const deps = getDepOn(edecl, typeemitter);
            if (cppdecl !== undefined) {
                if(cppdecl.isref) {
                    const refdecl = cppdecl as { fwddecl: string, fulldecl: string };
                    typedecls_fwd.push(refdecl.fwddecl);
                    itypedecls.push({name: edecl.tkey, decl: refdecl.fulldecl, deps: deps, ops: []});
                }
                else {
                    const structdecl = cppdecl as { fwddecl: string, fulldecl: string, boxeddecl: string, ops: string[] };

                    typedecls_fwd.push(structdecl.fwddecl);
                    itypedecls.push({name: edecl.tkey, decl: structdecl.fulldecl + structdecl.ops.join("\n"), deps: deps, ops: []});
                    itypedecls.push({name: `BOXED_${edecl.tkey}`, decl: structdecl.boxeddecl, deps: deps, ops: []});

                    //
                    //TODO: buildup ops for unions as well later
                    //
                }
            }

            const ereprk = typeemitter.getCPPReprFor(typeemitter.getMIRType(edecl.tkey));
            const enumv = `${typeemitter.mangleStringForCpp(edecl.tkey)} = BUILD_MIR_NOMINAL_TYPE(${ereprk.categoryinfo}, ${nominaltypeinfo.length + 1})`;
            const displayv = `"${edecl.tkey}"`;
            const dk = typeemitter.generateInitialDataKindFlag(typeemitter.getMIRType(edecl.tkey));

            nominaltypeinfo.push({ enum: enumv, display: displayv, datakind: dk });

            edecl.fields.forEach((fd) => {
                if (fd.enclosingDecl !== edecl.tkey) {
                    const rftype = typeemitter.getCPPReprFor(typeemitter.getMIRType(fd.declaredType)).std;
                    const isig = `virtual ${rftype} get$${typeemitter.mangleStringForCpp(fd.fkey)}() { printf("%s\\n", "Bad v-field resolve -- ${fd.fkey}"); exit(1); ${rftype} res; return res; }`;

                    if (!vfieldaccesses.includes(isig)) {
                        vfieldaccesses.push(isig);
                    }
                }
            });
        });
        let typedecls = depOrderDecls(itypedecls);

        let concepttypeinfo: {enum: string, display: string, datakind: string}[] = [];
        [...assembly.conceptDecls]
        .sort((a, b) => a[0]
        .localeCompare(b[0])).map((ce) => ce[1])
        .forEach((cdecl) => {
            const enumv = `${typeemitter.mangleStringForCpp(cdecl.tkey)} = BUILD_MIR_NOMINAL_TYPE(MIRNominalTypeEnum_Category_Empty, ${concepttypeinfo.length + nominaltypeinfo.length + 1})`;
            const displayv = `"${cdecl.tkey}"`;
            concepttypeinfo.push({ enum: enumv, display: displayv, datakind: "-1" });
        });
        
        const cginfo = constructCallGraphInfo(assembly.entryPoints, assembly);
        const rcg = [...cginfo.topologicalOrder].reverse();

        let funcdecls_fwd: string[] = [];
        let funcdecls: string[] = [];
        for (let i = 0; i < rcg.length; ++i) {
            const ikey = rcg[i].invoke;
            //
            //TODO: rec is implmented via stack recusion -- want to add option for bounded stack version
            //

            const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
            const finfo = bodyemitter.generateCPPInvoke(idcl);

            funcdecls_fwd.push(finfo.fwddecl);
            funcdecls.push(finfo.fulldecl);
        }

        let conceptSubtypes: string[] = [];
        typeemitter.conceptSubtypeRelation.forEach((stv, cpt) => {
            const nemums = stv.map((ek) => `MIRNominalTypeEnum::${typeemitter.mangleStringForCpp(ek)}`).sort();
            if (nemums.length !== 0) {
                const sta = `constexpr MIRNominalTypeEnum MIRConceptSubtypeArray__${typeemitter.mangleStringForCpp(cpt)}[${nemums.length}] = {${nemums.join(", ")}};`;
                conceptSubtypes.push(sta);
            }
        });

        const typechecks = [...bodyemitter.subtypeFMap].map(tcp => tcp[1]).sort((tc1, tc2) => tc1.order - tc2.order).map((tc) => tc.decl);

        let special_name_decls: string[] = [];
        let ephdecls: string[] = [];
        [...typeemitter.assembly.typeMap].forEach((te) => {
            const tt = te[1];

            if(typeemitter.typecheckIsName(tt, /^NSCore::None$/) || typeemitter.typecheckIsName(tt, /^NSCore::Bool$/) || typeemitter.typecheckIsName(tt, /^NSCore::Int$/) || typeemitter.typecheckIsName(tt, /^NSCore::BigInt$/) || typeemitter.typecheckIsName(tt, /^NSCore::Float64$/) 
                    || typeemitter.typecheckIsName(tt, /^NSCore::String$/) || typeemitter.typecheckIsName(tt, /^NSCore::UUID$/) || typeemitter.typecheckIsName(tt, /^NSCore::LogicalTime$/) || typeemitter.typecheckIsName(tt, /^NSCore::CryptoHash$/) || typeemitter.typecheckIsName(tt, /^NSCore::ByteBuffer$/)
                    || typeemitter.typecheckIsName(tt, /^NSCore::ISOTime$/) || typeemitter.typecheckIsName(tt, /^NSCore::Regex$/)) {
                        special_name_decls.push(`#define MIRNominalTypeEnum_${tt.trkey.substr(8)} MIRNominalTypeEnum::${typeemitter.mangleStringForCpp(tt.trkey)}`);
                    }

            if(tt.trkey === "NSCore::Tuple" || tt.trkey === "NSCore::Record") {
                special_name_decls.push(`#define MIRNominalTypeEnum_${tt.trkey.substr(8)} MIRNominalTypeEnum::${typeemitter.mangleStringForCpp(tt.trkey)}`);
            }

            if(tt.options.length === 1 && (tt.options[0] instanceof MIREphemeralListType)) {
                const ephdecl = typeemitter.generateCPPEphemeral(tt.options[0] as MIREphemeralListType);
                ephdecls.push(ephdecl);
            }
        });

        let vfieldaccess: string[] = [];
        for(let i = 0; i < bodyemitter.vfieldLookups.length; ++i) {
            //
            //TODO: generate vfield switches
            //
        }

        //
        //TODO: need to process virtual bulk data operations -- also see SMT versions
        //
        if(bodyemitter.vfieldProjects.length !== 0 || bodyemitter.vfieldUpdates.length !== 0 || bodyemitter.vobjmerges.length !== 0) {
            console.log("NOT IMPLEMENTED -- virtual bulk operators for nominal types");
            process.exit(1);
        }

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
            });
        });

        //
        //TODO: need to provide parse for API types and link in here
        //
        const entrypoint = assembly.invokeDecls.get(entrypointname) as MIRInvokeBodyDecl;
        const restype = typeemitter.getMIRType(entrypoint.resultType);
        const mainsig = `int main(int argc, char** argv)`;
        let oprarms = 0;
        const convargs = entrypoint.params.map((p, i) => {
            let ptype = p.type;
            if(ptype.includes("NSCore::None")) {
                oprarms++;
                const ndecl = `KeyValue ${p.name} = nullptr;`;
                let ivv = "";

                ptype = p.type.replace(" | NSCore::None", "");
                if (ptype === "NSCore::Bool") {
                    const fchk = `if(std::string(argv[${i}+1]) != "true" && std::string(argv[${i}+1]) != "false") { fprintf(stderr, "Bad argument for ${p.name} -- expected Bool got %s\\n", argv[${i}+1]); exit(1); }`;
                    const conv = `${p.name} = BSQ_ENCODE_VALUE_BOOL(std::string(argv[${i}+1]) == "true");`;
                    ivv = "     {\n    " + fchk + "\n    " + conv + "\n    }";
                }
                else if (ptype === "NSCore::Int") {
                    const fchk = `if(!std::regex_match(std::string(argv[${i}+1]), std::regex("^([+]|[-])?[0-9]{1,8}$"))) { fprintf(stderr, "Bad argument for ${p.name} -- expected (small) Int got %s\\n", argv[${i}+1]); exit(1); }`;
                    const conv = `${p.name} = BSQ_ENCODE_VALUE_TAGGED_INT(std::stoi(std::string(argv[${i}+1])));`;
                    ivv = "    {\n    " + fchk + "\n    " + conv + "\n    }";
                }
                else {
                    const conv = `BSQString __arg${i + 1}__(argv[${i}+1], 1); ${p.name} = &__arg${i + 1}__;`;
                    ivv = "    {\n    " + conv + "\n    }";
                }

                return ndecl + "\n" + `if (argc > ${i} + 1)\n` + ivv;
            }
            else {
                if (ptype === "NSCore::Bool") {
                    const fchk = `if(std::string(argv[${i}+1]) != "true" && std::string(argv[${i}+1]) != "false") { fprintf(stderr, "Bad argument for ${p.name} -- expected Bool got %s\\n", argv[${i}+1]); exit(1); }`;
                    const conv = `bool ${p.name} = std::string(argv[${i}+1]) == "true";`;
                    return "    " + fchk + "\n    " + conv;
                }
                else if (ptype === "NSCore::Int") {
                    const fchk = `if(!std::regex_match(std::string(argv[${i}+1]), std::regex("^([+]|[-])?[0-9]{1,8}$"))) { fprintf(stderr, "Bad argument for ${p.name} -- expected (small) Int got %s\\n", argv[${i}+1]); exit(1); }`;
                    const conv = `int64_t ${p.name} = std::stoi(std::string(argv[${i}+1]));`;
                    return "    \n    " + fchk + "\n    " + conv;
                }
                else {
                    const conv = `BSQString ${p.name}(argv[${i}+1], 1);`;
                    return "    " + conv;
                }
            }
        });

        const chkarglen = `    if(argc > ${entrypoint.params.length} + 1 || argc < ${entrypoint.params.length} + 1 - ${oprarms}) { fprintf(stderr, "Expected ${entrypoint.params.length} arguments but got %i\\n", argc - 1); exit(1); }`;

        let scopev = "";
        const scopevar = bodyemitter.varNameToCppName("$scope$");

        let callargs = entrypoint.params.map((p) => p.type !== "NSCore::String" ? p.name : `&${p.name}`);
        const resrc = typeemitter.getRefCountableStatus(restype);
        if (resrc !== "no") {
            scopev = `BSQRefScope ${scopevar};`;
            callargs.push(scopevar);
        }        
        const callv = `${bodyemitter.invokenameToCPP(entrypointname)}(${callargs.join(", ")})`;
        const fcall = `std::cout << diagnostic_format(${typeemitter.coerce(callv, restype, typeemitter.anyType)}) << "\\n"`;

        const maincall = `${mainsig} {\n${chkarglen}\n\n${convargs.join("\n")}\n\n  try {\n    ${scopev}\n    ${fcall};\n    fflush(stdout);\n    return 0;\n  } catch (BSQAbort& abrt) HANDLE_BSQ_ABORT(abrt) \n}\n`;

        return {
            STATIC_STRING_DECLARE: conststring_declare.sort().join("\n  "),
            STATIC_STRING_CREATE: conststring_create.sort().join("\n  "),
        
            STATIC_INT_DECLARE: constint_declare.sort().join("\n  "),
            STATIC_INT_CREATE: constint_create.sort().join("\n  "),
            
            TYPEDECLS_FWD: typedecls_fwd.sort().join("\n"),
            TYPEDECLS: [...typedecls.map((tde) => tde.decl), ...(([] as string[]).concat(...typedecls.map((tde) => tde.ops)))].join("\n"),
            EPHEMERAL_LIST_DECLARE: ephdecls.sort().join("\n"),
        
            PROPERTY_ENUM_DECLARE: [...propertyenums].sort().join(",\n  "), 
            NOMINAL_TYPE_ENUM_DECLARE: [...nominaltypeinfo, ...concepttypeinfo].map((nti) => nti.enum).join(",\n    "),
        
            PROPERTY_NAMES: [...propertynames].sort().join(",\n  "),
            NOMINAL_TYPE_DISPLAY_NAMES: [...nominaltypeinfo, ...concepttypeinfo].map((nti) => `${nti.display}`).join(",\n  "),
        
            CONCEPT_SUBTYPE_RELATION_DECLARE: conceptSubtypes.sort().join("\n"),
            NOMINAL_TYPE_TO_DATA_KIND: [...nominaltypeinfo].map((nti) => nti.datakind).join(",\n    "),
        
            SPECIAL_NAME_BLOCK_BEGIN: special_name_decls.sort().join("\n"),

            VFIELD_ACCESS: vfieldaccess.sort().join("\n"),

            TYPECHECKS: typechecks.join("\n"),
            FUNC_DECLS_FWD: funcdecls_fwd.join("\n"),
            FUNC_DECLS: funcdecls.join("\n"),
        
            MAIN_CALL: maincall
        };
    }
}

export {
    CPPEmitter
};
