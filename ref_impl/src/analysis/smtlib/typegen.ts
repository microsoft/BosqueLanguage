//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { MIRAssembly, MIRType, MIRTypeOption, MIREntityType, MIREntityTypeDecl, MIRTupleType, MIRRecordType, MIRNominalType, MIRConceptType } from "../../compiler/mir_assembly";
import { smtsanizite, BuiltinTypes, BuiltinTypeEmit } from "./builtins";

class SMTTypeGenerator {
    readonly assembly: MIRAssembly;

    readonly noneType: MIRType;
    readonly boolType: MIRType;
    readonly intType: MIRType;
    readonly stringType: MIRType;
    readonly anyType: MIRType;

    private structuraltypecheckdecls: string[] = [];

    constructor(assembly: MIRAssembly) {
        this.assembly = assembly;

        this.noneType = this.assembly.typeMap.get("NSCore::None") as MIRType;
        this.boolType = this.assembly.typeMap.get("NSCore::Bool") as MIRType;
        this.intType = this.assembly.typeMap.get("NSCore::Int") as MIRType;
        this.stringType = this.assembly.typeMap.get("NSCore::String") as MIRType;
        this.anyType = this.assembly.typeMap.get("NSCore::Any") as MIRType;
    }

    isTypeExact(type: MIRType | MIRTypeOption): boolean {
        if (type instanceof MIRType) {
            return type.options.length === 1 && this.isTypeExact(type.options[0]);
        }

        if (type instanceof MIREntityType) {
            const tdecl = this.assembly.entityDecls.get(type.ekey) as MIREntityTypeDecl;
            return [...tdecl.terms].every((etype) => this.isTypeExact(etype[1]));
        }
        else if (type instanceof MIRTupleType) {
            return !type.isOpen && type.entries.every((entry) => !entry.isOptional && this.isTypeExact(entry.type));
        }
        else if (type instanceof MIRRecordType) {
            return !type.isOpen && type.entries.every((entry) => !entry.isOptional && this.isTypeExact(entry.type));
        }
        else {
            return false;
        }
    }

    static getExactTypeFrom(from: MIRType | MIRTypeOption): MIRTypeOption {
        return (from instanceof MIRType) ? from.options[0] : from;
    }

    typeToSMT2Type(type: MIRType | MIRTypeOption): string {
        if (!this.isTypeExact(type)) {
            return "BTerm";
        }
        else {
            const topt = (type instanceof MIRType) ? type.options[0] : type;
            if (topt instanceof MIREntityType) {
                const tdecl = this.assembly.entityDecls.get(topt.ekey) as MIREntityTypeDecl;
                if (tdecl.ns === "NSCore" && (tdecl.name === "Bool" || tdecl.name === "Int" || tdecl.name === "String")) {
                    return tdecl.name;
                }
                else {
                    return "T" + smtsanizite(topt.trkey);
                }
            }
            else if (topt instanceof MIRTupleType) {
                const entryinfos = topt.entries.map((e) => this.typeToSMT2Type(e.type));
                return `Tbsq_tuple$_${entryinfos.join("$")}_$`;
            }
            else {
                assert(topt instanceof MIRRecordType);

                const entryinfos = (topt as MIRRecordType).entries.map((e) => `${this.propertyToSMT2Name(e.name)}@${this.typeToSMT2Type(e.type)}`);
                return `Tbsq_record$_${entryinfos.join("")}_$`;
            }
        }
    }

    typeToSMT2Constructor(type: MIRType | MIRTypeOption): string {
        assert(this.isTypeExact(type));

        const topt = (type instanceof MIRType) ? type.options[0] : type;
        if (topt instanceof MIREntityType) {
            return smtsanizite(topt.trkey);
        }
        else if (topt instanceof MIRTupleType) {
            const entryinfos = topt.entries.map((e) => this.typeToSMT2Type(e.type));
            return `bsq_tuple$_${entryinfos.join("$")}_$`;
        }
        else {
            assert(topt instanceof MIRRecordType);

            const entryinfos = (topt as MIRRecordType).entries.map((e) => `${this.propertyToSMT2Name(e.name)}@${this.typeToSMT2Type(e.type)}`);
            return `bsq_tuple$_${entryinfos.join("")}_$`;
        }
    }

    propertyToSMT2Name(pname: string): string {
        return pname;
    }

    generateTypeDecl(type: MIRType, typedecls: string[], consdecls: [string, string?][]) {
        if (this.isTypeExact(type)) {
            const topt = type.options[0];
            if (topt instanceof MIREntityType) {
                const edecl = this.assembly.entityDecls.get(topt.ekey) as MIREntityTypeDecl;
                if (edecl.ns === "NSCore" && (edecl.name === "None" || edecl.name === "Bool" || edecl.name === "Int" || edecl.name === "String")) {
                    //don't need to do anything as these are special cases
                }
                else if (edecl.isCollectionEntityType || edecl.isMapEntityType) {
                    typedecls.push(`(${this.typeToSMT2Type(topt)} 0)`);
                    consdecls.push((BuiltinTypes.get(edecl.name) as BuiltinTypeEmit)(this.typeToSMT2Constructor(topt), this.typeToSMT2Type(edecl.terms.get("T") as MIRType)));
                }
                else {
                    typedecls.push(`(${this.typeToSMT2Type(topt)} 0)`);

                    const tpfx = this.typeToSMT2Constructor(topt);
                    const entries: string[] = [];
                    for (let i = 0; i < edecl.fields.length; ++i) {
                        const ftype = this.assembly.typeMap.get(edecl.fields[i].declaredType) as MIRType;
                        entries.push(`(${tpfx}@${edecl.fields[i].name} ${this.typeToSMT2Type(ftype)})`);
                    }

                    consdecls.push([`((${tpfx} ${entries.join(" ")}))`]);
                }
            }
            else if (topt instanceof MIRTupleType ) {
                typedecls.push(`(${this.typeToSMT2Type(topt)} 0)`);

                const tpfx = this.typeToSMT2Constructor(topt);
                const entries: string[] = [];
                for (let i = 0; i < topt.entries.length; ++i) {
                    entries.push(`(${tpfx}@${i} ${this.typeToSMT2Type(topt.entries[i].type)})`);
                }

                consdecls.push([`((${tpfx} ${entries.join(" ")}))`]);
            }
            else if (topt instanceof MIRRecordType) {
                typedecls.push(`(${this.typeToSMT2Type(topt)} 0)`);

                const tpfx = this.typeToSMT2Constructor(topt);
                const entries: string[] = [];
                for (let i = 0; i < topt.entries.length; ++i) {
                    entries.push(`(${tpfx}@${topt.entries[i].name} ${this.typeToSMT2Type(topt.entries[i].type)})`);
                }

                consdecls.push([`((${tpfx} ${entries.join(" ")}))`]);
            }
            else {
                //don't need to do anything
            }
        }
    }

    private addTypeOfDecl(decl: string) {
        if (!this.structuraltypecheckdecls.includes(decl)) {
            this.structuraltypecheckdecls.push(decl);
        }
    }

    generateTypeOf_Tuple(arg: string, oftype: MIRTupleType): string {
        const ecdecl = `
            (define-fun typecheck@${smtsanizite(oftype.trkey)}@0 ((tuparr (Array Int BTerm))) Bool)
                ${this.generateTypeOfCall(`(select tuparr ${oftype.entries.length - 1})`, this.anyType, oftype.entries[oftype.entries.length - 1].type)}
            )
            `;
        this.addTypeOfDecl(ecdecl);

        for (let i = 1; i < oftype.entries.length; ++i) {
            const isubtype = this.generateTypeOfCall(`(select tuparr ${oftype.entries.length - (i + 1)})`, this.anyType, oftype.entries[oftype.entries.length - (i + 1)].type);
            const rdecl = `
            (define-fun typecheck@${smtsanizite(oftype.trkey)}@${i} ((tuparr (Array Int BTerm))) Bool)
                (and ${isubtype} (typecheck@${smtsanizite(oftype.trkey)}@${i - 1} tuparr))
            )
            `;
            this.addTypeOfDecl(rdecl);
        }

        const reqentries = (oftype.entries.some((e) => e.isOptional)) ? oftype.entries.findIndex((e) => e.isOptional) : oftype.entries.length;
        if (oftype.isOpen) {
            const tcdecl = `
            (define-fun typecheck@${smtsanizite(oftype.trkey)} ((tup BTerm)) Bool)
                (and (is-bsq_term_tuple ${arg}) (>= (bsq_term_tuple_size ${arg}) ${reqentries}) (typecheck@${smtsanizite(oftype.trkey)}@${oftype.entries.length - 1} (bsq_term_tuple_entries tup)))
            )
            `;
            this.addTypeOfDecl(tcdecl);

            return `(typecheck@${smtsanizite(oftype.trkey)} ${arg})`;
        }
        else {
            const tcdecl = `
            (define-fun typecheck@${smtsanizite(oftype.trkey)} ((tup BTerm)) Bool)
                (and (is-bsq_term_tuple ${arg}) (>= (bsq_term_tuple_size ${arg}) ${reqentries}) (<= (bsq_term_tuple_size ${arg}) ${oftype.entries.length}) (typecheck@${smtsanizite(oftype.trkey)}@${oftype.entries.length - 1} (bsq_term_tuple_entries tup)))
            )
            `;
            this.addTypeOfDecl(tcdecl);

            return `(typecheck@${smtsanizite(oftype.trkey)} ${arg})`;
        }
    }

    generateTypeOf_Record(arg: string, oftype: MIRRecordType): string {
        assert(false);
        //Need to have (Array String Bool) global arrays for record types to count covered requred properties -- values will also need to know their properties
        return "[NOT IMPLEMENTED]";
    }

    generateTypeOf_Nominal(arg: string, oftype: MIRNominalType): string {
        if (oftype.trkey === "NSCore::Any") {
            return "true";
        }
        else if (oftype.trkey === "NSCore::Some") {
            return `(not (= ${arg} bsq_term_none))`;
        }
        else if (oftype.trkey === "NSCore::Tuple") {
            return `(is-bsq_term_tuple ${arg})`;
        }
        else if (oftype.trkey === "NSCore::Record") {
            return `(is-bsq_term_record ${arg})`;
        }
        else if (oftype.trkey === "NSCore::Object") {
            return `(or (is-bsq_term_entity ${arg}) (is-bsq_term_list ${arg}))`;
        }
        else {
            return `(and (is-bsq_term_entity ${arg}) (typecheck@${smtsanizite(oftype.trkey)} (bsq_term_entity_type ${arg}))`;
        }
    }

    generateTypeOf_Collection(arg: string, oftype: MIREntityType): string {
        return `(and (is-bsq_term_list ${arg}) (typecheck@${smtsanizite(oftype.trkey)} (bsq_term_list_type ${arg}))`;
    }

    generateTypeOfCall(arg: string, argtype: MIRType, oftype: MIRType): string {
        if (this.isTypeExact(argtype)) {
            return this.assembly.subtypeOf(argtype, oftype) ? "true" : "false";
        }
        else {
            if (this.assembly.subtypeOf(argtype, oftype)) {
                return "true";
            }

            let opts: string[] = [];
            for (let i = 0; i < oftype.options.length; ++i) {
                const topt = oftype.options[i];

                if (this.assembly.subtypeOf(this.noneType, MIRType.createSingle(topt)) && this.assembly.subtypeOf(this.noneType, argtype)) {
                    opts.push(`(= ${arg} bsq_term_none)`);
                }
                else if (this.assembly.subtypeOf(this.boolType, MIRType.createSingle(topt)) && this.assembly.subtypeOf(this.boolType, argtype)) {
                    opts.push(`(is-bsq_term_bool ${arg})`);
                }
                else if (this.assembly.subtypeOf(this.intType, MIRType.createSingle(topt)) && this.assembly.subtypeOf(this.intType, argtype)) {
                    opts.push(`(is-bsq_term_int ${arg})`);
                }
                else if (this.assembly.subtypeOf(this.stringType, MIRType.createSingle(topt)) && this.assembly.subtypeOf(this.stringType, argtype)) {
                    opts.push(`(is-bsq_term_string ${arg})`);
                }
                else if (topt instanceof MIRTupleType) {
                    const tupchk = this.generateTypeOf_Tuple(arg, topt);
                    opts.push(tupchk);
                }
                else if (topt instanceof MIRRecordType) {
                    const recchk = this.generateTypeOf_Record(arg, topt);
                    opts.push(recchk);
                }
                else {
                    if (topt instanceof MIREntityType && (this.assembly.entityDecls.get(topt.ekey) as MIREntityTypeDecl).isCollectionEntityType) {
                        const cchk = this.generateTypeOf_Collection(arg, topt);
                        opts.push(cchk);
                    }
                    else {
                        const nchk = this.generateTypeOf_Nominal(arg, topt);
                        opts.push(nchk);
                    }
                }
            }

            return (opts.length > 1) ? `(and ${opts.join(" ")})` : opts[0];
        }
    }

    generateNominalTypeDecls(): string {
        let nsubf: string[] = [];

        const skipconcepts = ["NSCore::Any", "NSCore::Some", "NSCore::Tuple", "NSCore::Record", "NSCore::Object"];

        this.assembly.entityDecls.forEach((edcl, ekey) => {
            const etype = MIRType.createSingle(MIREntityType.create(ekey));
            let subts: MIRType[] = [];

            this.assembly.entityDecls.forEach((sdecl, skey) => {
                const stype = MIRType.createSingle(MIREntityType.create(skey));
                if (this.assembly.subtypeOf(stype, etype)) {
                    subts.push(stype);
                }
            });

            let cexps = subts.map((t) => `(= arg "${t.trkey}")`);
            const chk = `(define-fun typecheck@${smtsanizite(ekey)} ((arg String)) Bool
                ${cexps.length !== 1 ? `(or ${cexps.join(" ")})` : cexps[0]}
            )`;
            nsubf.push(chk);
        });

        this.assembly.conceptDecls.forEach((cdcl, ckey) => {
            if (skipconcepts.includes(ckey)) {
                return;
            }

            const ctype = MIRType.createSingle(MIRConceptType.create([ckey]));
            let subts: MIRType[] = [];

            this.assembly.entityDecls.forEach((sdecl, skey) => {
                const stype = MIRType.createSingle(MIREntityType.create(skey));
                if (this.assembly.subtypeOf(stype, ctype)) {
                    subts.push(stype);
                }
            });

            this.assembly.conceptDecls.forEach((sdecl, skey) => {
                const stype = MIRType.createSingle(MIREntityType.create(skey));
                if (this.assembly.subtypeOf(stype, ctype)) {
                    subts.push(stype);
                }
            });

            let cexps = subts.map((t) => `(= arg "${t.trkey}")`);
            const chk = `(define-fun typecheck@${smtsanizite(ckey)} ((arg String)) Bool
                ${cexps.length !== 1 ? `(or ${cexps.join(" ")})` : cexps[0]}
            )`;
            nsubf.push(chk);
        });

        return nsubf.join("\n\n");
    }

    generateStructuralTypeDecls(): string {
        return this.structuraltypecheckdecls.join("\n\n");
    }
}

export {
    SMTTypeGenerator
};
