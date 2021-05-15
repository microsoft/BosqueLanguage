//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRConceptType, MIRConceptTypeDecl, MIREntityType, MIREntityTypeDecl, MIREphemeralListType, MIRRecordType, MIRTupleType, MIRType } from "../../../compiler/mir_assembly";
import { MIRFieldKey, MIRResolvedTypeKey } from "../../../compiler/mir_ops";

import { ICCPType, ICCPTypeEntity, ICCPTypeEphemeralList, ICCPTypeHeapUnion, ICCPTypeInlineUnion, ICCPTypeKind, ICCPTypePrimitive, ICCPTypeRecord, ICCPTypeSizeInfo, ICCPTypeTuple, RefMask, TranspilerOptions } from "./iccp_assembly";

import * as assert from "assert";

const ICCP_WORD_SIZE = 8;

const UNIVERSAL_CONCEPTS = [
    "NSCore::Any",
    "NSCore::Some",
    "NSCore::KeyType",
    "NSCore::PODType",
    "NSCore::APIValue",
    "NSCore::APIType",
    "NSCore::Object"
];

class ICCPTypeEmitter {
    readonly topts: TranspilerOptions;
    readonly assembly: MIRAssembly;
    
    private typeDataMap: Map<MIRResolvedTypeKey, ICCPType> = new Map<MIRResolvedTypeKey, ICCPType>();

    constructor(assembly: MIRAssembly, topts: TranspilerOptions, mangledNameMap?: Map<string, string>) {
        this.assembly = assembly;
        this.topts = topts;
    }

    getMIRType(tkey: MIRResolvedTypeKey): MIRType {
        return this.assembly.typeMap.get(tkey) as MIRType;
    }

    isType(tt: MIRType, tkey: string): boolean {
        return tt.trkey === tkey;
    }

    isUniqueTupleType(tt: MIRType): boolean {
        return tt.options.length === 1 && (tt.options[0] instanceof MIRTupleType) && !(tt.options[0] as MIRTupleType).entries.some((entry) => entry.isOptional);
    }

    isUniqueRecordType(tt: MIRType): boolean {
        return tt.options.length === 1 && (tt.options[0] instanceof MIRRecordType) && !(tt.options[0] as MIRRecordType).entries.some((entry) => entry.isOptional);
    }

    isUniqueEntityType(tt: MIRType): boolean {
        return tt.options.length === 1 && (tt.options[0] instanceof MIREntityType);
    }

    isUniqueEphemeralType(tt: MIRType): boolean {
        return tt.options.length === 1 && (tt.options[0] instanceof MIREphemeralListType);
    }

    isUniqueType(tt: MIRType): boolean {
        return this.isUniqueTupleType(tt) || this.isUniqueRecordType(tt) || this.isUniqueEntityType(tt) || this.isUniqueEphemeralType(tt);
    }

    isTypeLeafEntry(iccptype: ICCPType): boolean {
        return iccptype.isLeafType && (iccptype.tkind === ICCPTypeKind.Register || iccptype.tkind === ICCPTypeKind.Struct || iccptype.tkind === ICCPTypeKind.InlineUnion);
    }

    private computeStructuralTypeLayoutInfoFromTypeList(tl: ICCPType[]): [ICCPTypeSizeInfo, boolean, number, RefMask | undefined, number[]] {
        let sldatasize = 0;
        let slmask = "";

        let isleaf = true;
        let refmask: string | undefined = "";
        let ptrcount = 0;

        let toffsets: number[] = [];
        let coffset = 0;
        tl.forEach((entry, pos) => {
            sldatasize += entry.allocinfo.slfullsize;
            slmask += entry.allocinfo.slmask;

            isleaf = isleaf && this.isTypeLeafEntry(entry);
            refmask += entry.allocinfo.slmask;
            if (ptrcount !== -1) {
                if (ptrcount === pos && (entry.tkind === ICCPTypeKind.Ref || entry.tkind === ICCPTypeKind.HeapUnion)) {
                    ptrcount++;
                }
                else {
                    ptrcount = -1;
                }
            }

            toffsets.push(coffset);
            coffset += entry.allocinfo.slfullsize;
        });

        if (isleaf) {
            assert(ptrcount === 0);
            refmask = undefined;
        }
        else if (ptrcount > 0) {
            assert(!isleaf);
            refmask = undefined;
        }
        else {
            assert(!isleaf);
            ptrcount = 0;
        }

        return [new ICCPTypeSizeInfo(sldatasize, sldatasize, sldatasize, slmask), isleaf, ptrcount, refmask, toffsets];
    }

    private computeInlineUnionTypeLayoutInfoFromTypeList(tl: ICCPType[]): [ICCPTypeSizeInfo, boolean] {
        let sldatasize = 0;
        let slmask = "4";

        let isleaf = true;

        tl.forEach((entry) => {
            sldatasize += entry.allocinfo.slfullsize;
            for(let i = 0; i < entry.allocinfo.slmask.length; ++i) {
                slmask += "1";
            }

            isleaf = isleaf && this.isTypeLeafEntry(entry);
        });

        return [new ICCPTypeSizeInfo(sldatasize, sldatasize, sldatasize + ICCP_WORD_SIZE, slmask), isleaf];
    }

    private computeReferenceTypeLayoutInfoFromTypeList(tl: ICCPType[]): [ICCPTypeSizeInfo, boolean, number, RefMask | undefined, number[]] {
        let heapsize = 0;

        let isleaf = true;
        let refmask: string | undefined = "";
        let ptrcount = 0;

        let toffsets: number[] = [];
        let coffset = 0;
        tl.forEach((entry, pos) => {
            heapsize += entry.allocinfo.slfullsize;

            isleaf = isleaf && this.isTypeLeafEntry(entry);
            refmask += entry.allocinfo.slmask;
            if (ptrcount !== -1) {
                if (ptrcount === pos && (entry.tkind === ICCPTypeKind.Ref || entry.tkind === ICCPTypeKind.HeapUnion)) {
                    ptrcount++;
                }
                else {
                    ptrcount = -1;
                }
            }

            toffsets.push(coffset);
            coffset += entry.allocinfo.slfullsize;
        });

        if (isleaf) {
            assert(ptrcount === 0);
            refmask = undefined;
        }
        else if (ptrcount > 0) {
            assert(!isleaf);
            refmask = undefined;
        }
        else {
            assert(!isleaf);
            ptrcount = 0;
        }

        return [new ICCPTypeSizeInfo(heapsize, ICCP_WORD_SIZE, ICCP_WORD_SIZE, "2"), isleaf, ptrcount, refmask, toffsets];
    }

    private computeHeapUnionTypeLayoutInfoFromTypeList(tl: ICCPType[]): ICCPTypeSizeInfo {
        let sldatasize = 0;

        tl.forEach((entry) => {
            sldatasize += entry.allocinfo.slfullsize;
        });

        return new ICCPTypeSizeInfo(sldatasize, ICCP_WORD_SIZE, ICCP_WORD_SIZE, "2");
    }

    private getICCPTypeForTuple(tt: MIRTupleType): ICCPType {
        const isuniontuple = tt.entries.some((entry) => entry.isOptional);
        const iccpentries = tt.entries.map((entry) => this.getICCPTypeData(entry.type));

        if(tt.isvalue) {
            if(isuniontuple) {
                const [utdata, isleaf] = this.computeInlineUnionTypeLayoutInfoFromTypeList(iccpentries);
                return new ICCPTypeInlineUnion(tt.trkey, tt.trkey, utdata, isleaf)
            }
            else {
                const [udata, isleaf, ptrcount, rmask, offsets] = this.computeStructuralTypeLayoutInfoFromTypeList(iccpentries);
                return new ICCPTypeTuple(tt.trkey, tt.trkey, ICCPTypeKind.Struct, udata, isleaf, rmask, ptrcount, tt.entries.length, tt.entries.map((entry) => entry.type.trkey), offsets);
            }
        }
        else {
            if(isuniontuple) {
                const udata = this.computeHeapUnionTypeLayoutInfoFromTypeList(iccpentries);
                return new ICCPTypeHeapUnion(tt.trkey, tt.trkey, udata);
            }
            else {
                const [udata, isleaf, ptrcount, rmask, offsets] = this.computeReferenceTypeLayoutInfoFromTypeList(iccpentries);
                return new ICCPTypeTuple(tt.trkey, tt.trkey, ICCPTypeKind.Ref, udata, isleaf, rmask, ptrcount, tt.entries.length, tt.entries.map((entry) => entry.type.trkey), offsets);
            }
        }
    }

    private getICCPTypeForRecord(tt: MIRRecordType): ICCPType {
        const isunionrecord = tt.entries.some((entry) => entry.isOptional);
        const iccpentries = tt.entries.map((entry) => this.getICCPTypeData(entry.type));

        if(tt.isvalue) {
            if(isunionrecord) {
                const [utdata, isleaf] = this.computeInlineUnionTypeLayoutInfoFromTypeList(iccpentries);
                return new ICCPTypeInlineUnion(tt.trkey, tt.trkey, utdata, isleaf)
            }
            else {
                const [udata, isleaf, ptrcount, rmask, offsets] = this.computeStructuralTypeLayoutInfoFromTypeList(iccpentries);
                return new ICCPTypeRecord(tt.trkey, tt.trkey, ICCPTypeKind.Struct, udata, isleaf, rmask, ptrcount, tt.entries.map((entry) => entry.name), tt.entries.map((entry) => entry.type.trkey), offsets);
            }
        }
        else {
            if(isunionrecord) {
                const udata = this.computeHeapUnionTypeLayoutInfoFromTypeList(iccpentries);
                return new ICCPTypeHeapUnion(tt.trkey, tt.trkey, udata);
            }
            else {
                const [udata, isleaf, ptrcount, rmask, offsets] = this.computeReferenceTypeLayoutInfoFromTypeList(iccpentries);
                return new ICCPTypeRecord(tt.trkey, tt.trkey, ICCPTypeKind.Ref, udata, isleaf, rmask, ptrcount, tt.entries.map((entry) => entry.name), tt.entries.map((entry) => entry.type.trkey), offsets);
            }
        }
    }

    private getICCPTypeForEntity(tt: MIREntityTypeDecl): ICCPType {
        const iccpentries = tt.fields.map((f) => this.getICCPTypeData(this.getMIRType(f.declaredType)));

        if (tt.attributes.includes("struct")) {
            const [udata, isleaf, ptrcount, rmask, offsets] = this.computeStructuralTypeLayoutInfoFromTypeList(iccpentries);
            return new ICCPTypeEntity(tt.tkey, tt.tkey, ICCPTypeKind.Struct, udata, isleaf, rmask, ptrcount, tt.fields.map((f) => f.fkey), tt.fields.map((f) => f.declaredType), offsets);
        }
        else {
            const [udata, isleaf, ptrcount, rmask, offsets] = this.computeReferenceTypeLayoutInfoFromTypeList(iccpentries);
            return new ICCPTypeEntity(tt.tkey, tt.tkey, ICCPTypeKind.Ref, udata, isleaf, rmask, ptrcount, tt.fields.map((f) => f.fkey), tt.fields.map((f) => f.declaredType), offsets);
        }
    }

    getICCPTypeData(tt: MIRType): ICCPType {
        if(this.typeDataMap.has(tt.trkey)) {
            return this.typeDataMap.get(tt.trkey) as ICCPType;
        }

        let iidata: ICCPType | undefined = undefined;
        if (this.isType(tt, "NSCore::None")) {
            iidata = new ICCPTypePrimitive(tt.trkey, "BSQNone", ICCPTypeKind.Register, new ICCPTypeSizeInfo(ICCP_WORD_SIZE, ICCP_WORD_SIZE, ICCP_WORD_SIZE, "1"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::Bool")) {
            iidata = new ICCPTypePrimitive(tt.trkey, "BSQBool", ICCPTypeKind.Register, new ICCPTypeSizeInfo(ICCP_WORD_SIZE, ICCP_WORD_SIZE, ICCP_WORD_SIZE, "1"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::Int")) {
            iidata = new ICCPTypePrimitive(tt.trkey, "BSQInt", ICCPTypeKind.Register, new ICCPTypeSizeInfo(ICCP_WORD_SIZE, ICCP_WORD_SIZE, ICCP_WORD_SIZE, "1"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::Nat")) {
            iidata = new ICCPTypePrimitive(tt.trkey, "BSQNat", ICCPTypeKind.Register, new ICCPTypeSizeInfo(ICCP_WORD_SIZE, ICCP_WORD_SIZE, ICCP_WORD_SIZE, "1"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::BigInt")) {
            iidata = new ICCPTypePrimitive(tt.trkey, "BSQBigInt", ICCPTypeKind.Register, new ICCPTypeSizeInfo(ICCP_WORD_SIZE, ICCP_WORD_SIZE, ICCP_WORD_SIZE, "1"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::BigNat")) {
            iidata = new ICCPTypePrimitive(tt.trkey, "BSQBigNat", ICCPTypeKind.Register, new ICCPTypeSizeInfo(ICCP_WORD_SIZE, ICCP_WORD_SIZE, ICCP_WORD_SIZE, "1"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::Float")) {
            iidata = new ICCPTypePrimitive(tt.trkey, "BSQFloat", ICCPTypeKind.Register, new ICCPTypeSizeInfo(ICCP_WORD_SIZE, ICCP_WORD_SIZE, ICCP_WORD_SIZE, "1"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::Decimal")) {
            iidata = new ICCPTypePrimitive(tt.trkey, "BSQDecimal", ICCPTypeKind.Register, new ICCPTypeSizeInfo(2*ICCP_WORD_SIZE, 2*ICCP_WORD_SIZE, 2*ICCP_WORD_SIZE, "11"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::Rational")) {
            iidata = new ICCPTypePrimitive(tt.trkey, "BSQRational", ICCPTypeKind.Struct, new ICCPTypeSizeInfo(3*ICCP_WORD_SIZE, 3*ICCP_WORD_SIZE, 3*ICCP_WORD_SIZE, "111"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::StringPos")) {
            iidata = new ICCPTypePrimitive(tt.trkey, "BSQStringIterator", ICCPTypeKind.Struct, new ICCPTypeSizeInfo(5*ICCP_WORD_SIZE, 5*ICCP_WORD_SIZE, 5*ICCP_WORD_SIZE, "31121"), false, "31121", 0); 
        }
        else if (this.isType(tt, "NSCore::String")) {
            iidata = new ICCPTypePrimitive(tt.trkey, "BSQString", ICCPTypeKind.String, new ICCPTypeSizeInfo(2*ICCP_WORD_SIZE, 2*ICCP_WORD_SIZE, 2*ICCP_WORD_SIZE, "31"), false, undefined, 0);
        }
        else if (this.isType(tt, "NSCore::ByteBuffer")) {
            iidata = new ICCPTypePrimitive(tt.trkey, "BSQByteBuffer", ICCPTypeKind.Ref, new ICCPTypeSizeInfo(34*ICCP_WORD_SIZE, ICCP_WORD_SIZE, ICCP_WORD_SIZE, "2"), false, undefined, 1);
        }
        else if(this.isType(tt, "NSCore::ISOTime")) {
            iidata = new ICCPTypePrimitive(tt.trkey, "BSQISOTime", ICCPTypeKind.Register, new ICCPTypeSizeInfo(ICCP_WORD_SIZE, ICCP_WORD_SIZE, ICCP_WORD_SIZE, "1"), true, undefined, 0); 
        }
        else if(this.isType(tt, "NSCore::LogicalTime")) {
            iidata = new ICCPTypePrimitive(tt.trkey, "BSQLogicalTime", ICCPTypeKind.Register, new ICCPTypeSizeInfo(ICCP_WORD_SIZE, ICCP_WORD_SIZE, ICCP_WORD_SIZE, "1"), true, undefined, 0); 
        }
        else if(this.isType(tt, "NSCore::UUID")) {
            iidata = new ICCPTypePrimitive(tt.trkey, "BSQUUID", ICCPTypeKind.Ref, new ICCPTypeSizeInfo(2*ICCP_WORD_SIZE, ICCP_WORD_SIZE, ICCP_WORD_SIZE, "2"), true, undefined, 0); 
        }
        else if(this.isType(tt, "NSCore::ContentHash")) {
            iidata = new ICCPTypePrimitive(tt.trkey, "BSQContentHash", ICCPTypeKind.Ref, new ICCPTypeSizeInfo(64*ICCP_WORD_SIZE, ICCP_WORD_SIZE, ICCP_WORD_SIZE, "2"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::Regex")) {
            iidata = new ICCPTypePrimitive(tt.trkey, "BSQRegex", ICCPTypeKind.Struct, new ICCPTypeSizeInfo(2*ICCP_WORD_SIZE, 2*ICCP_WORD_SIZE, 2*ICCP_WORD_SIZE, "11"), true, undefined, 0); 
        }
        else if(this.isUniqueTupleType(tt)) {
            iidata = this.getICCPTypeForTuple(tt.options[0] as MIRTupleType);
        }
        else if(this.isUniqueRecordType(tt)) {
            iidata = this.getICCPTypeForRecord(tt.options[0] as MIRRecordType);
        }
        else if(this.isUniqueEntityType(tt)) {
            iidata = this.getICCPTypeForEntity(this.assembly.entityDecls.get(tt.options[0].trkey) as MIREntityTypeDecl);
        }
        else if (this.isUniqueEphemeralType(tt)) {
            const iccpentries = (tt.options[0] as MIREphemeralListType).entries.map((entry) => this.getICCPTypeData(entry));
            const etypes =  (tt.options[0] as MIREphemeralListType).entries.map((entry) => entry.trkey);

            const [udata, isleaf, ptrcount, rmask, offsets] = this.computeStructuralTypeLayoutInfoFromTypeList(iccpentries);
            iidata = new ICCPTypeEphemeralList(tt.trkey, tt.trkey, ICCPTypeKind.Struct, udata, isleaf, rmask, ptrcount, etypes, offsets);
        }
        else {
            //It is a true union
            if (tt.options.length !== 1) {
                const utypes = tt.options.map((opt) => this.getICCPTypeData(this.getMIRType(opt.trkey)));

                if (utypes.some((iccptype) => iccptype.allocinfo.heapsize === -2)) {
                    iidata = new ICCPTypeHeapUnion(tt.trkey, tt.trkey, new ICCPTypeSizeInfo(-2, ICCP_WORD_SIZE, ICCP_WORD_SIZE, "2"));
                }
                else {
                    if (utypes.every((ut) => ut.tkind === ICCPTypeKind.Ref || ut.tkind === ICCPTypeKind.HeapUnion)) {
                        iidata = new ICCPTypeHeapUnion(tt.trkey, tt.trkey, new ICCPTypeSizeInfo(-1, ICCP_WORD_SIZE, ICCP_WORD_SIZE, "2"));
                    }
                    else {
                        const sldatasize = Math.max(...utypes.map((ut) => ut.allocinfo.slfullsize));
                        
                        let slmask = "4";
                        for(let i = 0; i < sldatasize / ICCP_WORD_SIZE; ++i) {
                            slmask += "1";
                        }
                    
                        iidata = new ICCPTypeInlineUnion(tt.trkey, tt.trkey, new ICCPTypeSizeInfo(sldatasize, sldatasize, sldatasize + ICCP_WORD_SIZE, slmask), utypes.every((ut) => this.isTypeLeafEntry(ut)));
                    }
                }
            }
            else {
                //if is a tuple or record with optional slots OR a concept
                const opt = tt.options[0];

                if(opt instanceof MIRTupleType) {
                    iidata = this.getICCPTypeForTuple(opt);
                }
                else if(opt instanceof MIRRecordType) {
                    iidata = this.getICCPTypeForRecord(opt);
                }
                else {
                    assert(opt instanceof MIRConceptType);
                    if(UNIVERSAL_CONCEPTS.includes(opt.trkey)) {
                        iidata = new ICCPTypeHeapUnion(opt.trkey, opt.trkey, new ICCPTypeSizeInfo(-2, ICCP_WORD_SIZE, ICCP_WORD_SIZE, "2"));
                    }
                    else {
                        const isref = (opt as MIRConceptType).ckeys.some((cpt) => !(this.assembly.conceptDecls.get(cpt) as MIRConceptTypeDecl).attributes.includes("struct"));

                        //if is ref or struct and then need to process over all 
                        if(isref) {
                            iidata = new ICCPTypeHeapUnion(opt.trkey, opt.trkey, new ICCPTypeSizeInfo(-1, ICCP_WORD_SIZE, ICCP_WORD_SIZE, "2"));
                        }
                        else {
                            const utypes = [...this.assembly.entityDecls]
                                .filter((edecl) => this.assembly.subtypeOf(this.getMIRType(edecl[0]), tt))
                                .map((edecl) => this.getICCPTypeData(this.getMIRType(edecl[0])));
                             
                                const sldatasize = Math.max(...utypes.map((ut) => ut.allocinfo.slfullsize));
                        
                                let slmask = "4";
                                for(let i = 0; i < sldatasize / ICCP_WORD_SIZE; ++i) {
                                    slmask += "1";
                                }
                            
                                iidata = new ICCPTypeInlineUnion(tt.trkey, tt.trkey, new ICCPTypeSizeInfo(sldatasize, sldatasize, sldatasize + ICCP_WORD_SIZE, slmask), utypes.every((ut) => this.isTypeLeafEntry(ut)));
                            }
                    }
                }   
            }
        }

        this.typeDataMap.set(tt.trkey, iidata as ICCPType);
        return this.typeDataMap.get(tt.trkey) as ICCPType;
    }

    private coerceFromAtomicToKey(exp: SMTExp, from: MIRType): SMTExp  {
        assert(this.assembly.subtypeOf(from, this.getMIRType("NSCore::KeyType")));

        if (from.trkey === "NSCore::None") {
            return new SMTConst("BKey@none");
        }
        else {
            let objval: SMTExp | undefined = undefined;
            let typetag = "[NOT SET]";

            if (this.isType(from, "NSCore::Bool")) {
                objval = new SMTCallSimple("bsqkey_bool@box", [exp]);
                typetag = "TypeTag_Bool";
            }
            else if (this.isType(from, "NSCore::Int")) {
                objval = new SMTCallSimple("bsqkey_int@box", [exp]);
                typetag = "TypeTag_Int";
            }
            else if (this.isType(from, "NSCore::Nat")) {
                objval = new SMTCallSimple("bsqkey_nat@box", [exp]);
                typetag = "TypeTag_Nat";
            }
            else if (this.isType(from, "NSCore::BigInt")) {
                objval = new SMTCallSimple("bsqkey_bigint@box", [exp]);
                typetag = "TypeTag_BigInt";
            }
            else if (this.isType(from, "NSCore::BigNat")) {
                objval = new SMTCallSimple("bsqkey_bignat@box", [exp]);
                typetag = "TypeTag_BigNat";
            }
            else if (this.isType(from, "NSCore::String")) {
                objval = new SMTCallSimple("bsqkey_string@box", [exp]);
                typetag = "TypeTag_String";
            }
            else if (this.isUniqueTupleType(from)) {
                objval = new SMTCallSimple(this.getSMTConstructorName(from).box, [exp]);
                typetag = this.getSMTTypeTag(from);
            }
            else if (this.isUniqueRecordType(from)) {
                objval = new SMTCallSimple(this.getSMTConstructorName(from).box, [exp]);
                typetag = this.getSMTTypeTag(from);
            }
            else {
                assert(this.isUniqueEntityType(from));

                objval = new SMTCallSimple(this.getSMTConstructorName(from).box, [exp]);
                typetag = this.getSMTTypeTag(from);
            }

            return new SMTCallSimple("BKey@box", [new SMTConst(typetag), objval as SMTExp]);
        }
    }

    private coerceFromAtomicToTerm(exp: SMTExp, from: MIRType): SMTExp {
        if (from.trkey === "NSCore::None") {
            return new SMTConst(`BTerm@none`);
        }
        else {
            if(this.assembly.subtypeOf(from, this.getMIRType("NSCore::KeyType"))) {
                return new SMTCallSimple("BTerm@keybox", [this.coerceFromAtomicToKey(exp, from)]);
            }
            else {
                let objval: SMTExp | undefined = undefined;
                let typetag = "[NOT SET]";

                if (this.isType(from, "NSCore::Float")) {
                    objval = new SMTCallSimple("bsq_float@box", [exp]);
                    typetag = "TypeTag_Float";
                }
                else if (this.isType(from, "NSCore::Decimal")) {
                    objval = new SMTCallSimple("bsq_decimal@box", [exp]);
                    typetag = "TypeTag_Decimal";
                }
                else if (this.isType(from, "NSCore::Rational")) {
                    objval = new SMTCallSimple("bsq_rational@box", [exp]);
                    typetag = "TypeTag_Rational";
                }
                else if (this.isType(from, "NSCore::Regex")) {
                    objval = new SMTCallSimple("bsq_regex@box", [exp]);
                    typetag = "TypeTag_Regex";
                }
                else if (this.isUniqueTupleType(from)) {
                    objval = new SMTCallSimple(this.getSMTConstructorName(from).box, [exp]);
                    typetag = this.getSMTTypeTag(from);
                }
                else if (this.isUniqueRecordType(from)) {
                    objval = new SMTCallSimple(this.getSMTConstructorName(from).box, [exp]);
                    typetag = this.getSMTTypeTag(from);
                }
                else {
                    assert(this.isUniqueEntityType(from));

                    objval = new SMTCallSimple(this.getSMTConstructorName(from).box, [exp]);
                    typetag = this.getSMTTypeTag(from);
                }

                return new SMTCallSimple("BTerm@termbox", [new SMTConst(typetag), objval as SMTExp]);
            }
        }
    }

    private coerceKeyIntoAtomic(exp: SMTExp, into: MIRType): SMTExp {
        if (this.isType(into, "NSCore::None")) {
            return new SMTConst("bsq_none@literal");
        }
        else {
            const oexp = new SMTCallSimple("BKey_value", [exp]);

            if (this.isType(into, "NSCore::Bool")) {
                return new SMTCallSimple("bsqkey_bool_value", [oexp]);
            }
            else if (this.isType(into, "NSCore::Int")) {
                return new SMTCallSimple("bsqkey_int_value", [oexp]);
            }
            else if (this.isType(into, "NSCore::Nat")) {
                return new SMTCallSimple("bsqkey_nat_value", [oexp]);
            }
            else if (this.isType(into, "NSCore::BigInt")) {
                return new SMTCallSimple("bsqkey_bigint_value", [oexp]);
            }
            else if (this.isType(into, "NSCore::BigNat")) {
                return new SMTCallSimple("bsqkey_bignat_value", [oexp]);
            }
            else if (this.isType(into, "NSCore::String")) {
                return new SMTCallSimple("bsqkey_string_value", [oexp]);
            }
            else if (this.isUniqueTupleType(into)) {
                return new SMTCallSimple(this.getSMTConstructorName(into).bfield, [oexp]);
            }
            else if (this.isUniqueRecordType(into)) {
                return new SMTCallSimple(this.getSMTConstructorName(into).bfield, [oexp]);
            }
            else {
                assert(this.isUniqueEntityType(into));

                return new SMTCallSimple(this.getSMTConstructorName(into).bfield, [oexp]);
            }
        }
    }

    private coerceTermIntoAtomic(exp: SMTExp, into: MIRType): SMTExp {
        if (this.isType(into, "NSCore::None")) {
            return new SMTConst("bsq_none@literal");
        }
        else {
            if(this.assembly.subtypeOf(into, this.getMIRType("NSCore::KeyType"))) {
                return this.coerceKeyIntoAtomic(new SMTCallSimple("BTerm_keyvalue", [exp]), into)
            }
            else {
                const oexp = new SMTCallSimple("BTerm_termvalue", [exp]);

                if (this.isType(into, "NSCore::Float")) {
                    return new SMTCallSimple("bsqobject_float_value", [oexp]);
                }
                else if (this.isType(into, "NSCore::Decimal")) {
                    return new SMTCallSimple("bsqobject_decimal_value", [oexp]);
                }
                else if (this.isType(into, "NSCore::Rational")) {
                    return new SMTCallSimple("bsqobject_rational_value", [oexp]);
                }
                else if (this.isType(into, "NSCore::Regex")) {
                    return new SMTCallSimple("bsqobject_regex_value", [oexp]);
                }
                else if (this.isUniqueTupleType(into)) {
                    return new SMTCallSimple(this.getSMTConstructorName(into).bfield, [oexp]);
                }
                else if (this.isUniqueRecordType(into)) {
                    return new SMTCallSimple(this.getSMTConstructorName(into).bfield, [oexp]);
                }
                else {
                    assert(this.isUniqueEntityType(into));

                    return new SMTCallSimple(this.getSMTConstructorName(into).bfield, [oexp]);
                }
            }
        }
    }

    coerce(exp: SMTExp, from: MIRType, into: MIRType): SMTExp {
        const smtfrom = this.getSMTTypeFor(from);
        const smtinto = this.getSMTTypeFor(into);

        if (smtfrom.name === smtinto.name) {
            return exp;
        }
        else if (smtinto.name === "BKey") {
            if(smtfrom.name === "BTerm") {
                return new SMTCallSimple("BTerm_keyvalue", [exp]);
            }
            else {
                return this.coerceFromAtomicToKey(exp, from);
            }
        }
        else if (smtinto.name === "BTerm") {
            if(smtfrom.name === "BKey") {
                return new SMTCallSimple("BTerm@keybox", [exp]);
            }
            else {
                return this.coerceFromAtomicToTerm(exp, from);
            }
        }
        else {
            if (smtfrom.name === "BKey") {
                return this.coerceKeyIntoAtomic(exp, into);
            }
            else {
                assert(smtfrom.name === "BTerm");

                return this.coerceTermIntoAtomic(exp, into);
            }
        }
    }

    coerceToKey(exp: SMTExp, from: MIRType): SMTExp {
        const smtfrom = this.getSMTTypeFor(from);

        if (smtfrom.name === "BKey") {
            return exp;
        }
        else {
            if(smtfrom.name === "BTerm") {
                return new SMTCallSimple("BTerm_keyvalue", [exp]);
            }
            else {
                return this.coerceFromAtomicToKey(exp, from);
            }
        }
    }

    generateTupleIndexGetFunction(tt: MIRTupleType, idx: number): string {
        return `${this.mangle(tt.trkey)}@_${idx}`;
    } 

    generateRecordPropertyGetFunction(tt: MIRRecordType, pname: string): string {
        return `${this.mangle(tt.trkey)}@_${pname}`;
    }

    generateEntityFieldGetFunction(tt: MIREntityTypeDecl, field: MIRFieldKey): string {
        return `${this.mangle(tt.tkey)}@_${this.mangle(field)}`;
    }

    generateEphemeralListGetFunction(tt: MIREphemeralListType, idx: number): string {
        return `${this.mangle(tt.trkey)}@_${idx}`;
    }

    generateResultType(ttype: MIRType): SMTType {
        return new SMTType(`$Result_${this.getSMTTypeFor(ttype).name}`);
    }

    generateResultTypeConstructorSuccess(ttype: MIRType, val: SMTExp): SMTExp {
        return new SMTCallSimple(`$Result_${this.getSMTTypeFor(ttype).name}@success`, [val]);
    }

    generateResultTypeConstructorError(ttype: MIRType, err: SMTExp): SMTExp {
        return new SMTCallSimple(`$Result_${this.getSMTTypeFor(ttype).name}@error`, [err]);
    }

    generateErrorResultAssert(rtype: MIRType): SMTExp {
        return this.generateResultTypeConstructorError(rtype, new SMTConst("ErrorID_AssumeCheck"));
    }

    generateResultIsSuccessTest(ttype: MIRType, exp: SMTExp): SMTExp {
        return new SMTCallSimple(`(_ is $Result_${this.getSMTTypeFor(ttype).name}@success)`, [exp]);
    }

    generateResultIsErrorTest(ttype: MIRType, exp: SMTExp): SMTExp {
        return new SMTCallSimple(`(_ is $Result_${this.getSMTTypeFor(ttype).name}@error)`, [exp]);
    }

    generateResultGetSuccess(ttype: MIRType, exp: SMTExp): SMTExp {
        return new SMTCallSimple(`$Result_${this.getSMTTypeFor(ttype).name}@success_value`, [exp]);
    }

    generateResultGetError(ttype: MIRType, exp: SMTExp): SMTExp {
        return new SMTCallSimple(`$Result_${this.getSMTTypeFor(ttype).name}@error_value`, [exp]);
    }
    
    generateAccessWithSetGuardResultType(ttype: MIRType): SMTType {
        return new SMTType(`$GuardResult_${this.getSMTTypeFor(ttype).name}`);
    }

    generateAccessWithSetGuardResultTypeConstructorLoad(ttype: MIRType, value: SMTExp, flag: boolean): SMTExp {
        return new SMTCallSimple(`$GuardResult_${this.getSMTTypeFor(ttype).name}@cons`, [value, new SMTConst(flag ? "true" : "false")]);
    }

    generateAccessWithSetGuardResultGetValue(ttype: MIRType, exp: SMTExp): SMTExp {
        return new SMTCallSimple(`$GuardResult_${this.getSMTTypeFor(ttype).name}@result`, [exp]);
    }

    generateAccessWithSetGuardResultGetFlag(ttype: MIRType, exp: SMTExp): SMTExp {
        return new SMTCallSimple(`$GuardResult_${this.getSMTTypeFor(ttype).name}@flag`, [exp]);
    }

    private havocTypeInfoGen(tt: MIRType): [string, boolean] {
        if (this.isType(tt, "NSCore::None")) {
            return ["BNone@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::Bool")) {
            return ["BBool@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::Int")) {
            return ["BInt@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::Nat")) {
            return ["BNat@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::BigInt")) {
            return ["BBigInt@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::BigNat")) {
            return ["BBigNat@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::Float")) {
            return ["BFloat@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::Decimal")) {
            return ["BDecimal@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::Rational")) {
            return ["BRational@UFCons_API", false];
        }
        else {
            return [`_@@cons_${this.getSMTTypeFor(tt).name}_entrypoint`, true];
        }
    }

    isPrimitiveHavocConstructorType(tt: MIRType): boolean {
        return (this.isType(tt, "NSCore::None") || this.isType(tt, "NSCore::Bool") 
        || this.isType(tt, "NSCore::Int") || this.isType(tt, "NSCore::Nat") || this.isType(tt, "NSCore::BigNat") || this.isType(tt, "NSCore::BigInt")
        || this.isType(tt, "NSCore::Float") || this.isType(tt, "NSCore::Decimal") || this.isType(tt, "NSCore::Rational"));
    }

    isKnownSafeHavocConstructorType(tt: MIRType): boolean {
        return !this.havocTypeInfoGen(tt)[1];
    }

    generateHavocConstructorName(tt: MIRType): string {
        return this.havocTypeInfoGen(tt)[0];
    }

    generateHavocConstructorPathExtend(path: SMTExp, step: SMTExp): SMTExp {
        return new SMTCallSimple("seq.++", [path, new SMTCallSimple("seq.unit", [step])]);
    }

    generateHavocConstructorCall(tt: MIRType, path: SMTExp, step: SMTExp): SMTExp {
        if(this.isKnownSafeHavocConstructorType(tt)) {
            return this.generateResultTypeConstructorSuccess(tt, new SMTCallSimple(this.generateHavocConstructorName(tt), [this.generateHavocConstructorPathExtend(path, step)]));
        }
        else {
            return new SMTCallGeneral(this.generateHavocConstructorName(tt), [this.generateHavocConstructorPathExtend(path, step)]);
        }
    }
}

export {
    ICCP_WORD_SIZE,
    ICCPTypeEmitter
};
