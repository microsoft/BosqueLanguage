//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRConceptType, MIRConceptTypeDecl, MIREntityType, MIREntityTypeDecl, MIREphemeralListType, MIRRecordType, MIRTupleType, MIRType } from "../../../compiler/mir_assembly";
import { MIRResolvedTypeKey } from "../../../compiler/mir_ops";

import { ICCPType, ICCPTypeEntity, ICCPTypeEphemeralList, ICCPTypeHeapUnion, ICCPTypeInlineUnion, ICCPTypeKind, ICCPTypePrimitive, ICCPTypeRecord, ICCPTypeSizeInfo, ICCPTypeTuple, RefMask, TranspilerOptions } from "./iccp_assembly";

import * as assert from "assert";
import { Argument, ICCPOp, ICCPOpEmitter, ICCPStatementGuard, TargetVar } from "./iccp_exp";
import { SourceInfo } from "../../../ast/parser";

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

    private coerceFromAtomicToInline(sinfo: SourceInfo, arg: Argument, from: MIRType, trgt: TargetVar, into: MIRType, sguard?: ICCPStatementGuard): ICCPOp {
        const iccptype = this.getICCPTypeData(from);
        if(iccptype.tkind === ICCPTypeKind.Register) {
            if(sguard !== undefined) {
                return ICCPOpEmitter.genGuardedBoxUniqueRegisterToInlineOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICCPOpEmitter.genBoxUniqueRegisterToInlineOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
        else if(iccptype.tkind === ICCPTypeKind.Struct || iccptype.tkind === ICCPTypeKind.String) {
            if(sguard !== undefined) {
                return ICCPOpEmitter.genGuardedBoxUniqueStructOrStringToInlineOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICCPOpEmitter.genBoxUniqueStructOrStringToInlineOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
        else {
            assert(iccptype.tkind === ICCPTypeKind.Ref);

            if(sguard !== undefined) {
                return ICCPOpEmitter.genGuardedBoxUniqueRefToInlineOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICCPOpEmitter.genBoxUniqueRefToInlineOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
    }

    private coerceFromAtomicToHeap(sinfo: SourceInfo, arg: Argument, from: MIRType, trgt: TargetVar, into: MIRType, sguard?: ICCPStatementGuard): ICCPOp {
        const iccptype = this.getICCPTypeData(from);
        if(iccptype.tkind === ICCPTypeKind.Register) {
            if(sguard !== undefined) {
                return ICCPOpEmitter.genGuardedBoxUniqueRegisterToHeapOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICCPOpEmitter.genBoxUniqueRegisterToHeapOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
        else if(iccptype.tkind === ICCPTypeKind.Struct || iccptype.tkind === ICCPTypeKind.String) {
            if(sguard !== undefined) {
                return ICCPOpEmitter.genGuardedBoxUniqueStructOrStringToHeapOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICCPOpEmitter.genBoxUniqueStructOrStringToHeapOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
        else {
            assert(iccptype.tkind === ICCPTypeKind.Ref);

            if(sguard !== undefined) {
                return ICCPOpEmitter.genGuardedBoxUniqueRefToHeapOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICCPOpEmitter.genBoxUniqueRefToHeapOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
    }

    private coerceFromInlineToAtomic(sinfo: SourceInfo, arg: Argument, from: MIRType, trgt: TargetVar, into: MIRType, sguard?: ICCPStatementGuard): ICCPOp {
        const iccptype = this.getICCPTypeData(into);
        if(iccptype.tkind === ICCPTypeKind.Register) {
            if(sguard !== undefined) {
                return ICCPOpEmitter.genGuardedExtractUniqueRegisterFromInlineOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICCPOpEmitter.genExtractUniqueRegisterFromInlineOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
        else if(iccptype.tkind === ICCPTypeKind.Struct || iccptype.tkind === ICCPTypeKind.String) {
            if(sguard !== undefined) {
                return ICCPOpEmitter.genGuardedExtractUniqueStructOrStringFromInlineOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICCPOpEmitter.genExtractUniqueStructOrStringFromInlineOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
        else {
            assert(iccptype.tkind === ICCPTypeKind.Ref);

            if(sguard !== undefined) {
                return ICCPOpEmitter.genGuardedExtractUniqueRefFromInlineOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICCPOpEmitter.genExtractUniqueRefFromInlineOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
    }

    private coerceFromHeapToAtomic(sinfo: SourceInfo, arg: Argument, from: MIRType, trgt: TargetVar, into: MIRType, sguard?: ICCPStatementGuard): ICCPOp {
        const iccptype = this.getICCPTypeData(into);
        if(iccptype.tkind === ICCPTypeKind.Register) {
            if(sguard !== undefined) {
                return ICCPOpEmitter.genGuardedExtractUniqueRegisterFromHeapOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICCPOpEmitter.genExtractUniqueRegisterFromHeapOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
        else if(iccptype.tkind === ICCPTypeKind.Struct || iccptype.tkind === ICCPTypeKind.String) {
            if(sguard !== undefined) {
                return ICCPOpEmitter.genGuardedExtractUniqueStructOrStringFromHeapOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICCPOpEmitter.genExtractUniqueStructOrStringFromHeapOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
        else {
            assert(iccptype.tkind === ICCPTypeKind.Ref);

            if(sguard !== undefined) {
                return ICCPOpEmitter.genGuardedExtractUniqueRefFromHeapOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICCPOpEmitter.genExtractUniqueRefFromHeapOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
    }

    private coerceSameRepr(sinfo: SourceInfo, arg: Argument, from: MIRType, trgt: TargetVar, into: MIRType, sguard?: ICCPStatementGuard): ICCPOp {
        const iccpinto = this.getICCPTypeData(into);

        if(iccpinto.tkind !== ICCPTypeKind.InlineUnion) {
            if(iccpinto.tkind === ICCPTypeKind.Register) {
                if(sguard !== undefined) {
                    return ICCPOpEmitter.genGuardedDirectAssignRegisterOp(sinfo, trgt, into.trkey, arg, iccpinto.allocinfo.slfullsize, sguard);
                }
                else {
                    return ICCPOpEmitter.genDirectAssignRegisterOp(sinfo, trgt, into.trkey, arg, iccpinto.allocinfo.slfullsize);
                }
            }
            else if(iccpinto.tkind === ICCPTypeKind.Struct || iccpinto.tkind === ICCPTypeKind.String) {
                if(sguard !== undefined) {
                    return ICCPOpEmitter.genGuardedDirectAssignValueOp(sinfo, trgt, into.trkey, arg, iccpinto.allocinfo.slfullsize, sguard);
                }
                else {
                    return ICCPOpEmitter.genDirectAssignValueOp(sinfo, trgt, into.trkey, arg, iccpinto.allocinfo.slfullsize);
                }
            }
            else {
                if(sguard !== undefined) {
                    return ICCPOpEmitter.genGuardedDirectAssignRefOp(sinfo, trgt, into.trkey, arg, iccpinto.allocinfo.slfullsize, sguard);
                }
                else {
                    return ICCPOpEmitter.genDirectAssignRefOp(sinfo, trgt, into.trkey, arg, iccpinto.allocinfo.slfullsize);
                }
            }
        }
        else {
            const iccpfrom = this.getICCPTypeData(from);
            if(iccpinto.allocinfo.sldatasize === iccpfrom.allocinfo.sldatasize) {
                if(sguard !== undefined) {
                    return ICCPOpEmitter.genGuardedDirectAssignValueOp(sinfo, trgt, into.trkey, arg, iccpinto.allocinfo.slfullsize, sguard);
                }
                else {
                    return ICCPOpEmitter.genDirectAssignValueOp(sinfo, trgt, into.trkey, arg, iccpinto.allocinfo.slfullsize);
                }
            }
            else if (iccpinto.allocinfo.sldatasize < iccpfrom.allocinfo.sldatasize) {
                if(sguard !== undefined) {
                    return ICCPOpEmitter.genGuardedNarrowInlineOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
                }
                else {
                    return ICCPOpEmitter.genNarrowInlineOp(sinfo, trgt, into.trkey, arg, from.trkey);
                }
            }
            else {
                if(sguard !== undefined) {
                    return ICCPOpEmitter.genGuardedWidenInlineOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
                }
                else {
                    return ICCPOpEmitter.genWidenInlineOp(sinfo, trgt, into.trkey, arg, from.trkey);
                }
            }
        }

    }

    coerce(sinfo: SourceInfo, arg: Argument, from: MIRType, trgt: TargetVar, into: MIRType, sguard?: ICCPStatementGuard): ICCPOp {
        const iccpfrom = this.getICCPTypeData(from);
        const iccpinto = this.getICCPTypeData(into);

        if(iccpfrom.tkind === iccpinto.tkind) {
            return this.coerceSameRepr(sinfo, arg, from, trgt, into, sguard);
        }
        else if(iccpfrom.tkind !== ICCPTypeKind.InlineUnion && iccpfrom.tkind !== ICCPTypeKind.HeapUnion) {
            if(iccpinto.tkind === ICCPTypeKind.InlineUnion) {
                return this.coerceFromAtomicToInline(sinfo, arg, from, trgt, into, sguard);
            }
            else {
                assert(iccpinto.tkind === ICCPTypeKind.HeapUnion);
                return this.coerceFromAtomicToHeap(sinfo, arg, from, trgt, into, sguard);
            }
        }
        else if(iccpfrom.tkind === ICCPTypeKind.InlineUnion) {
            if(iccpinto.tkind === ICCPTypeKind.HeapUnion) {
                if(sguard !== undefined) {
                    return ICCPOpEmitter.genGuardedBoxInlineBoxToHeapOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
                }
                else {
                    return ICCPOpEmitter.genBoxInlineBoxToHeapOp(sinfo, trgt, into.trkey, arg, from.trkey);
                }
            }
            else {
                return this.coerceFromInlineToAtomic(sinfo, arg, from, trgt, into, sguard);
            }
        }
        else {
            assert(iccpfrom.tkind === ICCPTypeKind.HeapUnion);
            
            if(iccpinto.tkind === ICCPTypeKind.InlineUnion) {
                if(sguard !== undefined) {
                    return ICCPOpEmitter.genGuardedExtractInlineBoxFromHeapOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
                }
                else {
                    return ICCPOpEmitter.genExtractInlineBoxFromHeapOp(sinfo, trgt, into.trkey, arg, from.trkey);
                }
            }
            else {
                return this.coerceFromHeapToAtomic(sinfo, arg, from, trgt, into, sguard);
            }
        }
    }
}

export {
    ICCP_WORD_SIZE,
    ICCPTypeEmitter
};
