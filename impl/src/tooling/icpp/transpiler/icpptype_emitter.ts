//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRConceptType, MIRConceptTypeDecl, MIREntityType, MIREntityTypeDecl, MIREphemeralListType, MIRRecordType, MIRTupleType, MIRType } from "../../../compiler/mir_assembly";
import { MIRFieldKey, MIRInvokeKey, MIRResolvedTypeKey, MIRVirtualMethodKey } from "../../../compiler/mir_ops";

import { ICPPType, ICPPTypeEntity, ICPPTypeEphemeralList, ICPPTypeHeapUnion, ICPPTypeInlineUnion, ICPPTypeKind, ICPPTypePrimitive, ICPPTypeRecord, ICPPTypeSizeInfo, ICPPTypeTuple, RefMask, TranspilerOptions } from "./icpp_assembly";

import * as assert from "assert";
import { Argument, ICPPOp, ICPPOpEmitter, ICPPStatementGuard, TargetVar } from "./icpp_exp";
import { SourceInfo } from "../../../ast/parser";

const ICPP_WORD_SIZE = 8;

const UNIVERSAL_CONCEPTS = [
    "NSCore::Any",
    "NSCore::Some",
    "NSCore::KeyType",
    "NSCore::PODType",
    "NSCore::APIValue",
    "NSCore::APIType",
    "NSCore::Object"
];

class ICPPTypeEmitter {
    readonly topts: TranspilerOptions;
    readonly assembly: MIRAssembly;
    
    private typeDataMap: Map<MIRResolvedTypeKey, ICPPType> = new Map<MIRResolvedTypeKey, ICPPType>();

    private propertyNameToIDMap: Map<string, number> = new Map<string, number>();
    private fieldNameToIDMap: Map<MIRFieldKey, number> = new Map<MIRFieldKey, number>();
    private invokeNameToIDMap: Map<MIRInvokeKey, number> = new Map<MIRInvokeKey, number>();
    private vinvokeNameToIDMap: Map<MIRVirtualMethodKey, number> = new Map<MIRVirtualMethodKey, number>();

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

    isTypeLeafEntry(icpptype: ICPPType): boolean {
        return icpptype.isLeafType && (icpptype.tkind === ICPPTypeKind.Register || icpptype.tkind === ICPPTypeKind.Struct || icpptype.tkind === ICPPTypeKind.InlineUnion);
    }

    registerPropertyName(name: string): number {
        if(!this.propertyNameToIDMap.has(name)) {
            this.propertyNameToIDMap.set(name, this.propertyNameToIDMap.size + 1);
        }
        return this.propertyNameToIDMap.get(name) as number;
    }

    registerFieldName(name: MIRFieldKey): number {
        if(!this.fieldNameToIDMap.has(name)) {
            this.fieldNameToIDMap.set(name, this.fieldNameToIDMap.size + 1);
        }
        return this.fieldNameToIDMap.get(name) as number;
    }

    registerInvokeName(name: MIRInvokeKey): number {
        if(!this.invokeNameToIDMap.has(name)) {
            this.invokeNameToIDMap.set(name, this.invokeNameToIDMap.size + 1);
        }
        return this.invokeNameToIDMap.get(name) as number;
    }

    registerVirtualInvokeName(name: string): number {
        if(!this.vinvokeNameToIDMap.has(name)) {
            this.vinvokeNameToIDMap.set(name, this.vinvokeNameToIDMap.size + 1);
        }
        return this.vinvokeNameToIDMap.get(name) as number;
    }

    private computeStructuralTypeLayoutInfoFromTypeList(tl: ICPPType[]): [ICPPTypeSizeInfo, boolean, number, RefMask | undefined, number[]] {
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
                if (ptrcount === pos && (entry.tkind === ICPPTypeKind.Ref || entry.tkind === ICPPTypeKind.HeapUnion)) {
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

        return [new ICPPTypeSizeInfo(sldatasize, sldatasize, sldatasize, slmask), isleaf, ptrcount, refmask, toffsets];
    }

    private computeInlineUnionTypeLayoutInfoFromTypeList(tl: ICPPType[]): [ICPPTypeSizeInfo, boolean] {
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

        return [new ICPPTypeSizeInfo(sldatasize, sldatasize, sldatasize + ICPP_WORD_SIZE, slmask), isleaf];
    }

    private computeReferenceTypeLayoutInfoFromTypeList(tl: ICPPType[]): [ICPPTypeSizeInfo, boolean, number, RefMask | undefined, number[]] {
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
                if (ptrcount === pos && (entry.tkind === ICPPTypeKind.Ref || entry.tkind === ICPPTypeKind.HeapUnion)) {
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

        return [new ICPPTypeSizeInfo(heapsize, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "2"), isleaf, ptrcount, refmask, toffsets];
    }

    private computeHeapUnionTypeLayoutInfoFromTypeList(tl: ICPPType[]): ICPPTypeSizeInfo {
        let sldatasize = 0;

        tl.forEach((entry) => {
            sldatasize += entry.allocinfo.slfullsize;
        });

        return new ICPPTypeSizeInfo(sldatasize, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "2");
    }

    private getICPPTypeForTuple(tt: MIRTupleType): ICPPType {
        const isuniontuple = tt.entries.some((entry) => entry.isOptional);
        const iccpentries = tt.entries.map((entry) => this.getICPPTypeData(entry.type));

        if(tt.isvalue) {
            if(isuniontuple) {
                const [utdata, isleaf] = this.computeInlineUnionTypeLayoutInfoFromTypeList(iccpentries);
                return new ICPPTypeInlineUnion(tt.trkey, tt.trkey, utdata, isleaf)
            }
            else {
                const [udata, isleaf, ptrcount, rmask, offsets] = this.computeStructuralTypeLayoutInfoFromTypeList(iccpentries);
                return new ICPPTypeTuple(tt.trkey, tt.trkey, ICPPTypeKind.Struct, udata, isleaf, rmask, ptrcount, tt.entries.length, tt.entries.map((entry) => entry.type.trkey), offsets);
            }
        }
        else {
            if(isuniontuple) {
                const udata = this.computeHeapUnionTypeLayoutInfoFromTypeList(iccpentries);
                return new ICPPTypeHeapUnion(tt.trkey, tt.trkey, udata);
            }
            else {
                const [udata, isleaf, ptrcount, rmask, offsets] = this.computeReferenceTypeLayoutInfoFromTypeList(iccpentries);
                return new ICPPTypeTuple(tt.trkey, tt.trkey, ICPPTypeKind.Ref, udata, isleaf, rmask, ptrcount, tt.entries.length, tt.entries.map((entry) => entry.type.trkey), offsets);
            }
        }
    }

    private getICPPTypeForRecord(tt: MIRRecordType): ICPPType {
        const isunionrecord = tt.entries.some((entry) => entry.isOptional);
        const iccpentries = tt.entries.map((entry) => this.getICPPTypeData(entry.type));

        if(tt.isvalue) {
            if(isunionrecord) {
                const [utdata, isleaf] = this.computeInlineUnionTypeLayoutInfoFromTypeList(iccpentries);
                return new ICPPTypeInlineUnion(tt.trkey, tt.trkey, utdata, isleaf)
            }
            else {
                const [udata, isleaf, ptrcount, rmask, offsets] = this.computeStructuralTypeLayoutInfoFromTypeList(iccpentries);
                return new ICPPTypeRecord(tt.trkey, tt.trkey, ICPPTypeKind.Struct, udata, isleaf, rmask, ptrcount, tt.entries.map((entry) => entry.name), tt.entries.map((entry) => entry.type.trkey), offsets);
            }
        }
        else {
            if(isunionrecord) {
                const udata = this.computeHeapUnionTypeLayoutInfoFromTypeList(iccpentries);
                return new ICPPTypeHeapUnion(tt.trkey, tt.trkey, udata);
            }
            else {
                const [udata, isleaf, ptrcount, rmask, offsets] = this.computeReferenceTypeLayoutInfoFromTypeList(iccpentries);
                return new ICPPTypeRecord(tt.trkey, tt.trkey, ICPPTypeKind.Ref, udata, isleaf, rmask, ptrcount, tt.entries.map((entry) => entry.name), tt.entries.map((entry) => entry.type.trkey), offsets);
            }
        }
    }

    private getICPPTypeForEntity(tt: MIREntityTypeDecl): ICPPType {
        const iccpentries = tt.fields.map((f) => this.getICPPTypeData(this.getMIRType(f.declaredType)));

        if (tt.attributes.includes("struct")) {
            const [udata, isleaf, ptrcount, rmask, offsets] = this.computeStructuralTypeLayoutInfoFromTypeList(iccpentries);
            return new ICPPTypeEntity(tt.tkey, tt.tkey, ICPPTypeKind.Struct, udata, isleaf, rmask, ptrcount, tt.fields.map((f) => f.fkey), tt.fields.map((f) => f.declaredType), offsets);
        }
        else {
            const [udata, isleaf, ptrcount, rmask, offsets] = this.computeReferenceTypeLayoutInfoFromTypeList(iccpentries);
            return new ICPPTypeEntity(tt.tkey, tt.tkey, ICPPTypeKind.Ref, udata, isleaf, rmask, ptrcount, tt.fields.map((f) => f.fkey), tt.fields.map((f) => f.declaredType), offsets);
        }
    }

    getICPPTypeData(tt: MIRType): ICPPType {
        if(this.typeDataMap.has(tt.trkey)) {
            return this.typeDataMap.get(tt.trkey) as ICPPType;
        }

        let iidata: ICPPType | undefined = undefined;
        if (this.isType(tt, "NSCore::None")) {
            iidata = new ICPPTypePrimitive(tt.trkey, "BSQNone", ICPPTypeKind.Register, new ICPPTypeSizeInfo(ICPP_WORD_SIZE, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::Bool")) {
            iidata = new ICPPTypePrimitive(tt.trkey, "BSQBool", ICPPTypeKind.Register, new ICPPTypeSizeInfo(ICPP_WORD_SIZE, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::Int")) {
            iidata = new ICPPTypePrimitive(tt.trkey, "BSQInt", ICPPTypeKind.Register, new ICPPTypeSizeInfo(ICPP_WORD_SIZE, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::Nat")) {
            iidata = new ICPPTypePrimitive(tt.trkey, "BSQNat", ICPPTypeKind.Register, new ICPPTypeSizeInfo(ICPP_WORD_SIZE, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::BigInt")) {
            iidata = new ICPPTypePrimitive(tt.trkey, "BSQBigInt", ICPPTypeKind.Register, new ICPPTypeSizeInfo(ICPP_WORD_SIZE, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::BigNat")) {
            iidata = new ICPPTypePrimitive(tt.trkey, "BSQBigNat", ICPPTypeKind.Register, new ICPPTypeSizeInfo(ICPP_WORD_SIZE, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::Float")) {
            iidata = new ICPPTypePrimitive(tt.trkey, "BSQFloat", ICPPTypeKind.Register, new ICPPTypeSizeInfo(ICPP_WORD_SIZE, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::Decimal")) {
            iidata = new ICPPTypePrimitive(tt.trkey, "BSQDecimal", ICPPTypeKind.Register, new ICPPTypeSizeInfo(2*ICPP_WORD_SIZE, 2*ICPP_WORD_SIZE, 2*ICPP_WORD_SIZE, "11"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::Rational")) {
            iidata = new ICPPTypePrimitive(tt.trkey, "BSQRational", ICPPTypeKind.Struct, new ICPPTypeSizeInfo(3*ICPP_WORD_SIZE, 3*ICPP_WORD_SIZE, 3*ICPP_WORD_SIZE, "111"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::StringPos")) {
            iidata = new ICPPTypePrimitive(tt.trkey, "BSQStringIterator", ICPPTypeKind.Struct, new ICPPTypeSizeInfo(5*ICPP_WORD_SIZE, 5*ICPP_WORD_SIZE, 5*ICPP_WORD_SIZE, "31121"), false, "31121", 0); 
        }
        else if (this.isType(tt, "NSCore::String")) {
            iidata = new ICPPTypePrimitive(tt.trkey, "BSQString", ICPPTypeKind.String, new ICPPTypeSizeInfo(2*ICPP_WORD_SIZE, 2*ICPP_WORD_SIZE, 2*ICPP_WORD_SIZE, "31"), false, undefined, 0);
        }
        else if (this.isType(tt, "NSCore::ByteBuffer")) {
            iidata = new ICPPTypePrimitive(tt.trkey, "BSQByteBuffer", ICPPTypeKind.Ref, new ICPPTypeSizeInfo(34*ICPP_WORD_SIZE, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "2"), false, undefined, 1);
        }
        else if(this.isType(tt, "NSCore::ISOTime")) {
            iidata = new ICPPTypePrimitive(tt.trkey, "BSQISOTime", ICPPTypeKind.Register, new ICPPTypeSizeInfo(ICPP_WORD_SIZE, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"), true, undefined, 0); 
        }
        else if(this.isType(tt, "NSCore::LogicalTime")) {
            iidata = new ICPPTypePrimitive(tt.trkey, "BSQLogicalTime", ICPPTypeKind.Register, new ICPPTypeSizeInfo(ICPP_WORD_SIZE, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"), true, undefined, 0); 
        }
        else if(this.isType(tt, "NSCore::UUID")) {
            iidata = new ICPPTypePrimitive(tt.trkey, "BSQUUID", ICPPTypeKind.Ref, new ICPPTypeSizeInfo(2*ICPP_WORD_SIZE, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "2"), true, undefined, 0); 
        }
        else if(this.isType(tt, "NSCore::ContentHash")) {
            iidata = new ICPPTypePrimitive(tt.trkey, "BSQContentHash", ICPPTypeKind.Ref, new ICPPTypeSizeInfo(64*ICPP_WORD_SIZE, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "2"), true, undefined, 0); 
        }
        else if (this.isType(tt, "NSCore::Regex")) {
            iidata = new ICPPTypePrimitive(tt.trkey, "BSQRegex", ICPPTypeKind.Struct, new ICPPTypeSizeInfo(2*ICPP_WORD_SIZE, 2*ICPP_WORD_SIZE, 2*ICPP_WORD_SIZE, "11"), true, undefined, 0); 
        }
        else if(this.isUniqueTupleType(tt)) {
            iidata = this.getICPPTypeForTuple(tt.options[0] as MIRTupleType);
        }
        else if(this.isUniqueRecordType(tt)) {
            iidata = this.getICPPTypeForRecord(tt.options[0] as MIRRecordType);
        }
        else if(this.isUniqueEntityType(tt)) {
            iidata = this.getICPPTypeForEntity(this.assembly.entityDecls.get(tt.options[0].trkey) as MIREntityTypeDecl);
        }
        else if (this.isUniqueEphemeralType(tt)) {
            const iccpentries = (tt.options[0] as MIREphemeralListType).entries.map((entry) => this.getICPPTypeData(entry));
            const etypes =  (tt.options[0] as MIREphemeralListType).entries.map((entry) => entry.trkey);

            const [udata, isleaf, ptrcount, rmask, offsets] = this.computeStructuralTypeLayoutInfoFromTypeList(iccpentries);
            iidata = new ICPPTypeEphemeralList(tt.trkey, tt.trkey, ICPPTypeKind.Struct, udata, isleaf, rmask, ptrcount, etypes, offsets);
        }
        else {
            //It is a true union
            if (tt.options.length !== 1) {
                const utypes = tt.options.map((opt) => this.getICPPTypeData(this.getMIRType(opt.trkey)));

                if (utypes.some((icpptype) => icpptype.allocinfo.heapsize === -2)) {
                    iidata = new ICPPTypeHeapUnion(tt.trkey, tt.trkey, new ICPPTypeSizeInfo(-2, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "2"));
                }
                else {
                    if (utypes.every((ut) => ut.tkind === ICPPTypeKind.Ref || ut.tkind === ICPPTypeKind.HeapUnion)) {
                        iidata = new ICPPTypeHeapUnion(tt.trkey, tt.trkey, new ICPPTypeSizeInfo(-1, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "2"));
                    }
                    else {
                        const sldatasize = Math.max(...utypes.map((ut) => ut.allocinfo.slfullsize));
                        
                        let slmask = "4";
                        for(let i = 0; i < sldatasize / ICPP_WORD_SIZE; ++i) {
                            slmask += "1";
                        }
                    
                        iidata = new ICPPTypeInlineUnion(tt.trkey, tt.trkey, new ICPPTypeSizeInfo(sldatasize, sldatasize, sldatasize + ICPP_WORD_SIZE, slmask), utypes.every((ut) => this.isTypeLeafEntry(ut)));
                    }
                }
            }
            else {
                //if is a tuple or record with optional slots OR a concept
                const opt = tt.options[0];

                if(opt instanceof MIRTupleType) {
                    iidata = this.getICPPTypeForTuple(opt);
                }
                else if(opt instanceof MIRRecordType) {
                    iidata = this.getICPPTypeForRecord(opt);
                }
                else {
                    assert(opt instanceof MIRConceptType);
                    if(UNIVERSAL_CONCEPTS.includes(opt.trkey)) {
                        iidata = new ICPPTypeHeapUnion(opt.trkey, opt.trkey, new ICPPTypeSizeInfo(-2, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "2"));
                    }
                    else {
                        const isref = (opt as MIRConceptType).ckeys.some((cpt) => !(this.assembly.conceptDecls.get(cpt) as MIRConceptTypeDecl).attributes.includes("struct"));

                        //if is ref or struct and then need to process over all 
                        if(isref) {
                            iidata = new ICPPTypeHeapUnion(opt.trkey, opt.trkey, new ICPPTypeSizeInfo(-1, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "2"));
                        }
                        else {
                            const utypes = [...this.assembly.entityDecls]
                                .filter((edecl) => this.assembly.subtypeOf(this.getMIRType(edecl[0]), tt))
                                .map((edecl) => this.getICPPTypeData(this.getMIRType(edecl[0])));
                             
                                const sldatasize = Math.max(...utypes.map((ut) => ut.allocinfo.slfullsize));
                        
                                let slmask = "4";
                                for(let i = 0; i < sldatasize / ICPP_WORD_SIZE; ++i) {
                                    slmask += "1";
                                }
                            
                                iidata = new ICPPTypeInlineUnion(tt.trkey, tt.trkey, new ICPPTypeSizeInfo(sldatasize, sldatasize, sldatasize + ICPP_WORD_SIZE, slmask), utypes.every((ut) => this.isTypeLeafEntry(ut)));
                            }
                    }
                }   
            }
        }

        this.typeDataMap.set(tt.trkey, iidata as ICPPType);
        return this.typeDataMap.get(tt.trkey) as ICPPType;
    }

    private coerceFromAtomicToInline(sinfo: SourceInfo, arg: Argument, from: MIRType, trgt: TargetVar, into: MIRType, sguard?: ICPPStatementGuard): ICPPOp {
        const icpptype = this.getICPPTypeData(from);
        if(icpptype.tkind === ICPPTypeKind.Register) {
            if(sguard !== undefined) {
                return ICPPOpEmitter.genGuardedBoxUniqueRegisterToInlineOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICPPOpEmitter.genBoxUniqueRegisterToInlineOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
        else if(icpptype.tkind === ICPPTypeKind.Struct || icpptype.tkind === ICPPTypeKind.String) {
            if(sguard !== undefined) {
                return ICPPOpEmitter.genGuardedBoxUniqueStructOrStringToInlineOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICPPOpEmitter.genBoxUniqueStructOrStringToInlineOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
        else {
            assert(icpptype.tkind === ICPPTypeKind.Ref);

            if(sguard !== undefined) {
                return ICPPOpEmitter.genGuardedBoxUniqueRefToInlineOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICPPOpEmitter.genBoxUniqueRefToInlineOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
    }

    private coerceFromAtomicToHeap(sinfo: SourceInfo, arg: Argument, from: MIRType, trgt: TargetVar, into: MIRType, sguard?: ICPPStatementGuard): ICPPOp {
        const icpptype = this.getICPPTypeData(from);
        if(icpptype.tkind === ICPPTypeKind.Register) {
            if(sguard !== undefined) {
                return ICPPOpEmitter.genGuardedBoxUniqueRegisterToHeapOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICPPOpEmitter.genBoxUniqueRegisterToHeapOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
        else if(icpptype.tkind === ICPPTypeKind.Struct || icpptype.tkind === ICPPTypeKind.String) {
            if(sguard !== undefined) {
                return ICPPOpEmitter.genGuardedBoxUniqueStructOrStringToHeapOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICPPOpEmitter.genBoxUniqueStructOrStringToHeapOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
        else {
            assert(icpptype.tkind === ICPPTypeKind.Ref);

            if(sguard !== undefined) {
                return ICPPOpEmitter.genGuardedBoxUniqueRefToHeapOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICPPOpEmitter.genBoxUniqueRefToHeapOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
    }

    private coerceFromInlineToAtomic(sinfo: SourceInfo, arg: Argument, from: MIRType, trgt: TargetVar, into: MIRType, sguard?: ICPPStatementGuard): ICPPOp {
        const icpptype = this.getICPPTypeData(into);
        if(icpptype.tkind === ICPPTypeKind.Register) {
            if(sguard !== undefined) {
                return ICPPOpEmitter.genGuardedExtractUniqueRegisterFromInlineOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICPPOpEmitter.genExtractUniqueRegisterFromInlineOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
        else if(icpptype.tkind === ICPPTypeKind.Struct || icpptype.tkind === ICPPTypeKind.String) {
            if(sguard !== undefined) {
                return ICPPOpEmitter.genGuardedExtractUniqueStructOrStringFromInlineOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICPPOpEmitter.genExtractUniqueStructOrStringFromInlineOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
        else {
            assert(icpptype.tkind === ICPPTypeKind.Ref);

            if(sguard !== undefined) {
                return ICPPOpEmitter.genGuardedExtractUniqueRefFromInlineOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICPPOpEmitter.genExtractUniqueRefFromInlineOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
    }

    private coerceFromHeapToAtomic(sinfo: SourceInfo, arg: Argument, from: MIRType, trgt: TargetVar, into: MIRType, sguard?: ICPPStatementGuard): ICPPOp {
        const icpptype = this.getICPPTypeData(into);
        if(icpptype.tkind === ICPPTypeKind.Register) {
            if(sguard !== undefined) {
                return ICPPOpEmitter.genGuardedExtractUniqueRegisterFromHeapOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICPPOpEmitter.genExtractUniqueRegisterFromHeapOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
        else if(icpptype.tkind === ICPPTypeKind.Struct || icpptype.tkind === ICPPTypeKind.String) {
            if(sguard !== undefined) {
                return ICPPOpEmitter.genGuardedExtractUniqueStructOrStringFromHeapOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICPPOpEmitter.genExtractUniqueStructOrStringFromHeapOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
        else {
            assert(icpptype.tkind === ICPPTypeKind.Ref);

            if(sguard !== undefined) {
                return ICPPOpEmitter.genGuardedExtractUniqueRefFromHeapOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
            else {
                return ICPPOpEmitter.genExtractUniqueRefFromHeapOp(sinfo, trgt, into.trkey, arg, from.trkey);
            }
        }
    }

    private coerceSameRepr(sinfo: SourceInfo, arg: Argument, from: MIRType, trgt: TargetVar, into: MIRType, sguard?: ICPPStatementGuard): ICPPOp {
        const icppinto = this.getICPPTypeData(into);

        if(icppinto.tkind !== ICPPTypeKind.InlineUnion) {
            if(icppinto.tkind === ICPPTypeKind.Register) {
                if(sguard !== undefined) {
                    return ICPPOpEmitter.genGuardedDirectAssignRegisterOp(sinfo, trgt, into.trkey, arg, icppinto.allocinfo.slfullsize, sguard);
                }
                else {
                    return ICPPOpEmitter.genDirectAssignRegisterOp(sinfo, trgt, into.trkey, arg, icppinto.allocinfo.slfullsize);
                }
            }
            else if(icppinto.tkind === ICPPTypeKind.Struct || icppinto.tkind === ICPPTypeKind.String) {
                if(sguard !== undefined) {
                    return ICPPOpEmitter.genGuardedDirectAssignValueOp(sinfo, trgt, into.trkey, arg, icppinto.allocinfo.slfullsize, sguard);
                }
                else {
                    return ICPPOpEmitter.genDirectAssignValueOp(sinfo, trgt, into.trkey, arg, icppinto.allocinfo.slfullsize);
                }
            }
            else {
                if(sguard !== undefined) {
                    return ICPPOpEmitter.genGuardedDirectAssignRefOp(sinfo, trgt, into.trkey, arg, icppinto.allocinfo.slfullsize, sguard);
                }
                else {
                    return ICPPOpEmitter.genDirectAssignRefOp(sinfo, trgt, into.trkey, arg, icppinto.allocinfo.slfullsize);
                }
            }
        }
        else {
            const iccpfrom = this.getICPPTypeData(from);
            if(icppinto.allocinfo.sldatasize === iccpfrom.allocinfo.sldatasize) {
                if(sguard !== undefined) {
                    return ICPPOpEmitter.genGuardedDirectAssignValueOp(sinfo, trgt, into.trkey, arg, icppinto.allocinfo.slfullsize, sguard);
                }
                else {
                    return ICPPOpEmitter.genDirectAssignValueOp(sinfo, trgt, into.trkey, arg, icppinto.allocinfo.slfullsize);
                }
            }
            else if (icppinto.allocinfo.sldatasize < iccpfrom.allocinfo.sldatasize) {
                if(sguard !== undefined) {
                    return ICPPOpEmitter.genGuardedNarrowInlineOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
                }
                else {
                    return ICPPOpEmitter.genNarrowInlineOp(sinfo, trgt, into.trkey, arg, from.trkey);
                }
            }
            else {
                if(sguard !== undefined) {
                    return ICPPOpEmitter.genGuardedWidenInlineOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
                }
                else {
                    return ICPPOpEmitter.genWidenInlineOp(sinfo, trgt, into.trkey, arg, from.trkey);
                }
            }
        }

    }

    coerce(sinfo: SourceInfo, arg: Argument, from: MIRType, trgt: TargetVar, into: MIRType, sguard?: ICPPStatementGuard): ICPPOp {
        const icppfrom = this.getICPPTypeData(from);
        const icppinto = this.getICPPTypeData(into);

        if(icppfrom.tkind === icppinto.tkind) {
            return this.coerceSameRepr(sinfo, arg, from, trgt, into, sguard);
        }
        else if(icppfrom.tkind !== ICPPTypeKind.InlineUnion && icppfrom.tkind !== ICPPTypeKind.HeapUnion) {
            if(icppinto.tkind === ICPPTypeKind.InlineUnion) {
                return this.coerceFromAtomicToInline(sinfo, arg, from, trgt, into, sguard);
            }
            else {
                assert(icppinto.tkind === ICPPTypeKind.HeapUnion);
                return this.coerceFromAtomicToHeap(sinfo, arg, from, trgt, into, sguard);
            }
        }
        else if(icppfrom.tkind === ICPPTypeKind.InlineUnion) {
            if(icppinto.tkind === ICPPTypeKind.HeapUnion) {
                if(sguard !== undefined) {
                    return ICPPOpEmitter.genGuardedBoxInlineBoxToHeapOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
                }
                else {
                    return ICPPOpEmitter.genBoxInlineBoxToHeapOp(sinfo, trgt, into.trkey, arg, from.trkey);
                }
            }
            else {
                return this.coerceFromInlineToAtomic(sinfo, arg, from, trgt, into, sguard);
            }
        }
        else {
            assert(icppfrom.tkind === ICPPTypeKind.HeapUnion);
            
            if(icppinto.tkind === ICPPTypeKind.InlineUnion) {
                if(sguard !== undefined) {
                    return ICPPOpEmitter.genGuardedExtractInlineBoxFromHeapOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
                }
                else {
                    return ICPPOpEmitter.genExtractInlineBoxFromHeapOp(sinfo, trgt, into.trkey, arg, from.trkey);
                }
            }
            else {
                return this.coerceFromHeapToAtomic(sinfo, arg, from, trgt, into, sguard);
            }
        }
    }
}

export {
    ICPP_WORD_SIZE,
    ICPPTypeEmitter
};
