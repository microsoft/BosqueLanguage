//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIREntityType, MIREntityTypeDecl, MIREphemeralListType, MIRRecordType, MIRTupleType, MIRType } from "../../../compiler/mir_assembly";
import { MIRFieldKey, MIRInvokeKey, MIRResolvedTypeKey, MIRVirtualMethodKey } from "../../../compiler/mir_ops";

import { ICPPType, ICPPTypeEntity, ICPPTypeEphemeralList, ICPPTypeKind, ICPPTypeRegister, ICPPTypeRecord, ICPPTypeSizeInfo, ICPPTypeTuple, RefMask, TranspilerOptions, ICPP_WORD_SIZE, ICPPTypeRefUnion, ICPPTypeInlineUnion } from "./icpp_assembly";

import { ArgumentTag, Argument, ICPPOp, ICPPOpEmitter, ICPPStatementGuard, TargetVar, NONE_VALUE_POSITION } from "./icpp_exp";
import { SourceInfo } from "../../../ast/parser";

import * as assert from "assert";

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

    private computeICCPTypeForUnion(utype: MIRType, tl: ICPPType[]): ICPPType {
        if(tl.every((t) => (t.tkey === "NSCore::None") || t.tkind === ICPPTypeKind.Ref || t.tkind === ICPPTypeKind.UnionRef)) {
            return new ICPPTypeRefUnion(utype.trkey, utype.trkey);
        }
        else {
            let size = Math.max(...tl.map((t) => t.tkind === ICPPTypeKind.UnionInline ? t.allocinfo.inlinedatasize : (ICPP_WORD_SIZE + t.allocinfo.inlinedatasize)));
            let mask: RefMask = "5";
            for(let i = 0; i < (size - ICPP_WORD_SIZE) / ICPP_WORD_SIZE; ++i) {
                mask = mask + "1";
            }

            return new ICPPTypeInlineUnion(utype.trkey, utype.trkey, size, mask);
        }
    }

    private getICPPTypeForTuple(tt: MIRTupleType): ICPPType {
        let idxtypes: MIRResolvedTypeKey[] = [];
        let idxoffsets: number[] = [];
        let size = 0;
        let mask: RefMask = "";

        const icppentries = tt.entries.map((entry) => this.getICPPTypeData(entry.type));
        for(let i = 0; i < icppentries.length; ++i) {
            idxtypes.push(icppentries[i].tkey);
            idxoffsets.push(size);
            size = size + icppentries[i].allocinfo.inlinedatasize;
            mask = mask + icppentries[i].allocinfo.inlinedmask;
        }

        if(this.isUniqueTupleType(this.getMIRType(tt.trkey))) {
            return tt.isvalue 
                ? ICPPTypeTuple.createByValueTuple(tt.trkey, tt.trkey, size, mask, idxtypes, idxoffsets)
                : ICPPTypeTuple.createByRefTuple(tt.trkey, tt.trkey, size, mask, idxtypes, idxoffsets)
        }
        else {
            return tt.isvalue 
                ? new ICPPTypeInlineUnion(tt.trkey, tt.trkey, ICPP_WORD_SIZE + size, "5" + mask)
                : new ICPPTypeRefUnion(tt.trkey, tt.trkey);
        }
    }

    private getICPPTypeForRecord(tt: MIRRecordType): ICPPType {
        let propertynames: string[] = [];
        let propertytypes: MIRResolvedTypeKey[] = [];
        let propertyoffsets: number[] = [];
        let size = 0;
        let mask: RefMask = "";

        const icppentries = tt.entries.map((entry) => this.getICPPTypeData(entry.type));
        for(let i = 0; i < icppentries.length; ++i) {
            propertynames.push(tt.entries[i].name);
            propertytypes.push(icppentries[i].tkey);
            propertyoffsets.push(size);
            size = size + icppentries[i].allocinfo.inlinedatasize;
            mask = mask + icppentries[i].allocinfo.inlinedmask;
        }

        if(this.isUniqueTupleType(this.getMIRType(tt.trkey))) {
            return tt.isvalue 
                ? ICPPTypeRecord.createByValueRecord(tt.trkey, tt.trkey, size, mask, propertynames, propertytypes, propertyoffsets)
                : ICPPTypeRecord.createByRefRecord(tt.trkey, tt.trkey, size, mask, propertynames, propertytypes, propertyoffsets)
        }
        else {
            return tt.isvalue 
                ? new ICPPTypeInlineUnion(tt.trkey, tt.trkey, ICPP_WORD_SIZE + size, "5" + mask)
                : new ICPPTypeRefUnion(tt.trkey, tt.trkey);
        }
    }

    private getICPPTypeForEntity(tt: MIREntityTypeDecl): ICPPTypeEntity {
        let fieldnames: MIRFieldKey[] = [];
        let fieldtypes: MIRResolvedTypeKey[] = [];
        let fieldoffsets: number[] = [];
        let size = 0;
        let mask: RefMask = "";

        const icppentries = tt.fields.map((f) => this.getICPPTypeData(this.getMIRType(f.declaredType)));
        for(let i = 0; i < icppentries.length; ++i) {
            fieldnames.push(tt.fields[i].name);
            fieldtypes.push(icppentries[i].tkey);
            fieldoffsets.push(size);
            size = size + icppentries[i].allocinfo.inlinedatasize;
            mask = mask + icppentries[i].allocinfo.inlinedmask;
        }

        return tt.attributes.includes("struct") 
            ? ICPPTypeEntity.createByValueEntity(tt.tkey, tt.tkey, size, mask, fieldnames, fieldtypes, fieldoffsets)
            : ICPPTypeEntity.createByRefEntity(tt.tkey, tt.tkey, size, mask, fieldnames, fieldtypes, fieldoffsets)
    }

    private getICPPTypeForEphemeralList(tt: MIREphemeralListType): ICPPTypeEphemeralList {
        let idxtypes: MIRResolvedTypeKey[] = [];
        let idxoffsets: number[] = [];
        let size = 0;
        let mask: RefMask = "";

        const icppentries = tt.entries.map((entry) => this.getICPPTypeData(this.getMIRType(entry.trkey)));
        for(let i = 0; i < icppentries.length; ++i) {
            idxtypes.push(icppentries[i].tkey);
            idxoffsets.push(size);
            size = size + icppentries[i].allocinfo.inlinedatasize;
            mask = mask + icppentries[i].allocinfo.inlinedmask;
        }

        return new ICPPTypeEphemeralList(tt.trkey, tt.trkey, size, mask, idxtypes, idxoffsets);
    }

    getICPPTypeData(tt: MIRType): ICPPType {
        if(this.typeDataMap.has(tt.trkey)) {
            return this.typeDataMap.get(tt.trkey) as ICPPType;
        }

        let iidata: ICPPType | undefined = undefined;
        if (this.isType(tt, "NSCore::None")) {
            iidata = new ICPPTypeRegister(tt.trkey, "BSQNone", ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"); 
        }
        else if (this.isType(tt, "NSCore::Bool")) {
            iidata = new ICPPTypeRegister(tt.trkey, "BSQBool", ICPP_WORD_SIZE, 1, "1"); 
        }
        else if (this.isType(tt, "NSCore::Int")) {
            iidata = new ICPPTypeRegister(tt.trkey, "BSQInt", ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"); 
        }
        else if (this.isType(tt, "NSCore::Nat")) {
            iidata = new ICPPTypeRegister(tt.trkey, "BSQNat", ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"); 
        }
        else if (this.isType(tt, "NSCore::BigInt")) {
            iidata = new ICPPType(tt.trkey, "BSQBigInt", ICPPTypeKind.BigNum, new ICPPTypeSizeInfo(3*ICPP_WORD_SIZE, 3*ICPP_WORD_SIZE, 3*ICPP_WORD_SIZE, undefined, "411"), true); 
        }
        else if (this.isType(tt, "NSCore::BigNat")) {
            iidata = new ICPPType(tt.trkey, "BSQBigNat", ICPPTypeKind.BigNum, new ICPPTypeSizeInfo(3*ICPP_WORD_SIZE, 3*ICPP_WORD_SIZE, 3*ICPP_WORD_SIZE, undefined, "411"), true); 
        }
        else if (this.isType(tt, "NSCore::Float")) {
            iidata = new ICPPTypeRegister(tt.trkey, "BSQFloat", ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"); 
        }
        else if (this.isType(tt, "NSCore::Decimal")) {
            iidata = new ICPPTypeRegister(tt.trkey, "BSQDecimal", ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"); 
        }
        else if (this.isType(tt, "NSCore::Rational")) {
            iidata = new ICPPTypeRegister(tt.trkey, "BSQRational", 4*ICPP_WORD_SIZE, 4*ICPP_WORD_SIZE, "1111"); 
        }
        else if (this.isType(tt, "NSCore::StringPos")) {
            iidata = new ICPPTypeRegister(tt.trkey, "BSQStringIterator", 5*ICPP_WORD_SIZE, 5*ICPP_WORD_SIZE, "31121"); 
        }
        else if (this.isType(tt, "NSCore::String")) {
            iidata = new ICPPType(tt.trkey, "BSQString", ICPPTypeKind.String, new ICPPTypeSizeInfo(2*ICPP_WORD_SIZE, 2*ICPP_WORD_SIZE, 2*ICPP_WORD_SIZE, "31", "31"), true);
        }
        else if (this.isType(tt, "NSCore::ByteBuffer")) {
            iidata = new ICPPType(tt.trkey, "BSQByteBuffer", ICPPTypeKind.Ref, ICPPTypeSizeInfo.createByRefTypeInfo(34*ICPP_WORD_SIZE, "2"), true)
        }
        else if(this.isType(tt, "NSCore::ISOTime")) {
            iidata = new ICPPTypeRegister(tt.trkey, "BSQISOTime", ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"); 
        }
        else if(this.isType(tt, "NSCore::LogicalTime")) {
            iidata = new ICPPTypeRegister(tt.trkey, "BSQLogicalTime", ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"); 
        }
        else if(this.isType(tt, "NSCore::UUID")) {
            iidata = new ICPPType(tt.trkey, "BSQUUID", ICPPTypeKind.Ref, ICPPTypeSizeInfo.createByRefTypeInfo(2*ICPP_WORD_SIZE, undefined), true); 
        }
        else if(this.isType(tt, "NSCore::ContentHash")) {
            iidata = new ICPPType(tt.trkey, "BSQContentHash", ICPPTypeKind.Ref, ICPPTypeSizeInfo.createByRefTypeInfo(64*ICPP_WORD_SIZE, undefined), true); 
        }
        else if (this.isType(tt, "NSCore::Regex")) {
            iidata = new ICPPTypeRegister(tt.trkey, "BSQRegex", 2*ICPP_WORD_SIZE, 2*ICPP_WORD_SIZE, "11"); 
        }
        else if (tt.options.length === 1) {
            const topt = tt.options[0];
            if (topt instanceof MIRTupleType) {
                iidata = this.getICPPTypeForTuple(topt);
            }
            else if (topt instanceof MIRRecordType) {
                iidata = this.getICPPTypeForRecord(topt);
            }
            else if(topt instanceof MIREphemeralListType) {
                iidata = this.getICPPTypeForEphemeralList(topt);
            }
            else if(topt instanceof MIREntityType) {
                iidata = this.getICPPTypeForEntity(this.assembly.entityDecls.get(topt.trkey) as MIREntityTypeDecl);
            }
            else {
                const allsubt = [...this.assembly.entityDecls].filter((edcl) => this.assembly.subtypeOf(this.getMIRType(edcl[1].tkey), tt));
                const iccpopts = allsubt.map((edcel) => this.getICPPTypeData(this.getMIRType(edcel[1].tkey)));

                iidata = this.computeICCPTypeForUnion(tt, iccpopts);
            }
        }
        else {
            const iccpopts = tt.options.map((opt) => this.getICPPTypeData(this.getMIRType(opt.trkey)));

            iidata = this.computeICCPTypeForUnion(tt, iccpopts);
        }

        this.typeDataMap.set(tt.trkey, iidata as ICPPType);
        return this.typeDataMap.get(tt.trkey) as ICPPType;
    }

    private coerceIntoUnion(sinfo: SourceInfo, arg: Argument, from: MIRType, trgt: TargetVar, into: MIRType, sguard: ICPPStatementGuard): ICPPOp {
        if(this.isType(from, "NSCore::None")) {
            return ICPPOpEmitter.genNoneInitUnionOp(sinfo, trgt, into.trkey);
        }
        else {
            const icppinto = this.getICPPTypeData(into);

            if(icppinto.tkind === ICPPTypeKind.UnionRef) {
                return ICPPOpEmitter.genDirectAssignOp(sinfo, trgt, into.trkey, arg, sguard);
            }
            else {
                return ICPPOpEmitter.genBoxOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
        }
    }

    private coerceFromUnion(sinfo: SourceInfo, arg: Argument, from: MIRType, trgt: TargetVar, into: MIRType, sguard: ICPPStatementGuard): ICPPOp {
        if(this.isType(into, "NSCore::None")) {
            return ICPPOpEmitter.genDirectAssignOp(sinfo, trgt, into.trkey, { kind: ArgumentTag.Const, location: NONE_VALUE_POSITION }, sguard);
        }
        else {
            const icppfrom = this.getICPPTypeData(from);

            if(icppfrom.tkind === ICPPTypeKind.UnionRef) {
                return ICPPOpEmitter.genDirectAssignOp(sinfo, trgt, into.trkey, arg, sguard);
            }
            else {
                return ICPPOpEmitter.genExtractOp(sinfo, trgt, into.trkey, arg, from.trkey, sguard);
            }
        }
    }

    private coerceEquivReprs(sinfo: SourceInfo, arg: Argument, trgt: TargetVar, into: MIRType, sguard: ICPPStatementGuard): ICPPOp {
        return ICPPOpEmitter.genDirectAssignOp(sinfo, trgt, into.trkey, arg, sguard);
    }

    coerce(sinfo: SourceInfo, arg: Argument, from: MIRType, trgt: TargetVar, into: MIRType, sguard: ICPPStatementGuard): ICPPOp {
        const icppfrom = this.getICPPTypeData(from);
        const icppinto = this.getICPPTypeData(into);

        if(icppinto.tkind === icppfrom.tkind) {
            return this.coerceEquivReprs(sinfo, arg, trgt, into, sguard);
        }
        else if(icppinto.tkind === ICPPTypeKind.UnionInline) {
            return this.coerceIntoUnion(sinfo, arg, from, trgt, into, sguard);
        }
        else if(icppfrom.tkind === ICPPTypeKind.UnionInline) {
            return this.coerceFromUnion(sinfo, arg, from, trgt, into, sguard);
        }
        else if(icppinto.tkind === ICPPTypeKind.UnionRef) {
            return this.coerceIntoUnion(sinfo, arg, from, trgt, into, sguard);
        }
        else {
            assert(icppfrom.tkind === ICPPTypeKind.UnionRef);

            return this.coerceFromUnion(sinfo, arg, from, trgt, into, sguard);
        }
    }
}

export {
    ICPP_WORD_SIZE,
    ICPPTypeEmitter
};
