//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIREntityType, MIREntityTypeDecl, MIREphemeralListType, MIRFieldDecl, MIRRecordType, MIRSpecialTypeCategory, MIRTupleType, MIRType } from "../../../compiler/mir_assembly";
import { MIRFieldKey, MIRResolvedTypeKey } from "../../../compiler/mir_ops";

import { ICPPType, ICPPTypeEntity, ICPPTypeEphemeralList, ICPPTypeKind, ICPPTypeRegister, ICPPTypeRecord, ICPPTypeSizeInfo, ICPPTypeTuple, RefMask, TranspilerOptions, ICPP_WORD_SIZE, ICPPTypeRefUnion, ICPPTypeInlineUnion, ICPPParseTag } from "./icpp_assembly";

import { ArgumentTag, Argument, ICPPOp, ICPPOpEmitter, ICPPStatementGuard, TargetVar, NONE_VALUE_POSITION } from "./icpp_exp";
import { SourceInfo } from "../../../ast/parser";

import * as assert from "assert";
import { BSQRegex } from "../../../ast/bsqregex";

class ICPPTypeEmitter {
    readonly topts: TranspilerOptions;
    readonly assembly: MIRAssembly;
    
    private typeDataMap: Map<MIRResolvedTypeKey, ICPPType> = new Map<MIRResolvedTypeKey, ICPPType>();

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

    private computeICCPTypeForUnion(utype: MIRType, tl: ICPPType[]): ICPPType {
        const iskey = this.assembly.subtypeOf(utype, this.getMIRType("NSCore::KeyType"));

        if(tl.every((t) => (t.tkey === "NSCore::None") || t.tkind === ICPPTypeKind.Ref || t.tkind === ICPPTypeKind.UnionRef)) {
            return new ICPPTypeRefUnion(utype.trkey, iskey);
        }
        else {
            let size = Math.max(...tl.map((t) => t.tkind === ICPPTypeKind.UnionInline ? t.allocinfo.inlinedatasize : (ICPP_WORD_SIZE + t.allocinfo.inlinedatasize)));
            let mask: RefMask = "5";
            for(let i = 0; i < (size - ICPP_WORD_SIZE) / ICPP_WORD_SIZE; ++i) {
                mask = mask + "1";
            }

            return new ICPPTypeInlineUnion(utype.trkey, size, mask, iskey);
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

        const iskey = this.assembly.subtypeOf(this.getMIRType(tt.trkey), this.getMIRType("NSCore::KeyType"));
        if(this.isUniqueTupleType(this.getMIRType(tt.trkey))) {
            return tt.isvalue 
                ? ICPPTypeTuple.createByValueTuple(tt.trkey, size, mask, idxtypes, idxoffsets, iskey)
                : ICPPTypeTuple.createByRefTuple(tt.trkey, size, mask, idxtypes, idxoffsets, iskey)
        }
        else {
            return tt.isvalue 
                ? new ICPPTypeInlineUnion(tt.trkey, ICPP_WORD_SIZE + size, "5" + mask, iskey)
                : new ICPPTypeRefUnion(tt.trkey, iskey);
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

        const iskey = this.assembly.subtypeOf(this.getMIRType(tt.trkey), this.getMIRType("NSCore::KeyType"));
        if(this.isUniqueRecordType(this.getMIRType(tt.trkey))) {
            return tt.isvalue 
                ? ICPPTypeRecord.createByValueRecord(tt.trkey, size, mask, propertynames, propertytypes, propertyoffsets, iskey)
                : ICPPTypeRecord.createByRefRecord(tt.trkey, size, mask, propertynames, propertytypes, propertyoffsets, iskey)
        }
        else {
            return tt.isvalue 
                ? new ICPPTypeInlineUnion(tt.trkey, ICPP_WORD_SIZE + size, "5" + mask, iskey)
                : new ICPPTypeRefUnion(tt.trkey, iskey);
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

        let ptag: ICPPParseTag = ICPPParseTag.EntityTag;
        let extradata: any = undefined;
        if(tt.specialDecls.has(MIRSpecialTypeCategory.ValidatorTypeDecl)) {
            ptag = ICPPParseTag.ValidatorTag;
            extradata = this.assembly.validatorRegexs.get(tt.tkey) as BSQRegex;
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.StringOfDecl)) {
            ptag = ICPPParseTag.StringOfTag;

            const ttdecl = this.assembly.entityDecls.get(tt.tkey) as MIREntityTypeDecl;
            const ctype = ((ttdecl.specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[]).find((tke) => tke.tname === "T") as { tname: string, tkind: MIRResolvedTypeKey }).tkind;
            extradata = ctype;
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.DataStringDecl)) {
            ptag = ICPPParseTag.DataStringTag;
            
            const ttdecl = this.assembly.entityDecls.get(tt.tkey) as MIREntityTypeDecl;
            const ctype = ((ttdecl.specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[]).find((tke) => tke.tname === "T") as { tname: string, tkind: MIRResolvedTypeKey }).tkind;
            extradata = ctype;
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.TypeDeclNumeric) || tt.specialDecls.has(MIRSpecialTypeCategory.TypeDeclDecl)) {
            //
            //TODO: this is odd... we want to handle general typedecl that are of API types as well somehow so we need to adjust this a bit
            //
            ptag = ICPPParseTag.TypedNumberTag;

            const tdecl = this.assembly.entityDecls.get(tt.tkey) as MIREntityTypeDecl;
            const mf = tdecl.fields.find((ff) => ff.fname == "v") as MIRFieldDecl;
            extradata = mf.declaredType;
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.VectorTypeDecl)) {
            ptag = ICPPParseTag.VectorTag;

            const ttdecl = this.assembly.entityDecls.get(tt.tkey) as MIREntityTypeDecl;
            const ctype = ((ttdecl.specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[]).find((tke) => tke.tname === "T") as { tname: string, tkind: MIRResolvedTypeKey }).tkind;
            extradata = ctype;
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.ListTypeDecl)) {
            ptag = ICPPParseTag.ListTag;

            const ttdecl = this.assembly.entityDecls.get(tt.tkey) as MIREntityTypeDecl;
            const ctype = ((ttdecl.specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[]).find((tke) => tke.tname === "T") as { tname: string, tkind: MIRResolvedTypeKey }).tkind;
            extradata = ctype;
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.StackTypeDecl)) {
            ptag = ICPPParseTag.StackTag;

            const ttdecl = this.assembly.entityDecls.get(tt.tkey) as MIREntityTypeDecl;
            const ctype = ((ttdecl.specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[]).find((tke) => tke.tname === "T") as { tname: string, tkind: MIRResolvedTypeKey }).tkind;
            extradata = ctype;
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.QueueTypeDecl)) {
            ptag = ICPPParseTag.QueueTag;

            const ttdecl = this.assembly.entityDecls.get(tt.tkey) as MIREntityTypeDecl;
            const ctype = ((ttdecl.specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[]).find((tke) => tke.tname === "T") as { tname: string, tkind: MIRResolvedTypeKey }).tkind;
            extradata = ctype;
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.SetTypeDecl)) {
            ptag = ICPPParseTag.SetTag;

            const ttdecl = this.assembly.entityDecls.get(tt.tkey) as MIREntityTypeDecl;
            const ctype = ((ttdecl.specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[]).find((tke) => tke.tname === "T") as { tname: string, tkind: MIRResolvedTypeKey }).tkind;
            extradata = ctype;
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.MapTypeDecl)) {
            ptag = ICPPParseTag.MapTag;

            const ttdecl = this.assembly.entityDecls.get(tt.tkey) as MIREntityTypeDecl;
            const ktype = ((ttdecl.specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[]).find((tke) => tke.tname === "K") as { tname: string, tkind: MIRResolvedTypeKey }).tkind;
            const vtype = ((ttdecl.specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[]).find((tke) => tke.tname === "V") as { tname: string, tkind: MIRResolvedTypeKey }).tkind;
            extradata = [ktype, vtype];
        }
        else {
            //No other tags handled yet
        }

        const iskey = this.assembly.subtypeOf(this.getMIRType(tt.tkey), this.getMIRType("NSCore::KeyType"));
        return tt.attributes.includes("struct") 
            ? ICPPTypeEntity.createByValueEntity(ptag, tt.tkey, size, mask, fieldnames, fieldtypes, fieldoffsets, iskey, extradata)
            : ICPPTypeEntity.createByRefEntity(ptag, tt.tkey, size, mask, fieldnames, fieldtypes, fieldoffsets, iskey, extradata)
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

        return new ICPPTypeEphemeralList(tt.trkey, size, mask, idxtypes, idxoffsets);
    }

    getICPPTypeData(tt: MIRType): ICPPType {
        if(this.typeDataMap.has(tt.trkey)) {
            return this.typeDataMap.get(tt.trkey) as ICPPType;
        }

        let iidata: ICPPType | undefined = undefined;
        if (this.isType(tt, "NSCore::None")) {
            iidata = new ICPPTypeRegister(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1", true); 
        }
        else if (this.isType(tt, "NSCore::Bool")) {
            iidata = new ICPPTypeRegister(tt.trkey, ICPP_WORD_SIZE, 1, "1", true); 
        }
        else if (this.isType(tt, "NSCore::Int")) {
            iidata = new ICPPTypeRegister(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1", true); 
        }
        else if (this.isType(tt, "NSCore::Nat")) {
            iidata = new ICPPTypeRegister(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1", true); 
        }
        else if (this.isType(tt, "NSCore::BigInt")) {
            iidata = new ICPPType(ICPPParseTag.BuiltinTag, tt.trkey, ICPPTypeKind.BigNum, new ICPPTypeSizeInfo(3*ICPP_WORD_SIZE, 3*ICPP_WORD_SIZE, 3*ICPP_WORD_SIZE, undefined, "411"), true); 
        }
        else if (this.isType(tt, "NSCore::BigNat")) {
            iidata = new ICPPType(ICPPParseTag.BuiltinTag, tt.trkey, ICPPTypeKind.BigNum, new ICPPTypeSizeInfo(3*ICPP_WORD_SIZE, 3*ICPP_WORD_SIZE, 3*ICPP_WORD_SIZE, undefined, "411"), true); 
        }
        else if (this.isType(tt, "NSCore::Float")) {
            iidata = new ICPPTypeRegister(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1", false); 
        }
        else if (this.isType(tt, "NSCore::Decimal")) {
            iidata = new ICPPTypeRegister(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1", false); 
        }
        else if (this.isType(tt, "NSCore::Rational")) {
            iidata = new ICPPTypeRegister(tt.trkey, 4*ICPP_WORD_SIZE, 4*ICPP_WORD_SIZE, "1111", false); 
        }
        else if (this.isType(tt, "NSCore::StringPos")) {
            iidata = new ICPPTypeRegister(tt.trkey, 5*ICPP_WORD_SIZE, 5*ICPP_WORD_SIZE, "31121", false); 
        }
        else if (this.isType(tt, "NSCore::String")) {
            iidata = new ICPPType(ICPPParseTag.BuiltinTag, tt.trkey, ICPPTypeKind.String, new ICPPTypeSizeInfo(2*ICPP_WORD_SIZE, 2*ICPP_WORD_SIZE, 2*ICPP_WORD_SIZE, "31", "31"), true);
        }
        else if (this.isType(tt, "NSCore::ByteBuffer")) {
            iidata = new ICPPType(ICPPParseTag.BuiltinTag, tt.trkey, ICPPTypeKind.Ref, ICPPTypeSizeInfo.createByRefTypeInfo(34*ICPP_WORD_SIZE, "2"), false);
        }
        else if(this.isType(tt, "NSCore::ISOTime")) {
            iidata = new ICPPTypeRegister(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1", false); 
        }
        else if(this.isType(tt, "NSCore::LogicalTime")) {
            iidata = new ICPPTypeRegister(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1", true); 
        }
        else if(this.isType(tt, "NSCore::UUID")) {
            iidata = new ICPPType(ICPPParseTag.BuiltinTag, tt.trkey, ICPPTypeKind.Ref, ICPPTypeSizeInfo.createByRefTypeInfo(2*ICPP_WORD_SIZE, undefined), true); 
        }
        else if(this.isType(tt, "NSCore::ContentHash")) {
            iidata = new ICPPType(ICPPParseTag.BuiltinTag, tt.trkey, ICPPTypeKind.Ref, ICPPTypeSizeInfo.createByRefTypeInfo(64*ICPP_WORD_SIZE, undefined), true); 
        }
        else if (this.isType(tt, "NSCore::Regex")) {
            iidata = new ICPPTypeRegister(tt.trkey, 2*ICPP_WORD_SIZE, 2*ICPP_WORD_SIZE, "11", false); 
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
