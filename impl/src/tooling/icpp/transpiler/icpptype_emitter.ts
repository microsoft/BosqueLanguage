//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRConstructableEntityTypeDecl, MIREntityType, MIREntityTypeDecl, MIREnumEntityTypeDecl, MIREphemeralListType, MIRObjectEntityTypeDecl, MIRRecordType, MIRTupleType, MIRType } from "../../../compiler/mir_assembly";
import { MIRFieldKey, MIRGlobalKey, MIRInvokeKey, MIRResolvedTypeKey } from "../../../compiler/mir_ops";

import { ICPPType, ICPPTypeEntity, ICPPTypeEphemeralList, ICPPTypeKind, ICPPTypeRegister, ICPPTypeRecord, ICPPTypeSizeInfo, ICPPTypeTuple, RefMask, TranspilerOptions, ICPP_WORD_SIZE, ICPPTypeRefUnion, ICPPTypeInlineUnion, ICPPParseTag, ICPPTypeSizeInfoSimple, ICPPTypeUniversalUnion } from "./icpp_assembly";

import { ArgumentTag, Argument, ICPPOp, ICPPOpEmitter, ICPPStatementGuard, TargetVar, NONE_VALUE_POSITION } from "./icpp_exp";
import { SourceInfo } from "../../../ast/parser";

import * as assert from "assert";
import { BSQRegex } from "../../../ast/bsqregex";

enum APIEmitTypeTag
{
    NoneTag = 0x0,
    NothingTag,
    BoolTag,
    NatTag,
    IntTag,
    BigNatTag,
    BigIntTag,
    RationalTag,
    FloatTag,
    DecimalTag,
    StringTag,
    StringOfTag,
    DataStringTag,
    ByteBufferTag,
    DateTimeTag,
    TickTimeTag,
    LogicalTimeTag,
    UUIDTag,
    ContentHashTag,
    ConstructableOfType,
    TupleTag,
    RecordTag,
    ContainerTag,
    EnumTag,
    EntityTag,
    UnionTag
};

class ICPPTypeEmitter {
    readonly topts: TranspilerOptions;
    readonly assembly: MIRAssembly;
    
    private namectr: number = 0;
    private allshortnames = new Set<string>();
    private mangledTypeNameMap: Map<string, string> = new Map<string, string>();
    private mangledFunctionNameMap: Map<string, string> = new Map<string, string>();
    private mangledGlobalNameMap: Map<string, string> = new Map<string, string>();

    private typeDataMap: Map<MIRResolvedTypeKey, ICPPType> = new Map<MIRResolvedTypeKey, ICPPType>();
    private typeInfoShallowMap: Map<MIRResolvedTypeKey, ICPPTypeSizeInfoSimple> = new Map<MIRResolvedTypeKey, ICPPTypeSizeInfoSimple>();

    constructor(assembly: MIRAssembly, topts: TranspilerOptions, namectr?: number, mangledTypeNameMap?: Map<string, string>, mangledFunctionNameMap?: Map<string, string>, mangledGlobalNameMap?: Map<string, string>) {
        this.assembly = assembly;
        this.topts = topts;

        this.namectr = namectr || 0;
        this.mangledTypeNameMap = mangledTypeNameMap || new Map<string, string>();
        this.mangledFunctionNameMap = mangledFunctionNameMap || new Map<string, string>();
        this.mangledGlobalNameMap = mangledGlobalNameMap || new Map<string, string>();
    }

    internTypeName(keyid: MIRResolvedTypeKey, shortname: string) {
        if (!this.mangledTypeNameMap.has(keyid)) {
            let cleanname = shortname.replace(/:/g, ".").replace(/[<>, \[\]\{\}\(\)\\\/\#\=\|]/g, "_");
            if(this.allshortnames.has(cleanname)) {
                cleanname = cleanname + "$" + this.namectr++;
            }

            this.mangledTypeNameMap.set(keyid, cleanname);
            this.allshortnames.add(cleanname);
        }
    }

    lookupTypeName(keyid: MIRResolvedTypeKey): string {
        assert(this.mangledTypeNameMap.has(keyid));

        return this.mangledTypeNameMap.get(keyid) as string;
    }

    internFunctionName(keyid: MIRInvokeKey, shortname: string) {
        if (!this.mangledFunctionNameMap.has(keyid)) {
            let cleanname = shortname.replace(/:/g, ".").replace(/[<>, \[\]\{\}\(\)\\\/\#\=\|]/g, "_");
            if(this.allshortnames.has(cleanname)) {
                cleanname = cleanname + "$" + this.namectr++;
            }

            this.mangledFunctionNameMap.set(keyid, cleanname);
            this.allshortnames.add(cleanname);
        }
    }

    lookupFunctionName(keyid: MIRInvokeKey): string {
        assert(this.mangledFunctionNameMap.has(keyid), `Missing -- ${keyid}`);

        return this.mangledFunctionNameMap.get(keyid) as string;
    }

    internGlobalName(keyid: MIRGlobalKey, shortname: string) {
        if (!this.mangledGlobalNameMap.has(keyid)) {
            let cleanname = shortname.replace(/:/g, ".").replace(/[<>, \[\]\{\}\(\)\\\/\#\=\|]/g, "_");
            if(this.allshortnames.has(cleanname)) {
                cleanname = cleanname + "$" + this.namectr++;
            }

            this.mangledGlobalNameMap.set(keyid, cleanname);
            this.allshortnames.add(cleanname);
        }
    }

    lookupGlobalName(keyid: MIRGlobalKey): string {
        assert(this.mangledGlobalNameMap.has(keyid));

        return this.mangledGlobalNameMap.get(keyid) as string;
    }

    getMIRType(tkey: MIRResolvedTypeKey): MIRType {
        return this.assembly.typeMap.get(tkey) as MIRType;
    }

    isType(tt: MIRType, tkey: MIRResolvedTypeKey): boolean {
        return tt.typeID === tkey;
    }

    isUniqueTupleType(tt: MIRType): boolean {
        return tt.options.length === 1 && (tt.options[0] instanceof MIRTupleType);
    }

    isUniqueRecordType(tt: MIRType): boolean {
        return tt.options.length === 1 && (tt.options[0] instanceof MIRRecordType);
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

    isTypeSmallInline(tt: MIRType): boolean {
        if(this.isType(tt, "Core::Bool") || this.isType(tt, "Core::Nat") || this.isType(tt, "Core::Int") || this.isType(tt, "Core::Float") || this.isType(tt, "Core::Decimal")) {
            return true;
        } 
        else if(this.isType(tt, "Core::BigNat") || this.isType(tt, "Core::BigInt") || this.isType(tt, "Core::String")) {
            return true;
        }
        else if(this.isType(tt, "Core::Mask")) {
            return true;
        }
        else {
            return tt.typeID.startsWith("NSCore::StringOf") || tt.typeID.startsWith("NSCore::DataString");
        }
    }

    isTypeInline(tt: MIRType): boolean {
        if(this.isTypeSmallInline(tt)) {
            return true;
        }
        else if(this.isType(tt, "Core::Rational")) {
            return true;
        }
        else if(this.isUniqueTupleType(tt)) {
            const ttup = tt.getUniqueTupleTargetType();
            return ttup.entries.length <= 4 && ttup.entries.every((ee) => this.isTypeSmallInline(ee));
        }
        else if(this.isUniqueRecordType(tt)) {
            const ttrec = tt.getUniqueRecordTargetType();
            return ttrec.entries.length <= 4 && ttrec.entries.every((ee) => this.isTypeSmallInline(ee.ptype));
        }
        else if(this.isUniqueEntityType(tt)) {
            const tted = this.assembly.entityDecls.get(tt.getUniqueCallTargetType().typeID) as MIREntityTypeDecl;
            if(tted instanceof MIREnumEntityTypeDecl) {
                return true;
            }
            else if(tted instanceof MIRConstructableEntityTypeDecl) {
                return this.isTypeSmallInline(this.getMIRType(tted.fromtype));
            }
            else if(tted instanceof MIRObjectEntityTypeDecl) {
                return tted.fields.length <= 4 && tted.fields.every((ff) => this.isTypeSmallInline(this.getMIRType(ff.declaredType)));
            }
            else {
                return false;
            }
        }
        else {
            return false;
        }
    }

    private computeICCPTypeForUnion(utype: MIRType, tl: ICPPType[]): ICPPType {
        const iskey = this.assembly.subtypeOf(utype, this.getMIRType("NSCore::KeyType"));

        if(tl.some((t) => t.tkind === ICPPTypeKind.UnionUniversal)) {
            return new ICPPTypeUniversalUnion(utype.typeID);
        }
        else if(tl.every((t) => t.tkind === ICPPTypeKind.Ref || t.tkind === ICPPTypeKind.UnionRef)) {
            return new ICPPTypeRefUnion(utype.typeID, iskey);
        }
        else {
            let size = Math.max(...tl.map((t) => t.tkind === ICPPTypeKind.UnionInline ? t.allocinfo.inlinedatasize : (ICPP_WORD_SIZE + t.allocinfo.inlinedatasize)));

            let mask: RefMask = "5";
            for(let i = 0; i < (size - ICPP_WORD_SIZE) / ICPP_WORD_SIZE; ++i) {
                mask = mask + "1";
            }

            return new ICPPTypeInlineUnion(utype.typeID, size, mask, iskey);
        }
    }

    private getICPPTypeInfoForTupleShallow(tt: MIRTupleType): ICPPTypeSizeInfoSimple {
        let size = 0;
        let mask: RefMask = "";

        for (let i = 0; i < tt.entries.length; ++i) {
            const sizeinfo = this.getICPPTypeInfoShallow(tt.entries[i]);

            size = size + sizeinfo.inlinedatasize;
            mask = mask + sizeinfo.inlinedmask;
        }

        return ICPPTypeSizeInfoSimple.createByValueTypeInfo(tt.typeID, size, mask);
    }

    private getICPPTypeForTuple(tt: MIRTupleType): ICPPType {
        let idxtypes: MIRResolvedTypeKey[] = [];
        let idxoffsets: number[] = [];
        let size = 0;
        let mask: RefMask = "";

        const icppentries = tt.entries.map((entry) => this.getICPPTypeInfoShallow(entry));
        for(let i = 0; i < icppentries.length; ++i) {
            idxtypes.push(icppentries[i].tkey);
            idxoffsets.push(size);
            size = size + icppentries[i].inlinedatasize;
            mask = mask + icppentries[i].inlinedmask;
        }

        const iskey = this.assembly.subtypeOf(this.getMIRType(tt.typeID), this.getMIRType("NSCore::KeyType"));
        if(this.isUniqueTupleType(this.getMIRType(tt.typeID))) {
            return this.isTypeInline(this.getMIRType(tt.typeID)) 
                ? ICPPTypeTuple.createByValueTuple(tt.typeID, size, mask, idxtypes, idxoffsets, iskey)
                : ICPPTypeTuple.createByRefTuple(tt.typeID, size, mask, idxtypes, idxoffsets, iskey)
        }
        else {
            return tt.isvalue 
                ? new ICPPTypeInlineUnion(tt.trkey, ICPP_WORD_SIZE + size, "5" + mask, iskey)
                : new ICPPTypeRefUnion(tt.trkey, iskey);
        }
    }

    private getICPPTypeInfoForRecordShallow(tt: MIRRecordType): ICPPTypeSizeInfoSimple {
        if(!tt.isvalue) {
            return ICPPTypeSizeInfoSimple.createByRefTypeInfo(tt.trkey);
        }
        else {
            let size = 0;
            let mask: RefMask = "";

            for(let i = 0; i < tt.entries.length; ++i) {
                const sizeinfo = this.getICPPTypeInfoShallow(tt.entries[i].type);

                size = size + sizeinfo.inlinedatasize;
                mask = mask + sizeinfo.inlinedmask;
            }

            return ICPPTypeSizeInfoSimple.createByValueTypeInfo(tt.trkey, size, mask);
        }
    }

    private getICPPTypeForRecord(tt: MIRRecordType): ICPPType {
        let propertynames: string[] = [];
        let propertytypes: MIRResolvedTypeKey[] = [];
        let propertyoffsets: number[] = [];
        let size = 0;
        let mask: RefMask = "";

        const icppentries = tt.entries.map((entry) => this.getICPPTypeInfoShallow(entry.type));
        for(let i = 0; i < icppentries.length; ++i) {
            propertynames.push(tt.entries[i].name);
            propertytypes.push(icppentries[i].tkey);
            propertyoffsets.push(size);
            size = size + icppentries[i].inlinedatasize;
            mask = mask + icppentries[i].inlinedmask;
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

    private getICPPTypeInfoForEntityShallow(tt: MIREntityTypeDecl): ICPPTypeSizeInfoSimple {
        if(tt.attributes.includes("struct")) {
            return ICPPTypeSizeInfoSimple.createByRefTypeInfo(tt.tkey);
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.StringOfDecl) || tt.specialDecls.has(MIRSpecialTypeCategory.DataStringDecl)) {
            return this.getICPPTypeInfoShallow(this.getMIRType("NSCore::String"));
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.TypeDeclNumeric)) {
            return this.getICPPTypeInfoShallow(this.getMIRType((tt.specialTemplateInfo as {tname: string, tkind: MIRResolvedTypeKey}[])[0].tkind));
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.EnumTypeDecl)) {
            return this.getICPPTypeInfoShallow(this.getMIRType((tt.specialTemplateInfo as {tname: string, tkind: MIRResolvedTypeKey}[])[0].tkind));
        }
        else {
            let size = 0;
            let mask: RefMask = "";

            for(let i = 0; i < tt.fields.length; ++i) {
                const sizeinfo = this.getICPPTypeInfoShallow(this.getMIRType(tt.fields[i].declaredType));

                size = size + sizeinfo.inlinedatasize;
                mask = mask + sizeinfo.inlinedmask;
            }

            return ICPPTypeSizeInfoSimple.createByValueTypeInfo(tt.tkey, size, mask);
        }
    }

    private getICPPTypeForEntity(tt: MIREntityTypeDecl): ICPPTypeEntity {
        let fieldnames: MIRFieldKey[] = [];
        let fieldtypes: MIRResolvedTypeKey[] = [];
        let fieldoffsets: number[] = [];
        let size = 0;
        let mask: RefMask = "";

        const icppentries = tt.fields.map((fd) => this.getICPPTypeInfoShallow(this.getMIRType(fd.declaredType)));
        for(let i = 0; i < icppentries.length; ++i) {
            fieldnames.push(tt.fields[i].name);
            fieldtypes.push(tt.fields[i].declaredType);
            fieldoffsets.push(size);
            size = size + icppentries[i].inlinedatasize;
            mask = mask + icppentries[i].inlinedmask;
        }

        let ptag: ICPPParseTag = ICPPParseTag.EntityTag;
        let extradata: any = undefined;
        if(tt.specialDecls.has(MIRSpecialTypeCategory.ValidatorTypeDecl)) {
            ptag = ICPPParseTag.ValidatorTag;
            extradata = this.assembly.validatorRegexs.get(tt.tkey) as BSQRegex;
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.StringOfDecl)) {
            ptag = ICPPParseTag.StringOfTag;
            extradata = (tt.specialTemplateInfo as {tname: string, tkind: MIRResolvedTypeKey}[])[0].tkind
            const ecc = this.getICPPTypeInfoShallow(this.getMIRType("NSCore::String"));

            size += ecc.inlinedatasize;
            mask += ecc.inlinedmask;
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.DataStringDecl)) {
            ptag = ICPPParseTag.DataStringTag;
            extradata = (tt.specialTemplateInfo as {tname: string, tkind: MIRResolvedTypeKey}[])[0].tkind;
            const ecc = this.getICPPTypeInfoShallow(this.getMIRType("NSCore::String"));
            
            size += ecc.inlinedatasize;
            mask += ecc.inlinedmask;
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.TypeDeclNumeric) || tt.specialDecls.has(MIRSpecialTypeCategory.TypeDeclDecl)) {
            //
            //TODO: this is odd... we want to handle general typedecl that are of API types as well somehow so we need to adjust this a bit
            //
            ptag = ICPPParseTag.TypedNumberTag;
            extradata = (tt.specialTemplateInfo as {tname: string, tkind: MIRResolvedTypeKey}[])[0].tkind;
            const ecc = this.getICPPTypeInfoShallow(this.getMIRType(extradata as MIRResolvedTypeKey));
            
            
            size += ecc.inlinedatasize;
            mask += ecc.inlinedmask;
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.EnumTypeDecl)) {
            ptag = ICPPParseTag.EnumTag;
            extradata = (tt.specialTemplateInfo as {tname: string, tkind: MIRResolvedTypeKey}[])[0].tkind;
            const ecc = this.getICPPTypeInfoShallow(this.getMIRType(extradata as MIRResolvedTypeKey));
            
            size += ecc.inlinedatasize;
            mask += ecc.inlinedmask;
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.BufferDecl)) {
            //
            //TODO: implement this representation in the C++ interpreter etc.
            //
            assert(false, "Buffer is not implemented yet");
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.DataBufferDecl)) {
            //
            //TODO: implement this representation in the C++ interpreter etc.
            //
            assert(false, "Buffer is not implemented yet");
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.VectorTypeDecl)) {
            ptag = ICPPParseTag.VectorTag;
            extradata = this.getICPPTypeInfoShallow(this.getMIRType((tt.specialTemplateInfo as {tname: string, tkind: MIRResolvedTypeKey}[])[0].tkind));
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.ListTypeDecl)) {
            ptag = ICPPParseTag.ListTag;
            extradata = this.getICPPTypeInfoShallow(this.getMIRType((tt.specialTemplateInfo as {tname: string, tkind: MIRResolvedTypeKey}[])[0].tkind));
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.StackTypeDecl)) {
            ptag = ICPPParseTag.StackTag;
            extradata = this.getICPPTypeInfoShallow(this.getMIRType((tt.specialTemplateInfo as {tname: string, tkind: MIRResolvedTypeKey}[])[0].tkind));
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.QueueTypeDecl)) {
            ptag = ICPPParseTag.QueueTag;
            extradata = this.getICPPTypeInfoShallow(this.getMIRType((tt.specialTemplateInfo as {tname: string, tkind: MIRResolvedTypeKey}[])[0].tkind));
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.SetTypeDecl)) {
            ptag = ICPPParseTag.SetTag;
            extradata = this.getICPPTypeInfoShallow(this.getMIRType((tt.specialTemplateInfo as {tname: string, tkind: MIRResolvedTypeKey}[])[0].tkind));
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.MapTypeDecl)) {
            ptag = ICPPParseTag.MapTag;
            const ktype = this.getICPPTypeInfoShallow(this.getMIRType(((tt.specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[]).find((tke) => tke.tname === "K") as { tname: string, tkind: MIRResolvedTypeKey }).tkind));
            const vtype = this.getICPPTypeInfoShallow(this.getMIRType(((tt.specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[]).find((tke) => tke.tname === "V") as { tname: string, tkind: MIRResolvedTypeKey }).tkind));
            extradata = [ktype, vtype];
        }
        else {
            //No other tags handled yet
        }

        const iskey = this.assembly.subtypeOf(this.getMIRType(tt.tkey), this.getMIRType("NSCore::KeyType"));
        return tt.attributes.includes("struct") 
            ? ICPPTypeEntity.createByValueEntity(ptag, tt.tkey, size, mask, fieldnames, fieldtypes, fieldoffsets, iskey, extradata)
            : ICPPTypeEntity.createByRefEntity(ptag, tt.tkey, size, mask, fieldnames, fieldtypes, fieldoffsets, iskey, extradata);
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

    getICPPTypeInfoShallow(tt: MIRType): ICPPTypeSizeInfoSimple {
        if(this.typeInfoShallowMap.has(tt.typeID)) {
            return this.typeInfoShallowMap.get(tt.typeID) as ICPPTypeSizeInfoSimple;
        }

        if(!this.isTypeInline(tt)) {
            this.typeInfoShallowMap.set(tt.typeID, ICPPTypeSizeInfoSimple.createByRefTypeInfo(tt.typeID));
            return this.typeInfoShallowMap.get(tt.typeID) as ICPPTypeSizeInfoSimple;
        }

        let iidata: ICPPTypeSizeInfoSimple | undefined = undefined;
        if (this.isType(tt, "NSCore::None")) {
            iidata = ICPPTypeSizeInfoSimple.createByRegisterTypeInfo(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"); 
        }
        else if (this.isType(tt, "NSCore::Bool")) {
            iidata = ICPPTypeSizeInfoSimple.createByRegisterTypeInfo(tt.trkey, ICPP_WORD_SIZE, 1, "1"); 
        }
        else if (this.isType(tt, "NSCore::Int")) {
            iidata = ICPPTypeSizeInfoSimple.createByRegisterTypeInfo(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"); 
        }
        else if (this.isType(tt, "NSCore::Nat")) {
            iidata = ICPPTypeSizeInfoSimple.createByRegisterTypeInfo(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"); 
        }
        else if (this.isType(tt, "NSCore::BigInt")) {
            iidata = ICPPTypeSizeInfoSimple.createByValueTypeInfo(tt.trkey, 3*ICPP_WORD_SIZE, "411"); 
        }
        else if (this.isType(tt, "NSCore::BigNat")) {
            iidata = ICPPTypeSizeInfoSimple.createByValueTypeInfo(tt.trkey,3*ICPP_WORD_SIZE, "411"); 
        }
        else if (this.isType(tt, "NSCore::Float")) {
            iidata = ICPPTypeSizeInfoSimple.createByRegisterTypeInfo(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"); 
        }
        else if (this.isType(tt, "NSCore::Decimal")) {
            iidata = ICPPTypeSizeInfoSimple.createByRegisterTypeInfo(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"); 
        }
        else if (this.isType(tt, "NSCore::Rational")) {
            iidata = ICPPTypeSizeInfoSimple.createByRegisterTypeInfo(tt.trkey, 4*ICPP_WORD_SIZE, 4*ICPP_WORD_SIZE, "1111"); 
        }
        else if (this.isType(tt, "NSCore::StringPos")) {
            iidata = ICPPTypeSizeInfoSimple.createByRegisterTypeInfo(tt.trkey, 5*ICPP_WORD_SIZE, 5*ICPP_WORD_SIZE, "31121"); 
        }
        else if (this.isType(tt, "NSCore::String")) {
            iidata = ICPPTypeSizeInfoSimple.createByValueTypeInfo(tt.trkey, 2*ICPP_WORD_SIZE, "31");
        }
        else if (this.isType(tt, "NSCore::ByteBuffer")) {
            iidata = ICPPTypeSizeInfoSimple.createByRefTypeInfo(tt.trkey);
        }
        else if(this.isType(tt, "NSCore::ISOTime")) {
            iidata = ICPPTypeSizeInfoSimple.createByRegisterTypeInfo(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"); 
        }
        else if(this.isType(tt, "NSCore::LogicalTime")) {
            iidata = ICPPTypeSizeInfoSimple.createByRegisterTypeInfo(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1"); 
        }
        else if(this.isType(tt, "NSCore::UUID")) {
            iidata = ICPPTypeSizeInfoSimple.createByRefTypeInfo(tt.trkey);
        }
        else if(this.isType(tt, "NSCore::ContentHash")) {
            iidata = ICPPTypeSizeInfoSimple.createByRefTypeInfo(tt.trkey); 
        }
        else if (this.isType(tt, "NSCore::Regex")) {
            iidata = ICPPTypeSizeInfoSimple.createByRegisterTypeInfo(tt.trkey, 2*ICPP_WORD_SIZE, 2*ICPP_WORD_SIZE, "11"); 
        }
        else if (tt.options.length === 1) {
            const topt = tt.options[0];
            if (topt instanceof MIRTupleType) {
                iidata = this.getICPPTypeInfoForTupleShallow(topt);
            }
            else if (topt instanceof MIRRecordType) {
                iidata = this.getICPPTypeInfoForRecordShallow(topt);
            }
            else if(topt instanceof MIREphemeralListType) {
                const icppel = this.getICPPTypeForEphemeralList(topt);
                iidata = ICPPTypeSizeInfoSimple.createByValueTypeInfo(tt.trkey, icppel.allocinfo.inlinedatasize, icppel.allocinfo.inlinedmask);
            }
            else if(topt instanceof MIREntityType) {
                iidata = this.getICPPTypeInfoForEntityShallow(this.assembly.entityDecls.get(topt.trkey) as MIREntityTypeDecl);
            }
            else {
                const allsubt = [...this.assembly.entityDecls].filter((edcl) => this.assembly.subtypeOf(this.getMIRType(edcl[1].tkey), tt));
                const iccpopts = allsubt.map((edcel) => this.getICPPTypeData(this.getMIRType(edcel[1].tkey)));

                const icppel = this.computeICCPTypeForUnion(tt, iccpopts);
                if(icppel.tkind === ICPPTypeKind.UnionRef) {
                    iidata = ICPPTypeSizeInfoSimple.createByRefTypeInfo(tt.trkey);
                }
                else {
                    iidata = ICPPTypeSizeInfoSimple.createByValueTypeInfo(tt.trkey, icppel.allocinfo.inlinedatasize, icppel.allocinfo.inlinedmask);
                }
            }
        }
        else {
            const iccpopts = tt.options.map((opt) => this.getICPPTypeData(this.getMIRType(opt.trkey)));

            const icppel = this.computeICCPTypeForUnion(tt, iccpopts);
            if(icppel.tkind === ICPPTypeKind.UnionRef) {
                iidata = ICPPTypeSizeInfoSimple.createByRefTypeInfo(tt.trkey);
            }
            else {
                iidata = ICPPTypeSizeInfoSimple.createByValueTypeInfo(tt.trkey, icppel.allocinfo.inlinedatasize, icppel.allocinfo.inlinedmask);
            }
        }

        this.typeInfoShallowMap.set(tt.trkey, iidata as ICPPTypeSizeInfoSimple);
        return this.typeInfoShallowMap.get(tt.trkey) as ICPPTypeSizeInfoSimple;
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
            iidata = new ICPPType(ICPPParseTag.BuiltinTag, tt.trkey, ICPPTypeKind.String, new ICPPTypeSizeInfo(2*ICPP_WORD_SIZE, 2*ICPP_WORD_SIZE, 2*ICPP_WORD_SIZE, undefined, "31"), true);
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
