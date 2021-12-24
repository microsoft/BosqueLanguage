//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRConstructableEntityTypeDecl, MIRConstructableInternalEntityTypeDecl, MIREntityType, MIREntityTypeDecl, MIREnumEntityTypeDecl, MIREphemeralListType, MIRInternalEntityTypeDecl, MIRMaskEntityTypeDecl, MIRObjectEntityTypeDecl, MIRPartialVectorEntityTypeDecl, MIRPrimitiveCollectionEntityTypeDecl, MIRPrimitiveInternalEntityTypeDecl, MIRPrimitiveListEntityTypeDecl, MIRPrimitiveMapEntityTypeDecl, MIRPrimitiveQueueEntityTypeDecl, MIRPrimitiveSetEntityTypeDecl, MIRPrimitiveStackEntityTypeDecl, MIRRecordType, MIRTupleType, MIRType } from "../../../compiler/mir_assembly";
import { MIRFieldKey, MIRGlobalKey, MIRInvokeKey, MIRResolvedTypeKey } from "../../../compiler/mir_ops";

import { ICPPTypeSizeInfoSimple, ICPPTypeSizeInfo, RefMask, TranspilerOptions, ICPP_WORD_SIZE, ICPPLayoutInfo,  } from "./icpp_assembly";

import { ArgumentTag, Argument, ICPPOp, ICPPOpEmitter, ICPPStatementGuard, TargetVar, NONE_VALUE_POSITION } from "./icpp_exp";
import { SourceInfo } from "../../../ast/parser";

import * as assert from "assert";
import { BSQRegex } from "../../../ast/bsqregex";

class ICPPTypeEmitter {
    readonly topts: TranspilerOptions;
    readonly assembly: MIRAssembly;
    
    private namectr: number = 0;
    private allshortnames = new Set<string>();
    private mangledTypeNameMap: Map<string, string> = new Map<string, string>();
    private mangledFunctionNameMap: Map<string, string> = new Map<string, string>();
    private mangledGlobalNameMap: Map<string, string> = new Map<string, string>();

    private typeDataMap: Map<MIRResolvedTypeKey, ICPPLayoutInfo> = new Map<MIRResolvedTypeKey, ICPPLayoutInfo>();
    private typeInfoShallowMap: Map<MIRResolvedTypeKey, ICPPTypeSizeInfoSimple> = new Map<MIRResolvedTypeKey, ICPPTypeSizeInfoSimple>();

    constructor(assembly: MIRAssembly, topts: TranspilerOptions, namectr?: number, mangledTypeNameMap?: Map<string, string>, mangledFunctionNameMap?: Map<string, string>, mangledGlobalNameMap?: Map<string, string>) {
        this.assembly = assembly;
        this.topts = topts;

        this.namectr = namectr || 0;
        this.mangledTypeNameMap = mangledTypeNameMap || new Map<string, string>();
        this.mangledFunctionNameMap = mangledFunctionNameMap || new Map<string, string>();
        this.mangledGlobalNameMap = mangledGlobalNameMap || new Map<string, string>();
    }

    internTypeName(keyid: MIRResolvedTypeKey) {
        if (!this.mangledTypeNameMap.has(keyid)) {
            let cleanname = keyid;
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
            let cleanname = shortname;
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
            let cleanname = shortname;
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

    getICPPTypeInfoShallow(tt: MIRType): ICPPTypeSizeInfoSimple {
        if(this.typeInfoShallowMap.has(tt.typeID)) {
            return this.typeInfoShallowMap.get(tt.typeID) as ICPPTypeSizeInfoSimple;
        }

        this.internTypeName(tt.typeID);
        let res: ICPPTypeSizeInfoSimple | undefined = undefined;

        if(this.isUniqueTupleType(tt)) {
            let isinline = true;
            let size = 0;
            let mask: RefMask = "";

            const tuptt = tt.getUniqueTupleTargetType();
            for (let i = 0; i < tuptt.entries.length; ++i) {
                const sizeinfo = this.getICPPTypeInfoShallow(tuptt.entries[i]);

                isinline = isinline && sizeinfo.issmallinlinevalue;
                size = size + sizeinfo.inlinedatasize;
                mask = mask + sizeinfo.inlinedmask;
            }

            if(tuptt.entries.length <= 4 && isinline) {
                res = ICPPTypeSizeInfoSimple.createByValueSizeInfo(tt.typeID, size, mask, false);
            }
            else {
                res = ICPPTypeSizeInfoSimple.createByRefSizeInfo(tt.typeID);
            }
        }
        else if(this.isUniqueRecordType(tt)) {
            let isinline = true;
            let size = 0;
            let mask: RefMask = "";

            const rectt = tt.getUniqueRecordTargetType();
            for (let i = 0; i < rectt.entries.length; ++i) {
                const sizeinfo = this.getICPPTypeInfoShallow(rectt.entries[i].ptype);

                isinline = isinline && sizeinfo.issmallinlinevalue;
                size = size + sizeinfo.inlinedatasize;
                mask = mask + sizeinfo.inlinedmask;
            }

            if(rectt.entries.length <= 4 && isinline) {
                res = ICPPTypeSizeInfoSimple.createByValueSizeInfo(tt.typeID, size, mask, false);
            }
            else {
                res = ICPPTypeSizeInfoSimple.createByRefSizeInfo(tt.typeID);
            }
        }
        else if(this.isUniqueEntityType(tt)) {
            return this.getICPPTypeInfoShallowForEntity(tt, this.assembly.entityDecls.get(tt.typeID) as MIREntityTypeDecl);
        }
        else if (this.isUniqueEphemeralType(tt)) {
            let size = 0;
            let mask: RefMask = "";

            const eltt = tt.options[0] as MIREphemeralListType;
            for (let i = 0; i < eltt.entries.length; ++i) {
                const sizeinfo = this.getICPPTypeInfoShallow(eltt.entries[i]);

                size = size + sizeinfo.inlinedatasize;
                mask = mask + sizeinfo.inlinedmask;
            }

            res = ICPPTypeSizeInfoSimple.createByValueSizeInfo(tt.typeID, size, mask, false);
        }
        else if(this.assembly.subtypeOf(tt, this.getMIRType("NSKeyType"))) {
            return new SMTType("BKey", "[BKEY]", tt.typeID);
        }
        else {
            return new SMTType("BTerm", "[BTERM]", tt.typeID);
        }

        this.typeInfoShallowMap.set(tt.typeID, res as ICPPTypeSizeInfoSimple);
        return this.typeInfoShallowMap.get(tt.typeID) as ICPPTypeSizeInfoSimple;
    }

    private getICPPTypeInfoShallowForEntity(tt: MIRType, entity: MIREntityTypeDecl): ICPPTypeSizeInfoSimple {
        if(entity instanceof MIRInternalEntityTypeDecl) {
            if(entity instanceof MIRPrimitiveInternalEntityTypeDecl) {
                if (this.isType(tt, "None")) {
                    return ICPPTypeSizeInfoSimple.createByRegisterSizeInfo(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
                }
                else if (this.isType(tt, "Nothing")) {
                    return ICPPTypeSizeInfoSimple.createByRegisterSizeInfo(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
                }
                else if (this.isType(tt, "Bool")) {
                    return ICPPTypeSizeInfoSimple.createByRegisterSizeInfo(entity.tkey, ICPP_WORD_SIZE, 1, "1");
                }
                else if (this.isType(tt, "Int")) {
                    return ICPPTypeSizeInfoSimple.createByRegisterSizeInfo(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
                }
                else if (this.isType(tt, "Nat")) {
                    return ICPPTypeSizeInfoSimple.createByRegisterSizeInfo(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
                }
                else if (this.isType(tt, "BigInt")) {
                    return ICPPTypeSizeInfoSimple.createByValueSizeInfo(entity.tkey, ICPP_WORD_SIZE, "4", true);
                }
                else if (this.isType(tt, "BigNat")) {
                    return ICPPTypeSizeInfoSimple.createByValueSizeInfo(entity.tkey, ICPP_WORD_SIZE, "4", true);
                }
                else if (this.isType(tt, "Float")) {
                    return ICPPTypeSizeInfoSimple.createByRegisterSizeInfo(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
                }
                else if (this.isType(tt, "Decimal")) {
                    return ICPPTypeSizeInfoSimple.createByRegisterSizeInfo(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
                }
                else if (this.isType(tt, "Rational")) {
                    return ICPPTypeSizeInfoSimple.createByValueSizeInfo(entity.tkey, 2*ICPP_WORD_SIZE, "41", true);
                }
                else if (this.isType(tt, "String")) {
                    return ICPPTypeSizeInfoSimple.createByValueSizeInfo(entity.tkey, 2*ICPP_WORD_SIZE, "31", true);
                }
                else if (this.isType(tt, "ByteBuffer")) {
                    return ICPPTypeSizeInfoSimple.createByRefSizeInfo(entity.tkey);
                }
                else if(this.isType(tt, "DateTime")) {
                    return ICPPTypeSizeInfoSimple.createByRefSizeInfo(entity.tkey);
                }
                else if(this.isType(tt, "TickTime")) {
                    return ICPPTypeSizeInfoSimple.createByRegisterSizeInfo(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
                }
                else if(this.isType(tt, "LogicalTime")) {
                    return ICPPTypeSizeInfoSimple.createByRegisterSizeInfo(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
                }
                else if(this.isType(tt, "UUID")) {
                    return ICPPTypeSizeInfoSimple.createByRegisterSizeInfo(entity.tkey, 2*ICPP_WORD_SIZE, 2*ICPP_WORD_SIZE, "11");
                }
                else if(this.isType(tt, "ContentHash")) {
                    return ICPPTypeSizeInfoSimple.createByRefSizeInfo(entity.tkey);
                }
                else if(this.isType(tt, "Regex")) {
                    return ICPPTypeSizeInfoSimple.createByRegisterSizeInfo(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
                }
                else {
                    assert(false, "Unknown primitive internal entity");
                    ICPPTypeSizeInfoSimple.createByRefSizeInfo(entity.tkey);
                }
            }
            else if (entity instanceof MIRConstructableInternalEntityTypeDecl) {
                const mirtype = this.getMIRType(entity.fromtype);
                xxxx;
                const fromlayout = this.getICPPTypeInfoShallowForEntity(mirtype, mirdecl);

                return fromlayout.createFromSizeInfo(entity.tkey);
            }
            else if (entity instanceof MIRMaskEntityTypeDecl) {
                return ICPPTypeSizeInfoSimple.createByValueSizeInfo(entity.tkey, ICPP_WORD_SIZE, "1", true);
            }
            else if (entity instanceof MIRPartialVectorEntityTypeDecl) {
                return ICPPTypeSizeInfoSimple.createByRefSizeInfo(entity.tkey);
            }
            else {
                assert(entity instanceof MIRPrimitiveCollectionEntityTypeDecl, "Should be a collection type");

                if(entity instanceof MIRPrimitiveMapEntityTypeDecl) {
                    return new SMTType(this.lookupTypeName(entity.ultype), `TypeTag_${this.lookupTypeName(entity.ultype)}`, entity.ultype)
                }
                else if(entity instanceof MIRPrimitiveStackEntityTypeDecl) {
                    return new SMTType(this.lookupTypeName(entity.ultype), `TypeTag_${this.lookupTypeName(entity.ultype)}`, entity.ultype)
                }
                else if(entity instanceof MIRPrimitiveQueueEntityTypeDecl) {
                    return new SMTType(this.lookupTypeName(entity.ultype), `TypeTag_${this.lookupTypeName(entity.ultype)}`, entity.ultype)
                }
                else if(entity instanceof MIRPrimitiveSetEntityTypeDecl) {
                    return new SMTType(this.lookupTypeName(entity.ultype), `TypeTag_${this.lookupTypeName(entity.ultype)}`, entity.ultype)
                }
                else {
                    assert(entity instanceof MIRPrimitiveListEntityTypeDecl, "Should be a list type");

                    const ultype = (entity as MIRPrimitiveListEntityTypeDecl).oftype;
                    const mirtype = this.getMIRType(ultype);
                    const fromlayout = this.getICPPTypeInfoShallow(mirtype);

                    return fromlayout.createFromSizeInfo(entity.tkey);
                }
            }
        }
        else if (entity instanceof MIRConstructableEntityTypeDecl) {
            const mirtype = this.getMIRType(entity.fromtype);
            const fromlayout = this.getICPPTypeInfoShallow(mirtype);

            return fromlayout.createFromSizeInfo(entity.tkey);
        }
        else if (entity instanceof MIREnumEntityTypeDecl) {
            return ICPPTypeSizeInfoSimple.createByRegisterSizeInfo(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
        }
        else {
            let isinline = true;
            let size = 0;
            let mask: RefMask = "";

            const ett = this.assembly.entityDecls.get(tt.getUniqueCallTargetType().typeID) as MIRObjectEntityTypeDecl;
            for (let i = 0; i < ett.fields.length; ++i) {
                const sizeinfo = this.getICPPTypeInfoShallow(this.getMIRType(ett.fields[i].declaredType));

                isinline = isinline && sizeinfo.issmallinlinevalue;
                size = size + sizeinfo.inlinedatasize;
                mask = mask + sizeinfo.inlinedmask;
            }

            if(ett.fields.length <= 4 && isinline) {
                return ICPPTypeSizeInfoSimple.createByValueSizeInfo(tt.typeID, size, mask, false);
            }
            else {
                return ICPPTypeSizeInfoSimple.createByRefSizeInfo(tt.typeID);
            }
        }
    }

    private computeICCPTypeForUnion(utype: MIRType, tl: ICPPType[]): ICPPType {
        const iskey = this.assembly.subtypeOf(utype, this.getMIRType("KeyType"));

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

        const iskey = this.assembly.subtypeOf(this.getMIRType(tt.typeID), this.getMIRType("NSKeyType"));
        if(this.isUniqueTupleType(this.getMIRType(tt.typeID))) {
            return this.isTypeInline(this.getMIRType(tt.typeID)) 
                ? ICPPTypeTuple.createByValueTuple(tt.typeID, size, mask, idxtypes, idxoffsets, iskey)
                : ICPPTypeTuple.createByRefTuple(tt.typeID, size, mask, idxtypes, idxoffsets, iskey)
        }
        else {
            return this.isTypeInline(this.getMIRType(tt.typeID))
                ? new ICPPTypeInlineUnion(tt.typeID, ICPP_WORD_SIZE + size, "5" + mask, iskey)
                : new ICPPTypeRefUnion(tt.typeID, iskey);
        }
    }

    private getICPPTypeForRecord(tt: MIRRecordType): ICPPType {
        let propertynames: string[] = [];
        let propertytypes: MIRResolvedTypeKey[] = [];
        let propertyoffsets: number[] = [];
        let size = 0;
        let mask: RefMask = "";

        const icppentries = tt.entries.map((entry) => this.getICPPTypeInfoShallow(entry.ptype));
        for(let i = 0; i < icppentries.length; ++i) {
            propertynames.push(tt.entries[i].pname);
            propertytypes.push(icppentries[i].tkey);
            propertyoffsets.push(size);
            size = size + icppentries[i].inlinedatasize;
            mask = mask + icppentries[i].inlinedmask;
        }

        const iskey = this.assembly.subtypeOf(this.getMIRType(tt.typeID), this.getMIRType("NSKeyType"));
        if(this.isUniqueRecordType(this.getMIRType(tt.typeID))) {
            return this.isTypeInline(this.getMIRType(tt.typeID)) 
                ? ICPPTypeRecord.createByValueRecord(tt.typeID, size, mask, propertynames, propertytypes, propertyoffsets, iskey)
                : ICPPTypeRecord.createByRefRecord(tt.typeID, size, mask, propertynames, propertytypes, propertyoffsets, iskey)
        }
        else {
            return this.isTypeInline(this.getMIRType(tt.typeID)) 
                ? new ICPPTypeInlineUnion(tt.typeID, ICPP_WORD_SIZE + size, "5" + mask, iskey)
                : new ICPPTypeRefUnion(tt.typeID, iskey);
        }
    }

    private getICPPTypeForObjectEntity(tt: MIRObjectEntityTypeDecl): ICPPTypeEntity {
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
            const ecc = this.getICPPTypeInfoShallow(this.getMIRType("NSString"));

            size += ecc.inlinedatasize;
            mask += ecc.inlinedmask;
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.DataStringDecl)) {
            ptag = ICPPParseTag.DataStringTag;
            extradata = (tt.specialTemplateInfo as {tname: string, tkind: MIRResolvedTypeKey}[])[0].tkind;
            const ecc = this.getICPPTypeInfoShallow(this.getMIRType("NSString"));
            
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

        const iskey = this.assembly.subtypeOf(this.getMIRType(tt.tkey), this.getMIRType("NSKeyType"));
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

    

    getICPPTypeData(tt: MIRType): ICPPType {
        if(this.typeDataMap.has(tt.trkey)) {
            return this.typeDataMap.get(tt.trkey) as ICPPType;
        }

        let iidata: ICPPType | undefined = undefined;
        if (this.isType(tt, "NSNone")) {
            iidata = new ICPPTypeRegister(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1", true); 
        }
        else if (this.isType(tt, "NSBool")) {
            iidata = new ICPPTypeRegister(tt.trkey, ICPP_WORD_SIZE, 1, "1", true); 
        }
        else if (this.isType(tt, "NSInt")) {
            iidata = new ICPPTypeRegister(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1", true); 
        }
        else if (this.isType(tt, "NSNat")) {
            iidata = new ICPPTypeRegister(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1", true); 
        }
        else if (this.isType(tt, "NSBigInt")) {
            iidata = new ICPPType(ICPPParseTag.BuiltinTag, tt.trkey, ICPPTypeKind.BigNum, new ICPPTypeSizeInfo(3*ICPP_WORD_SIZE, 3*ICPP_WORD_SIZE, 3*ICPP_WORD_SIZE, undefined, "411"), true); 
        }
        else if (this.isType(tt, "NSBigNat")) {
            iidata = new ICPPType(ICPPParseTag.BuiltinTag, tt.trkey, ICPPTypeKind.BigNum, new ICPPTypeSizeInfo(3*ICPP_WORD_SIZE, 3*ICPP_WORD_SIZE, 3*ICPP_WORD_SIZE, undefined, "411"), true); 
        }
        else if (this.isType(tt, "NSFloat")) {
            iidata = new ICPPTypeRegister(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1", false); 
        }
        else if (this.isType(tt, "NSDecimal")) {
            iidata = new ICPPTypeRegister(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1", false); 
        }
        else if (this.isType(tt, "NSRational")) {
            iidata = new ICPPTypeRegister(tt.trkey, 4*ICPP_WORD_SIZE, 4*ICPP_WORD_SIZE, "1111", false); 
        }
        else if (this.isType(tt, "NSStringPos")) {
            iidata = new ICPPTypeRegister(tt.trkey, 5*ICPP_WORD_SIZE, 5*ICPP_WORD_SIZE, "31121", false); 
        }
        else if (this.isType(tt, "NSString")) {
            iidata = new ICPPType(ICPPParseTag.BuiltinTag, tt.trkey, ICPPTypeKind.String, new ICPPTypeSizeInfo(2*ICPP_WORD_SIZE, 2*ICPP_WORD_SIZE, 2*ICPP_WORD_SIZE, undefined, "31"), true);
        }
        else if (this.isType(tt, "NSByteBuffer")) {
            iidata = new ICPPType(ICPPParseTag.BuiltinTag, tt.trkey, ICPPTypeKind.Ref, ICPPTypeSizeInfo.createByRefTypeInfo(34*ICPP_WORD_SIZE, "2"), false);
        }
        else if(this.isType(tt, "NSISOTime")) {
            iidata = new ICPPTypeRegister(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1", false); 
        }
        else if(this.isType(tt, "NSLogicalTime")) {
            iidata = new ICPPTypeRegister(tt.trkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1", true); 
        }
        else if(this.isType(tt, "NSUUID")) {
            iidata = new ICPPType(ICPPParseTag.BuiltinTag, tt.trkey, ICPPTypeKind.Ref, ICPPTypeSizeInfo.createByRefTypeInfo(2*ICPP_WORD_SIZE, undefined), true); 
        }
        else if(this.isType(tt, "NSContentHash")) {
            iidata = new ICPPType(ICPPParseTag.BuiltinTag, tt.trkey, ICPPTypeKind.Ref, ICPPTypeSizeInfo.createByRefTypeInfo(64*ICPP_WORD_SIZE, undefined), true); 
        }
        else if (this.isType(tt, "NSRegex")) {
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
        if(this.isType(from, "NSNone")) {
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
        if(this.isType(into, "NSNone")) {
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
