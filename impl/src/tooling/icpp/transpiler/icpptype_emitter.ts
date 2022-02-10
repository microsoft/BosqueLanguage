//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRConceptType, MIRConceptTypeDecl, MIRConstructableEntityTypeDecl, MIRConstructableInternalEntityTypeDecl, MIRDataBufferInternalEntityTypeDecl, MIRDataStringInternalEntityTypeDecl, MIREntityType, MIREntityTypeDecl, MIREnumEntityTypeDecl, MIREphemeralListType, MIRInternalEntityTypeDecl, MIRObjectEntityTypeDecl, MIRPrimitiveCollectionEntityTypeDecl, MIRPrimitiveInternalEntityTypeDecl, MIRPrimitiveListEntityTypeDecl, MIRPrimitiveMapEntityTypeDecl, MIRPrimitiveQueueEntityTypeDecl, MIRPrimitiveSetEntityTypeDecl, MIRPrimitiveStackEntityTypeDecl, MIRRecordType, MIRStringOfInternalEntityTypeDecl, MIRTupleType, MIRType } from "../../../compiler/mir_assembly";
import { MIRFieldKey, MIRGlobalKey, MIRInvokeKey, MIRResolvedTypeKey } from "../../../compiler/mir_ops";

import { ICPPTypeSizeInfoSimple, RefMask, TranspilerOptions, ICPP_WORD_SIZE, ICPPLayoutInfo, UNIVERSAL_MASK, UNIVERSAL_TOTAL_SIZE, ICPPLayoutCategory, ICPPLayoutUniversalUnion, ICPPLayoutRefUnion, ICPPLayoutInlineUnion, ICPPTupleLayoutInfo, ICPPRecordLayoutInfo, ICPPEntityLayoutInfo, ICPPLayoutInfoFixed, ICPPEphemeralListLayoutInfo, ICPPCollectionInternalsLayoutInfo, ICPPTypeSizeInfo,  } from "./icpp_assembly";

import { ArgumentTag, Argument, ICPPOp, ICPPOpEmitter, ICPPStatementGuard, TargetVar, NONE_VALUE_POSITION } from "./icpp_exp";
import { SourceInfo } from "../../../ast/parser";

import * as assert from "assert";

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
        else {
            const isuniversal = tt.options.some((opt) => opt instanceof MIRConceptType && opt.ckeys.some((ckk) => (this.assembly.conceptDecls.get(ckk) as MIRConceptTypeDecl).attributes.includes("__universal")));
            if(isuniversal) {
                res = ICPPTypeSizeInfoSimple.createInlineUnionSizeInfo(tt.typeID, UNIVERSAL_TOTAL_SIZE, UNIVERSAL_MASK);
            }
            else {
                const allsubtt = tt.options.map((opt) => this.getICPPTypeInfoShallow(this.getMIRType(opt.typeID)));
                if(allsubtt.every((sttr) => !sttr.isinlinevalue)) {
                    res = ICPPTypeSizeInfoSimple.createByRefSizeInfo(tt.typeID);
                }
                else {
                    const realdatasize = Math.max(...allsubtt.map((linfo) => linfo.realdatasize));

                    let mask = "5";
                    for(let i = 0; i < realdatasize / ICPP_WORD_SIZE; ++i) {
                        mask += "1";
                    }

                    res = ICPPTypeSizeInfoSimple.createInlineUnionSizeInfo(tt.typeID, realdatasize + ICPP_WORD_SIZE, mask);
                }
            }
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

                    return ICPPTypeSizeInfoSimple.createByRefSizeInfo(entity.tkey);
                }
            }
            else if (entity instanceof MIRStringOfInternalEntityTypeDecl) {
                const mirtype = this.getMIRType("String");
                const fromlayout = this.getICPPTypeInfoShallow(mirtype);

                return fromlayout.createFromSizeInfo(entity.tkey);
            }
            else if (entity instanceof MIRDataStringInternalEntityTypeDecl) {
                const mirtype = this.getMIRType("String");
                const fromlayout = this.getICPPTypeInfoShallow(mirtype);

                return fromlayout.createFromSizeInfo(entity.tkey);
            }
            else if (entity instanceof MIRDataBufferInternalEntityTypeDecl) {
                const mirtype = this.getMIRType("ByteBuffer");
                const fromlayout = this.getICPPTypeInfoShallow(mirtype);

                return fromlayout.createFromSizeInfo(entity.tkey);
            }
            else if (entity instanceof MIRConstructableInternalEntityTypeDecl) {
                const mirtype = this.getMIRType(entity.fromtype);
                const fromlayout = this.getICPPTypeInfoShallow(mirtype);

                return fromlayout.createFromSizeInfo(entity.tkey);
            }
            else {
                assert(entity instanceof MIRPrimitiveCollectionEntityTypeDecl, "Should be a collection type");

                if(entity instanceof MIRPrimitiveMapEntityTypeDecl) {
                    const ultype = entity.oftype;
                    const mirtype = this.getMIRType(ultype);
                    const fromlayout = this.getICPPTypeInfoShallow(mirtype);

                    return fromlayout.createFromSizeInfo(entity.tkey);
                }
                else if(entity instanceof MIRPrimitiveStackEntityTypeDecl) {
                    const ultype = entity.oftype;
                    const mirtype = this.getMIRType(ultype);
                    const fromlayout = this.getICPPTypeInfoShallow(mirtype);

                    return fromlayout.createFromSizeInfo(entity.tkey);
                }
                else if(entity instanceof MIRPrimitiveQueueEntityTypeDecl) {
                    const ultype = entity.oftype;
                    const mirtype = this.getMIRType(ultype);
                    const fromlayout = this.getICPPTypeInfoShallow(mirtype);

                    return fromlayout.createFromSizeInfo(entity.tkey);
                }
                else if(entity instanceof MIRPrimitiveSetEntityTypeDecl) {
                    const ultype = entity.oftype;
                    const mirtype = this.getMIRType(ultype);
                    const fromlayout = this.getICPPTypeInfoShallow(mirtype);

                    return fromlayout.createFromSizeInfo(entity.tkey);
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

    private computeICCPLayoutForUnion(utype: MIRType, tl: ICPPLayoutInfo[]): ICPPLayoutInfo {

        if(tl.some((t) => t.layout === ICPPLayoutCategory.UnionUniversal)) {
            return new ICPPLayoutUniversalUnion(utype.typeID);
        }
        else if(tl.every((t) => t.layout === ICPPLayoutCategory.Ref || t.layout === ICPPLayoutCategory.UnionRef)) {
            return new ICPPLayoutRefUnion(utype.typeID);
        }
        else {
            let size = Math.max(...tl.map((t) => t.allocinfo.realdatasize));

            let mask: RefMask = "5";
            for(let i = 0; i < (size - ICPP_WORD_SIZE) / ICPP_WORD_SIZE; ++i) {
                mask = mask + "1";
            }

            return new ICPPLayoutInlineUnion(utype.typeID, size, mask);
        }
    }

    private getICPPLayoutForTuple(tt: MIRTupleType): ICPPLayoutInfo {
        let idxtypes: MIRResolvedTypeKey[] = [];
        let idxoffsets: number[] = [];
        let isinline = true;
        let size = 0;
        let mask: RefMask = "";

        const icppentries = tt.entries.map((entry) => this.getICPPTypeInfoShallow(entry));
        for (let i = 0; i < icppentries.length; ++i) {
            idxtypes.push(icppentries[i].tkey);
            idxoffsets.push(size);
            isinline = isinline && icppentries[i].issmallinlinevalue;
            size = size + icppentries[i].inlinedatasize;
            mask = mask + icppentries[i].inlinedmask;
        }

        if (isinline) { 
            return ICPPTupleLayoutInfo.createByValueTuple(tt.typeID, size, mask, idxtypes, idxoffsets);
        }
        else {
            return ICPPTupleLayoutInfo.createByRefTuple(tt.typeID, size, mask, idxtypes, idxoffsets);
        }
    }

    private getICPPLayoutForRecord(tt: MIRRecordType): ICPPLayoutInfo {
        let propertynames: string[] = [];
        let propertytypes: MIRResolvedTypeKey[] = [];
        let propertyoffsets: number[] = [];
        let isinline = true;
        let size = 0;
        let mask: RefMask = "";

        const icppentries = tt.entries.map((entry) => this.getICPPTypeInfoShallow(entry.ptype));
        for(let i = 0; i < icppentries.length; ++i) {
            propertynames.push(tt.entries[i].pname);
            propertytypes.push(icppentries[i].tkey);
            propertyoffsets.push(size);
            isinline = isinline && icppentries[i].issmallinlinevalue;
            size = size + icppentries[i].inlinedatasize;
            mask = mask + icppentries[i].inlinedmask;
        }

    
        if (isinline) { 
            return ICPPRecordLayoutInfo.createByValueRecord(tt.typeID, size, mask, propertynames, propertytypes, propertyoffsets);
        }
        else {
            return ICPPRecordLayoutInfo.createByRefRecord(tt.typeID, size, mask, propertynames, propertytypes, propertyoffsets);
        }
    }

    private getICPPLayoutForEphemeralList(tt: MIREphemeralListType): ICPPEphemeralListLayoutInfo {
        let idxtypes: MIRResolvedTypeKey[] = [];
        let idxoffsets: number[] = [];
        let size = 0;
        let mask: RefMask = "";

        const icppentries = tt.entries.map((entry) => this.getICPPTypeInfoShallow(this.getMIRType(entry.typeID)));
        for(let i = 0; i < icppentries.length; ++i) {
            idxtypes.push(icppentries[i].tkey);
            idxoffsets.push(size);
            size = size + icppentries[i].inlinedatasize;
            mask = mask + icppentries[i].inlinedmask;
        }

        return new ICPPEphemeralListLayoutInfo(tt.typeID, size, mask, idxtypes, idxoffsets);
    }

    private getICPPLayoutForEntity(tt: MIRType, entity: MIREntityTypeDecl): ICPPLayoutInfo {
        if(entity instanceof MIRInternalEntityTypeDecl) {
            if(entity instanceof MIRPrimitiveInternalEntityTypeDecl) {
                if (this.isType(tt, "None")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
                }
                else if (this.isType(tt, "Nothing")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
                }
                else if (this.isType(tt, "Bool")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, ICPP_WORD_SIZE, 1, "1");
                }
                else if (this.isType(tt, "Int")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
                }
                else if (this.isType(tt, "Nat")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
                }
                else if (this.isType(tt, "BigInt")) {
                    return ICPPLayoutInfoFixed.createByValueLayout(entity.tkey, ICPP_WORD_SIZE, "4", true);
                }
                else if (this.isType(tt, "BigNat")) {
                    return ICPPLayoutInfoFixed.createByValueLayout(entity.tkey, ICPP_WORD_SIZE, "4", true);
                }
                else if (this.isType(tt, "Float")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
                }
                else if (this.isType(tt, "Decimal")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
                }
                else if (this.isType(tt, "Rational")) {
                    return ICPPLayoutInfoFixed.createByValueLayout(entity.tkey, 2*ICPP_WORD_SIZE, "41", true);
                }
                else if (this.isType(tt, "String")) {
                    return ICPPLayoutInfoFixed.createByValueLayout(entity.tkey, 2*ICPP_WORD_SIZE, "31", true);
                }
                else if (this.isType(tt, "ByteBuffer")) {
                    return ICPPLayoutInfoFixed.createByRefLayout(entity.tkey, 3*ICPP_WORD_SIZE, "2");
                }
                else if(this.isType(tt, "DateTime")) {
                    return ICPPLayoutInfoFixed.createByRefLayout(entity.tkey, 5*ICPP_WORD_SIZE, undefined);
                }
                else if(this.isType(tt, "TickTime")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
                }
                else if(this.isType(tt, "LogicalTime")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
                }
                else if(this.isType(tt, "UUID")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, 2*ICPP_WORD_SIZE, 2*ICPP_WORD_SIZE, "11");
                }
                else if(this.isType(tt, "ContentHash")) {
                    return ICPPLayoutInfoFixed.createByRefLayout(entity.tkey, 8*ICPP_WORD_SIZE, undefined);
                }
                else if(this.isType(tt, "Regex")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
                }
                else {
                    if(entity.name === "PartialVector4") {
                        const etype = entity.terms.get("T") as MIRType;
                        const elayout = this.getICPPTypeInfoShallow(etype);
                        const allocinfo = ICPPTypeSizeInfo.createByRefSizeInfo(entity.tkey, elayout.inlinedatasize * 4, (elayout.inlinedmask + elayout.inlinedmask + elayout.inlinedmask + elayout.inlinedmask));

                        return new ICPPCollectionInternalsLayoutInfo(entity.tkey, allocinfo, [{name: "T", type: etype.typeID, size: elayout.inlinedatasize, offset: 0}]);
                    }
                    else if (entity.name === "PartialVector8") {
                        const etype = entity.terms.get("T") as MIRType;
                        const elayout = this.getICPPTypeInfoShallow(etype);
                        const allocinfo = ICPPTypeSizeInfo.createByRefSizeInfo(entity.tkey, elayout.inlinedatasize * 8, (elayout.inlinedmask + elayout.inlinedmask + elayout.inlinedmask + elayout.inlinedmask + elayout.inlinedmask + elayout.inlinedmask + elayout.inlinedmask + elayout.inlinedmask));

                        return new ICPPCollectionInternalsLayoutInfo(entity.tkey, allocinfo, [{name: "T", type: etype.typeID, size: elayout.inlinedatasize, offset: 0}]);
                    }
                    else if (entity.name === "ListTree") {
                        const allocinfo = ICPPTypeSizeInfo.createByRefSizeInfo(entity.tkey, ICPP_WORD_SIZE * 3, "221");

                        return new ICPPCollectionInternalsLayoutInfo(entity.tkey, allocinfo, []);
                    }
                    else if (entity.name === "MapTree") {
                        const ktype = entity.terms.get("K") as MIRType;
                        const klayout = this.getICPPTypeInfoShallow(ktype);
                
                        const vtype = entity.terms.get("V") as MIRType;
                        const vlayout = this.getICPPTypeInfoShallow(vtype);

                        const allocinfo = ICPPTypeSizeInfo.createByRefSizeInfo(entity.tkey, (ICPP_WORD_SIZE * 2) + klayout.inlinedatasize + vlayout.inlinedatasize, ("22" + klayout.inlinedmask + vlayout.inlinedmask));

                        return new ICPPCollectionInternalsLayoutInfo(entity.tkey, allocinfo, [{name: "K", type: ktype.typeID, size: klayout.inlinedatasize, offset: 16}, {name: "V", type: vtype.typeID, size: vlayout.inlinedatasize, offset: 16 + klayout.inlinedatasize}]);
                    }
                    else {
                        assert(false, "Unknown primitive internal entity");
                        return ICPPLayoutInfoFixed.createByRefLayout(entity.tkey, ICPP_WORD_SIZE, undefined);
                    }
                }
            }
            else if (entity instanceof MIRStringOfInternalEntityTypeDecl) {
                const mirtype = this.getMIRType("String");
                const fromlayout = this.getICPPLayoutInfo(mirtype);

                return fromlayout.createFromLayoutInfo(entity.tkey);
            }
            else if (entity instanceof MIRDataStringInternalEntityTypeDecl) {
                const mirtype = this.getMIRType("String");
                const fromlayout = this.getICPPLayoutInfo(mirtype);

                return fromlayout.createFromLayoutInfo(entity.tkey);
            }
            else if (entity instanceof MIRDataBufferInternalEntityTypeDecl) {
                const mirtype = this.getMIRType("ByteBuffer");
                const fromlayout = this.getICPPLayoutInfo(mirtype);

                return fromlayout.createFromLayoutInfo(entity.tkey);
            }
            else if (entity instanceof MIRConstructableInternalEntityTypeDecl) {
                const mirtype = this.getMIRType(entity.fromtype);
                const fromlayout = this.getICPPLayoutInfo(mirtype);

                return fromlayout.createFromLayoutInfo(entity.tkey);
            }
            else {
                assert(entity instanceof MIRPrimitiveCollectionEntityTypeDecl, "Should be a collection type");

                if(entity instanceof MIRPrimitiveMapEntityTypeDecl) {
                    const ultype = entity.oftype;
                    const mirtype = this.getMIRType(ultype);
                    const fromlayout = this.getICPPLayoutInfo(mirtype);

                    return fromlayout.createFromLayoutInfo(entity.tkey);
                }
                else if(entity instanceof MIRPrimitiveStackEntityTypeDecl) {
                    const ultype = entity.oftype;
                    const mirtype = this.getMIRType(ultype);
                    const fromlayout = this.getICPPLayoutInfo(mirtype);

                    return fromlayout.createFromLayoutInfo(entity.tkey);
                }
                else if(entity instanceof MIRPrimitiveQueueEntityTypeDecl) {
                    const ultype = entity.oftype;
                    const mirtype = this.getMIRType(ultype);
                    const fromlayout = this.getICPPLayoutInfo(mirtype);

                    return fromlayout.createFromLayoutInfo(entity.tkey);
                }
                else if(entity instanceof MIRPrimitiveSetEntityTypeDecl) {
                    const ultype = entity.oftype;
                    const mirtype = this.getMIRType(ultype);
                    const fromlayout = this.getICPPLayoutInfo(mirtype);

                    return fromlayout.createFromLayoutInfo(entity.tkey);
                }
                else {
                    assert(entity instanceof MIRPrimitiveListEntityTypeDecl, "Should be a list type");

                    const ultype = (entity as MIRPrimitiveListEntityTypeDecl).oftype;
                    const mirtype = this.getMIRType(ultype);
                    const fromlayout = this.getICPPLayoutInfo(mirtype);

                    return fromlayout.createFromLayoutInfo(entity.tkey);
                }
            }
        }
        else if (entity instanceof MIRConstructableEntityTypeDecl) {
            const mirtype = this.getMIRType(entity.fromtype);
            const fromlayout = this.getICPPLayoutInfo(mirtype);

            return fromlayout.createFromLayoutInfo(entity.tkey);
        }
        else if (entity instanceof MIREnumEntityTypeDecl) {
            return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "1");
        }
        else {
            let isinline = true;
            let fieldnames: MIRFieldKey[] = [];
            let fieldtypes: MIRResolvedTypeKey[] = [];
            let fieldoffsets: number[] = [];
            let size = 0;
            let mask: RefMask = "";

            const ett = this.assembly.entityDecls.get(tt.getUniqueCallTargetType().typeID) as MIRObjectEntityTypeDecl;
            for(let i = 0; i < ett.fields.length; ++i) {
                const sizeinfo = this.getICPPTypeInfoShallow(this.getMIRType(ett.fields[i].declaredType));

                fieldnames.push(ett.fields[i].fkey);
                fieldtypes.push(ett.fields[i].declaredType);
                fieldoffsets.push(size);

                isinline = isinline && sizeinfo.issmallinlinevalue;
                size = size + sizeinfo.inlinedatasize;
                mask = mask + sizeinfo.inlinedmask;
            }

            if(ett.fields.length <= 4 && isinline) {
                return ICPPEntityLayoutInfo.createByValueEntity(tt.typeID, size, mask, fieldnames, fieldtypes, fieldoffsets);
            }
            else {
                return ICPPEntityLayoutInfo.createByRefEntity(tt.typeID, size, mask, fieldnames, fieldtypes, fieldoffsets);
            }
        }
    }

    getICPPLayoutInfo(tt: MIRType): ICPPLayoutInfo {
        if(this.typeDataMap.has(tt.typeID)) {
            return this.typeDataMap.get(tt.typeID) as ICPPLayoutInfo;
        }

        this.internTypeName(tt.typeID);
        let iidata: ICPPLayoutInfo | undefined = undefined;
        if (tt.options.length === 1) {
            const topt = tt.options[0];
            if (topt instanceof MIRTupleType) {
                iidata = this.getICPPLayoutForTuple(topt);
            }
            else if (topt instanceof MIRRecordType) {
                iidata = this.getICPPLayoutForRecord(topt);
            }
            else if(topt instanceof MIREphemeralListType) {
                iidata = this.getICPPLayoutForEphemeralList(topt);
            }
            else if(topt instanceof MIREntityType) {
                iidata = this.getICPPLayoutForEntity(tt, this.assembly.entityDecls.get(topt.typeID) as MIREntityTypeDecl);
            }
            else {
                const copt = tt.options[0] as MIRConceptType;

                const isuniversal = copt.ckeys.some((ckk) => (this.assembly.conceptDecls.get(ckk) as MIRConceptTypeDecl).attributes.includes("__universal"));
                if(isuniversal) {
                    iidata = new ICPPLayoutUniversalUnion(tt.typeID);
                }
                else {
                    const cttype = this.getMIRType(copt.typeID);
                    const iccpopts = [...this.assembly.entityDecls]
                        .filter((edp) => this.assembly.subtypeOf(this.getMIRType(edp[0]), cttype))
                        .map((edp) => this.getICPPLayoutInfo(this.getMIRType(edp[0])));

                    iidata = this.computeICCPLayoutForUnion(tt, iccpopts);
                }
            }
        }
        else {
            const iccpopts = tt.options.map((opt) => this.getICPPLayoutInfo(this.getMIRType(opt.typeID)));
            iidata = this.computeICCPLayoutForUnion(tt, iccpopts);
        }

        this.typeDataMap.set(tt.typeID, iidata as ICPPLayoutInfo);
        return this.typeDataMap.get(tt.typeID) as ICPPLayoutInfo;
    }

    private coerceIntoUnion(sinfo: SourceInfo, arg: Argument, from: MIRType, trgt: TargetVar, into: MIRType, sguard: ICPPStatementGuard): ICPPOp {
        if(this.isType(from, "None")) {
            return ICPPOpEmitter.genNoneInitUnionOp(sinfo, trgt, into.typeID);
        }
        else {
            const icppinto = this.getICPPLayoutInfo(into);

            if(icppinto.layout === ICPPLayoutCategory.UnionInline) {
                return ICPPOpEmitter.genDirectAssignOp(sinfo, trgt, into.typeID, arg, sguard);
            }
            else {
                return ICPPOpEmitter.genBoxOp(sinfo, trgt, into.typeID, arg, from.typeID, sguard);
            }
        }
    }

    private coerceFromUnion(sinfo: SourceInfo, arg: Argument, from: MIRType, trgt: TargetVar, into: MIRType, sguard: ICPPStatementGuard): ICPPOp {
        if(this.isType(into, "None")) {
            return ICPPOpEmitter.genDirectAssignOp(sinfo, trgt, into.typeID, { kind: ArgumentTag.Const, location: NONE_VALUE_POSITION }, sguard);
        }
        else {
            const icppfrom = this.getICPPLayoutInfo(from);

            if(icppfrom.layout === ICPPLayoutCategory.UnionRef) {
                return ICPPOpEmitter.genDirectAssignOp(sinfo, trgt, into.typeID, arg, sguard);
            }
            else {
                return ICPPOpEmitter.genExtractOp(sinfo, trgt, into.typeID, arg, from.typeID, sguard);
            }
        }
    }

    coerceEquivReprs(sinfo: SourceInfo, arg: Argument, trgt: TargetVar, into: MIRType, sguard: ICPPStatementGuard): ICPPOp {
        return ICPPOpEmitter.genDirectAssignOp(sinfo, trgt, into.typeID, arg, sguard);
    }

    coerce(sinfo: SourceInfo, arg: Argument, from: MIRType, trgt: TargetVar, into: MIRType, sguard: ICPPStatementGuard): ICPPOp {
        const icppfrom = this.getICPPLayoutInfo(from);
        const icppinto = this.getICPPLayoutInfo(into);

        if(icppfrom.tkey === icppinto.tkey) {
            return this.coerceEquivReprs(sinfo, arg, trgt, into, sguard);
        }

        if(icppinto.layout === ICPPLayoutCategory.Ref && icppfrom.layout === ICPPLayoutCategory.Ref) {
            return this.coerceEquivReprs(sinfo, arg, trgt, into, sguard);
        }
        else if(icppinto.layout === ICPPLayoutCategory.UnionRef && icppfrom.layout === ICPPLayoutCategory.UnionRef) {
            return this.coerceEquivReprs(sinfo, arg, trgt, into, sguard);
        }
        else if(icppinto.layout === ICPPLayoutCategory.UnionRef || icppinto.layout === ICPPLayoutCategory.UnionInline || icppinto.layout === ICPPLayoutCategory.UnionUniversal) {
            return this.coerceIntoUnion(sinfo, arg, from, trgt, into, sguard);
        }
        else {
            return this.coerceFromUnion(sinfo, arg, from, trgt, into, sguard);
        }
    }
}

export {
    ICPPTypeEmitter
};
