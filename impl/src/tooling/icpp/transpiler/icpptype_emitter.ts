//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRConceptType, MIRConceptTypeDecl, MIRConstructableEntityTypeDecl, MIRConstructableInternalEntityTypeDecl, MIRDataBufferInternalEntityTypeDecl, MIRDataStringInternalEntityTypeDecl, MIREntityType, MIREntityTypeDecl, MIREnumEntityTypeDecl, MIREphemeralListType, MIRInternalEntityTypeDecl, MIRObjectEntityTypeDecl, MIRPrimitiveCollectionEntityTypeDecl, MIRPrimitiveInternalEntityTypeDecl, MIRPrimitiveListEntityTypeDecl, MIRPrimitiveMapEntityTypeDecl, MIRPrimitiveQueueEntityTypeDecl, MIRPrimitiveSetEntityTypeDecl, MIRPrimitiveStackEntityTypeDecl, MIRRecordType, MIRStringOfInternalEntityTypeDecl, MIRTupleType, MIRType } from "../../../compiler/mir_assembly";
import { MIRFieldKey, MIRGlobalKey, MIRInvokeKey, MIRResolvedTypeKey } from "../../../compiler/mir_ops";

import { RefMask, TranspilerOptions, ICPP_WORD_SIZE, ICPPLayoutInfo, UNIVERSAL_MASK, UNIVERSAL_TOTAL_SIZE, ICPPLayoutCategory, ICPPLayoutUniversalUnion, ICPPLayoutRefUnion, ICPPLayoutInlineUnion, ICPPTupleLayoutInfo, ICPPRecordLayoutInfo, ICPPEntityLayoutInfo, ICPPLayoutInfoFixed, ICPPEphemeralListLayoutInfo, ICPPCollectionInternalsLayoutInfo, ICPPTypeSizeInfo } from "./icpp_assembly";

import { ArgumentTag, Argument, ICPPOp, ICPPOpEmitter, ICPPStatementGuard, TargetVar, NONE_VALUE_POSITION } from "./icpp_exp";
import { SourceInfo } from "../../../ast/parser";

import * as assert from "assert";

const SMALL_INLINEABLE_TYPES = [
    "None", "Nothing", "Bool", "Int", "Nat", "BigInt", "BigNat", "Float", "Decimal", "Rational", "String", "TickTime", "LogicalTime", "UUID", "Regex"
];

type ICPPTypeInlineInfo = { 
    layout: ICPPLayoutCategory,
    size: number, 
    asize: number, 
    mask: string 
};

class ICPPTypeEmitter {
    readonly topts: TranspilerOptions;
    readonly assembly: MIRAssembly;
    
    private namectr: number = 0;
    private allshortnames = new Set<string>();
    private mangledTypeNameMap: Map<string, string> = new Map<string, string>();
    private mangledFunctionNameMap: Map<string, string> = new Map<string, string>();
    private mangledGlobalNameMap: Map<string, string> = new Map<string, string>();

    private typeDataMap: Map<MIRResolvedTypeKey, ICPPLayoutInfo> = new Map<MIRResolvedTypeKey, ICPPLayoutInfo>();
    private typeInlineMap: Map<MIRResolvedTypeKey, ICPPTypeInlineInfo> = new Map<MIRResolvedTypeKey, ICPPTypeInlineInfo>();

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

    getICPPTypeInfoIsSmallInlineable(tt: MIRType): boolean {
        if(!this.isUniqueEntityType(tt)) {
            return false;
        }
        else {
            const entity = this.assembly.entityDecls.get(tt.typeID) as MIREntityTypeDecl;
            if(entity instanceof MIRInternalEntityTypeDecl) {
                if(entity instanceof MIRPrimitiveInternalEntityTypeDecl) {
                    return SMALL_INLINEABLE_TYPES.includes(tt.typeID);
                }
                else if (entity instanceof MIRStringOfInternalEntityTypeDecl) {
                    const mirtype = this.getMIRType("String");
                    return this.getICPPTypeInfoIsSmallInlineable(mirtype);
                }
                else if (entity instanceof MIRDataStringInternalEntityTypeDecl) {
                    const mirtype = this.getMIRType("String");
                    return this.getICPPTypeInfoIsSmallInlineable(mirtype);

                }
                else if (entity instanceof MIRDataBufferInternalEntityTypeDecl) {
                    const mirtype = this.getMIRType("ByteBuffer");
                    return this.getICPPTypeInfoIsSmallInlineable(mirtype);

                }
                else if (entity instanceof MIRConstructableInternalEntityTypeDecl) {
                    const mirtype = this.getMIRType(entity.fromtype);
                    return this.getICPPTypeInfoIsSmallInlineable(mirtype);
                }
                else {
                    return false;
                }
            }
            else if (entity instanceof MIRConstructableEntityTypeDecl) {
                const mirtype = this.getMIRType(entity.fromtype);
                return this.getICPPTypeInfoIsSmallInlineable(mirtype);
            }
            else if (entity instanceof MIREnumEntityTypeDecl) {
                return true;
            }
            else {
                return false;
            }
        }
    }

    private computeICCPInlineLayoutForUnion(tl: ICPPTypeInlineInfo[]): ICPPTypeInlineInfo {
        if(tl.some((t) => t.layout === ICPPLayoutCategory.UnionUniversal)) {
            return {layout: ICPPLayoutCategory.UnionUniversal, size: UNIVERSAL_TOTAL_SIZE, asize: UNIVERSAL_TOTAL_SIZE, mask: UNIVERSAL_MASK};
        }
        else if(tl.every((t) => t.layout === ICPPLayoutCategory.Ref || t.layout === ICPPLayoutCategory.UnionRef)) {
            return {layout: ICPPLayoutCategory.UnionRef, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "2"};
        }
        else {
            const size = Math.max(...tl.map((oi) => oi.layout === ICPPLayoutCategory.UnionInline ? (oi.size - ICPP_WORD_SIZE) : oi.size));
            
            let mask: RefMask = "5";
            for(let i = 0; i < (size / ICPP_WORD_SIZE); ++i) {
                mask = mask + "1";
            }

            return {layout: ICPPLayoutCategory.UnionInline, size: size + ICPP_WORD_SIZE, asize: size + ICPP_WORD_SIZE, mask: mask};
        }
    }

    private getICPPTypeInfoInlineLayout_MIRPrimitiveInternalEntityTypeDecl(tt: MIRType, entity: MIREntityTypeDecl): ICPPTypeInlineInfo {
        if (this.isType(tt, "None")) {
            return {layout: ICPPLayoutCategory.Inline, size: 0, asize: 0, mask: ""};
        }
        else if (this.isType(tt, "Nothing")) {
            return {layout: ICPPLayoutCategory.Inline, size: 0, asize: 0, mask: ""};
        }
        else if (this.isType(tt, "Bool")) {
            return {layout: ICPPLayoutCategory.Inline, size: ICPP_WORD_SIZE, asize: 1, mask: "1"};
        }
        else if (this.isType(tt, "Int")) {
            return {layout: ICPPLayoutCategory.Inline, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "1"};
        }
        else if (this.isType(tt, "Nat")) {
            return {layout: ICPPLayoutCategory.Inline, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "1"};
        }
        else if (this.isType(tt, "BigInt")) {
            return {layout: ICPPLayoutCategory.Inline, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "4"};
        }
        else if (this.isType(tt, "BigNat")) {
            return {layout: ICPPLayoutCategory.Inline, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "4"};
        }
        else if (this.isType(tt, "Float")) {
            return {layout: ICPPLayoutCategory.Inline, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "1"};
        }
        else if (this.isType(tt, "Decimal")) {
            return {layout: ICPPLayoutCategory.Inline, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "1"};
        }
        else if (this.isType(tt, "Rational")) {
            return {layout: ICPPLayoutCategory.Inline, size: 2*ICPP_WORD_SIZE, asize: 2*ICPP_WORD_SIZE, mask: "41"};
        }
        else if (this.isType(tt, "String")) {
            return {layout: ICPPLayoutCategory.Inline, size: 2*ICPP_WORD_SIZE, asize: 2*ICPP_WORD_SIZE, mask: "31"};
        }
        else if (this.isType(tt, "ByteBuffer")) {
            return {layout: ICPPLayoutCategory.Ref, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "2"};
        }
        else if (this.isType(tt, "DateTime")) {
            return {layout: ICPPLayoutCategory.Inline, size: 2*ICPP_WORD_SIZE, asize: 2*ICPP_WORD_SIZE, mask: "11"};
        }
        else if (this.isType(tt, "TickTime")) {
            return {layout: ICPPLayoutCategory.Inline, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "1"};
        }
        else if (this.isType(tt, "LogicalTime")) {
            return {layout: ICPPLayoutCategory.Inline, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "1"};
        }
        else if (this.isType(tt, "UUID")) {
            return {layout: ICPPLayoutCategory.Inline, size: 2*ICPP_WORD_SIZE, asize: 2*ICPP_WORD_SIZE, mask: "11"};
        }
        else if (this.isType(tt, "ContentHash")) {
            return {layout: ICPPLayoutCategory.Ref, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "2"};
        }
        else if (this.isType(tt, "Regex")) {
            return {layout: ICPPLayoutCategory.Inline, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "1"};
        }
        else {
            if(entity.name === "PartialVector4") {
                return {layout: ICPPLayoutCategory.Ref, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "2"};
            }
            else if (entity.name === "PartialVector8") {
                return {layout: ICPPLayoutCategory.Ref, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "2"};
            }
            else if (entity.name === "ListTree") {
                return {layout: ICPPLayoutCategory.Ref, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "2"};
            }
            else if (entity.name === "MapTree") {
                return {layout: ICPPLayoutCategory.Ref, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "2"};
            }
            else {
                assert(false, "Unknown primitive internal entity");
                return {layout: ICPPLayoutCategory.Inline, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "1"};
            }
        }
    }

    getICPPTypeInfoInlineLayout(tt: MIRType): ICPPTypeInlineInfo {
        if(this.typeInlineMap.has(tt.typeID)) {
            return this.typeInlineMap.get(tt.typeID) as ICPPTypeInlineInfo;
        }

        let res: ICPPTypeInlineInfo | undefined = undefined;
        if(this.isUniqueTupleType(tt)) {
            const tuptt = tt.getUniqueTupleTargetType();

            const byval = tuptt.entries.length <= 4 && tuptt.entries.every((ee) => this.getICPPTypeInfoIsSmallInlineable(ee));
            if (!byval) {
                res = {layout: ICPPLayoutCategory.Ref, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "2"}
            }
            else {
                let size = 0;
                let mask: RefMask = "";

                for (let i = 0; i < tuptt.entries.length; ++i) {
                    const sizeinfo = this.getICPPTypeInfoInlineLayout(tuptt.entries[i]);

                    size = size + sizeinfo.size;
                    mask = mask + sizeinfo.mask;
                }

                res = {layout: ICPPLayoutCategory.Inline, size: size, asize: size, mask: mask};
            }
        }
        else if(this.isUniqueRecordType(tt)) {
            const rectt = tt.getUniqueRecordTargetType();

            const byval = rectt.entries.length <= 4 && rectt.entries.every((ee) => this.getICPPTypeInfoIsSmallInlineable(ee.ptype));
            if (!byval) {
                res = {layout: ICPPLayoutCategory.Ref, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "2"}
            }
            else {
                let size = 0;
                let mask: RefMask = "";

                for (let i = 0; i < rectt.entries.length; ++i) {
                    const sizeinfo = this.getICPPTypeInfoInlineLayout(rectt.entries[i].ptype);

                    size = size + sizeinfo.size;
                    mask = mask + sizeinfo.mask;
                }

                res = {layout: ICPPLayoutCategory.Inline, size: size, asize: size, mask: mask};
            }
        }
        else if(this.isUniqueEntityType(tt)) {
            const entity = this.assembly.entityDecls.get(tt.typeID) as MIREntityTypeDecl;
            
            if(entity instanceof MIRInternalEntityTypeDecl) {
                if(entity instanceof MIRPrimitiveInternalEntityTypeDecl) {
                    res = this.getICPPTypeInfoInlineLayout_MIRPrimitiveInternalEntityTypeDecl(tt, this.assembly.entityDecls.get(tt.typeID) as MIREntityTypeDecl);
                }
                else if (entity instanceof MIRStringOfInternalEntityTypeDecl) {
                    const mirtype = this.getMIRType("String");
                    res = this.getICPPTypeInfoInlineLayout(mirtype);
                }
                else if (entity instanceof MIRDataStringInternalEntityTypeDecl) {
                    const mirtype = this.getMIRType("String");
                    res = this.getICPPTypeInfoInlineLayout(mirtype);
                }
                else if (entity instanceof MIRDataBufferInternalEntityTypeDecl) {
                    const mirtype = this.getMIRType("ByteBuffer");
                    res = this.getICPPTypeInfoInlineLayout(mirtype);
                }
                else if (entity instanceof MIRConstructableInternalEntityTypeDecl) {
                    const mirtype = this.getMIRType(entity.fromtype);
                    res = this.getICPPTypeInfoInlineLayout(mirtype);
                }
                else {
                    assert(entity instanceof MIRPrimitiveCollectionEntityTypeDecl, "Should be a collection type");

                    if(entity instanceof MIRPrimitiveMapEntityTypeDecl) {
                        res = {layout: ICPPLayoutCategory.Inline, size: 3*ICPP_WORD_SIZE, asize: 3*ICPP_WORD_SIZE, mask: "112"};
                    }
                    else if(entity instanceof MIRPrimitiveStackEntityTypeDecl) {
                        res = {layout: ICPPLayoutCategory.Inline, size: 2*ICPP_WORD_SIZE, asize: 2*ICPP_WORD_SIZE, mask: "12"};
                    }
                    else if(entity instanceof MIRPrimitiveQueueEntityTypeDecl) {
                        res = {layout: ICPPLayoutCategory.Inline, size: 2*ICPP_WORD_SIZE, asize: 2*ICPP_WORD_SIZE, mask: "12"};
                    }
                    else if(entity instanceof MIRPrimitiveSetEntityTypeDecl) {
                        res = {layout: ICPPLayoutCategory.Inline, size: 3*ICPP_WORD_SIZE, asize: 3*ICPP_WORD_SIZE, mask: "112"};
                    }
                    else {
                        assert(entity instanceof MIRPrimitiveListEntityTypeDecl, "Should be a list type");
    
                        res = {layout: ICPPLayoutCategory.Inline, size: 2*ICPP_WORD_SIZE, asize: 2*ICPP_WORD_SIZE, mask: "12"};
                    }
                }
            }
            else if (entity instanceof MIRConstructableEntityTypeDecl) {
                const mirtype = this.getMIRType(entity.fromtype);
                res = this.getICPPTypeInfoInlineLayout(mirtype);
            }
            else if (entity instanceof MIREnumEntityTypeDecl) {
                res = {layout: ICPPLayoutCategory.Inline, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "1"};
            }
            else {
                const ett = this.assembly.entityDecls.get(tt.getUniqueCallTargetType().typeID) as MIRObjectEntityTypeDecl;                
                const byval = ett.fields.length <= 4 && ett.fields.every((ff) => this.getICPPTypeInfoIsSmallInlineable(this.getMIRType(ff.declaredType)));

                if (!byval) {
                    res = {layout: ICPPLayoutCategory.Ref, size: ICPP_WORD_SIZE, asize: ICPP_WORD_SIZE, mask: "2"}
                }
                else {
                    let size = 0;
                    let mask: RefMask = "";
    
                    for (let i = 0; i < ett.fields.length; ++i) {
                        const sizeinfo = this.getICPPTypeInfoInlineLayout(this.getMIRType(ett.fields[i].declaredType));
    
                        size = size + sizeinfo.size;
                        mask = mask + sizeinfo.mask;
                    }
    
                    res = {layout: ICPPLayoutCategory.Inline, size: size, asize: size, mask: mask};
                }
            }    
        }
        else if (this.isUniqueEphemeralType(tt)) {
            const ett = tt.options[0] as MIREphemeralListType;

            let size = 0;
            let mask: RefMask = "";

            for (let i = 0; i < ett.entries.length; ++i) {
                const sizeinfo = this.getICPPTypeInfoInlineLayout(ett.entries[i]);

                size = size + sizeinfo.size;
                mask = mask + sizeinfo.mask;
            }

            res = {layout: ICPPLayoutCategory.Inline, size: size, asize: size, mask: mask};
        }
        else {
            if(tt.options.length === 1) {
                const copt = tt.options[0] as MIRConceptType;

                const isuniversal = copt.ckeys.some((ckk) => (this.assembly.conceptDecls.get(ckk) as MIRConceptTypeDecl).attributes.includes("__universal"));
                if(isuniversal) {
                    res =  {layout: ICPPLayoutCategory.UnionUniversal, size: UNIVERSAL_TOTAL_SIZE, asize: UNIVERSAL_TOTAL_SIZE, mask: UNIVERSAL_MASK};
                }
                else {
                    const cttype = this.getMIRType(copt.typeID);
                    const iccpopts = [...this.assembly.entityDecls]
                        .filter((edp) => this.assembly.subtypeOf(this.getMIRType(edp[0]), cttype))
                        .map((edp) => this.getICPPTypeInfoInlineLayout(this.getMIRType(edp[0])));

                    res = this.computeICCPInlineLayoutForUnion(iccpopts);
                }
            }
            else {
                const optinfo = tt.options.map((stt) => this.getICPPTypeInfoInlineLayout(this.getMIRType(stt.typeID)));
                res = this.computeICCPInlineLayoutForUnion(optinfo);
            }
        }

        this.typeInlineMap.set(tt.typeID, res);
        return res;
    }

    private computeICCPLayoutForUnion(utype: MIRType, tl: ICPPTypeInlineInfo[]): ICPPLayoutInfo {
        if(tl.some((t) => t.layout === ICPPLayoutCategory.UnionUniversal)) {
            return new ICPPLayoutUniversalUnion(utype.typeID);
        }
        else if(tl.every((t) => t.layout === ICPPLayoutCategory.Ref || t.layout === ICPPLayoutCategory.UnionRef)) {
            return new ICPPLayoutRefUnion(utype.typeID);
        }
        else {
            const size = Math.max(...tl.map((oi) => oi.layout === ICPPLayoutCategory.UnionInline ? (oi.size - ICPP_WORD_SIZE) : oi.size));

            let mask: RefMask = "5";
            for(let i = 0; i < (size / ICPP_WORD_SIZE); ++i) {
                mask = mask + "1";
            }

            return new ICPPLayoutInlineUnion(utype.typeID, size + ICPP_WORD_SIZE, mask);
        }
    }

    private getICPPLayoutForTuple(tt: MIRTupleType): ICPPLayoutInfo {
        const inlineinfo = this.getICPPTypeInfoInlineLayout(this.getMIRType(tt.typeID));

        let idxtypes: MIRResolvedTypeKey[] = [];
        let idxoffsets: number[] = [];
        let endoffest = 0;

        let hsize = 0;
        let hmask = "";

        const icppentries = tt.entries.map((entry) => this.getICPPTypeInfoInlineLayout(entry));
        for (let i = 0; i < icppentries.length; ++i) {
            idxtypes.push(tt.entries[i].typeID);
            idxoffsets.push(endoffest);
            endoffest += icppentries[i].size;

            hsize += icppentries[i].size;
            hmask += icppentries[i].mask;
        }

        if (inlineinfo.layout === ICPPLayoutCategory.Inline) { 
            return ICPPTupleLayoutInfo.createByValueTuple(tt.typeID, inlineinfo.size, inlineinfo.mask, idxtypes, idxoffsets);
        }
        else {
            return ICPPTupleLayoutInfo.createByRefTuple(tt.typeID, hsize, hmask, idxtypes, idxoffsets);
        }
    }

    private getICPPLayoutForRecord(tt: MIRRecordType): ICPPLayoutInfo {
        const inlineinfo = this.getICPPTypeInfoInlineLayout(this.getMIRType(tt.typeID));
        
        let propertynames: string[] = [];
        let propertytypes: MIRResolvedTypeKey[] = [];
        let propertyoffsets: number[] = [];
        let endoffest = 0;

        let hsize = 0;
        let hmask = "";

        const icppentries = tt.entries.map((entry) => this.getICPPTypeInfoInlineLayout(entry.ptype));
        for(let i = 0; i < icppentries.length; ++i) {
            propertynames.push(tt.entries[i].pname);
            propertytypes.push(tt.entries[i].ptype.typeID);
            propertyoffsets.push(endoffest);
            endoffest += icppentries[i].size;

            hsize += icppentries[i].size;
            hmask += icppentries[i].mask;
        }
    
        if (inlineinfo.layout === ICPPLayoutCategory.Inline) { 
            return ICPPRecordLayoutInfo.createByValueRecord(tt.typeID, inlineinfo.size, inlineinfo.mask, propertynames, propertytypes, propertyoffsets);
        }
        else {
            return ICPPRecordLayoutInfo.createByRefRecord(tt.typeID, hsize, hmask, propertynames, propertytypes, propertyoffsets);
        }
    }

    private getICPPLayoutForEphemeralList(tt: MIREphemeralListType): ICPPEphemeralListLayoutInfo {
        const inlineinfo = this.getICPPTypeInfoInlineLayout(this.getMIRType(tt.typeID));

        let idxtypes: MIRResolvedTypeKey[] = [];
        let idxoffsets: number[] = [];
        let endoffest = 0;

        const icppentries = tt.entries.map((entry) => this.getICPPTypeInfoInlineLayout(this.getMIRType(entry.typeID)));
        for(let i = 0; i < icppentries.length; ++i) {
            idxtypes.push(tt.entries[i].typeID);
            idxoffsets.push(endoffest);
            endoffest += icppentries[i].size;
        }

        return new ICPPEphemeralListLayoutInfo(tt.typeID, inlineinfo.size, inlineinfo.mask, idxtypes, idxoffsets);
    }

    private getICPPLayoutForEntity(tt: MIRType, entity: MIREntityTypeDecl): ICPPLayoutInfo {
        const inlineinfo = this.getICPPTypeInfoInlineLayout(this.getMIRType(tt.typeID));

        if(entity instanceof MIRInternalEntityTypeDecl) {
            if(entity instanceof MIRPrimitiveInternalEntityTypeDecl) {
                if (this.isType(tt, "None")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, inlineinfo.size, inlineinfo.asize, inlineinfo.mask);
                }
                else if (this.isType(tt, "Nothing")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, inlineinfo.size, inlineinfo.asize, inlineinfo.mask);
                }
                else if (this.isType(tt, "Bool")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, inlineinfo.size, inlineinfo.asize, inlineinfo.mask);
                }
                else if (this.isType(tt, "Int")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, inlineinfo.size, inlineinfo.asize, inlineinfo.mask);
                }
                else if (this.isType(tt, "Nat")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, inlineinfo.size, inlineinfo.asize, inlineinfo.mask);
                }
                else if (this.isType(tt, "BigInt")) {
                    return ICPPLayoutInfoFixed.createByValueLayout(entity.tkey, inlineinfo.size, inlineinfo.mask);
                }
                else if (this.isType(tt, "BigNat")) {
                    return ICPPLayoutInfoFixed.createByValueLayout(entity.tkey, inlineinfo.size, inlineinfo.mask);
                }
                else if (this.isType(tt, "Float")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, inlineinfo.size, inlineinfo.asize, inlineinfo.mask);
                }
                else if (this.isType(tt, "Decimal")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, inlineinfo.size, inlineinfo.asize, inlineinfo.mask);
                }
                else if (this.isType(tt, "Rational")) {
                    return ICPPLayoutInfoFixed.createByValueLayout(entity.tkey, inlineinfo.size, inlineinfo.mask);
                }
                else if (this.isType(tt, "String")) {
                    return ICPPLayoutInfoFixed.createByValueLayout(entity.tkey, inlineinfo.size, inlineinfo.mask);
                }
                else if (this.isType(tt, "ByteBuffer")) {
                    return ICPPLayoutInfoFixed.createByRefLayout(entity.tkey, 3*ICPP_WORD_SIZE, "2");
                }
                else if(this.isType(tt, "DateTime")) {
                    return ICPPLayoutInfoFixed.createByValueLayout(entity.tkey, inlineinfo.size, inlineinfo.mask);
                }
                else if(this.isType(tt, "TickTime")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, inlineinfo.size, inlineinfo.asize, inlineinfo.mask);
                }
                else if(this.isType(tt, "LogicalTime")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, inlineinfo.size, inlineinfo.asize, inlineinfo.mask);
                }
                else if(this.isType(tt, "UUID")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, inlineinfo.size, inlineinfo.asize, inlineinfo.mask);
                }
                else if(this.isType(tt, "ContentHash")) {
                    return ICPPLayoutInfoFixed.createByRefLayout(entity.tkey, 8*ICPP_WORD_SIZE, undefined);
                }
                else if(this.isType(tt, "Regex")) {
                    return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, inlineinfo.size, inlineinfo.asize, inlineinfo.mask);
                }
                else {
                    if(entity.name === "PartialVector4") {
                        const etype = entity.terms.get("T") as MIRType;
                        const elayout = this.getICPPTypeInfoInlineLayout(etype);
                        const allocinfo = ICPPTypeSizeInfo.createByRefSizeInfo(entity.tkey, ICPP_WORD_SIZE + elayout.size * 4, ("1" + elayout.mask + elayout.mask + elayout.mask + elayout.mask));

                        return new ICPPCollectionInternalsLayoutInfo(entity.tkey, allocinfo, [{name: "T", type: etype.typeID, size: elayout.size, offset: 0}]);
                    }
                    else if (entity.name === "PartialVector8") {
                        const etype = entity.terms.get("T") as MIRType;
                        const elayout = this.getICPPTypeInfoInlineLayout(etype);
                        const allocinfo = ICPPTypeSizeInfo.createByRefSizeInfo(entity.tkey, ICPP_WORD_SIZE + elayout.size * 8, ("1" + elayout.mask + elayout.mask + elayout.mask + elayout.mask + elayout.mask + elayout.mask + elayout.mask + elayout.mask));

                        return new ICPPCollectionInternalsLayoutInfo(entity.tkey, allocinfo, [{name: "T", type: etype.typeID, size: elayout.size, offset: 0}]);
                    }
                    else if (entity.name === "ListTree") {
                        const etype = entity.terms.get("T") as MIRType;
                        const elayout = this.getICPPTypeInfoInlineLayout(etype);
                        const allocinfo = ICPPTypeSizeInfo.createByRefSizeInfo(entity.tkey, ICPP_WORD_SIZE * 3, "221");

                        return new ICPPCollectionInternalsLayoutInfo(entity.tkey, allocinfo, [{name: "T", type: etype.typeID, size: elayout.size, offset: 0}]);
                    }
                    else if (entity.name === "MapTree") {
                        const ktype = entity.terms.get("K") as MIRType;
                        const klayout = this.getICPPTypeInfoInlineLayout(ktype);
                
                        const vtype = entity.terms.get("V") as MIRType;
                        const vlayout = this.getICPPTypeInfoInlineLayout(vtype);

                        const allocinfo = ICPPTypeSizeInfo.createByRefSizeInfo(entity.tkey, (ICPP_WORD_SIZE * 2) + klayout.size + vlayout.size, ("22" + klayout.mask + vlayout.mask));

                        return new ICPPCollectionInternalsLayoutInfo(entity.tkey, allocinfo, [{name: "K", type: ktype.typeID, size: klayout.size, offset: 16}, {name: "V", type: vtype.typeID, size: vlayout.size, offset: 16 + klayout.size}]);
                    }
                    else {
                        assert(false, "Unknown primitive internal entity");
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
                    return ICPPLayoutInfoFixed.createByValueLayout(entity.tkey, inlineinfo.size, inlineinfo.mask);
                }
                else if(entity instanceof MIRPrimitiveStackEntityTypeDecl) {
                    return ICPPLayoutInfoFixed.createByValueLayout(entity.tkey, inlineinfo.size, inlineinfo.mask);
                }
                else if(entity instanceof MIRPrimitiveQueueEntityTypeDecl) {
                    return ICPPLayoutInfoFixed.createByValueLayout(entity.tkey, inlineinfo.size, inlineinfo.mask);
                }
                else if(entity instanceof MIRPrimitiveSetEntityTypeDecl) {
                    return ICPPLayoutInfoFixed.createByValueLayout(entity.tkey, inlineinfo.size, inlineinfo.mask);
                }
                else {
                    assert(entity instanceof MIRPrimitiveListEntityTypeDecl, "Should be a list type");

                    return ICPPLayoutInfoFixed.createByValueLayout(entity.tkey, inlineinfo.size, inlineinfo.mask);
                }
            }
        }
        else if (entity instanceof MIRConstructableEntityTypeDecl) {
            const mirtype = this.getMIRType(entity.fromtype);
            const fromlayout = this.getICPPLayoutInfo(mirtype);

            return fromlayout.createFromLayoutInfo(entity.tkey);
        }
        else if (entity instanceof MIREnumEntityTypeDecl) {
            return ICPPLayoutInfoFixed.createByRegisterLayout(entity.tkey, inlineinfo.size, inlineinfo.asize, inlineinfo.mask);
        }
        else {
            let fieldnames: MIRFieldKey[] = [];
            let fieldtypes: MIRResolvedTypeKey[] = [];
            let fieldoffsets: number[] = [];
            let endoffest = 0;
            
            let hsize = 0;
            let hmask = "";

            const ett = this.assembly.entityDecls.get(tt.getUniqueCallTargetType().typeID) as MIRObjectEntityTypeDecl;
            for(let i = 0; i < ett.fields.length; ++i) {
                const sizeinfo = this.getICPPTypeInfoInlineLayout(this.getMIRType(ett.fields[i].declaredType));

                fieldnames.push(ett.fields[i].fkey);
                fieldtypes.push(ett.fields[i].declaredType);
                fieldoffsets.push(endoffest);
                endoffest += sizeinfo.size;

                hsize += sizeinfo.size;
                hmask += sizeinfo.mask;
            }

            if(inlineinfo.layout === ICPPLayoutCategory.Inline) {
                return ICPPEntityLayoutInfo.createByValueEntity(tt.typeID, inlineinfo.size, inlineinfo.mask, fieldnames, fieldtypes, fieldoffsets);
            }
            else {
                return ICPPEntityLayoutInfo.createByRefEntity(tt.typeID, hsize, hmask, fieldnames, fieldtypes, fieldoffsets);
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
                        .map((edp) => this.getICPPTypeInfoInlineLayout(this.getMIRType(edp[0])));

                    iidata = this.computeICCPLayoutForUnion(tt, iccpopts);
                }
            }
        }
        else {
            const iccpopts = tt.options.map((opt) => this.getICPPTypeInfoInlineLayout(this.getMIRType(opt.typeID)));
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

            if(icppinto.layout === ICPPLayoutCategory.UnionRef) {
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
