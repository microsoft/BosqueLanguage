//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRFieldKey, MIRGlobalKey, MIRInvokeKey, MIRResolvedTypeKey, MIRVirtualMethodKey } from "../../../compiler/mir_ops";
import { Argument, ICPPOp } from "./icpp_exp";

import * as assert from "assert";
import { BSQRegex } from "../../../ast/bsqregex";

type TranspilerOptions = {
};

type SourceInfo = {
    line: number;
    column: number;
};

const ICPP_WORD_SIZE = 8;
const UNIVERSAL_SIZE = 48;

enum ICPPTypeKind
{
    Invalid = 0x0,
    Register,
    Struct,
    String,
    BigNum,
    Ref,
    UnionInline,
    UnionRef
}

type RefMask = string;

class ICPPTypeSizeInfo {
    readonly heapsize: number;   //number of bytes needed to represent the data (no type ptr) when storing in the heap
    readonly inlinedatasize: number; //number of bytes needed in storage location for this (includes type tag for inline union -- is the size of a pointer for ref -- and word size for BSQBool)
    readonly assigndatasize: number; //number of bytes needed to copy when assigning this to a location -- 1 for BSQBool -- others should be same as inlined size

    readonly heapmask: RefMask | undefined; //The mask to used to traverse this object during gc (if it is heap allocated) -- null if this is a leaf object -- partial if tailing scalars
    readonly inlinedmask: RefMask; //The mask used to traverse this object as part of inline storage (on stack or inline in an object) -- must traverse full object

    constructor(heapsize: number, inlinedatasize: number, assigndatasize: number, heapmask: RefMask | undefined, inlinedmask: RefMask) {
        this.heapsize = heapsize;
        this.inlinedatasize = inlinedatasize;
        this.assigndatasize = assigndatasize;
        this.heapmask = heapmask;
        this.inlinedmask = inlinedmask;
    }

    isScalarOnlyInline(): boolean {
        return /1*/.test(this.inlinedmask);
    }

    static createByRegisterTypeInfo(inlinedatasize: number, assigndatasize: number, inlinedmask: RefMask): ICPPTypeSizeInfo {
        return new ICPPTypeSizeInfo(inlinedatasize, inlinedatasize, assigndatasize, undefined, inlinedmask);
    }

    static createByValueTypeInfo(inlinedatasize: number, inlinedmask: RefMask): ICPPTypeSizeInfo {
        return new ICPPTypeSizeInfo(inlinedatasize, inlinedatasize, inlinedatasize, undefined, inlinedmask);
    }

    static createByRefTypeInfo(heapsize: number, heapmask: RefMask | undefined): ICPPTypeSizeInfo {
        return new ICPPTypeSizeInfo(heapsize, ICPP_WORD_SIZE, ICPP_WORD_SIZE, heapmask, "2");
    }

    jemit(): any {
        return {heapsize: this.heapsize, inlinedatasize: this.inlinedatasize, assigndatasize: this.assigndatasize, heapmask: this.heapmask || null, inlinedmask: this.inlinedmask};
    }
}

enum ICPPParseTag
{
    BuiltinTag = 0x0,
    ValidatorTag,
    StringOfTag,
    DataStringTag,
    TypedNumberTag,
    VectorTag,
    ListTag,
    StackTag,
    QueueTag,
    SetTag,
    MapTag,
    TupleTag,
    RecordTag,
    EntityTag,
    EphemeralListTag,
    EnumTag,
    InlineUnionTag,
    RefUnionTag
}

class ICPPType {
    readonly tkey: MIRResolvedTypeKey;
    readonly tkind: ICPPTypeKind;
    
    readonly allocinfo: ICPPTypeSizeInfo; //memory size information

    readonly ptag: ICPPParseTag
    readonly iskey: boolean;
    
    constructor(ptag: ICPPParseTag, tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, allocinfo: ICPPTypeSizeInfo, iskey: boolean) {
        this.tkey = tkey;
        this.tkind = tkind;
        this.allocinfo = allocinfo;

        this.ptag = ptag;
        this.iskey = iskey;
    }

    jemitType(vtable: {vcall: MIRVirtualMethodKey, inv: MIRInvokeKey}[]): object {
        assert(this.ptag !== ICPPParseTag.BuiltinTag); //shouldn't be emitting these since they are "well known"

        return {ptag: this.ptag, iskey: this.iskey, tkey: this.tkey, tkind: this.tkind, allocinfo: this.allocinfo.jemit(), name: this.tkey, vtable: vtable};
    }
}

class ICPPTypeRegister extends ICPPType {
    constructor(tkey: MIRResolvedTypeKey, inlinedatasize: number, assigndatasize: number, inlinedmask: RefMask, iskey: boolean) {
        super(ICPPParseTag.BuiltinTag, tkey, ICPPTypeKind.Register, ICPPTypeSizeInfo.createByRegisterTypeInfo(inlinedatasize, assigndatasize, inlinedmask), iskey);
        assert(inlinedatasize <= UNIVERSAL_SIZE);
    }

    jemitRegister(vtable: {vcall: MIRVirtualMethodKey, inv: MIRInvokeKey}[]): object {
        return this.jemitType(vtable);
    }
}

class ICPPTypeTuple extends ICPPType {
    readonly maxIndex: number;
    readonly ttypes: MIRResolvedTypeKey[];
    readonly idxoffsets: number[];

    constructor(tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, allocinfo: ICPPTypeSizeInfo, idxtypes: MIRResolvedTypeKey[], idxoffsets: number[], iskey: boolean) {
        super(ICPPParseTag.TupleTag, tkey, tkind, allocinfo, iskey);

        this.maxIndex = idxtypes.length;
        this.ttypes = idxtypes;
        this.idxoffsets = idxoffsets;
    }

    static createByValueTuple(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, idxtypes: MIRResolvedTypeKey[], idxoffsets: number[], iskey: boolean): ICPPTypeTuple {
        assert(inlinedatasize <= UNIVERSAL_SIZE);
        return new ICPPTypeTuple(tkey, ICPPTypeKind.Struct, ICPPTypeSizeInfo.createByValueTypeInfo(inlinedatasize, inlinedmask), idxtypes, idxoffsets, iskey);
    }

    static createByRefTuple(tkey: MIRResolvedTypeKey, heapsize: number, heapmask: RefMask, idxtypes: MIRResolvedTypeKey[], idxoffsets: number[], iskey: boolean): ICPPTypeTuple {
        return new ICPPTypeTuple(tkey, ICPPTypeKind.Ref, ICPPTypeSizeInfo.createByRefTypeInfo(heapsize, heapmask), idxtypes, idxoffsets, iskey);
    }

    jemitTupleType(vtable: {vcall: MIRVirtualMethodKey, inv: MIRInvokeKey}[]): object {
        return {...this.jemitType(vtable), maxIndex: this.maxIndex, ttypes: this.ttypes, idxoffsets: this.idxoffsets};
    }
}

class ICPPTypeRecord extends ICPPType {
    readonly propertynames: string[];
    readonly propertytypes: MIRResolvedTypeKey[];
    readonly propertyoffsets: number[];

    constructor(tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, allocinfo: ICPPTypeSizeInfo, propertynames: string[], propertytypes: MIRResolvedTypeKey[], propertyoffsets: number[], iskey: boolean) {
        super(ICPPParseTag.RecordTag, tkey, tkind, allocinfo, iskey);

        this.propertynames = propertynames;
        this.propertytypes = propertytypes;
        this.propertyoffsets = propertyoffsets;
    }

    static createByValueRecord(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, propertynames: string[], propertytypes: MIRResolvedTypeKey[], propertyoffsets: number[], iskey: boolean): ICPPTypeRecord {
        assert(inlinedatasize <= UNIVERSAL_SIZE);
        return new ICPPTypeRecord(tkey, ICPPTypeKind.Struct, ICPPTypeSizeInfo.createByValueTypeInfo(inlinedatasize, inlinedmask), propertynames, propertytypes, propertyoffsets, iskey);
    }

    static createByRefRecord(tkey: MIRResolvedTypeKey, heapsize: number, heapmask: RefMask, propertynames: string[], propertytypes: MIRResolvedTypeKey[], propertyoffsets: number[], iskey: boolean): ICPPTypeRecord {
        return new ICPPTypeRecord(tkey, ICPPTypeKind.Ref, ICPPTypeSizeInfo.createByRefTypeInfo(heapsize, heapmask), propertynames, propertytypes, propertyoffsets, iskey);
    }

    jemitRecord(vtable: {vcall: MIRVirtualMethodKey, inv: MIRInvokeKey}[]): object {
        return {...this.jemitType(vtable), propertynames: this.propertynames, propertytypes: this.propertytypes, propertyoffsets: this.propertyoffsets};
    }
}

class ICPPTypeEntity extends ICPPType {
    readonly fieldnames: MIRFieldKey[];
    readonly fieldtypes: MIRResolvedTypeKey[];
    readonly fieldoffsets: number[];
    readonly extradata: any;

    constructor(ptag: ICPPParseTag, tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, allocinfo: ICPPTypeSizeInfo, fieldnames: string[], fieldtypes: MIRResolvedTypeKey[], fieldoffsets: number[], iskey: boolean, extradata: any) {
        super(ptag, tkey, tkind, allocinfo, iskey);

        this.fieldnames = fieldnames;
        this.fieldtypes = fieldtypes;
        this.fieldoffsets = fieldoffsets;

        this.extradata = extradata;
    }

    static createByValueEntity(ptag: ICPPParseTag, tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, fieldnames: string[], fieldtypes: MIRResolvedTypeKey[], fieldoffsets: number[], iskey: boolean, extradata: any): ICPPTypeEntity {
        assert(inlinedatasize <= UNIVERSAL_SIZE);
        return new ICPPTypeEntity(ptag, tkey, ICPPTypeKind.Struct, ICPPTypeSizeInfo.createByValueTypeInfo(inlinedatasize, inlinedmask), fieldnames, fieldtypes, fieldoffsets, iskey, extradata);
    }

    static createByRefEntity(ptag: ICPPParseTag, tkey: MIRResolvedTypeKey, heapsize: number, heapmask: RefMask, fieldnames: string[], fieldtypes: MIRResolvedTypeKey[], fieldoffsets: number[], iskey: boolean, extradata: any): ICPPTypeEntity {
        return new ICPPTypeEntity(ptag, tkey, ICPPTypeKind.Ref, ICPPTypeSizeInfo.createByRefTypeInfo(heapsize, heapmask), fieldnames, fieldtypes, fieldoffsets, iskey, extradata);
    }

    jemitValidator(re: object): object {
        return {...this.jemitType([]), regex: re};
    }

    jemitStringOf(validator: MIRResolvedTypeKey): object {
        return {...this.jemitType([]), validator: validator};
    }

    jemitDataString(chkinv: MIRInvokeKey): object {
        return {...this.jemitType([]), chkinv: chkinv};
    }

    jemitTypedNumber(underlying: MIRResolvedTypeKey, primitive: MIRResolvedTypeKey): object {
        return {...this.jemitType([]), underlying: underlying, primitive: primitive};
    }

    jemitEnum(underlying: MIRResolvedTypeKey, enuminvs: [string, number][]): object {
        return {...this.jemitType([]), underlying: underlying, enuminvs: enuminvs};
    }

    jemitVector(etype: MIRResolvedTypeKey, esize: number, emask: RefMask): object {
        assert(false);
        return (undefined as any) as object;
    }

    jemitList(etype: MIRResolvedTypeKey, esize: number, emask: RefMask): object {
        return {...this.jemitType([]), etype: etype, esize: esize, emask: emask};
    }

    jemitStack(t: MIRResolvedTypeKey): object {
        assert(false);
        return (undefined as any) as object;
    }

    jemitQueue(t: MIRResolvedTypeKey): object {
        assert(false);
        return (undefined as any) as object;
    }

    jemitSet(t: MIRResolvedTypeKey): object {
        assert(false);
        return (undefined as any) as object;
    }

    jemitMap(k: MIRResolvedTypeKey, v: MIRResolvedTypeKey): object {
        assert(false);
        return (undefined as any) as object;
    }

    jemitEntity(vtable: {vcall: MIRVirtualMethodKey, inv: MIRInvokeKey}[]): object {
        return {...this.jemitType(vtable), fieldnames: this.fieldnames, fieldtypes: this.fieldtypes, fieldoffsets: this.fieldoffsets};
    }
}

class ICPPTypeEphemeralList extends ICPPType {
    readonly etypes: MIRResolvedTypeKey[];
    readonly eoffsets: number[];

    constructor(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, etypes: MIRResolvedTypeKey[], eoffsets: number[]) {
        super(ICPPParseTag.EphemeralListTag, tkey, ICPPTypeKind.Struct, ICPPTypeSizeInfo.createByValueTypeInfo(inlinedatasize, inlinedmask), false);

        this.etypes = etypes;
        this.eoffsets = eoffsets;
    }

    jemitEphemeralList(): object {
        return {...this.jemitType([]), etypes: this.etypes, eoffsets: this.eoffsets};
    }
}

class ICPPTypeInlineUnion extends ICPPType {
    constructor(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, iskey: boolean) {
        super(ICPPParseTag.InlineUnionTag, tkey, ICPPTypeKind.UnionInline, ICPPTypeSizeInfo.createByValueTypeInfo(inlinedatasize, inlinedmask), iskey);
    }

    jemitInlineUnion(subtypes: MIRResolvedTypeKey[]): object {
        return {...this.jemitType([]), subtypes: subtypes};
    }
}

class ICPPTypeRefUnion extends ICPPType {
    constructor(tkey: MIRResolvedTypeKey, iskey: boolean) {
        super(ICPPParseTag.RefUnionTag, tkey, ICPPTypeKind.UnionRef, ICPPTypeSizeInfo.createByRefTypeInfo(0, "2"), iskey);
    }

    jemitRefUnion(subtypes: MIRResolvedTypeKey[]): object {
        return {...this.jemitType([]), subtypes: subtypes};
    }
}

class ICPPFunctionParameter {
    readonly name: string;
    readonly ptype: ICPPType;

    constructor(name: string, ptype: ICPPType) {
        this.name = name;
        this.ptype = ptype;
    }

    jsonEmit(): object {
        return {name: this.name, ptype: this.ptype.tkey};
    }
}

class ICPPInvokeDecl {
    readonly name: string;
    readonly ikey: MIRInvokeKey;

    readonly srcFile: string;
    readonly sinfo: SourceInfo;
    
    readonly recursive: boolean;

    readonly params: ICPPFunctionParameter[];
    readonly resultType: ICPPType;

    readonly scalarStackBytes: number;
    readonly mixedStackBytes: number;
    readonly mixedStackMask: RefMask;

    readonly maskSlots: number;

    constructor(name: string, ikey: MIRInvokeKey, srcFile: string, sinfo: SourceInfo, recursive: boolean, params: ICPPFunctionParameter[], resultType: ICPPType, scalarStackBytes: number, mixedStackBytes: number, mixedStackMask: RefMask, maskSlots: number) {
        this.name = name;
        this.ikey = ikey;
        this.srcFile = srcFile;
        this.sinfo = sinfo;
        this.recursive = recursive;
        this.params = params;
        this.resultType = resultType;

        this.scalarStackBytes = scalarStackBytes;
        this.mixedStackBytes = mixedStackBytes;
        this.mixedStackMask = mixedStackMask;

        this.maskSlots = maskSlots;
    }

    jsonEmit(): object {
        return {name: this.name, ikey: this.ikey, srcFile: this.srcFile, sinfo: this.sinfo, recursive: this.recursive, params: this.params.map((param) => param.jsonEmit()), resultType: this.resultType.tkey, scalarStackBytes: this.scalarStackBytes, mixedStackBytes: this.mixedStackBytes, mixedStackMask: this.mixedStackMask, maskSlots: this.maskSlots};
    }
}

class ICPPInvokeBodyDecl extends ICPPInvokeDecl 
{
    readonly body: ICPPOp[];
    readonly resultArg: Argument;
    readonly argmaskSize: number;

    constructor(name: string, ikey: MIRInvokeKey, srcFile: string, sinfo: SourceInfo, recursive: boolean, params: ICPPFunctionParameter[], resultType: ICPPType, resultArg: Argument, scalarStackBytes: number, mixedStackBytes: number, mixedStackMask: RefMask, maskSlots: number, body: ICPPOp[], argmaskSize: number) {
        super(name, ikey, srcFile, sinfo, recursive, params, resultType, scalarStackBytes, mixedStackBytes, mixedStackMask, maskSlots);
        this.body = body;
        this.resultArg = resultArg;
        this.argmaskSize = argmaskSize;
    }

    jsonEmit(): object {
        return {...super.jsonEmit(), isbuiltin: false, resultArg: this.resultArg, body: this.body, argmaskSize: this.argmaskSize};
    }
}

class ICPPPCode
{
    readonly code: MIRInvokeKey;
    readonly cargs: Argument[];

    constructor(code: MIRInvokeKey, cargs: Argument[]) {
        this.code = code;
        this.cargs = cargs;
    }

    jsonEmit(): object {
        return {code: this.code, cargs: this.cargs};
    }
}

class ICPPInvokePrimitiveDecl extends ICPPInvokeDecl 
{
    readonly enclosingtype: string | undefined;
    readonly implkeyname: string;
    readonly scalaroffsetMap: Map<string, [number, MIRResolvedTypeKey]>;
    readonly mixedoffsetMap: Map<string, [number, MIRResolvedTypeKey]>;
    readonly binds: Map<string, ICPPType>;
    readonly pcodes: Map<string, ICPPPCode>;

    constructor(name: string, ikey: MIRInvokeKey, srcFile: string, sinfo: SourceInfo, recursive: boolean, params: ICPPFunctionParameter[], resultType: ICPPType, scalarStackBytes: number, mixedStackBytes: number, mixedStackMask: RefMask, maskSlots: number, enclosingtype: string | undefined, implkeyname: string, scalaroffsetMap: Map<string, [number, MIRResolvedTypeKey]>, mixedoffsetMap: Map<string, [number, MIRResolvedTypeKey]>, binds: Map<string, ICPPType>, pcodes: Map<string, ICPPPCode>) {
        super(name, ikey, srcFile, sinfo, recursive, params, resultType, scalarStackBytes, mixedStackBytes, mixedStackMask, maskSlots);
        this.enclosingtype = enclosingtype;
        this.implkeyname = implkeyname;
        this.scalaroffsetMap = scalaroffsetMap;
        this.mixedoffsetMap = mixedoffsetMap;
        this.binds = binds;
        this.pcodes = pcodes;
    }

    jsonEmit(): object {
        const soffsets = [...this.scalaroffsetMap].map((v) => {
            return {name: v[0], info: v[1]};
        });

        const moffsets = [...this.mixedoffsetMap].map((v) => {
            return {name: v[0], info: v[1]};
        });

        const binds = [...this.binds].map((v) => {
            return {name: v[0], ttype: v[1].tkey};
        });

        const pcodes = [...this.pcodes].map((v) => {
            return {name: v[0], pc: v[1]};
        });

        return {...super.jsonEmit(), isbuiltin: true, enclosingtype: this.enclosingtype, implkeyname: this.implkeyname, scalaroffsetMap: soffsets, mixedoffsetMap: moffsets, binds: binds, pcodes: pcodes};
    }
}

class ICPPConstDecl 
{
    readonly gkey: MIRGlobalKey;
    readonly optenumname: [MIRResolvedTypeKey, string] | undefined;
    readonly storageOffset: number;
    readonly valueInvoke: MIRInvokeKey;
    readonly ctype: ICPPType;

    constructor(gkey: MIRGlobalKey, optenumname: [MIRResolvedTypeKey, string] | undefined, storageOffset: number, valueInvoke: MIRInvokeKey, ctype: ICPPType) {
        this.gkey = gkey;
        this.optenumname = optenumname;
        this.storageOffset = storageOffset;
        this.valueInvoke = valueInvoke;
        this.ctype = ctype;
    }

    jsonEmit(): object {
        return { storageOffset: this.storageOffset, valueInvoke: this.valueInvoke, ctype: this.ctype.tkey };
    }
}

class ICPPAssembly
{
    readonly typecount: number;
    cbuffsize: number = 0;
    cmask: RefMask = "";

    readonly typenames: MIRResolvedTypeKey[];
    readonly propertynames: string[];
    readonly fieldnames: MIRFieldKey[];

    readonly invokenames: MIRInvokeKey[];
    readonly vinvokenames: MIRVirtualMethodKey[];

    vtable: {oftype: MIRResolvedTypeKey, vtable: {vcall: MIRVirtualMethodKey, inv: MIRInvokeKey}[]}[] = [];
    subtypes: Map<MIRResolvedTypeKey, Set<MIRResolvedTypeKey>> = new Map<MIRResolvedTypeKey, Set<MIRResolvedTypeKey>>();

    typedecls: ICPPType[] = [];
    invdecls: ICPPInvokeDecl[] = [];

    litdecls: { offset: number, storage: ICPPType, value: string }[] = [];
    constdecls: ICPPConstDecl[] = [];

    readonly entrypoint: MIRInvokeKey;

    constructor(typecount: number, typenames: MIRResolvedTypeKey[], propertynames: string[], fieldnames: MIRFieldKey[], invokenames: MIRInvokeKey[], vinvokenames: MIRVirtualMethodKey[], entrypoint: MIRInvokeKey) {
        this.typecount = typecount;

        this.typenames = typenames;
        this.propertynames = propertynames;
        this.fieldnames = fieldnames;

        this.invokenames = invokenames;
        this.vinvokenames = vinvokenames;

        this.entrypoint = entrypoint;
    }

    jsonEmit(): object {
        return {
            typecount: this.typecount,
            cbuffsize: this.cbuffsize,
            cmask: this.cmask,

            typenames: this.typenames.sort(),
            propertynames: this.propertynames.sort(),
            fieldnames: this.fieldnames.sort(),

            invokenames: this.invokenames.sort(),
            vinvokenames: this.vinvokenames.sort(),

            vtable: this.vtable.sort((a, b) => a.oftype.localeCompare(b.oftype)),

            typedecls: this.typedecls.sort((a, b) => a.tkey.localeCompare(b.tkey)).map((tdecl) => {
                const vtbl = this.vtable.find((vte) => vte.oftype === tdecl.tkey) as {oftype: MIRResolvedTypeKey, vtable: {vcall: MIRVirtualMethodKey, inv: MIRInvokeKey}[]};

                if(tdecl instanceof ICPPTypeRegister) {
                    return tdecl.jemitRegister(vtbl.vtable);
                }
                else if (tdecl instanceof ICPPTypeTuple) {
                    return tdecl.jemitTupleType(vtbl.vtable);
                }
                else if (tdecl instanceof ICPPTypeRecord) {
                    return tdecl.jemitRecord(vtbl.vtable);
                }
                else if (tdecl instanceof ICPPTypeEphemeralList) {
                    return tdecl.jemitEphemeralList();
                }
                else if(tdecl instanceof ICPPTypeInlineUnion) {
                    return tdecl.jemitInlineUnion([...(this.subtypes.get(tdecl.tkey) as Set<MIRResolvedTypeKey>)].sort());
                }
                else if (tdecl instanceof ICPPTypeRefUnion) {
                    return tdecl.jemitRefUnion([...(this.subtypes.get(tdecl.tkey) as Set<MIRResolvedTypeKey>)].sort());
                }
                else {
                    const edecl = tdecl as ICPPTypeEntity;

                    switch(edecl.ptag) {
                        case ICPPParseTag.ValidatorTag: {
                            return edecl.jemitValidator((edecl.extradata as BSQRegex).jemit());
                        }
                        case ICPPParseTag.StringOfTag: {
                            return edecl.jemitStringOf(edecl.extradata as MIRResolvedTypeKey);
                        }
                        case ICPPParseTag.DataStringTag: {
                            return edecl.jemitDataString(edecl.extradata as MIRResolvedTypeKey);
                        }
                        case ICPPParseTag.TypedNumberTag: {
                            //
                            //TODO: we need to switch this to encode the underlying and primitive types in the type decl really -- not as
                            //         the funky v field -- we probably want to add some extra access (and maybe constructor) magic too 
                            //
                            return edecl.jemitTypedNumber(edecl.extradata as MIRResolvedTypeKey, edecl.extradata as MIRResolvedTypeKey);
                        }
                        case ICPPParseTag.EnumTag: {
                            const ddcls = this.constdecls.filter((cdcl) => cdcl.optenumname !== undefined && cdcl.optenumname[0] === tdecl.tkey);
                            const enuminvs = ddcls.map((ddcl) => [`${(ddcl.optenumname as [string, string])[0]}::${(ddcl.optenumname as [string, string])[1]}`, ddcl.storageOffset] as [string, number]);
                            return edecl.jemitEnum(edecl.extradata as MIRResolvedTypeKey, enuminvs);
                        }
                        case ICPPParseTag.VectorTag: {
                            const oftype = this.typedecls.find((oft) => oft.tkey === edecl.extradata as MIRResolvedTypeKey) as ICPPType;
                            return edecl.jemitVector(oftype.tkey, oftype.allocinfo.inlinedatasize, oftype.allocinfo.inlinedmask);
                        }
                        case ICPPParseTag.ListTag: {
                            const oftype = this.typedecls.find((oft) => oft.tkey === edecl.extradata as MIRResolvedTypeKey) as ICPPType;
                            return edecl.jemitList(oftype.tkey, oftype.allocinfo.inlinedatasize, oftype.allocinfo.inlinedmask);
                        }
                        case ICPPParseTag.StackTag: {
                            const oftype = this.typedecls.find((oft) => oft.tkey === edecl.extradata as MIRResolvedTypeKey) as ICPPType;
                            return edecl.jemitStack(oftype.tkey);
                        }
                        case ICPPParseTag.QueueTag: {
                            const oftype = this.typedecls.find((oft) => oft.tkey === edecl.extradata as MIRResolvedTypeKey) as ICPPType;
                            return edecl.jemitQueue(oftype.tkey);
                        }
                        case ICPPParseTag.SetTag: {
                            const oftype = this.typedecls.find((oft) => oft.tkey === edecl.extradata as MIRResolvedTypeKey) as ICPPType;
                            return edecl.jemitSet(oftype.tkey);
                        }
                        case ICPPParseTag.MapTag: {
                            const ktype = this.typedecls.find((oft) => oft.tkey === edecl.extradata[0] as MIRResolvedTypeKey) as ICPPType;
                            const vtype = this.typedecls.find((oft) => oft.tkey === edecl.extradata[1] as MIRResolvedTypeKey) as ICPPType;
                            return edecl.jemitMap(ktype.tkey, vtype.tkey);
                        }
                        default:
                            return edecl.jemitEntity(vtbl.vtable);
                    }
                }
            }),

            invdecls: this.invdecls.sort((a, b) => a.ikey.localeCompare(b.ikey)).map((inv) => inv.jsonEmit()),

            litdecls: this.litdecls.sort((a, b) => a.value.localeCompare(b.value)).map((lv) => {
                return {offset: lv.offset, storage: lv.storage.tkey, value: lv.value};
            }),

            constdecls: this.constdecls.sort((a, b) => a.gkey.localeCompare(b.gkey)).map((cd) => cd.jsonEmit()),

            entrypoint: this.entrypoint
        };
    }
}

export {
    TranspilerOptions, SourceInfo, ICPP_WORD_SIZE, UNIVERSAL_SIZE, ICPPParseTag,
    ICPPTypeKind, ICPPTypeSizeInfo, RefMask,
    ICPPType, ICPPTypeRegister, ICPPTypeTuple, ICPPTypeRecord, ICPPTypeEntity, ICPPTypeEphemeralList, ICPPTypeInlineUnion, ICPPTypeRefUnion,
    ICPPInvokeDecl, ICPPFunctionParameter, ICPPPCode, ICPPInvokeBodyDecl, ICPPInvokePrimitiveDecl,
    ICPPConstDecl,
    ICPPAssembly
};
