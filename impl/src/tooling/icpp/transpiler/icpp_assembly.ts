//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRFieldKey, MIRGlobalKey, MIRInvokeKey, MIRResolvedTypeKey, MIRVirtualMethodKey } from "../../../compiler/mir_ops";
import { Argument, ICPPOp } from "./icpp_exp";

import * as assert from "assert";

type TranspilerOptions = {
};

type SourceInfo = {
    line: number;
    column: number;
};

const ICPP_WORD_SIZE = 8;
const UNIVERSAL_SIZE = 40;

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
        return {heapsize: this.heapsize, inlinedatasize: this.inlinedatasize, assigndatasize: this.assigndatasize, heapmask: this.heapmask, inlinedmask: this.inlinedmask};
    }
}

enum ICPPParseTag
{
    BuiltinTag = 0x0,
    ValidatorTag,
    StringOfTag,
    DataStringTag,
    TypedNumberTag,
    ListTag,
    TupleTag,
    RecordTag,
    EntityTag,
    EphemeralListTag,
    InlineUnionTag,
    RefUnionTag
}

class ICPPType {
    readonly tkey: MIRResolvedTypeKey;
    readonly tkind: ICPPTypeKind;
    
    readonly allocinfo: ICPPTypeSizeInfo; //memory size information

    readonly ptag: ICPPParseTag

    constructor(ptag: ICPPParseTag, tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, allocinfo: ICPPTypeSizeInfo) {
        this.tkey = tkey;
        this.tkind = tkind;
        this.allocinfo = allocinfo;

        this.ptag = ptag;
    }

    jemitType(vtable: {vcall: MIRVirtualMethodKey, inv: MIRInvokeKey}[]): object {
        assert(this.ptag !== ICPPParseTag.BuiltinTag); //shouldn't be emitting these since they are "well known"

        return {ptag: this.ptag, tkey: this.tkey, tkind: this.tkind, allocinfo: this.allocinfo, vtable: vtable};
    }
}

class ICPPTypeRegister extends ICPPType {
    constructor(tkey: MIRResolvedTypeKey, inlinedatasize: number, assigndatasize: number, inlinedmask: RefMask) {
        super(ICPPParseTag.BuiltinTag, tkey, ICPPTypeKind.Register, ICPPTypeSizeInfo.createByRegisterTypeInfo(inlinedatasize, assigndatasize, inlinedmask));
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

    constructor(tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, allocinfo: ICPPTypeSizeInfo, idxtypes: MIRResolvedTypeKey[], idxoffsets: number[]) {
        super(ICPPParseTag.TupleTag, tkey, tkind, allocinfo);

        this.maxIndex = idxtypes.length;
        this.ttypes = idxtypes;
        this.idxoffsets = idxoffsets;
    }

    static createByValueTuple(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, idxtypes: MIRResolvedTypeKey[], idxoffsets: number[]): ICPPTypeTuple {
        assert(inlinedatasize <= UNIVERSAL_SIZE);
        return new ICPPTypeTuple(tkey, ICPPTypeKind.Struct, ICPPTypeSizeInfo.createByValueTypeInfo(inlinedatasize, inlinedmask), idxtypes, idxoffsets);
    }

    static createByRefTuple(tkey: MIRResolvedTypeKey, heapsize: number, heapmask: RefMask, idxtypes: MIRResolvedTypeKey[], idxoffsets: number[]): ICPPTypeTuple {
        return new ICPPTypeTuple(tkey, ICPPTypeKind.Ref, ICPPTypeSizeInfo.createByRefTypeInfo(heapsize, heapmask), idxtypes, idxoffsets);
    }

    jemitTupleType(iskey: boolean, vtable: {vcall: MIRVirtualMethodKey, inv: MIRInvokeKey}[]): object {
        return {...this.jemitType(vtable), iskey: iskey, maxIndex: this.maxIndex, ttypes: this.ttypes, idxoffsets: this.idxoffsets};
    }
}

class ICPPTypeRecord extends ICPPType {
    readonly propertynames: string[];
    readonly propertytypes: MIRResolvedTypeKey[];
    readonly propertyoffsets: number[];

    constructor(tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, allocinfo: ICPPTypeSizeInfo, propertynames: string[], propertytypes: MIRResolvedTypeKey[], propertyoffsets: number[]) {
        super(ICPPParseTag.RecordTag, tkey, tkind, allocinfo);

        this.propertynames = propertynames;
        this.propertytypes = propertytypes;
        this.propertyoffsets = propertyoffsets;
    }

    static createByValueRecord(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, propertynames: string[], propertytypes: MIRResolvedTypeKey[], propertyoffsets: number[]): ICPPTypeRecord {
        assert(inlinedatasize <= UNIVERSAL_SIZE);
        return new ICPPTypeRecord(tkey, ICPPTypeKind.Struct, ICPPTypeSizeInfo.createByValueTypeInfo(inlinedatasize, inlinedmask), propertynames, propertytypes, propertyoffsets);
    }

    static createByRefRecord(tkey: MIRResolvedTypeKey, heapsize: number, heapmask: RefMask, propertynames: string[], propertytypes: MIRResolvedTypeKey[], propertyoffsets: number[]): ICPPTypeRecord {
        return new ICPPTypeRecord(tkey, ICPPTypeKind.Ref, ICPPTypeSizeInfo.createByRefTypeInfo(heapsize, heapmask), propertynames, propertytypes, propertyoffsets);
    }

    jemitRecord(vtable: {vcall: MIRVirtualMethodKey, inv: MIRInvokeKey}[]): object {
        return {...this.jemitType(vtable), propertynames: this.propertynames, propertytypes: this.propertytypes, propertyoffsets: this.propertyoffsets};
    }
}

class ICPPTypeEntity extends ICPPType {
    readonly fieldnames: MIRFieldKey[];
    readonly fieldtypes: MIRResolvedTypeKey[];
    readonly fieldoffsets: number[];

    constructor(ptag: ICPPParseTag, tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, allocinfo: ICPPTypeSizeInfo, fieldnames: string[], fieldtypes: MIRResolvedTypeKey[], fieldoffsets: number[]) {
        super(ptag, tkey, tkind, allocinfo);

        this.fieldnames = fieldnames;
        this.fieldtypes = fieldtypes;
        this.fieldoffsets = fieldoffsets;
    }

    static createByValueEntity(ptag: ICPPParseTag, tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, fieldnames: string[], fieldtypes: MIRResolvedTypeKey[], fieldoffsets: number[]): ICPPTypeEntity {
        assert(inlinedatasize <= UNIVERSAL_SIZE);
        return new ICPPTypeEntity(ptag, tkey, ICPPTypeKind.Struct, ICPPTypeSizeInfo.createByValueTypeInfo(inlinedatasize, inlinedmask), fieldnames, fieldtypes, fieldoffsets);
    }

    static createByRefEntity(ptag: ICPPParseTag, tkey: MIRResolvedTypeKey, heapsize: number, heapmask: RefMask, fieldnames: string[], fieldtypes: MIRResolvedTypeKey[], fieldoffsets: number[]): ICPPTypeEntity {
        return new ICPPTypeEntity(ptag, tkey, ICPPTypeKind.Ref, ICPPTypeSizeInfo.createByRefTypeInfo(heapsize, heapmask), fieldnames, fieldtypes, fieldoffsets);
    }

    jemitValidator(re: object): object {
        return {...this.jemitType([]), regex: re};
    }

    jemitStringOf(validator: MIRResolvedTypeKey): object {
        return {...this.jemitType([]), validator: validator, fieldnames: this.fieldnames, fieldtypes: this.fieldtypes, fieldoffsets: this.fieldoffsets};
    }

    jemitDataString(chkinv: MIRInvokeKey): object {
        return {...this.jemitType([]), chkinv: chkinv, fieldnames: this.fieldnames, fieldtypes: this.fieldtypes, fieldoffsets: this.fieldoffsets};
    }

    jemitTypedNumber(underlying: MIRResolvedTypeKey, primitive: MIRResolvedTypeKey): object {
        return {...this.jemitType([]), underlying: underlying, primitive: primitive, fieldnames: this.fieldnames, fieldtypes: this.fieldtypes, fieldoffsets: this.fieldoffsets};
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
        super(ICPPParseTag.EphemeralListTag, tkey, ICPPTypeKind.Struct, ICPPTypeSizeInfo.createByValueTypeInfo(inlinedatasize, inlinedmask));

        this.etypes = etypes;
        this.eoffsets = eoffsets;
    }

    jemitEphemeralList(): object {
        return {...this.jemitType([]), etypes: this.etypes, eoffsets: this.eoffsets};
    }
}

class ICPPTypeInlineUnion extends ICPPType {
    constructor(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask) {
        super(ICPPParseTag.InlineUnionTag, tkey, ICPPTypeKind.UnionInline, ICPPTypeSizeInfo.createByValueTypeInfo(inlinedatasize, inlinedmask));
    }

    jemitInlineUnion(subtypes: MIRResolvedTypeKey[]): object {
        return {...this.jemitType([]), subtypes: subtypes};
    }
}

class ICPPTypeRefUnion extends ICPPType {
    constructor(tkey: MIRResolvedTypeKey) {
        super(ICPPParseTag.RefUnionTag, tkey, ICPPTypeKind.UnionRef, ICPPTypeSizeInfo.createByRefTypeInfo(0, "2"));
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
    readonly argmaskSize: number;

    constructor(name: string, ikey: MIRInvokeKey, srcFile: string, sinfo: SourceInfo, recursive: boolean, params: ICPPFunctionParameter[], resultType: ICPPType, scalarStackBytes: number, mixedStackBytes: number, mixedStackMask: RefMask, maskSlots: number, body: ICPPOp[], argmaskSize: number) {
        super(name, ikey, srcFile, sinfo, recursive, params, resultType, scalarStackBytes, mixedStackBytes, mixedStackMask, maskSlots);
        this.body = body;
        this.argmaskSize = argmaskSize;
    }

    jsonEmit(): object {
        return {...super.jsonEmit(), isbuiltin: false, body: this.body, argmaskSize: this.argmaskSize};
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
    readonly storageOffset: number;
    readonly valueInvoke: MIRInvokeKey;
    readonly ctype: ICPPType;

    constructor(gkey: MIRGlobalKey, storageOffset: number, valueInvoke: MIRInvokeKey, ctype: ICPPType) {
        this.gkey = gkey;
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
    readonly cbuffsize: number;
    readonly cmask: RefMask;

    readonly typenames: MIRResolvedTypeKey[];
    readonly propertynames: string[];
    readonly fieldnames: MIRFieldKey[];

    readonly invokenames: MIRInvokeKey[];
    readonly vinvokenames: MIRVirtualMethodKey[];

    readonly typedecls: ICPPType[];
    readonly invdecls: ICPPInvokeDecl[];

    readonly litdecls: { offset: number, storage: ICPPType, value: string }[];
    readonly constdecls: ICPPConstDecl[];
}

export {
    TranspilerOptions, SourceInfo, ICPP_WORD_SIZE, UNIVERSAL_SIZE, ICPPParseTag,
    ICPPTypeKind, ICPPTypeSizeInfo, RefMask,
    ICPPType, ICPPTypeRegister, ICPPTypeTuple, ICPPTypeRecord, ICPPTypeEntity, ICPPTypeEphemeralList, ICPPTypeInlineUnion, ICPPTypeRefUnion,
    ICPPInvokeDecl, ICPPFunctionParameter, ICPPPCode, ICPPInvokeBodyDecl, ICPPInvokePrimitiveDecl,
    ICPPConstDecl,
    ICPPAssembly
};
