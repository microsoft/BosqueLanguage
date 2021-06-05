//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRFieldKey, MIRInvokeKey, MIRResolvedTypeKey } from "../../../compiler/mir_ops";
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
    Invalid = "BSQTypeKind::Invalid",
    Register = "BSQTypeKind::Register",
    Struct = "BSQTypeKind::Struct",
    String = "BSQTypeKind::String",
    BigNum = "BSQTypeKind::BigNum",
    Ref = "BSQTypeKind::Ref",
    UnionInline = "BSQTypeKind::UnionInline",
    UnionRef = "BSQTypeKind::UnionRef"
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
}

class ICPPType {
    readonly tkey: MIRResolvedTypeKey;
    readonly tkind: ICPPTypeKind;
    
    readonly allocinfo: ICPPTypeSizeInfo; //memory size information
    readonly isbuiltin: boolean;

    constructor(tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, allocinfo: ICPPTypeSizeInfo, isbuiltin: boolean) {
        this.tkey = tkey;
        this.tkind = tkind;
        this.allocinfo = allocinfo;
        this.isbuiltin = isbuiltin;
    }
}

class ICPPTypeRegister extends ICPPType {
    constructor(tkey: MIRResolvedTypeKey, inlinedatasize: number, assigndatasize: number, inlinedmask: RefMask) {
        super(tkey, ICPPTypeKind.Register, ICPPTypeSizeInfo.createByRegisterTypeInfo(inlinedatasize, assigndatasize, inlinedmask), true);
        assert(inlinedatasize <= UNIVERSAL_SIZE);
    }
}

class ICPPTypeTuple extends ICPPType {
    readonly maxIndex: number;
    readonly ttypes: MIRResolvedTypeKey[];
    readonly idxoffsets: number[];

    constructor(tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, allocinfo: ICPPTypeSizeInfo, idxtypes: MIRResolvedTypeKey[], idxoffsets: number[]) {
        super(tkey, tkind, allocinfo, false);

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
}

class ICPPTypeRecord extends ICPPType {
    readonly propertynames: string[];
    readonly propertytypes: MIRResolvedTypeKey[];
    readonly propertyoffsets: number[];

    constructor(tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, allocinfo: ICPPTypeSizeInfo, propertynames: string[], propertytypes: MIRResolvedTypeKey[], propertyoffsets: number[]) {
        super(tkey, tkind, allocinfo, false);

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
}

class ICPPTypeEntity extends ICPPType {
    readonly fieldnames: MIRFieldKey[];
    readonly fieldtypes: MIRResolvedTypeKey[];
    readonly fieldoffsets: number[];

    constructor(tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, allocinfo: ICPPTypeSizeInfo, fieldnames: string[], fieldtypes: MIRResolvedTypeKey[], fieldoffsets: number[]) {
        super(tkey, tkind, allocinfo, false);

        this.fieldnames = fieldnames;
        this.fieldtypes = fieldtypes;
        this.fieldoffsets = fieldoffsets;
    }

    static createByValueEntity(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, fieldnames: string[], fieldtypes: MIRResolvedTypeKey[], fieldoffsets: number[]): ICPPTypeEntity {
        assert(inlinedatasize <= UNIVERSAL_SIZE);
        return new ICPPTypeEntity(tkey, ICPPTypeKind.Struct, ICPPTypeSizeInfo.createByValueTypeInfo(inlinedatasize, inlinedmask), fieldnames, fieldtypes, fieldoffsets);
    }

    static createByRefEntity(tkey: MIRResolvedTypeKey, heapsize: number, heapmask: RefMask, fieldnames: string[], fieldtypes: MIRResolvedTypeKey[], fieldoffsets: number[]): ICPPTypeEntity {
        return new ICPPTypeEntity(tkey, ICPPTypeKind.Ref, ICPPTypeSizeInfo.createByRefTypeInfo(heapsize, heapmask), fieldnames, fieldtypes, fieldoffsets);
    }
}

class ICPPTypeEphemeralList extends ICPPType {
    readonly etypes: MIRResolvedTypeKey[];
    readonly eoffsets: number[];

    constructor(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, etypes: MIRResolvedTypeKey[], eoffsets: number[]) {
        super(tkey, ICPPTypeKind.Struct, ICPPTypeSizeInfo.createByValueTypeInfo(inlinedatasize, inlinedmask), false);

        this.etypes = etypes;
        this.eoffsets = eoffsets;
    }
}

class ICPPTypeInlineUnion extends ICPPType {
    constructor(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask) {
        super(tkey, ICPPTypeKind.UnionInline, ICPPTypeSizeInfo.createByValueTypeInfo(inlinedatasize, inlinedmask), false);
    }
}

class ICPPTypeRefUnion extends ICPPType {
    constructor(tkey: MIRResolvedTypeKey) {
        super( tkey, ICPPTypeKind.UnionRef, ICPPTypeSizeInfo.createByRefTypeInfo(0, "2"), false);
    }
}

class ICPPFunctionParameter {
    readonly name: string;
    readonly ptype: ICPPType;

    constructor(name: string, ptype: ICPPType) {
        this.name = name;
        this.ptype = ptype;
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
}

class ICPPPCode
{
    readonly code: MIRInvokeKey;
    readonly cargs: Argument[];

    constructor(code: MIRInvokeKey, cargs: Argument[]) {
        this.code = code;
        this.cargs = cargs;
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
}

export {
    TranspilerOptions, SourceInfo, ICPP_WORD_SIZE, UNIVERSAL_SIZE,
    ICPPTypeKind, ICPPTypeSizeInfo, RefMask,
    ICPPType, ICPPTypeRegister, ICPPTypeTuple, ICPPTypeRecord, ICPPTypeEntity, ICPPTypeEphemeralList, ICPPTypeInlineUnion, ICPPTypeRefUnion,
    ICPPInvokeDecl, ICPPFunctionParameter, ICPPPCode, ICPPInvokeBodyDecl, ICPPInvokePrimitiveDecl
};
