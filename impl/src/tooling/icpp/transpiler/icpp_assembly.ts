//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRFieldKey, MIRInvokeKey, MIRResolvedTypeKey } from "../../../compiler/mir_ops";
import { Argument, ICPPOp } from "./icpp_exp";

type TranspilerOptions = {
};

type SourceInfo = {
    line: number;
    column: number;
};

enum ICPPTypeKind
{
    Invalid = "BSQTypeKind::Invalid",
    Register = "BSQTypeKind::Register",
    Struct = "BSQTypeKind::Struct",
    String = "BSQTypeKind::String",
    BigNum = "BSQTypeKind::BigNum",
    Ref = "BSQTypeKind::Ref",
    InlineUnion = "BSQTypeKind::InlineUnion",
    HeapUnion = "BSQTypeKind::HeapUnion"
}

type RefMask = string;

class ICPPTypeSizeInfo {
    readonly heapsize: number;   //number of bytes needed to represent the data (no type ptr) when storing in the heap
    readonly sldatasize: number; //number of bytes needed in storage location for this -- 4 bytes for refs, same as heap size for others
    readonly slfullsize: number; //number of bytes + typeptr tag if needed in storage location for this -- inline union is bigger

    readonly slmask: RefMask; //The mask to use to traverse this object (even if this isn't a mixed obj -- e.g. it may be embedded in a mixed obj and we need to use this)   

    constructor(heapsize: number, sldatasize: number, slfullsize: number, slmask: RefMask) {
        this.heapsize = heapsize;
        this.sldatasize = sldatasize;
        this.slfullsize = slfullsize;
        this.slmask = slmask;
    }
}

class ICPPType {
    readonly name: string;
    readonly tkey: MIRResolvedTypeKey;
    readonly tkind: ICPPTypeKind;
    readonly reprkind: string;
    
    readonly allocinfo: ICPPTypeSizeInfo; //memory size information
    
    readonly isLeafType: boolean; //if refmask == undefined && ptrcount == 0
    readonly refmask: RefMask | undefined;
    readonly ptrcount: number; //if this is a packed object the number of pointers at the front

    constructor(name: string, tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, reprkind: string, allocinfo: ICPPTypeSizeInfo, isLeafType: boolean, refmask: RefMask | undefined, ptrcount: number) {
        this.name = name;
        this.tkey = tkey;
        this.tkind = tkind;
        this.reprkind = reprkind;
        this.allocinfo = allocinfo;
        this.isLeafType = isLeafType;
        this.refmask = refmask;
        this.ptrcount = ptrcount;
    }
}

class ICPPTypePrimitive extends ICPPType {
    constructor(name: string, tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, allocinfo: ICPPTypeSizeInfo, isLeafType: boolean, refmask: RefMask | undefined, ptrcount: number) {
        super(name, tkey, tkind, allocinfo, isLeafType, refmask, ptrcount);
    }
}

class ICPPTypeTuple extends ICPPType {
    readonly maxIndex: number;
    readonly ttypes: MIRResolvedTypeKey[];
    readonly idxoffsets: number[];

    constructor(name: string, tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, allocinfo: ICPPTypeSizeInfo, isLeafType: boolean, refmask: RefMask | undefined, ptrcount: number, maxIndex: number, ttypes: MIRResolvedTypeKey[], idxoffsets: number[]) {
        super(name, tkey, tkind, allocinfo, isLeafType, refmask, ptrcount);

        this.maxIndex = maxIndex;
        this.ttypes = ttypes;
        this.idxoffsets = idxoffsets;
    }
}

class ICPPTypeRecord extends ICPPType {
    readonly propertynames: string[];
    readonly ttypes: MIRResolvedTypeKey[];
    readonly propertyoffsets: number[];

    constructor(name: string, tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, allocinfo: ICPPTypeSizeInfo, isLeafType: boolean, refmask: RefMask | undefined, ptrcount: number, propertynames: string[], ttypes: MIRResolvedTypeKey[], propertyoffsets: number[]) {
        super(name, tkey, tkind, allocinfo, isLeafType, refmask, ptrcount);

        this.propertynames = propertynames;
        this.ttypes = ttypes;
        this.propertyoffsets = propertyoffsets;
    }
}

class ICPPTypeEntity extends ICPPType {
    readonly fieldnames: MIRFieldKey[];
    readonly ttypes: MIRResolvedTypeKey[];
    readonly fieldoffsets: number[];

    constructor(name: string, tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, allocinfo: ICPPTypeSizeInfo, isLeafType: boolean, refmask: RefMask | undefined, ptrcount: number, fieldnames: MIRFieldKey[], ttypes: MIRResolvedTypeKey[], fieldoffsets: number[]) {
        super(name, tkey, tkind, allocinfo, isLeafType, refmask, ptrcount);

        this.fieldnames = fieldnames;
        this.ttypes = ttypes;
        this.fieldoffsets = fieldoffsets;
    }
}

class ICPPTypeEphemeralList extends ICPPType {
    readonly ttypes: MIRResolvedTypeKey[];
    readonly idxoffsets: number[];

    constructor(name: string, tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, allocinfo: ICPPTypeSizeInfo, isLeafType: boolean, refmask: RefMask | undefined, ptrcount: number, ttypes: MIRResolvedTypeKey[], idxoffsets: number[]) {
        super(name, tkey, tkind, allocinfo, isLeafType, refmask, ptrcount);

        this.ttypes = ttypes;
        this.idxoffsets = idxoffsets;
    }
}

class ICPPTypeAbstract extends ICPPType {
    constructor(name: string, tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, allocinfo: ICPPTypeSizeInfo, isLeafType: boolean) {
        super(name, tkey, tkind, allocinfo, isLeafType, undefined, 0);
    }
}

class ICPPTypeInlineUnion extends ICPPTypeAbstract {
    constructor(name: string, tkey: MIRResolvedTypeKey, allocinfo: ICPPTypeSizeInfo, isLeafType: boolean) {
        super(name, tkey, ICPPTypeKind.InlineUnion, allocinfo, isLeafType);
    }
}

class ICPPTypeHeapUnion extends ICPPTypeAbstract {
    constructor(name: string, tkey: MIRResolvedTypeKey, allocinfo: ICPPTypeSizeInfo) {
        super(name, tkey, ICPPTypeKind.HeapUnion, allocinfo, false);
    }
}


class ICPPFunctionParameter 
{
    readonly name: string;
    readonly ptype: ICPPType;

    constructor(name: string, ptype: ICPPType) {
        this.name = name;
        this.ptype = ptype;
    }
}

class ICPPInvokeDecl {
    readonly name: string;
    readonly iname: string;
    readonly ikey: MIRInvokeKey;

    readonly srcFile: string;
    readonly sinfo: SourceInfo;
    
    readonly recursive: boolean;

    readonly params: ICPPFunctionParameter[];
    readonly resultType: ICPPType;

    readonly scalarstackBytes: number;
    readonly refstackSlots: number;
    readonly mixedstackBytes: number;
    readonly mixedMask: RefMask;

    readonly maskSlots: number;

    constructor(name: string, iname: string, ikey: MIRInvokeKey, srcFile: string, sinfo: SourceInfo, recursive: boolean, params: ICPPFunctionParameter[], resultType: ICPPType, scalarstackBytes: number refstackSlots: number, mixedstackBytes: number, mixedMask: RefMask, maskSlots: number) {
        this.name = name;
        this.iname = iname;
        this.ikey = ikey;
        this.srcFile = srcFile;
        this.sinfo = sinfo;
        this.recursive = recursive;
        this.params = params;
        this.resultType = resultType;

        this.scalarstackBytes = scalarstackBytes;
        this.refstackSlots = refstackSlots;
        this.mixedstackBytes = mixedstackBytes;
        this.mixedMask = mixedMask;

        this.maskSlots = maskSlots;
    }
}

class ICPPInvokeBodyDecl extends ICPPInvokeDecl 
{
    readonly body: ICPPOp[];
    readonly argmaskSize: number;

    constructor(name: string, iname: string, ikey: MIRInvokeKey, srcFile: string, sinfo: SourceInfo, recursive: boolean, params: ICPPFunctionParameter[], resultType: ICPPType, scalarstackBytes: number refstackSlots: number, mixedstackBytes: number, mixedMask: RefMask, maskSlots: number, body: ICPPOp[], argmaskSize: number) {
        super(name, iname, ikey, srcFile, sinfo, recursive, params, resultType, scalarstackBytes, refstackSlots, mixedstackBytes, mixedMask, maskSlots);
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
    readonly implkeyname: string;
    readonly binds: Map<string, ICPPType>;
    readonly pcodes: Map<string, ICPPPCode>;

    constructor(name: string, iname: string, ikey: MIRInvokeKey, srcFile: string, sinfo: SourceInfo, recursive: boolean, params: ICPPFunctionParameter[], resultType: ICPPType, scalarstackBytes: number refstackSlots: number, mixedstackBytes: number, mixedMask: RefMask, maskSlots: number, implkeyname: string, binds: Map<string, ICPPType>, pcodes: Map<string, ICPPPCode>) {
        super(name, iname, ikey, srcFile, sinfo, recursive, params, resultType, scalarstackBytes, refstackSlots, mixedstackBytes, mixedMask, maskSlots);
        this.implkeyname = implkeyname;
        this.binds = binds;
        this.pcodes = pcodes;
    }
}

export {
    TranspilerOptions, SourceInfo,
    ICPPTypeKind, ICPPTypeSizeInfo, RefMask,
    ICPPType, ICPPTypePrimitive, ICPPTypeTuple, ICPPTypeRecord, ICPPTypeEntity, ICPPTypeEphemeralList,
    ICPPTypeAbstract, ICPPTypeInlineUnion, ICPPTypeHeapUnion,
    ICPPInvokeDecl, ICPPFunctionParameter, ICPPPCode, ICPPInvokeBodyDecl, ICPPInvokePrimitiveDecl
};
