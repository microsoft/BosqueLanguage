//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRFieldKey, MIRResolvedTypeKey } from "../../../compiler/mir_ops";

type TranspilerOptions = {
};

enum ICPPTypeKind
{
    Invalid = "BSQTypeKind::Invalid",
    Register = "BSQTypeKind::Register",
    Struct = "BSQTypeKind::Struct",
    String = "BSQTypeKind::String",
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
    
    readonly allocinfo: ICPPTypeSizeInfo; //memory size information
    
    readonly isLeafType: boolean; //if refmask == undefined && ptrcount == 0
    readonly refmask: RefMask | undefined;
    readonly ptrcount: number; //if this is a packed object the number of pointers at the front

    constructor(name: string, tkey: MIRResolvedTypeKey, tkind: ICPPTypeKind, allocinfo: ICPPTypeSizeInfo, isLeafType: boolean, refmask: RefMask | undefined, ptrcount: number) {
        this.name = name;
        this.tkey = tkey;
        this.tkind = tkind;
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

export {
    TranspilerOptions,
    ICPPTypeKind, ICPPTypeSizeInfo, RefMask,
    ICPPType, ICPPTypePrimitive, ICPPTypeTuple, ICPPTypeRecord, ICPPTypeEntity, ICPPTypeEphemeralList,
    ICPPTypeAbstract, ICPPTypeInlineUnion, ICPPTypeHeapUnion
};
