//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";
import { MIRType } from "../../compiler/mir_assembly";

enum LayoutMaskEnum {
    End = 0,
    Scalar = 1,
    Ptr = 2,
    Union = 4
};

const StorageByteAlignment = 8;

enum ReprStorageKind
{
    Primitive,
    Pointer,
    ValueStruct,
    GeneralStruct
}

abstract class TypeRepr {
    readonly mirtype: MIRType;

    readonly iskey: boolean;
    readonly basetype: string;
    readonly storagetype: string;
    readonly passingtype: string;

    readonly storage: ReprStorageKind;

    readonly metadataName: string;
    readonly realSize: number;
    readonly alignedSize: number;
    readonly packedPtrCount: number;
    readonly layoutmask: LayoutMaskEnum[];

    constructor(mirtype: MIRType, iskey: boolean, basetype: string, storagetype: string, storage: ReprStorageKind, metadataName: string, realSize: number, packedPtrCount: number, layoutmask: LayoutMaskEnum[]) {
        this.mirtype = mirtype;

        this.iskey = iskey;
        this.basetype = basetype;
        this.storagetype = storagetype;
        this.passingtype = this.storagetype + (storage !== ReprStorageKind.Primitive ? "&" : "");
        
        this.storage = storage;

        this.metadataName = metadataName;
        this.realSize = realSize;
        this.alignedSize = (((this.realSize) + 0x7) & 0xFFFFFFFFFFFC);

        this.packedPtrCount = packedPtrCount;
        this.layoutmask = layoutmask;
    }

    constructStringReprOfMask(): string {
        return this.layoutmask.map((c) => `${c}`).join("");
    }
}

class NoneRepr extends TypeRepr {
    constructor() {
        super(true, "NoneValue", "NoneValue", false, true, "MetaData_None", false, MemoryByteAlignment, MemoryByteAlignment, -1, [LayoutMaskEnum.Scalar]);
    }
}

class PrimitiveRepr extends TypeRepr {
    constructor() {
        super(true, "NoneValue", "NoneValue", false, true, "MetaData_None", false, MemoryByteAlignment, MemoryByteAlignment, -1, [LayoutMaskEnum.Scalar]);
    }
}

class StructRepr extends TypeRepr {
    constructor(iskey: boolean, base: string, boxed: string, nominaltype: string, categoryinfo: string) {
        super(iskey, base, base, categoryinfo);
        this.boxed = boxed;
        this.nominaltype = nominaltype;
    }
}

class TRRepr extends TypeRepr {
    readonly kind: "tuple" | "record";
    readonly elemcount: number;
    
    constructor(iskey: boolean, base: string, boxed: string, nominaltype: string, categoryinfo: string) {
        super(iskey, base, base, categoryinfo);
        this.boxed = boxed;
        this.nominaltype = nominaltype;
    }
}

class RefRepr extends TypeRepr {
    constructor(iskey: boolean, base: string, std: string, categoryinfo: string) {
        super(iskey, base, std, categoryinfo);
    }
}

class UnionRepr extends TypeRepr {
    readonly oftypes: (NoneRepr | StructRepr | TRRepr | RefRepr)[];
    readonly datasize: number;

    constructor(iskey: boolean, hasPointers: boolean, datasize: number, realSize: number, alignedSize: number, oftypes: (NoneRepr | StructRepr | RefRepr)[]) {
        super(iskey, "UnionValue", "UnionValue", true, false, "[NO META]", hasPointers, realSize, alignedSize, -1, []);

        this.oftypes = oftypes;
        this.datasize = datasize;
    }

    static create(oftypes: (NoneRepr | StructRepr | TRRepr | RefRepr)[]): TypeRepr {
        const iskey = oftypes.every((tr) => tr.iskey);
        const hasptrs = oftypes.some((tr) => tr.hasPointers);
        const datasize = oftypes.reduce((acc, v) => Math.max(acc, (v instanceof RefRepr) ? MemoryByteAlignment : v.alignedSize), 0);
        const realSize = oftypes.reduce((acc, v) => Math.max(acc, (v instanceof RefRepr) ? MemoryByteAlignment : v.realSize), 0) + 4;
        const alignedSize = oftypes.reduce((acc, v) => Math.max(acc, (v instanceof RefRepr) ? MemoryByteAlignment : v.alignedSize), 0) + 4;

        return new UnionRepr(iskey, hasptrs, realSize, alignedSize, oftypes);
    }
}

class KeyValueRepr extends TypeRepr {
    constructor() {
        super(true, "KeyValue", "KeyValue", "MIRNominalTypeEnum_Category_Empty");
    }
}

class ValueRepr extends TypeRepr {
    constructor() {
        super(false, "Value", "Value", "MIRNominalTypeEnum_Category_Empty");
    }

    static singleton = new ValueRepr();
}

class EphemeralListRepr extends TypeRepr {
    readonly elist: TypeRepr[];

    constructor(base: string) {
        super(false, base, base, "MIRNominalTypeEnum_Category_Empty");
    }
}

function joinTypeRepr(tr1: TypeRepr, tr2: TypeRepr): TypeRepr {
    if(tr1.base === tr2.base) {
        return tr1;
    }

    xxxx; //Union types and TR types!!!
    
    if (tr1 instanceof NoneRepr) {
        if (tr2 instanceof NoneRepr) {
            return new NoneRepr();
        }
        else if (tr1.iskey && tr2.iskey) {
            return new KeyValueRepr();
        }
        else {
            return new ValueRepr();
        }
    }
    else if (tr1 instanceof StructRepr) {
        if (tr1.iskey && tr2.iskey) {
            return new KeyValueRepr();
        }
        else {
            return new ValueRepr();
        }
    }
    else {
        if (tr1.iskey && tr2.iskey) {
            return new KeyValueRepr();
        }
        else {
            return new ValueRepr();
        }
    }
}

function joinTypeReprs(...trl: TypeRepr[]): TypeRepr {
    assert(trl.length > 1);

    let ctype = trl[0];
    for(let i = 1; i < trl.length; ++i) {
        ctype = joinTypeRepr(ctype, trl[i]);
    }

    return ctype;
}

export {
    ReprStorageKind, LayoutMaskEnum, TypeRepr, NoneRepr, PrimitiveRepr, StructRepr, TRRepr, RefRepr, UnionRepr, KeyValueRepr, ValueRepr, EphemeralListRepr,
    joinTypeReprs,
    StorageByteAlignment
};
