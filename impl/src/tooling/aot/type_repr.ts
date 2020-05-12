//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

type TypeEncodingOpPack = {
    RCIncFunctor: string,
    RCDecFunctor: string,
    DisplayFunctor: string
}

type TypeEncodingOpPackKey = {
    EqualFunctor: string,
    LessFunctor: string
}

type TypeEncodingOpPackStruct = {
    RCReturnFunctor: string
}

abstract class TypeRepr {
    readonly iskey: boolean;
    readonly base: string;
    readonly std: string;
    readonly categoryinfo: string;

    constructor(iskey: boolean, base: string, std: string, categoryinfo: string) {
        this.iskey = iskey;
        this.base = base;
        this.std = std;
        this.categoryinfo = categoryinfo;
    }
}

class NoneRepr extends TypeRepr {
    constructor() {
        super(true, "NoneValue", "NoneValue", "MIRNominalTypeEnum_Category_Empty");
    }
}

class StructRepr extends TypeRepr {
    readonly boxed: string;
    readonly nominaltype: string;

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

class KeyValueRepr extends TypeRepr {
    constructor() {
        super(true, "KeyValue", "KeyValue", "MIRNominalTypeEnum_Category_Empty");
    }
}

class ValueRepr extends TypeRepr {
    constructor() {
        super(false, "Value", "Value", "MIRNominalTypeEnum_Category_Empty");
    }
}

class EphemeralListRepr extends TypeRepr {
    constructor(base: string) {
        super(false, base, base + "*", "MIRNominalTypeEnum_Category_Empty");
    }
}

function joinTypeRepr(tr1: TypeRepr, tr2: TypeRepr): TypeRepr {
    if(tr1.base === tr2.base) {
        return tr1;
    }

    if(tr1.base === "BSQTuple" || tr1.base === "BSQRecord" || tr2.base === "BSQTuple" || tr2.base === "BSQRecord") {
        return new ValueRepr(); 
    }
    
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
    TypeEncodingOpPack, TypeEncodingOpPackKey, TypeEncodingOpPackStruct,
    TypeRepr, NoneRepr, StructRepr, RefRepr, KeyValueRepr, ValueRepr, EphemeralListRepr,
    joinTypeReprs
};
