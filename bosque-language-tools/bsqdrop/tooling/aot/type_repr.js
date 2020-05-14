"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const assert = require("assert");
class TypeRepr {
    constructor(iskey, base, std, categoryinfo) {
        this.iskey = iskey;
        this.base = base;
        this.std = std;
        this.categoryinfo = categoryinfo;
    }
}
exports.TypeRepr = TypeRepr;
class NoneRepr extends TypeRepr {
    constructor() {
        super(true, "NoneValue", "NoneValue", "MIRNominalTypeEnum_Category_Empty");
    }
}
exports.NoneRepr = NoneRepr;
class StructRepr extends TypeRepr {
    constructor(iskey, base, boxed, nominaltype, categoryinfo) {
        super(iskey, base, base, categoryinfo);
        this.boxed = boxed;
        this.nominaltype = nominaltype;
    }
}
exports.StructRepr = StructRepr;
class RefRepr extends TypeRepr {
    constructor(iskey, base, std, categoryinfo) {
        super(iskey, base, std, categoryinfo);
    }
}
exports.RefRepr = RefRepr;
class KeyValueRepr extends TypeRepr {
    constructor() {
        super(true, "KeyValue", "KeyValue", "MIRNominalTypeEnum_Category_Empty");
    }
}
exports.KeyValueRepr = KeyValueRepr;
class ValueRepr extends TypeRepr {
    constructor() {
        super(false, "Value", "Value", "MIRNominalTypeEnum_Category_Empty");
    }
}
exports.ValueRepr = ValueRepr;
class EphemeralListRepr extends TypeRepr {
    constructor(base) {
        super(false, base, base + "*", "MIRNominalTypeEnum_Category_Empty");
    }
}
exports.EphemeralListRepr = EphemeralListRepr;
function joinTypeRepr(tr1, tr2) {
    if (tr1.base === tr2.base) {
        return tr1;
    }
    if (tr1.base === "BSQTuple" || tr1.base === "BSQRecord" || tr2.base === "BSQTuple" || tr2.base === "BSQRecord") {
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
function joinTypeReprs(...trl) {
    assert(trl.length > 1);
    let ctype = trl[0];
    for (let i = 1; i < trl.length; ++i) {
        ctype = joinTypeRepr(ctype, trl[i]);
    }
    return ctype;
}
exports.joinTypeReprs = joinTypeReprs;
//# sourceMappingURL=type_repr.js.map