//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";
import { MIRType, MIROOTypeDecl, MIRTupleType, MIRRecordType, MIRFunctionType, MIRInvokeDecl, MIREntityType } from "../compiler/mir_assembly";

type Value = undefined | boolean | number | string | FloatValue | TypedStringValue | RegexValue | GUIDValue | EntityValue | TupleValue | RecordValue | LambdaValue;
type KeyValue = undefined | boolean | number | string | GUIDValue | EnumValue | TupleValue | RecordValue | CustomKeyValue;

class FloatValue {
    readonly value: number;

    constructor(v: number) {
        this.value = v;
    }
}

class TypedStringValue {
    readonly oftype: MIROOTypeDecl;
    readonly stype: MIRType;
    readonly value: string;

    constructor(oftype: MIROOTypeDecl, stype: MIRType, value: string) {
        this.oftype = oftype;
        this.stype = stype;
        this.value = value;
    }
}

class RegexValue {
    readonly value: string;
    readonly re: RegExp;

    constructor(v: string) {
        this.value = v;
        this.re = new RegExp(v, "yu");
    }
}

class GUIDValue {
    readonly host: string;
    readonly tag: number;

    constructor(host: string, tag: number) {
        this.host = host;
        this.tag = tag;
    }
}

class TupleValue {
    readonly ttype: MIRTupleType;
    readonly values: Value[];

    constructor(ttype: MIRTupleType, values: Value[]) {
        this.ttype = ttype;
        this.values = values;
    }
}

class RecordValue {
    readonly rtype: MIRRecordType;
    readonly values: [string, Value][];

    constructor(rtype: MIRRecordType, values: [string, Value][]) {
        this.rtype = rtype;
        this.values = values;
    }
}

class LambdaValue {
    readonly ftype: MIRFunctionType;
    readonly invoke: MIRInvokeDecl;
    readonly capturedVars: Map<string, Value>;

    constructor(ftype: MIRFunctionType, invoke: MIRInvokeDecl, capturedVars: Map<string, Value>) {
        this.ftype = ftype;
        this.invoke = invoke;
        this.capturedVars = capturedVars;
    }
}

class EntityValue {
    readonly etype: MIREntityType;

    constructor(etype: MIREntityType) {
        this.etype = etype;
    }
}

class EntityValueSimple extends EntityValue {
    readonly fields: [string, Value][];

    constructor(etype: MIREntityType, fields: [string, Value][]) {
        super(etype);
        this.fields = fields;
    }
}

class EnumValue extends EntityValue {
    readonly enumValue: number;

    constructor(etype: MIREntityType, v: number) {
        super(etype);
        this.enumValue = v;
    }
}

class CustomKeyValue extends EntityValue {
    readonly cvalue: undefined | boolean | number | string | GUIDValue | EnumValue | TupleValue | RecordValue;

    constructor(etype: MIREntityType, cvalue: undefined | boolean | number | string | GUIDValue | EnumValue | TupleValue | RecordValue) {
        super(etype);
        this.cvalue = cvalue;
    }
}

abstract class CollectionValue extends EntityValue {
    constructor(etype: MIREntityType) {
        super(etype);
    }

    abstract getEnumContents(): Value[];
}

class ListValue extends CollectionValue {
    readonly values: Value[];

    constructor(etype: MIREntityType, values: Value[]) {
        super(etype);
        this.values = values;
    }

    getEnumContents(): Value[] {
        return this.values;
    }
}

class HashSetValue extends CollectionValue {
    readonly enumContents: Value[];
    readonly values: Map<number, Value[]>;

    constructor(etype: MIREntityType, enumContents: Value[], values: Map<number, Value[]>) {
        super(etype);
        this.enumContents = enumContents;
        this.values = values;
    }

    private static has(k: number, v: Value, values: Map<number, [number, Value][]>): boolean {
        const bucket = values.get(k);
        if (bucket === undefined) {
            return false;
        }

        return bucket.findIndex((e) => ValueOps.valueEqualTo(e[1], v)) !== -1;
    }

    private static insert(k: number, v: Value, ictr: number, values: Map<number, [number, Value][]>) {
        const bucket = values.get(k);
        if (bucket === undefined) {
            values.set(k, [[ictr, v]]);
        }
        else {
            bucket.push([ictr, v]);
        }
    }

    private static update(k: number, v: Value, ictr: number, values: Map<number, [number, Value][]>) {
        const bucket = values.get(k) as [number, Value][];
        const bidx = bucket.findIndex((e) => ValueOps.valueEqualTo(e[1], v));
        bucket[bidx] = [ictr, v];
    }

    static create(etype: MIREntityType, values: Value[]): HashSetValue {
        let tvm = new Map<number, [number, Value][]>();
        values.forEach((v, idx) => {
            const key = ValueOps.valueHash(v);
            if (HashSetValue.has(key, v, tvm)) {
                HashSetValue.update(key, v, idx, tvm);
            }
            else {
                HashSetValue.insert(key, v, idx, tvm);
            }
        });

        let ec: [number, Value][] = [];
        let vm = new Map<number, Value[]>();
        tvm.forEach((v, k) => {
            ec.push(...v);
            vm.set(k, v.map((nv) => nv[1]));
        });

        return new HashSetValue(etype, ec.sort((nv1, nv2) => nv1[0] - nv2[0]).map((nv) => nv[1]), vm);
    }

    getEnumContents(): Value[] {
        return this.enumContents;
    }
}

abstract class MapValue extends EntityValue {
    constructor(etype: MIREntityType) {
        super(etype);
    }

    abstract lookup(key: KeyValue): Value | null;
    abstract getEnumContents(): Value[];
}

class HashMapValue extends MapValue {
    readonly enumContents: Value[];
    readonly values: Map<number, TupleValue[]>;

    constructor(etype: MIREntityType, enumContents: Value[], values: Map<number, TupleValue[]>) {
        super(etype);
        this.enumContents = enumContents;
        this.values = values;
    }

    private static has(k: number, v: TupleValue, values: Map<number, [number, TupleValue][]>): boolean {
        const bucket = values.get(k);
        if (bucket === undefined) {
            return false;
        }

        return bucket.findIndex((e) => ValueOps.valueEqualTo(e[1].values[0], v.values[0])) !== -1;
    }

    private static insert(k: number, v: TupleValue, ictr: number, values: Map<number, [number, TupleValue][]>) {
        const bucket = values.get(k);
        if (bucket === undefined) {
            values.set(k, [[ictr, v]]);
        }
        else {
            bucket.push([ictr, v]);
        }
    }

    private static update(k: number, v: TupleValue, ictr: number, values: Map<number, [number, TupleValue][]>) {
        const bucket = values.get(k) as [number, TupleValue][];
        const bidx = bucket.findIndex((e) => ValueOps.valueEqualTo(e[1].values[0], v.values[0]));
        bucket[bidx] = [ictr, v];
    }

    static create(etype: MIREntityType, values: TupleValue[]): HashMapValue {
        let tvm = new Map<number, [number, TupleValue][]>();
        values.forEach((v, idx) => {
            const key = ValueOps.valueHash(v.values[0]);
            if (HashMapValue.has(key, v, tvm)) {
                HashMapValue.update(key, v, idx, tvm);
            }
            else {
                HashMapValue.insert(key, v, idx, tvm);
            }
        });

        let ec: [number, TupleValue][] = [];
        let vm = new Map<number, TupleValue[]>();
        tvm.forEach((v, k) => {
            ec.push(...v);
            vm.set(k, v.map((nv) => nv[1]));
        });

        return new HashMapValue(etype, ec.sort((nv1, nv2) => nv1[0] - nv2[0]).map((nv) => nv[1]), vm);
    }

    lookup(key: Value): Value | null {
        const bucket = this.values.get(ValueOps.valueHash(key));
        if (bucket === undefined) {
            return null;
        }

        const bidx = bucket.findIndex((e) => ValueOps.valueEqualTo(e.values[0], key));
        return (bidx !== -1) ? bucket[bidx].values[1] : null;
    }

    getEnumContents(): Value[] {
        return this.enumContents;
    }
}

class ValueOps {
    static isNone(v: Value): boolean {
        return v === undefined;
    }

    static isBool(v: Value): boolean {
        return typeof (v) === "boolean";
    }

    static isInt(v: Value): boolean {
        return typeof (v) === "number";
    }

    static isString(v: Value): boolean {
        return typeof (v) === "string";
    }

    static unescapeString(str: string): string {
        //
        //TODO: should do more here
        //
        return str.substr(1, str.length - 2);
    }

    static escapeString(str: string): string {
        //
        //TODO: should do more here
        //
        return "\"" + str + "\"";
    }

    static unescapeTypedString(str: string): string {
        //
        //TODO: should do more here
        //
        return str.substr(1, str.length - 2);
    }

    static escapeTypedString(str: string): string {
        //
        //TODO: should do more here
        //
        return "'" + str + "'";
    }

    static convertBoolOrNoneToBool(v: Value): boolean {
        if (v === undefined) {
            return false;
        }
        else {
            return v as boolean;
        }
    }

    static convertToBasicString(v: Value): string {
        return typeof (v) === "string" ? v : (v as TypedStringValue).value;
    }

    static diagnosticPrintValue(v: Value): string {
        if (v === undefined) {
            return "none";
        }

        const t = typeof (v);
        if (t === "boolean" || t === "number") {
            return v.toString();
        }
        else if (t === "string") {
            return ValueOps.escapeString(v as string);
        }
        else {
            if (v instanceof FloatValue) {
                return v.value.toString();
            }
            else if (v instanceof TypedStringValue) {
                return `${ValueOps.escapeTypedString(v.value)}#${v.oftype.tkey}`;
            }
            else if (v instanceof RegexValue) {
                return v.value;
            }
            else if (v instanceof GUIDValue) {
                return `${v.host}$${v.tag}`;
            }
            else if (v instanceof TupleValue) {
                const vals = v.values.map((tv) => ValueOps.diagnosticPrintValue(tv));
                return vals.length === 0 ? "@[]" : `@[ ${vals.join(", ")} ]`;
            }
            else if (v instanceof RecordValue) {
                let vals: string[] = [];
                v.values.forEach((vk) => vals.push(`${vk[0]}=${ValueOps.diagnosticPrintValue(vk[1])}`));
                return vals.length === 0 ? "@{}" : `@{ ${vals.join(", ")} }`;
            }
            else if (v instanceof LambdaValue) {
                return v.ftype.trkey;
            }
            else {
                if (v instanceof EnumValue) {
                    return v.etype.ekey + "::" + v.enumValue;
                }
                else if (v instanceof CustomKeyValue) {
                    return v.etype.ekey + "::" + v.cvalue;
                }
                else if (v instanceof EntityValueSimple) {
                    let vals: string[] = [];
                    v.fields.forEach((kv) => vals.push(`${kv[0]}=${ValueOps.diagnosticPrintValue(kv[1])}`));
                    return v.etype.ekey + (vals.length === 0 ? "@{}" : `@{ ${vals.sort().join(", ")} }`);
                }
                else if (v instanceof ListValue) {
                    const vals = v.values.map((lv) => ValueOps.diagnosticPrintValue(lv));
                    return v.etype.ekey + (vals.length === 0 ? "@{}" : `@{ ${vals.join(", ")} }`);
                }
                else if (v instanceof HashSetValue) {
                    const vals = v.getEnumContents().map((sv) => ValueOps.diagnosticPrintValue(sv));
                    return v.etype.ekey + (vals.length === 0 ? "@{}" : `@{ ${vals.join(", ")} }`);
                }
                else if (v instanceof HashMapValue) {
                    const vals = v.getEnumContents().map((mv) => ValueOps.diagnosticPrintValue(mv));
                    return v.etype.ekey + (vals.length === 0 ? "@{}" : `@{ ${vals.join(", ")} }`);
                }
                else {
                    return "[NOT IMPLEMENTED YET]";
                }
            }
        }
    }

    static getValueType(v: Value): MIRType {
        switch (typeof (v)) {
            case "undefined": return MIRType.createSingle(MIREntityType.create("NSCore::None"));
            case "boolean": return MIRType.createSingle(MIREntityType.create("NSCore::Bool"));
            case "number": return MIRType.createSingle(MIREntityType.create("NSCore::Int"));
            case "string": return MIRType.createSingle(MIREntityType.create("NSCore::String[T=NSCore::Any]"));
            default: {
                if (v instanceof FloatValue) {
                    return MIRType.createSingle(MIREntityType.create("NSCore::Float"));
                }
                else if (v instanceof TypedStringValue) {
                    return v.stype;
                }
                else if (v instanceof RegexValue) {
                    return MIRType.createSingle(MIREntityType.create("NSCore::Regex"));
                }
                else if (v instanceof GUIDValue) {
                    return MIRType.createSingle(MIREntityType.create("NSCore::GUID"));
                }
                else if (v instanceof TupleValue) {
                    return MIRType.createSingle(v.ttype);
                }
                else if (v instanceof RecordValue) {
                    return MIRType.createSingle(v.rtype);
                }
                else if (v instanceof LambdaValue) {
                    return MIRType.createSingle(v.ftype);
                }
                else {
                    assert(v instanceof EntityValue);

                    return MIRType.createSingle((v as EntityValue).etype);
                }
            }
        }
    }

    static getContainerContentsEnumeration(v: Value): Value[] {
        if (v instanceof CollectionValue) {
            return v.getEnumContents();
        }
        else {
            assert(v instanceof MapValue);

            return (v as MapValue).getEnumContents();
        }
    }

    static getKeyForValue(v: Value): KeyValue {
        if (typeof (v) === "object") {
            if (v instanceof TypedStringValue) {
                return v.value;
            }

            if (v instanceof EntityValueSimple) {
                const kidx = v.fields.findIndex((kv) => kv[0] === "key");
                assert(kidx !== -1);

                return v.fields[kidx][1] as KeyValue;
            }
        }

        return v as KeyValue;
    }

    private static hashHelper(hash: number, addtl: number): number {
        return (hash * addtl) % 452930477; //a mediocre hash with a largish prime
    }

    private static hashStringHelper(str: string, hvbase: number): number {
        let hv = hvbase;
        for (let i = 0; i < str.length; ++i) {
            hv = ValueOps.hashHelper(hv, str.charCodeAt(i));
        }
        return hv;
    }

    static keyValueHash(v: KeyValue): number {
        if (v === undefined) {
            return 0;
        }

        const tof = typeof (v);
        if (tof === "boolean") {
            return (v ? 3 : 1);
        }
        else if (tof === "number") {
            return v === -1 ? 1 : v as number;
        }
        else if (tof === "string") {
            return ValueOps.hashStringHelper(v as string, 23);
        }
        else {
            if (v instanceof GUIDValue) {
                return ValueOps.hashHelper(ValueOps.hashStringHelper(v.host, 31), v.tag);
            }
            else if (v instanceof EnumValue) {
                return ValueOps.hashHelper(ValueOps.hashStringHelper(v.etype.ekey as string, 43), v.enumValue);
            }
            else if (v instanceof TupleValue) {
                let hv = ValueOps.hashStringHelper(v.ttype.trkey, 33);
                v.values.forEach((tv) => {
                    hv = ValueOps.hashHelper(hv, ValueOps.valueHash(tv));
                });
                return hv;
            }
            else if (v instanceof RecordValue) {
                let hv = ValueOps.hashStringHelper(v.rtype.trkey, 53);
                v.values.forEach((rv) => {
                    hv = ValueOps.hashHelper(hv, ValueOps.hashStringHelper(rv[0], 101));
                    hv = ValueOps.hashHelper(hv, ValueOps.valueHash(rv[1]));
                });
                return hv;
            }
            else {
                assert(v instanceof CustomKeyValue);

                return ValueOps.keyValueHash((v as CustomKeyValue).cvalue);
            }
        }
    }

    static valueHash(v: Value): number {
        return ValueOps.keyValueHash(ValueOps.getKeyForValue(v));
    }

    static keyValueEqualTo(v1: KeyValue, v2: KeyValue): boolean {
        if (v1 === undefined || v2 === undefined) {
            return v1 === v2;
        }

        if (ValueOps.keyValueHash(v1) !== ValueOps.keyValueHash(v2)) {
            return false;
        }

        const t1 = typeof (v1);
        const t2 = typeof (v2);
        if (t1 === "boolean" && t2 === "boolean") {
            return v1 === v2;
        }
        else if (t1 === "number" && t2 === "number") {
            return v1 === v2;
        }
        else if (t1 === "string" && t2 === "string") {
            return v1 === v2;
        }
        else {
            if (v1 instanceof GUIDValue && v2 instanceof GUIDValue) {
                return v1.host === v2.host && v1.tag === v2.tag;
            }
            else if (v1 instanceof EnumValue && v2 instanceof EnumValue) {
                return v1.etype.ekey === v2.etype.ekey && v1.enumValue === v2.enumValue;
            }
            else if (v1 instanceof TupleValue && v2 instanceof TupleValue) {
                if (v1.values.length !== v2.values.length) {
                    return false;
                }

                for (let i = 0; i < v1.values.length; ++i) {
                    if (!ValueOps.valueEqualTo(v1.values[i], v2.values[i])) {
                        return false;
                    }
                }

                return true;
            }
            else if (v1 instanceof RecordValue && v2 instanceof RecordValue) {
                if (v1.values.length !== v2.values.length) {
                    return false;
                }

                for (let i = 0; i < v1.values.length; ++i) {
                    if (v1.values[i][0] !== v2.values[i][0] || !ValueOps.valueEqualTo(v1.values[i][1], v2.values[i][1])) {
                        return false;
                    }
                }

                return true;
            }
            else if (v1 instanceof CustomKeyValue && v2 instanceof CustomKeyValue) {
                return (v1.etype.ekey === v2.etype.ekey) && ValueOps.keyValueEqualTo((v1 as CustomKeyValue).cvalue, (v2 as CustomKeyValue).cvalue);
            }
            else {
                return false;
            }
        }
    }

    static valueEqualTo(v1: Value, v2: Value): boolean {
        return ValueOps.keyValueEqualTo(ValueOps.getKeyForValue(v1), ValueOps.getKeyForValue(v2));
    }

    static valueLessThan(v1: Value, v2: Value): boolean {
        const rv1 = (typeof(v1) === "object" && v1 instanceof TypedStringValue) ? v1.value : v1;
        const rv2 = (typeof(v2) === "object" && v2 instanceof TypedStringValue) ? v2.value : v2;

        if (typeof(rv1) === "number" && typeof(rv2) === "number") {
            return (rv1 as number) < (rv2 as number);
        }
        else {
            return (rv1 as string) < (rv2 as string);
        }
    }
}

export {
    Value, KeyValue, FloatValue, TypedStringValue, RegexValue, GUIDValue, ValueOps,
    TupleValue, RecordValue, LambdaValue,
    EntityValue, EntityValueSimple, EnumValue, CustomKeyValue,
    CollectionValue, ListValue, HashSetValue, MapValue, HashMapValue
};
