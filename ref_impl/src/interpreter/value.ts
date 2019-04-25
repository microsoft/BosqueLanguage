//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";
import { MIRType, MIROOTypeDecl, MIRTupleType, MIRRecordType, MIRFunctionType, MIRInvokeDecl, MIREntityType } from "../compiler/mir_assembly";

type Value = undefined | boolean | number | string | FloatValue | TypedStringValue | RegexValue | GUIDValue | EntityValue | TupleValue | RecordValue | LambdaValue;
type KeyValue = undefined | boolean | number | string | GUIDValue | EnumValue | CustomKeyValue;

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
    readonly prefix: string;
    readonly key: string[];
    readonly value: string;

    constructor(etype: MIREntityType, prefix: string, key: string[]) {
        super(etype);
        this.prefix = prefix;
        this.key = key;
        this.value = `${prefix}$[${key.join(",")}]`;
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

//
//TODO: make this a RB tree -- we expect terrible performance for anything but small trees with this impl
//
class BSTNode {
    private key: KeyValue;
    private left: BSTNode | undefined;
    private right: BSTNode | undefined;

    data: Value; //value for set [K, V] tuple for map

    constructor(key: KeyValue, left: BSTNode | undefined, right: BSTNode | undefined, data: Value) {
        this.key = key;
        this.left = left;
        this.right = right;
        this.data = data;
    }

    static create(key: KeyValue, data: Value): BSTNode {
        return new BSTNode(key, undefined, undefined, data);
    }

    getContentsInto(contents: Value[]) {
        if (this.left !== undefined) {
            this.left.getContentsInto(contents);
        }

        contents.push(this.data);

        if (this.right !== undefined) {
            this.right.getContentsInto(contents);
        }
    }

    find(k: KeyValue): BSTNode | undefined {
        let curr: BSTNode | undefined = this;
        while (curr !== undefined) {
            if (ValueOps.keyValueEqualTo(k, curr.key)) {
                return curr;
            }
            else if (ValueOps.keyValueLessThan(k, curr.key)) {
                curr = curr.left;
            }
            else {
                curr = curr.right;
            }
        }
        return curr;
    }

    insertDirect(k: KeyValue, v: Value) {
        if (ValueOps.keyValueEqualTo(this.key, k)) {
            this.data = v;
        }
        else if (ValueOps.keyValueLessThan(k, this.key)) {
            if (this.left === undefined) {
                this.left = BSTNode.create(k, v);
            }
            else {
                this.left.insertDirect(k, v);
            }
        }
        else {
            if (this.right === undefined) {
                this.right = BSTNode.create(k, v);
            }
            else {
                this.right.insertDirect(k, v);
            }
        }
    }

    insertPersist(k: KeyValue, v: Value): BSTNode {
        if (ValueOps.keyValueEqualTo(this.key, k)) {
            return new BSTNode(k, this.left, this.right, v);
        }
        else if (ValueOps.keyValueLessThan(k, this.key)) {
            return (this.left === undefined) ? BSTNode.create(k, v) : this.left.insertPersist(k, v);
        }
        else {
            return (this.right === undefined) ? BSTNode.create(k, v) : this.right.insertPersist(k, v);
        }
    }
}

class TreeSetValue extends CollectionValue {
    private enumContents: Value[] | undefined;
    readonly tree: BSTNode | undefined;

    constructor(etype: MIREntityType, tree: BSTNode | undefined) {
        super(etype);
        this.enumContents = undefined;
        this.tree = tree;
    }

    static create(etype: MIREntityType, values: Value[]): TreeSetValue {
        if (values.length === 0) {
            return new TreeSetValue(etype, undefined);
        }
        else {
            let n = BSTNode.create(ValueOps.getKeyForValue(values[0]), values[0]);
            for (let i = 1; i < values.length; ++i) {
                n.insertDirect(ValueOps.getKeyForValue(values[i]), values[i]);
            }
            return new TreeSetValue(etype, n);
        }
    }

    getEnumContents(): Value[] {
        if (this.enumContents === undefined) {
            this.enumContents = [];
            if (this.tree !== undefined) {
                this.tree.getContentsInto(this.enumContents);
            }
        }

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

class TreeMapValue extends MapValue {
    private enumContents: Value[] | undefined;
    readonly tree: BSTNode | undefined;

    constructor(etype: MIREntityType, tree: BSTNode | undefined) {
        super(etype);
        this.enumContents = undefined;
        this.tree = tree;
    }

    static create(etype: MIREntityType, values: TupleValue[]): TreeSetValue {
        if (values.length === 0) {
            return new TreeSetValue(etype, undefined);
        }
        else {
            let n = BSTNode.create(ValueOps.getKeyForValue(values[0].values[0]), values[0]);
            for (let i = 1; i < values.length; ++i) {
                n.insertDirect(ValueOps.getKeyForValue(values[i].values[0]), values[i]);
            }
            return new TreeSetValue(etype, n);
        }
    }

    lookup(key: KeyValue): Value | null {
        if (this.tree === undefined) {
            return null;
        }

        const nn = this.tree.find(key);
        return nn !== undefined ? nn.data : null;
    }

    getEnumContents(): Value[] {
        if (this.enumContents === undefined) {
            this.enumContents = [];
            if (this.tree !== undefined) {
                this.tree.getContentsInto(this.enumContents);
            }
        }

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
                    return v.etype.ekey + "::" + v.value;
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
                else if (v instanceof TreeSetValue) {
                    const vals = v.getEnumContents().map((sv) => ValueOps.diagnosticPrintValue(sv));
                    return v.etype.ekey + (vals.length === 0 ? "@{}" : `@{ ${vals.join(", ")} }`);
                }
                else if (v instanceof TreeMapValue) {
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
            else {
                assert(v instanceof CustomKeyValue);

                return ValueOps.hashStringHelper((v as CustomKeyValue).value, 101);
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
            else if (v1 instanceof CustomKeyValue && v2 instanceof CustomKeyValue) {
                return (v1 as CustomKeyValue).value === (v2 as CustomKeyValue).value;
            }
            else {
                return false;
            }
        }
    }

    static valueEqualTo(v1: Value, v2: Value): boolean {
        return ValueOps.keyValueEqualTo(ValueOps.getKeyForValue(v1), ValueOps.getKeyForValue(v2));
    }

    static keyValueLessThan(v1: KeyValue, v2: KeyValue): boolean {
        if (v1 === undefined || v2 === undefined) {
            return v1 === undefined || v2 !== undefined;
        }

        const t1 = typeof (v1);
        const t2 = typeof (v2);
        if (t1 !== t2) {
            if (t1 === "boolean") {
                return true;
            }

            if (t1 === "number" && t2 !== "boolean") {
                return true;
            }

            if (t1 === "string" && t2 !== "boolean" && t2 !== "number") {
                return true;
            }

            if (t1 === "object") {
                return false;
            }
        }

        if (t1 === "boolean" && t2 === "boolean") {
            return !(v1 as boolean) && (v2 as boolean);
        }
        else if (t1 === "number" && t2 === "number") {
            return (v1 as number) < (v2 as number);
        }
        else if (t1 === "string" && t2 === "string") {
            return (v1 as string) < (v2 as string);
        }
        else {
            if (v1 instanceof GUIDValue && v2 instanceof GUIDValue) {
                return v1.host < v2.host || (v1.host === v2.host && v1.tag < v2.tag);
            }
            else if (v1 instanceof EnumValue && v2 instanceof EnumValue) {
                return v1.etype.trkey < v2.etype.trkey || (v1.etype.trkey === v2.etype.trkey && v1.enumValue < v2.enumValue);
            }
            else if (v1 instanceof CustomKeyValue && v2 instanceof CustomKeyValue) {
                return (v1 as CustomKeyValue).value < (v2 as CustomKeyValue).value;
            }
            else {
                return (v1 as EntityValue).etype.ekey < (v2 as EntityValue).etype.ekey;
            }
        }
    }

    static valueLessThan(v1: Value, v2: Value): boolean {
        return ValueOps.keyValueLessThan(ValueOps.getKeyForValue(v1), ValueOps.getKeyForValue(v2));
    }
}

export {
    Value, KeyValue, FloatValue, TypedStringValue, RegexValue, GUIDValue, ValueOps,
    TupleValue, RecordValue, LambdaValue,
    EntityValue, EntityValueSimple, EnumValue, CustomKeyValue,
    CollectionValue, ListValue, TreeSetValue, MapValue, TreeMapValue
};
