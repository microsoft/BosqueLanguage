//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo } from "../ast/parser";
import { MIRBody, MIRResolvedTypeKey, MIRFieldKey, MIRInvokeKey, MIRVirtualMethodKey, MIRGlobalKey } from "./mir_ops";
import { BSQRegex } from "../ast/bsqregex";

import assert = require("assert");

function jemitsinfo(sinfo: SourceInfo): object {
    return { line: sinfo.line, column: sinfo.column, pos: sinfo.pos, span: sinfo.span };
}

function jparsesinfo(jobj: any): SourceInfo {
    return new SourceInfo(jobj.line, jobj.column, jobj.pos, jobj.span);
}

class MIRFunctionParameter {
    readonly name: string;
    readonly type: MIRResolvedTypeKey;

    constructor(name: string, type: MIRResolvedTypeKey) {
        this.name = name;
        this.type = type;
    }

    jemit(): object {
        return { name: this.name, type: this.type };
    }

    static jparse(jobj: any): MIRFunctionParameter {
        return new MIRFunctionParameter(jobj.name, jobj.type);
    }
}

class MIRConstantDecl {
    readonly enclosingDecl: MIRResolvedTypeKey | undefined;
    readonly cname: string;
    readonly gkey: MIRGlobalKey;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly declaredType: MIRResolvedTypeKey;
    readonly value: MIRInvokeKey;

    constructor(enclosingDecl: MIRResolvedTypeKey | undefined, cname: string, valuekey: MIRInvokeKey, sinfo: SourceInfo, srcFile: string, declaredType: MIRResolvedTypeKey, gkey: MIRGlobalKey) {
        this.enclosingDecl = enclosingDecl;
        this.cname = cname;
        this.gkey = gkey;
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

        this.declaredType = declaredType;
        this.value = valuekey;
    }

    jemit(): object {
        return { enclosingDecl: this.enclosingDecl, cname: this.cname, gkey: this.gkey, sinfo: jemitsinfo(this.sourceLocation), file: this.srcFile, declaredType: this.declaredType, value: this.value };
    }

    static jparse(jobj: any): MIRConstantDecl {
        return new MIRConstantDecl(jobj.enclosingDecl, jobj.cname, jobj.gkey, jparsesinfo(jobj.sinfo), jobj.file, jobj.declaredType, jobj.value);
    }
}

abstract class MIRInvokeDecl {
    readonly enclosingDecl: MIRResolvedTypeKey | undefined;
    readonly name: string;
    readonly iname: string;
    readonly key: MIRInvokeKey;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly recursive: boolean;

    readonly params: MIRFunctionParameter[];
    readonly resultType: MIRResolvedTypeKey;

    readonly preconditions: MIRInvokeKey[] | undefined;
    readonly postconditions: MIRInvokeKey[] | undefined;

    constructor(enclosingDecl: MIRResolvedTypeKey | undefined, name: string, iname: string, key: MIRInvokeKey, attributes: string[], recursive: boolean, sinfo: SourceInfo, srcFile: string, params: MIRFunctionParameter[], resultType: MIRResolvedTypeKey, preconds: MIRInvokeKey[] | undefined, postconds: MIRInvokeKey[] | undefined) {
        this.enclosingDecl = enclosingDecl;
        this.name = name;
        this.iname = iname;
        this.key = key;

        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

        this.attributes = attributes;
        this.recursive = recursive;

        this.params = params;
        this.resultType = resultType;

        this.preconditions = preconds;
        this.postconditions = postconds;

    }

    abstract jemit(): object;

    static jparse(jobj: any): MIRInvokeDecl {
        if (jobj.body) {
            return new MIRInvokeBodyDecl(jobj.enclosingDecl, jobj.name, jobj.iname, jobj.key, jobj.attributes, jobj.recursive, jparsesinfo(jobj.sinfo), jobj.file, jobj.params.map((p: any) => MIRFunctionParameter.jparse(p)), jobj.masksize, jobj.resultType, jobj.preconditions || undefined, jobj.postconditions || undefined, MIRBody.jparse(jobj.body));
        }
        else {
            let binds = new Map<string, MIRResolvedTypeKey>();
            jobj.binds.forEach((bind: any) => binds.set(bind[0], bind[1]));

            let pcodes = new Map<string, MIRPCode>();
            jobj.pcodes.forEach((pc: any) => pcodes.set(pc[0], pc[1]));

            return new MIRInvokePrimitiveDecl(jobj.enclosingDecl, jobj.name, jobj.iname, jobj.key, jobj.attributes, jobj.recursive, jparsesinfo(jobj.sinfo), jobj.file, binds, jobj.params.map((p: any) => MIRFunctionParameter.jparse(p)), jobj.resultType, jobj.implkey, pcodes);
        }
    }
}

class MIRInvokeBodyDecl extends MIRInvokeDecl {
    readonly body: MIRBody;
    readonly masksize: number;

    constructor(enclosingDecl: MIRResolvedTypeKey | undefined, name: string, iname: string, key: MIRInvokeKey, attributes: string[], recursive: boolean, sinfo: SourceInfo, srcFile: string, params: MIRFunctionParameter[], masksize: number, resultType: MIRResolvedTypeKey, preconds: MIRInvokeKey[] | undefined, postconds: MIRInvokeKey[] | undefined, body: MIRBody) {
        super(enclosingDecl, name, iname, key, attributes, recursive, sinfo, srcFile, params, resultType, preconds, postconds);

        this.body = body;
        this.masksize = masksize;
    }

    jemit(): object {
        return { enclosingDecl: this.enclosingDecl, name: this.name, iname: this.iname, key: this.key, sinfo: jemitsinfo(this.sourceLocation), file: this.srcFile, attributes: this.attributes, recursive: this.recursive, params: this.params.map((p) => p.jemit()), masksize: this.masksize, resultType: this.resultType, preconditions: this.preconditions, postconditions: this.postconditions, body: this.body.jemit() };
    }
}

type MIRPCode = {
    code: MIRInvokeKey,
    cargs: string[]
};

class MIRInvokePrimitiveDecl extends MIRInvokeDecl {
    readonly implkey: string;
    readonly binds: Map<string, MIRResolvedTypeKey>;
    readonly pcodes: Map<string, MIRPCode>;

    constructor(enclosingDecl: MIRResolvedTypeKey | undefined, name: string, iname: string, key: MIRInvokeKey, attributes: string[], recursive: boolean, sinfo: SourceInfo, srcFile: string, binds: Map<string, MIRResolvedTypeKey>, params: MIRFunctionParameter[], resultType: MIRResolvedTypeKey, implkey: string, pcodes: Map<string, MIRPCode>) {
        super(enclosingDecl, name, iname, key, attributes, recursive, sinfo, srcFile, params, resultType, undefined, undefined);

        this.implkey = implkey;
        this.binds = binds;
        this.pcodes = pcodes;
    }

    jemit(): object {
        return {enclosingDecl: this.enclosingDecl, name: this.name, iname: this.iname, key: this.key, sinfo: jemitsinfo(this.sourceLocation), file: this.srcFile, attributes: this.attributes, recursive: this.recursive, params: this.params.map((p) => p.jemit()), resultType: this.resultType, implkey: this.implkey, binds: [...this.binds], pcodes: [... this.pcodes] };
    }
}

class MIRFieldDecl {
    readonly enclosingDecl: MIRResolvedTypeKey;
    readonly attributes: string[];

    readonly fname: string;
    readonly fkey: MIRFieldKey;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly name: string;
    readonly declaredType: MIRResolvedTypeKey;

    constructor(enclosingDecl: MIRResolvedTypeKey, attributes: string[], fname: string, srcInfo: SourceInfo, srcFile: string, fkey: MIRFieldKey, name: string, dtype: MIRResolvedTypeKey) {
        this.enclosingDecl = enclosingDecl;
        this.attributes = attributes;

        this.fname = fname;
        this.fkey = fkey;

        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;

        this.name = name;
        this.declaredType = dtype;
    }

    jemit(): object {
        return { enclosingDecl: this.enclosingDecl, attributes: this.attributes, fname: this.fname, fkey: this.fkey, sinfo: jemitsinfo(this.sourceLocation), file: this.srcFile, name: this.name, declaredType: this.declaredType };
    }

    static jparse(jobj: any): MIRFieldDecl {
        return new MIRFieldDecl(jobj.enclosingDecl, jobj.attributes, jobj.fname, jparsesinfo(jobj.sinfo), jobj.file, jobj.fkey, jobj.name, jobj.declaredType);
    }
}

abstract class MIROOTypeDecl {
    readonly ooname: string;
    readonly tkey: MIRResolvedTypeKey;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];

    readonly ns: string;
    readonly name: string;
    readonly terms: Map<string, MIRType>;
    readonly provides: MIRResolvedTypeKey[];

    constructor(ooname: string, srcInfo: SourceInfo, srcFile: string, tkey: MIRResolvedTypeKey, attributes: string[], ns: string, name: string, terms: Map<string, MIRType>, provides: MIRResolvedTypeKey[]) {
        this.ooname = ooname;
        this.tkey = tkey;

        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;

        this.attributes = attributes;

        this.ns = ns;
        this.name = name;
        this.terms = terms;
        this.provides = provides;
    }

    abstract jemit(): object;

    static jparse(jobj: any): MIROOTypeDecl {
        let terms = new Map<string, MIRType>();
            jobj.terms.forEach((t: any) => terms.set(t[0], MIRType.jparse(t[1])));

        if (!jobj.isentity) {
            return new MIRConceptTypeDecl(jobj.ooname, jparsesinfo(jobj.sinfo), jobj.file, jobj.tkey, jobj.attributes, jobj.ns, jobj.name, terms, jobj.provides);
        }
        else {
            const entity = new MIREntityTypeDecl(jobj.ooname, jparsesinfo(jobj.sinfo), jobj.file, jobj.tkey, jobj.attributes, jobj.ns, jobj.name, terms, jobj.provides, jobj.consfunc, jobj.consfuncfields, jobj.fields.map((f: any) => MIRFieldDecl.jparse(f)), jobj.specialDecls, jobj.specialTemplateInfo);
            jobj.vcallMap.forEach((vc: any) => entity.vcallMap.set(vc[0], vc[1]));
            return entity;
        }
    }
}

class MIRConceptTypeDecl extends MIROOTypeDecl {
    constructor(ooname: string, srcInfo: SourceInfo, srcFile: string, tkey: MIRResolvedTypeKey, attributes: string[], ns: string, name: string, terms: Map<string, MIRType>, provides: MIRResolvedTypeKey[]) {
        super(ooname, srcInfo, srcFile, tkey, attributes, ns, name, terms, provides);
    }

    jemit(): object {
        return { isentity: false, ooname: this.ooname, tkey: this.tkey, sinfo: jemitsinfo(this.sourceLocation), file: this.srcFile, attributes: this.attributes, ns: this.ns, name: this.name, terms: [...this.terms].map((t) => [t[0], t[1].jemit()]), provides: this.provides };
    }
}

enum MIRSpecialTypeCategory {
    GroundedTypeDecl = "GroundedTypeDecl",
    ParsableTypeDecl = "ParsableTypeDecl",
    ValidatorTypeDecl = "ValidatorTypeDecl",
    EnumTypeDecl = "EnumTypeDecl",
    TypeDeclDecl = "TypeDeclDecl",
    TypeDeclNumeric = "TypeDeclNumeric",
    StringOfDecl = "StringOfDecl",
    DataStringDecl = "DataStringDecl",
    BufferDecl = "BufferDecl",
    DataBufferDecl = "DataBufferDecl",
    ResultDecl = "ResultDecl",
    ResultOkDecl = "ResultOkDecl",
    ResultErrDecl = "ResultErrDecl",
    VectorTypeDecl = "VectorTypeDecl",
    ListTypeDecl = "ListTypeDecl",
    StackTypeDecl = "StackTypeDecl",
    QueueTypeDecl = "QueueTypeDecl",
    SetTypeDecl = "SetTypeDecl",
    DynamicSetTypeDecl = "DynamicSetTypeDecl",
    MapTypeDecl = "MapTypeDecl",
    DynamicMapTypeDecl = "DynamicMapTypeDecl"
}

class MIREntityTypeDecl extends MIROOTypeDecl {
    readonly consfunc: MIRInvokeKey | undefined;
    readonly consfuncfields: MIRFieldKey[];

    readonly fields: MIRFieldDecl[];
    readonly vcallMap: Map<MIRVirtualMethodKey, MIRInvokeKey> = new Map<string, MIRInvokeKey>();

    readonly specialDecls: Set<MIRSpecialTypeCategory>;
    readonly specialTemplateInfo: {tname: string, tkind: MIRResolvedTypeKey}[] | undefined;

    constructor(ooname: string, srcInfo: SourceInfo, srcFile: string, tkey: MIRResolvedTypeKey, attributes: string[], ns: string, name: string, terms: Map<string, MIRType>, provides: MIRResolvedTypeKey[], consfunc: MIRInvokeKey | undefined, consfuncfields: MIRFieldKey[], fields: MIRFieldDecl[], specialDecls: MIRSpecialTypeCategory[], specialTemplateInfo: {tname: string, tkind: MIRResolvedTypeKey}[] | undefined) {
        super(ooname, srcInfo, srcFile, tkey, attributes, ns, name, terms, provides);

        this.consfunc = consfunc;

        this.consfuncfields = consfuncfields;

        this.fields = fields;

        this.specialDecls = new Set<MIRSpecialTypeCategory>(specialDecls);
        this.specialTemplateInfo = specialTemplateInfo;
    }

    jemit(): object {
        return { isentity: true, ooname: this.ooname, tkey: this.tkey, sinfo: jemitsinfo(this.sourceLocation), file: this.srcFile, attributes: this.attributes, ns: this.ns, name: this.name, terms: [...this.terms].map((t) => [t[0], t[1].jemit()]), provides: this.provides, consfunc: this.consfunc, consfuncfields: this.consfuncfields, fields: this.fields.map((f) => f.jemit()), vcallMap: [...this.vcallMap], specialDecls: [...this.specialDecls], specialTemplateInfo: this.specialTemplateInfo };
    }

    isTypeAListEntity(): boolean {
        return this.specialDecls.has(MIRSpecialTypeCategory.VectorTypeDecl) || this.specialDecls.has(MIRSpecialTypeCategory.ListTypeDecl);
    }

    isTypeAQueueEntity(): boolean {
        return this.specialDecls.has(MIRSpecialTypeCategory.QueueTypeDecl);
    }

    isTypeAStackEntity(): boolean {
        return this.specialDecls.has(MIRSpecialTypeCategory.StackTypeDecl);
    }

    isTypeASetEntity(): boolean {
        return this.specialDecls.has(MIRSpecialTypeCategory.SetTypeDecl) || this.specialDecls.has(MIRSpecialTypeCategory.DynamicSetTypeDecl);
    }

    isTypeAMapEntity(): boolean {
        return this.specialDecls.has(MIRSpecialTypeCategory.MapTypeDecl) || this.specialDecls.has(MIRSpecialTypeCategory.DynamicMapTypeDecl);
    }

    isTypeGrounded(): boolean {
        return this.specialDecls.has(MIRSpecialTypeCategory.GroundedTypeDecl);
    }
}

abstract class MIRTypeOption {
    readonly trkey: MIRResolvedTypeKey;

    constructor(trkey: MIRResolvedTypeKey) {
        this.trkey = trkey;
    }

    abstract jemit(): object;

    static jparse(jobj: any): MIRTypeOption {
        switch (jobj.kind) {
            case "entity":
                return MIREntityType.jparse(jobj);
            case "concept":
                return MIRConceptType.jparse(jobj);
            case "tuple":
                return MIRTupleType.jparse(jobj);
            case "record":
                return MIRRecordType.jparse(jobj);
            case "literal":
                return MIRLiteralType.jparse(jobj);
            default:
                assert(jobj.kind === "ephemeral"); 
                return MIREphemeralListType.jparse(jobj);
        }
    }
}

class MIREntityType extends MIRTypeOption {
    private constructor(ekey: MIRResolvedTypeKey) {
        super(ekey);
    }

    static create(ekey: MIRResolvedTypeKey): MIREntityType {
        return new MIREntityType(ekey);
    }

    jemit(): object {
        return {kind: "entity", ekey: this.trkey };
    }

    static jparse(jobj: any): MIREntityType {
        return MIREntityType.create(jobj.ekey);
    }
}

class MIRConceptType extends MIRTypeOption {
    readonly ckeys: MIRResolvedTypeKey[];

    private constructor(trkey: MIRResolvedTypeKey, ckeys: MIRResolvedTypeKey[]) {
        super(trkey);
        this.ckeys = ckeys;
    }

    static create(ckeys: MIRResolvedTypeKey[]): MIRConceptType {
        const skeys = ckeys.sort();
        return new MIRConceptType(skeys.join(" & "), skeys);
    }

    jemit(): object {
        return {kind: "concept", ckeys: this.ckeys };
    }

    static jparse(jobj: any): MIRConceptType {
        return MIRConceptType.create(jobj.ckeys);
    }
}

class MIRTupleTypeEntry {
    readonly type: MIRType;
    readonly isOptional: boolean;

    constructor(type: MIRType, isOpt: boolean) {
        this.isOptional = isOpt;
        this.type = type;
    }

    jemit(): object {
        return { type: this.type.jemit(), isOptional: this.isOptional };
    }

    static jparse(jobj: any): MIRTupleTypeEntry {
        return new MIRTupleTypeEntry(MIRType.jparse(jobj.type), jobj.isOptional);
    }
}

class MIRTupleType extends MIRTypeOption {
    readonly isvalue: boolean;
    readonly grounded: boolean;
    readonly entries: MIRTupleTypeEntry[];

    private constructor(trkey: MIRResolvedTypeKey, isvalue: boolean, isgrounded: boolean, entries: MIRTupleTypeEntry[]) {
        super(trkey);
        this.isvalue = isvalue;
        this.grounded = isgrounded;
        this.entries = entries;
    }

    static create(isvalue: boolean, isgrounded: boolean, entries: MIRTupleTypeEntry[]): MIRTupleType {
        let cvalue = entries.map((entry) => (entry.isOptional ? "?:" : "") + entry.type.trkey).join(", ");
        let vvalue = isvalue ? "#" : "@";
        return new MIRTupleType(vvalue + "[" + cvalue + "]", isvalue, isgrounded, [...entries]);
    }

    jemit(): object {
        return { kind: "tuple", isvalue: this.isvalue, isgrounded: this.grounded, entries: this.entries.map((e) => e.jemit()) };
    }

    static jparse(jobj: any): MIRTupleType {
        return MIRTupleType.create(jobj.isvalue, jobj.isgrounded, jobj.entries.map((e: any) => MIRTupleTypeEntry.jparse(e)));
    }
}

class MIRRecordTypeEntry {
    readonly name: string;
    readonly type: MIRType;
    readonly isOptional: boolean;

    constructor(name: string, type: MIRType, isOpt: boolean) {
        this.name = name;
        this.type = type;
        this.isOptional = isOpt;
    }

    jemit(): object {
        return { name: this.name, type: this.type.jemit(), isOptional: this.isOptional };
    }

    static jparse(jobj: any): MIRRecordTypeEntry {
        return new MIRRecordTypeEntry(jobj.name, MIRType.jparse(jobj.type), jobj.isOptional);
    }
}

class MIRRecordType extends MIRTypeOption {
    readonly isvalue: boolean;
    readonly grounded: boolean;
    readonly entries: MIRRecordTypeEntry[];

    constructor(rstr: string, isvalue: boolean, isgrounded: boolean, entries: MIRRecordTypeEntry[]) {
        super(rstr);
        this.isvalue = isvalue;
        this.grounded = isgrounded;
        this.entries = entries;
    }

    static create(isvalue: boolean, isgrounded: boolean, entries: MIRRecordTypeEntry[]): MIRRecordType {
        const rentries = [...entries].sort((a, b) => a.name.localeCompare(b.name));

        let cvalue = rentries.map((entry) => entry.name + (entry.isOptional ? "?:" : ":") + entry.type.trkey).join(", ");
        let vvalue = isvalue ? "#" : "@";
        return new MIRRecordType(vvalue + "{" + cvalue + "}", isvalue, isgrounded, rentries);
    }

    jemit(): object {
        return { kind: "record", isvalue: this.isvalue, isgrounded: this.grounded, entries: this.entries.map((e) => e.jemit()) };
    }

    static jparse(jobj: any): MIRRecordType {
        return MIRRecordType.create(jobj.isvalue, jobj.isgrounded, jobj.entries.map((e: any) => MIRRecordTypeEntry.jparse(e)));
    }
}

class MIRLiteralType extends MIRTypeOption {
    readonly primitiveValue: boolean | number | undefined;

    private constructor(ekey: MIRResolvedTypeKey, primitiveValue: boolean | number | undefined) {
        super(ekey);

        this.primitiveValue = primitiveValue;
    }

    static create(ekey: MIRResolvedTypeKey, primitiveValue: boolean | number | undefined): MIRLiteralType {
        return new MIRLiteralType(ekey, primitiveValue);
    }

    jemit(): object {
        return {kind: "literal", ekey: this.trkey, primitiveValue: this.primitiveValue };
    }

    static jparse(jobj: any): MIREntityType {
        return MIRLiteralType.create(jobj.ekey, jobj.primitiveValue);
    }
}

class MIREphemeralListType extends MIRTypeOption {
    readonly entries: MIRType[];

    private constructor(trkey: MIRResolvedTypeKey, entries: MIRType[]) {
        super(trkey);
        this.entries = entries;
    }

    static create(entries: MIRType[]): MIREphemeralListType {
        let cvalue = entries.map((entry) => entry.trkey).join(", ");
        return new MIREphemeralListType("(|" + cvalue + "|)", [...entries]);
    }

    jemit(): object {
        return { kind: "ephemeral", entries: this.entries.map((e) => e.jemit()) };
    }

    static jparse(jobj: any): MIREphemeralListType {
        return MIREphemeralListType.create(jobj.entries.map((e: any) => MIRType.jparse(e)));
    }
}

class MIRType {
    readonly trkey: MIRResolvedTypeKey;
    readonly options: MIRTypeOption[];

    private constructor(trkey: MIRResolvedTypeKey, options: MIRTypeOption[]) {
        this.trkey = trkey;
        this.options = options;
    }

    static createSingle(option: MIRTypeOption): MIRType {
        return new MIRType(option.trkey, [option]);
    }

    static create(options: MIRTypeOption[]): MIRType {
        if (options.length === 1) {
            return MIRType.createSingle(options[0]);
        }
        else {
            const trkey = [...options].sort().map((tk) => tk.trkey).join(" | ");
            return new MIRType(trkey, options);
        }
    }

    jemit(): object {
        return { options: this.options.map((opt) => opt.jemit()) };
    }

    static jparse(jobj: any): MIRType {
        return MIRType.create(jobj.options.map((opt: any) => MIRTypeOption.jparse(opt)));
    }
}

class PackageConfig {
    //TODO: package.config data

    jemit(): object {
        return { };
    }

    static jparse(jobj: any): PackageConfig {
        return new PackageConfig();
    }
}

class MIRAssembly {
    readonly package: PackageConfig;
    readonly srcFiles: { relativePath: string, contents: string }[];
    readonly srcHash: string;

    readonly literalRegexs: BSQRegex[] = [];
    readonly validatorRegexs: Map<MIRResolvedTypeKey, BSQRegex> = new Map<MIRResolvedTypeKey, BSQRegex>();

    readonly constantDecls: Map<MIRGlobalKey, MIRConstantDecl> = new Map<MIRGlobalKey, MIRConstantDecl>();
    readonly fieldDecls: Map<MIRFieldKey, MIRFieldDecl> = new Map<MIRFieldKey, MIRFieldDecl>();

    readonly invokeDecls: Map<MIRInvokeKey, MIRInvokeBodyDecl> = new Map<MIRInvokeKey, MIRInvokeBodyDecl>();
    readonly primitiveInvokeDecls: Map<MIRInvokeKey, MIRInvokePrimitiveDecl> = new Map<MIRInvokeKey, MIRInvokePrimitiveDecl>();
    readonly virtualOperatorDecls: Map<MIRVirtualMethodKey, MIRInvokeKey[]> = new Map<MIRVirtualMethodKey, MIRInvokeKey[]>();

    readonly conceptDecls: Map<MIRResolvedTypeKey, MIRConceptTypeDecl> = new Map<MIRResolvedTypeKey, MIRConceptTypeDecl>();
    readonly entityDecls: Map<MIRResolvedTypeKey, MIREntityTypeDecl> = new Map<MIRResolvedTypeKey, MIREntityTypeDecl>();

    readonly tupleDecls: Map<MIRResolvedTypeKey, MIRTupleType> = new Map<MIRResolvedTypeKey, MIRTupleType>();
    readonly recordDecls: Map<MIRResolvedTypeKey, MIRRecordType> = new Map<MIRResolvedTypeKey, MIRRecordType>();

    readonly ephemeralListDecls: Map<MIRResolvedTypeKey, MIREphemeralListType> = new Map<MIRResolvedTypeKey, MIREphemeralListType>();

    readonly literalTypes: Map<MIRResolvedTypeKey, MIRLiteralType> = new Map<MIRResolvedTypeKey, MIRLiteralType>();

    readonly typeMap: Map<MIRResolvedTypeKey, MIRType> = new Map<MIRResolvedTypeKey, MIRType>();

    private m_subtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();
    private m_atomSubtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();

    private atomSubtypeOf_EntityConcept(t1: MIREntityType, t2: MIRConceptType): boolean {
        const t1e = this.entityDecls.get(t1.trkey) as MIREntityTypeDecl;
        const mcc = MIRType.createSingle(t2);
        return t1e.provides.some((provide) => this.subtypeOf(this.typeMap.get(provide) as MIRType, mcc));
    }

    private atomSubtypeOf_ConceptConcept(t1: MIRConceptType, t2: MIRConceptType): boolean {
        return t2.ckeys.every((c2t) => {
            return t1.ckeys.some((c1t) => {
                const c1 = this.conceptDecls.get(c1t) as MIRConceptTypeDecl;
                const c2 = this.conceptDecls.get(c2t) as MIRConceptTypeDecl;

                if (c1.ns === c2.ns && c1.name === c2.name) {
                    return true;
                }

                return c1.provides.some((provide) => this.subtypeOf(this.typeMap.get(provide) as MIRType, this.typeMap.get(c2t) as MIRType));
            });
        });
    }

    private checkAllTupleEntriesOfType(t1: MIRTupleType, t2: MIRType): boolean {
        return t1.entries.every((entry) => this.subtypeOf(entry.type, t2));
    }

    private getConceptsProvidedByTuple(tt: MIRTupleType): MIRType {
        let tci: MIRResolvedTypeKey[] = ["NSCore::Some"];
        if (tt.grounded) {
            if (tt.isvalue && this.checkAllTupleEntriesOfType(tt, this.typeMap.get("NSCore::KeyType") as MIRType)) {
                tci.push("NSCore::KeyType");
            }
            if (this.checkAllTupleEntriesOfType(tt, this.typeMap.get("NSCore::APIType") as MIRType)) {
                if (this.checkAllTupleEntriesOfType(tt, this.typeMap.get("NSCore::PODType") as MIRType)) {
                    tci.push("NSCore::APIType");
                }
                else {
                    tci.push("NSCore::PODType");
                }
            }
        }

        return MIRType.createSingle(MIRConceptType.create(tci));
    }

    private atomSubtypeOf_TupleConcept(t1: MIRTupleType, t2: MIRConceptType): boolean {
        const t2type = this.typeMap.get(t2.trkey) as MIRType;
        const tcitype = this.getConceptsProvidedByTuple(t1);
        return this.subtypeOf(tcitype, t2type);
    }

    private atomSubtypeOf_TupleTuple(t1: MIRTupleType, t2: MIRTupleType): boolean {
        if(t1.isvalue !== t2.isvalue) {
            return false;
        }

       for (let i = 0; i < t1.entries.length; ++i) {
            const t1e = t1.entries[i];

           if (i >= t2.entries.length) {
               return false;
           }
           else {
               const t2e = t2.entries[i];
               if ((t1e.isOptional && !t2e.isOptional) || t1e.type.trkey !== t2e.type.trkey) {
                   return false;
               }
            }
        }

        //t2 has a required entry that is not required in t1
        if (t2.entries.length > t1.entries.length && t2.entries.slice(t1.entries.length).some((entry) => !entry.isOptional)) {
            return false;
        }

        return true;
    }

    private checkAllRecordEntriesOfType(t1: MIRRecordType, t2: MIRType): boolean {
        return t1.entries.every((entry) => this.subtypeOf(entry.type, t2));
    }

    private getConceptsProvidedByRecord(tt: MIRRecordType): MIRType {
        let tci: MIRResolvedTypeKey[] = ["NSCore::Some"];
        if (tt.grounded) {
            if (tt.isvalue && this.checkAllRecordEntriesOfType(tt, this.typeMap.get("NSCore::KeyType") as MIRType)) {
                tci.push("NSCore::KeyType");
            }
            if (this.checkAllRecordEntriesOfType(tt, this.typeMap.get("NSCore::APIType") as MIRType)) {
                if (this.checkAllRecordEntriesOfType(tt, this.typeMap.get("NSCore::PODType") as MIRType)) {
                    tci.push("NSCore::APIType");
                }
                else {
                    tci.push("NSCore::PODType");
                }
            }
        }

        return MIRType.createSingle(MIRConceptType.create(tci));
    }

    private atomSubtypeOf_RecordConcept(t1: MIRRecordType, t2: MIRConceptType): boolean {
        const t2type = this.typeMap.get(t2.trkey) as MIRType;
        const tcitype = this.getConceptsProvidedByRecord(t1);
        return this.subtypeOf(tcitype, t2type);
    }

    private atomSubtypeOf_RecordRecord(t1: MIRRecordType, t2: MIRRecordType): boolean {
        if(t1.isvalue !== t2.isvalue) {
            return false;
        }

        let badEntry = false;
        t1.entries.forEach((entry) => {
            const t2e = t2.entries.find((e) => e.name === entry.name);
            if (t2e === undefined) {
                badEntry = badEntry || true;
            }
            else {
                if ((entry.isOptional && !t2e.isOptional) || entry.type.trkey !== t2e.type.trkey) {
                    badEntry = badEntry || true;
                }
            }
        });

        t2.entries.forEach((entry) => {
            badEntry = badEntry || (t1.entries.find((e) => e.name === entry.name) === undefined && !entry.isOptional);
        });

        if (badEntry) {
            return false;
        }

        return true;
    }

    private atomSubtypeOf(t1: MIRTypeOption, t2: MIRTypeOption): boolean {
        let memores = this.m_atomSubtypeRelationMemo.get(t1.trkey);
        if (memores === undefined) {
            this.m_atomSubtypeRelationMemo.set(t1.trkey, new Map<string, boolean>());
            memores = this.m_atomSubtypeRelationMemo.get(t1.trkey) as Map<string, boolean>;
        }

        let memoval = memores.get(t2.trkey);
        if (memoval !== undefined) {
            return memoval;
        }

        let res = false;

        if (t1.trkey === t2.trkey) {
            res = true;
        }
        else {
            if (t1 instanceof MIRConceptType && t2 instanceof MIRConceptType) {
                res = this.atomSubtypeOf_ConceptConcept(t1, t2);
            }
            else if (t1 instanceof MIRConceptType) {
                //res stays false
            }
            else if (t2 instanceof MIRConceptType) {
                if (t1 instanceof MIREntityType) {
                    res = this.atomSubtypeOf_EntityConcept(t1, t2);
                }
                else if (t1 instanceof MIRTupleType) {
                    res = this.atomSubtypeOf_TupleConcept(t1, t2);
                }
                else if (t1 instanceof MIRRecordType) {
                    res = this.atomSubtypeOf_RecordConcept(t1, t2);
                }
                else {
                    //fall-through
                }
            }
            else {
                if (t1 instanceof MIRTupleType && t2 instanceof MIRTupleType) {
                    res = this.atomSubtypeOf_TupleTuple(t1, t2);
                }
                else if (t1 instanceof MIRRecordType && t2 instanceof MIRRecordType) {
                    res = this.atomSubtypeOf_RecordRecord(t1, t2);
                }
                else {
                    //fall-through
                }
            }
        }

        memores.set(t2.trkey, res);
        return res;
    }

    constructor(pckge: PackageConfig, srcFiles: { relativePath: string, contents: string }[], srcHash: string) {
        this.package = pckge;
        this.srcFiles = srcFiles;
        this.srcHash = srcHash;
    }

    subtypeOf(t1: MIRType, t2: MIRType): boolean {
        let memores = this.m_subtypeRelationMemo.get(t1.trkey);
        if (memores === undefined) {
            this.m_subtypeRelationMemo.set(t1.trkey, new Map<string, boolean>());
            memores = this.m_subtypeRelationMemo.get(t1.trkey) as Map<string, boolean>;
        }

        let memoval = memores.get(t2.trkey);
        if (memoval !== undefined) {
            return memoval;
        }

        const res = (t1.trkey === t2.trkey) || t1.options.every((t1opt) => t2.options.some((t2opt) => this.atomSubtypeOf(t1opt, t2opt)));

        memores.set(t2.trkey, res);
        return res;
    }

    jemit(): object {
        return {
            package: this.package.jemit(),
            srcFiles: this.srcFiles,
            srcHash: this.srcHash,
            literalRegexs: [...this.literalRegexs].map((lre) => lre.jemit()),
            validatorRegexs: [...this.validatorRegexs].map((vre) => [vre[0], vre[1]]),
            constantDecls: [...this.constantDecls].map((cd) => [cd[0], cd[1].jemit()]),
            fieldDecls: [...this.fieldDecls].map((fd) => [fd[0], fd[1].jemit()]),
            invokeDecls: [...this.invokeDecls].map((id) => [id[0], id[1].jemit()]),
            primitiveInvokeDecls: [...this.primitiveInvokeDecls].map((id) => [id[0], id[1].jemit()]),
            virtualOperatorDecls: [...this.virtualOperatorDecls],
            conceptDecls: [...this.conceptDecls].map((cd) => [cd[0], cd[1].jemit()]),
            entityDecls: [...this.entityDecls].map((ed) => [ed[0], ed[1].jemit()]),
            literalTypes: [...this.literalTypes].map((lt) => [lt[0], lt[1].jemit()]),
            typeMap: [...this.typeMap].map((t) => [t[0], t[1].jemit()])
        };
    }

    static jparse(jobj: any): MIRAssembly {
        let masm = new MIRAssembly(PackageConfig.jparse(jobj.package), jobj.srcFiles, jobj.srcHash);

        jobj.literalRegexs.forEach((lre: any) => masm.literalRegexs.push(BSQRegex.jparse(lre)));
        jobj.validatorRegexs.forEach((vre: any) => masm.validatorRegexs.set(vre[0], vre[1]));
        jobj.constantDecls.forEach((cd: any) => masm.constantDecls.set(cd[0], MIRConstantDecl.jparse(cd[1])));
        jobj.fieldDecls.forEach((fd: any) => masm.fieldDecls.set(fd[0], MIRFieldDecl.jparse(fd[1])));
        jobj.invokeDecls.forEach((id: any) => masm.invokeDecls.set(id[0], MIRInvokeDecl.jparse(id[1]) as MIRInvokeBodyDecl));
        jobj.primitiveInvokeDecls.forEach((id: any) => masm.primitiveInvokeDecls.set(id[0], MIRInvokeDecl.jparse(id[1]) as MIRInvokePrimitiveDecl));
        jobj.virtualOperatorDecls.forEach((od: any) => masm.virtualOperatorDecls.set(od[0], od[1]));
        jobj.conceptDecls.forEach((cd: any) => masm.conceptDecls.set(cd[0], MIROOTypeDecl.jparse(cd[1]) as MIRConceptTypeDecl));
        jobj.entityDecls.forEach((id: any) => masm.entityDecls.set(id[0], MIROOTypeDecl.jparse(id[1]) as MIREntityTypeDecl));
        jobj.literalTypes.forEach((lt: any) => masm.literalTypes.set(lt[0], MIRLiteralType.jparse(lt[1]) as MIRLiteralType));
        jobj.typeMap.forEach((t: any) => masm.typeMap.set(t[0], MIRType.jparse(t[1])));

        return masm;
    }
}

export {
    MIRConstantDecl, MIRFunctionParameter, MIRInvokeDecl, MIRInvokeBodyDecl, MIRPCode, MIRInvokePrimitiveDecl, MIRFieldDecl,
    MIROOTypeDecl, MIRConceptTypeDecl, MIREntityTypeDecl,
    MIRType, MIRTypeOption, MIRSpecialTypeCategory, MIREntityType, MIRConceptType, MIRTupleTypeEntry, MIRTupleType, MIRRecordTypeEntry, MIRRecordType, MIRLiteralType, MIREphemeralListType,
    PackageConfig, MIRAssembly
};
