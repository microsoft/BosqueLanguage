//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo } from "../ast/parser";
import { MIRBody, MIRResolvedTypeKey, MIRConstantKey, MIRFieldKey, MIRInvokeKey, MIRVirtualMethodKey, MIRNominalTypeKey } from "./mir_ops";
import assert = require("assert");

//
//Probably want to declare a MIRSourceInfo class
//
function jemitsinfo(sinfo: SourceInfo): object {
    return { line: sinfo.line, column: sinfo.column, pos: sinfo.pos, span: sinfo.span };
}

function jparsesinfo(jobj: any): SourceInfo {
    return new SourceInfo(jobj.line, jobj.column, jobj.pos, jobj.span);
}

function jemitpragmas(pragmas: [MIRType, string][]): object {
    return pragmas.map((p) => [p[0].jemit(), p[1]]);
}

function jparsepragmas(jobj: any): [MIRType, string][] {
    return jobj.map((p: any) => [MIRType.jparse(p[0]), p[1]]);
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
    readonly enclosingDecl: MIRNominalTypeKey | undefined;
    readonly cname: string;
    readonly key: MIRConstantKey;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly pragmas: [MIRType, string][];

    readonly declaredType: MIRResolvedTypeKey;
    readonly value: MIRBody;

    constructor(enclosingDecl: MIRNominalTypeKey | undefined, cname: string, key: MIRConstantKey, pragmas: [MIRType, string][], sinfo: SourceInfo, srcFile: string, declaredType: MIRResolvedTypeKey, value: MIRBody) {
        this.enclosingDecl = enclosingDecl;
        this.cname = cname;
        this.key = key;
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

        this.pragmas = pragmas;

        this.declaredType = declaredType;
        this.value = value;
    }

    jemit(): object {
        return { enclosingDecl: this.enclosingDecl, cname: this.cname, key: this.key, sinfo: jemitsinfo(this.sourceLocation), file: this.srcFile, pragmas: jemitpragmas(this.pragmas), declaredType: this.declaredType, value: this.value.jemit() };
    }

    static jparse(jobj: any): MIRConstantDecl {
        return new MIRConstantDecl(jobj.enclosingDecl, jobj.cname, jobj.key, jparsepragmas(jobj.pragmas), jparsesinfo(jobj.sinfo), jobj.file, jobj.declaredType, MIRBody.jparse(jobj.value));
    }
}

abstract class MIRInvokeDecl {
    readonly enclosingDecl: MIRNominalTypeKey | undefined;
    readonly iname: string;
    readonly key: MIRInvokeKey;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly recursive: boolean;
    readonly pragmas: [MIRType, string][];

    readonly params: MIRFunctionParameter[];
    readonly resultType: MIRResolvedTypeKey;

    readonly preconditions: [MIRBody, boolean][];
    readonly postconditions: MIRBody[];

    constructor(enclosingDecl: MIRNominalTypeKey | undefined, iname: string, key: MIRInvokeKey, attributes: string[], recursive: boolean, pragmas: [MIRType, string][], sinfo: SourceInfo, srcFile: string, params: MIRFunctionParameter[], resultType: MIRResolvedTypeKey, preconds: [MIRBody, boolean][], postconds: MIRBody[]) {
        this.enclosingDecl = enclosingDecl;
        this.iname = iname;
        this.key = key;

        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

        this.attributes = attributes;
        this.recursive = recursive;
        this.pragmas = pragmas;

        this.params = params;
        this.resultType = resultType;

        this.preconditions = preconds;
        this.postconditions = postconds;

    }

    abstract jemit(): object;

    static jparse(jobj: any): MIRInvokeDecl {
        if (jobj.body) {
            return new MIRInvokeBodyDecl(jobj.enclosingDecl, jobj.iname, jobj.key, jobj.attributes, jobj.recursive, jparsepragmas(jobj.pragmas), jparsesinfo(jobj.sinfo), jobj.file, jobj.params.map((p: any) => MIRFunctionParameter.jparse(p)), jobj.resultType, jobj.preconditions.map((pre: any) => [MIRBody.jparse(pre[0]), pre[1]]), jobj.postconditions.map((post: any) => MIRBody.jparse(post)), MIRBody.jparse(jobj.body));
        }
        else {
            let binds = new Map<string, MIRResolvedTypeKey>();
            jobj.binds.forEach((bind: any) => binds.set(bind[0], bind[1]));

            let pcodes = new Map<string, MIRPCode>();
            jobj.pcodes.forEach((pc: any) => pcodes.set(pc[0], pc[1]));

            return new MIRInvokePrimitiveDecl(jobj.enclosingDecl, jobj.iname, jobj.key, jobj.attributes, jobj.recursive, jparsepragmas(jobj.pragmas), jparsesinfo(jobj.sinfo), jobj.file, binds, jobj.params.map((p: any) => MIRFunctionParameter.jparse(p)), jobj.resultType, jobj.preconditions.map((pre: any) => [MIRBody.jparse(pre[0]), pre[1]]), jobj.postconditions.map((post: any) => MIRBody.jparse(post)), jobj.implkey, pcodes);
        }
    }
}

class MIRInvokeBodyDecl extends MIRInvokeDecl {
    readonly body: MIRBody;

    constructor(enclosingDecl: MIRNominalTypeKey | undefined, iname: string, key: MIRInvokeKey, attributes: string[], recursive: boolean, pragmas: [MIRType, string][], sinfo: SourceInfo, srcFile: string, params: MIRFunctionParameter[], resultType: MIRResolvedTypeKey, preconds: [MIRBody, boolean][], postconds: MIRBody[], body: MIRBody) {
        super(enclosingDecl, iname, key, attributes, recursive, pragmas, sinfo, srcFile, params, resultType, preconds, postconds);

        this.body = body;
    }

    jemit(): object {
        return { enclosingDecl: this.enclosingDecl, iname: this.iname, key: this.key, sinfo: jemitsinfo(this.sourceLocation), file: this.srcFile, attributes: this.attributes, recursive: this.recursive, pragmas: jemitpragmas(this.pragmas), params: this.params.map((p) => p.jemit()), resultType: this.resultType, preconditions: this.preconditions.map((pre) => [pre[0].jemit(), pre[1]]), postconditions: this.postconditions.map((post) => post.jemit()), body: this.body.jemit() };
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

    constructor(enclosingDecl: MIRNominalTypeKey | undefined, iname: string, key: MIRInvokeKey, attributes: string[], recursive: boolean, pragmas: [MIRType, string][], sinfo: SourceInfo, srcFile: string, binds: Map<string, MIRResolvedTypeKey>, params: MIRFunctionParameter[], resultType: MIRResolvedTypeKey, preconds: [MIRBody, boolean][], postconds: MIRBody[], implkey: string, pcodes: Map<string, MIRPCode>) {
        super(enclosingDecl, iname, key, attributes, recursive, pragmas, sinfo, srcFile, params, resultType, preconds, postconds);

        this.implkey = implkey;
        this.binds = binds;
        this.pcodes = pcodes;
    }

    jemit(): object {
        return {enclosingDecl: this.enclosingDecl, iname: this.iname, key: this.key, sinfo: jemitsinfo(this.sourceLocation), file: this.srcFile, attributes: this.attributes, recursive: this.recursive, pragmas: jemitpragmas(this.pragmas), params: this.params.map((p) => p.jemit()), resultType: this.resultType, preconditions: this.preconditions.map((pre) => [pre[0].jemit(), pre[1]]), postconditions: this.postconditions.map((post) => post.jemit()), implkey: this.implkey, binds: [...this.binds], pcodes: [... this.pcodes] };
    }
}

class MIRFieldDecl {
    readonly enclosingDecl: MIRNominalTypeKey;
    readonly attributes: string[];

    readonly fname: string;
    readonly fkey: MIRFieldKey;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly pragmas: [MIRType, string][];

    readonly name: string;

    readonly declaredType: MIRResolvedTypeKey;
    readonly value: MIRBody | undefined;

    constructor(enclosingDecl: MIRNominalTypeKey, attributes: string[], fname: string, srcInfo: SourceInfo, srcFile: string, fkey: MIRFieldKey, pragmas: [MIRType, string][], name: string, dtype: MIRResolvedTypeKey, value: MIRBody | undefined) {
        this.enclosingDecl = enclosingDecl;
        this.attributes = attributes;

        this.fname = fname;
        this.fkey = fkey;

        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;

        this.pragmas = pragmas;

        this.name = name;
        this.declaredType = dtype;
        this.value = value;
    }

    jemit(): object {
        return { enclosingDecl: this.enclosingDecl, attributes: this.attributes, fname: this.fname, fkey: this.fkey, sinfo: jemitsinfo(this.sourceLocation), file: this.srcFile, pragmas: jemitpragmas(this.pragmas), name: this.name, declaredType: this.declaredType, value: this.value ? this.value.jemit() : null };
    }

    static jparse(jobj: any): MIRFieldDecl {
        return new MIRFieldDecl(jobj.enclosingDecl, jobj.attributes, jobj.fname, jparsesinfo(jobj.sinfo), jobj.file, jobj.fkey, jparsepragmas(jobj.pragmas), jobj.name, jobj.declaredType, jobj.value ? MIRBody.jparse(jobj.value) : undefined);
    }
}

abstract class MIROOTypeDecl {
    readonly ooname: string;
    readonly tkey: MIRNominalTypeKey;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly pragmas: [MIRType, string][];

    readonly ns: string;
    readonly name: string;
    readonly terms: Map<string, MIRType>;
    readonly provides: MIRNominalTypeKey[];

    readonly invariants: MIRBody[] = [];
    readonly fields: MIRFieldDecl[] = [];
    readonly vcallMap: Map<MIRVirtualMethodKey, MIRInvokeKey> = new Map<string, MIRInvokeKey>();

    constructor(ooname: string, srcInfo: SourceInfo, srcFile: string, tkey: MIRNominalTypeKey, attributes: string[], pragmas: [MIRType, string][], ns: string, name: string, terms: Map<string, MIRType>, provides: MIRNominalTypeKey[], invariants: MIRBody[], fields: MIRFieldDecl[]) {
        this.ooname = ooname;
        this.tkey = tkey;

        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;

        this.attributes = attributes;
        this.pragmas = pragmas;

        this.ns = ns;
        this.name = name;
        this.terms = terms;
        this.provides = provides;

        this.invariants = invariants;
        this.fields = fields;
    }

    abstract jemit(): object;

    static jparse(jobj: any): MIROOTypeDecl {
        let terms = new Map<string, MIRType>();
            jobj.terms.forEach((t: any) => terms.set(t[0], MIRType.jparse(t[1])));

        if (jobj.isentity) {
            const entity = new MIREntityTypeDecl(jobj.ooname, jparsesinfo(jobj.sinfo), jobj.file, jobj.tkey, jobj.attributes, jparsepragmas(jobj.pragmas), jobj.ns, jobj.name, terms, jobj.provides, jobj.invariants.map((i: any) => MIRBody.jparse(i)), jobj.fields.map((f: any) => MIRFieldDecl.jparse(f)), jobj.isCollectionEntityType, jobj.isMapEntityType, jobj.isEnum, jobj.isKey);
            jobj.vcallMap.forEach((vc: any) => entity.vcallMap.set(vc[0], vc[1]));
            return entity;
        }
        else {
            const concept = new MIRConceptTypeDecl(jobj.ooname, jparsesinfo(jobj.sinfo), jobj.file, jobj.tkey, jobj.attributes, jparsepragmas(jobj.pragmas), jobj.ns, jobj.name, terms, jobj.provides, jobj.invariants.map((i: any) => MIRBody.jparse(i)), jobj.fields.map((f: any) => MIRFieldDecl.jparse(f)));
            jobj.vcallMap.forEach((vc: any) => concept.vcallMap.set(vc[0], vc[1]));
            return concept;
        }
    }
}

class MIRConceptTypeDecl extends MIROOTypeDecl {
    constructor(ooname: string, srcInfo: SourceInfo, srcFile: string, tkey: MIRNominalTypeKey, attributes: string[], pragmas: [MIRType, string][], ns: string, name: string, terms: Map<string, MIRType>, provides: MIRNominalTypeKey[], invariants: MIRBody[], fields: MIRFieldDecl[]) {
        super(ooname, srcInfo, srcFile, tkey, attributes, pragmas, ns, name, terms, provides, invariants, fields);
    }

    jemit(): object {
        return { isentity: false, ooname: this.ooname, tkey: this.tkey, sinfo: jemitsinfo(this.sourceLocation), file: this.srcFile, attributes: this.attributes, pragmas: jemitpragmas(this.pragmas), ns: this.ns, name: this.name, terms: [...this.terms].map((t) => [t[0], t[1].jemit()]), provides: this.provides, invariants: this.invariants.map((i) => i.jemit()), fields: this.fields.map((f) => f.jemit()), vcallMap: [...this.vcallMap] };
    }
}

class MIREntityTypeDecl extends MIROOTypeDecl {
    readonly isEnum: boolean;
    readonly isKey: boolean;

    readonly isCollectionEntityType: boolean;
    readonly isMapEntityType: boolean;

    constructor(ooname: string, srcInfo: SourceInfo, srcFile: string, tkey: MIRNominalTypeKey, attributes: string[], pragmas: [MIRType, string][], ns: string, name: string, terms: Map<string, MIRType>, provides: MIRNominalTypeKey[], invariants: MIRBody[], fields: MIRFieldDecl[], isCollectionEntityType: boolean, isMapEntityType: boolean, isEnum: boolean, isKey: boolean) {
        super(ooname, srcInfo, srcFile, tkey, attributes, pragmas, ns, name, terms, provides, invariants, fields);

        this.isEnum = isEnum;
        this.isKey = isKey;

        this.isCollectionEntityType = isCollectionEntityType;
        this.isMapEntityType = isMapEntityType;
    }

    jemit(): object {
        return { isentity: true, ooname: this.ooname, tkey: this.tkey, sinfo: jemitsinfo(this.sourceLocation), file: this.srcFile, attributes: this.attributes, pragmas: jemitpragmas(this.pragmas), ns: this.ns, name: this.name, terms: [...this.terms].map((t) => [t[0], t[1].jemit()]), provides: this.provides, invariants: this.invariants.map((i) => i.jemit()), fields: this.fields.map((f) => f.jemit()), vcallMap: [...this.vcallMap], isEnum: this.isEnum, isKey: this.isKey, isCollectionEntityType: this.isCollectionEntityType, isMapEntityType: this.isMapEntityType };
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
            default:
                assert(jobj.kind === "record");
                return MIRRecordType.jparse(jobj);
        }
    }
}

abstract class MIRNominalType extends MIRTypeOption {
    constructor(trkey: MIRResolvedTypeKey) {
        super(trkey);
    }
}

class MIREntityType extends MIRNominalType {
    readonly ekey: MIRNominalTypeKey;

    private constructor(ekey: MIRNominalTypeKey) {
        super(ekey);
        this.ekey = ekey;
    }

    static create(ekey: MIRNominalTypeKey): MIREntityType {
        return new MIREntityType(ekey);
    }

    jemit(): object {
        return {kind: "entity", ekey: this.ekey };
    }

    static jparse(jobj: any): MIREntityType {
        return MIREntityType.create(jobj.ekey);
    }
}

class MIRConceptType extends MIRNominalType {
    readonly ckeys: MIRNominalTypeKey[];

    private constructor(trkey: MIRResolvedTypeKey, ckeys: MIRNominalTypeKey[]) {
        super(trkey);
        this.ckeys = ckeys;
    }

    static create(ckeys: MIRNominalTypeKey[]): MIRConceptType {
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

abstract class MIRStructuralType extends MIRTypeOption {
    constructor(trkey: MIRResolvedTypeKey) {
        super(trkey);
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

class MIRTupleType extends MIRStructuralType {
    readonly entries: MIRTupleTypeEntry[];

    private constructor(trkey: MIRResolvedTypeKey, entries: MIRTupleTypeEntry[]) {
        super(trkey);
        this.entries = entries;
    }

    static create(entries: MIRTupleTypeEntry[]): MIRTupleType {
        let cvalue = entries.map((entry) => (entry.isOptional ? "?:" : "") + entry.type.trkey).join(", ");
        return new MIRTupleType("[" + cvalue + "]", [...entries]);
    }

    jemit(): object {
        return { kind: "tuple", entries: this.entries.map((e) => e.jemit()) };
    }

    static jparse(jobj: any): MIRTupleType {
        return MIRTupleType.create(jobj.entries.map((e: any) => MIRTupleTypeEntry.jparse(e)));
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

class MIRRecordType extends MIRStructuralType {
    readonly entries: MIRRecordTypeEntry[];

    constructor(rstr: string, entries: MIRRecordTypeEntry[]) {
        super(rstr);
        this.entries = entries;
    }

    static create(entries: MIRRecordTypeEntry[]): MIRRecordType {
        const rentries = [...entries].sort((a, b) => a.name.localeCompare(b.name));

        let cvalue = rentries.map((entry) => entry.name + (entry.isOptional ? "?:" : ":") + entry.type.trkey).join(", ");
        return new MIRRecordType("{" + cvalue + "}", rentries);
    }

    jemit(): object {
        return { kind: "record", entries: this.entries.map((e) => e.jemit()) };
    }

    static jparse(jobj: any): MIRRecordType {
        return MIRRecordType.create(jobj.entries.map((e: any) => MIRRecordTypeEntry.jparse(e)));
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

    readonly constantDecls: Map<MIRConstantKey, MIRConstantDecl> = new Map<MIRConstantKey, MIRConstantDecl>();
    readonly fieldDecls: Map<MIRFieldKey, MIRFieldDecl> = new Map<MIRFieldKey, MIRFieldDecl>();

    readonly entryPoints: MIRInvokeKey[] = [];
    readonly invokeDecls: Map<MIRInvokeKey, MIRInvokeBodyDecl> = new Map<MIRInvokeKey, MIRInvokeBodyDecl>();
    readonly primitiveInvokeDecls: Map<MIRInvokeKey, MIRInvokePrimitiveDecl> = new Map<MIRInvokeKey, MIRInvokePrimitiveDecl>();

    readonly conceptDecls: Map<MIRNominalTypeKey, MIRConceptTypeDecl> = new Map<MIRNominalTypeKey, MIRConceptTypeDecl>();
    readonly entityDecls: Map<MIRNominalTypeKey, MIREntityTypeDecl> = new Map<MIRNominalTypeKey, MIREntityTypeDecl>();

    readonly typeMap: Map<MIRResolvedTypeKey, MIRType> = new Map<MIRResolvedTypeKey, MIRType>();

    private m_subtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();
    private m_atomSubtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();

    private atomSubtypeOf_EntityEntity(t1: MIREntityType, t2: MIREntityType): boolean {
        const t1e = this.entityDecls.get(t1.ekey) as MIREntityTypeDecl;
        const t2e = this.entityDecls.get(t2.ekey) as MIREntityTypeDecl;
        return (t1e.ns === t2e.ns && t1e.name === t2e.name);
    }

    private atomSubtypeOf_EntityConcept(t1: MIREntityType, t2: MIRConceptType): boolean {
        const t1e = this.entityDecls.get(t1.ekey) as MIREntityTypeDecl;
        const mcc = MIRType.createSingle(t2);
        return t1e.provides.some((provide) => this.subtypeOf(this.typeMap.get(provide) as MIRType, mcc));
    }

    private atomSubtypeOf_ConceptConcept(t1: MIRConceptType, t2: MIRConceptType): boolean {
        return t1.ckeys.every((c1t) => {
            return t2.ckeys.some((c2t) => {
                const c1 = this.conceptDecls.get(c1t) as MIRConceptTypeDecl;
                const c2 = this.conceptDecls.get(c2t) as MIRConceptTypeDecl;

                if (c1.ns === c2.ns && c1.name === c2.name) {
                    return true;
                }

                return c1.provides.some((provide) => this.subtypeOf(this.typeMap.get(provide) as MIRType, this.typeMap.get(c2t) as MIRType));
            });
        });
    }

    private atomSubtypeOf_TupleTuple(t1: MIRTupleType, t2: MIRTupleType): boolean {
        for (let i = 0; i < t1.entries.length; ++i) {
            const t1e = t1.entries[i];

            if (i >= t2.entries.length) {
                return false;
            }
            else {
                const t2e = t2.entries[i];
                if ((t1e.isOptional && !t2e.isOptional) || !this.subtypeOf(t1e.type, t2e.type)) {
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

    private atomSubtypeOf_RecordRecord(t1: MIRRecordType, t2: MIRRecordType): boolean {
        let badEntry = false;
        t1.entries.forEach((entry) => {
            const t2e = t2.entries.find((e) => e.name === entry.name);
            if (t2e === undefined) {
                badEntry = badEntry || true;
            }
            else {
                if ((entry.isOptional && !t2e.isOptional) || !this.subtypeOf(entry.type, t2e.type)) {
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
                    res = this.atomSubtypeOf_ConceptConcept(MIRConceptType.create(["NSCore::Tuple"]), t2);
                }
                else if (t1 instanceof MIRRecordType) {
                    res = this.atomSubtypeOf_ConceptConcept(MIRConceptType.create(["NSCore::Record"]), t2);
                }
                else {
                    res = this.atomSubtypeOf_ConceptConcept(MIRConceptType.create(["NSCore::Function"]), t2);
                }
            }
            else {
                if (t1 instanceof MIREntityType && t2 instanceof MIREntityType) {
                    res = this.atomSubtypeOf_EntityEntity(t1, t2);
                }
                else if (t1 instanceof MIRTupleType && t2 instanceof MIRTupleType) {
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

    registerUnionTypeIfNeeded(options: MIRType[]): MIRType {
        const flatoptions = ([] as MIRTypeOption[]).concat(...options.map((opt) => opt.options));

        //do a simplification based on A | B when A \Subtypeeq B is B
        let simplifiedTypes: MIRTypeOption[] = [];
        for (let i = 0; i < flatoptions.length; ++i) {
            let docopy = true;
            for (let j = 0; j < flatoptions.length; ++j) {
                if (i === j) {
                    continue; //ignore check on same element
                }

                //if \exists a Tj s.t. Ti \Subtypeeq Tj then we discard Ti
                if (this.atomSubtypeOf(flatoptions[i], flatoptions[j])) {
                    docopy = (flatoptions[i].trkey === flatoptions[j].trkey) && i < j; //if same type only keep one copy
                    break;
                }
            }

            if (docopy) {
                simplifiedTypes.push(flatoptions[i]);
            }
        }

        const tt = MIRType.create(simplifiedTypes);
        if (!this.typeMap.has(tt.trkey)) {
            this.typeMap.set(tt.trkey, tt);
        }

        return tt;
    }

    jemit(): object {
        return {
            package: this.package.jemit(),
            srcFiles: this.srcFiles,
            srcHash: this.srcHash,
            constantDecls: [...this.constantDecls].map((cd) => [cd[0], cd[1].jemit()]),
            fieldDecls: [...this.fieldDecls].map((fd) => [fd[0], fd[1].jemit()]),
            entryPoints: this.entryPoints,
            invokeDecls: [...this.invokeDecls].map((id) => [id[0], id[1].jemit()]),
            primitiveInvokeDecls: [...this.primitiveInvokeDecls].map((id) => [id[0], id[1].jemit()]),
            conceptDecls: [...this.conceptDecls].map((cd) => [cd[0], cd[1].jemit()]),
            entityDecls: [...this.entityDecls].map((ed) => [ed[0], ed[1].jemit()]),
            typeMap: [...this.typeMap].map((t) => [t[0], t[1].jemit()])
        };
    }

    static jparse(jobj: any): MIRAssembly {
        let masm = new MIRAssembly(PackageConfig.jparse(jobj.package), jobj.srcFiles, jobj.srcHash);

        jobj.constantDecls.forEach((cd: any) => masm.constantDecls.set(cd[0], MIRConstantDecl.jparse(cd[1])));
        jobj.fieldDecls.forEach((fd: any) => masm.fieldDecls.set(fd[0], MIRFieldDecl.jparse(fd[1])));
        jobj.entryPoints.forEach((ep: any) => masm.entryPoints.push(ep));
        jobj.invokeDecls.forEach((id: any) => masm.invokeDecls.set(id[0], MIRInvokeDecl.jparse(id[1]) as MIRInvokeBodyDecl));
        jobj.primitiveInvokeDecls.forEach((id: any) => masm.primitiveInvokeDecls.set(id[0], MIRInvokeDecl.jparse(id[1]) as MIRInvokePrimitiveDecl));
        jobj.conceptDecls.forEach((cd: any) => masm.conceptDecls.set(cd[0], MIROOTypeDecl.jparse(cd[1]) as MIRConceptTypeDecl));
        jobj.entityDecls.forEach((id: any) => masm.entityDecls.set(id[0], MIROOTypeDecl.jparse(id[1]) as MIREntityTypeDecl));
        jobj.typeMap.forEach((t: any) => masm.typeMap.set(t[0], MIRType.jparse(t[1])));

        return masm;
    }
}

export {
    MIRConstantDecl, MIRFunctionParameter, MIRInvokeDecl, MIRInvokeBodyDecl, MIRPCode, MIRInvokePrimitiveDecl, MIRFieldDecl,
    MIROOTypeDecl, MIRConceptTypeDecl, MIREntityTypeDecl,
    MIRType, MIRTypeOption, MIRNominalType, MIREntityType, MIRConceptType,
    MIRStructuralType, MIRTupleTypeEntry, MIRTupleType, MIRRecordTypeEntry, MIRRecordType,
    PackageConfig, MIRAssembly
};
