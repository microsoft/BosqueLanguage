"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const parser_1 = require("../ast/parser");
const mir_ops_1 = require("./mir_ops");
const assert = require("assert");
//
//Probably want to declare a MIRSourceInfo class
//
function jemitsinfo(sinfo) {
    return { line: sinfo.line, column: sinfo.column, pos: sinfo.pos, span: sinfo.span };
}
function jparsesinfo(jobj) {
    return new parser_1.SourceInfo(jobj.line, jobj.column, jobj.pos, jobj.span);
}
function jemitpragmas(pragmas) {
    return pragmas.map((p) => [p[0].jemit(), p[1]]);
}
function jparsepragmas(jobj) {
    return jobj.map((p) => [MIRType.jparse(p[0]), p[1]]);
}
class MIRFunctionParameter {
    constructor(name, type) {
        this.name = name;
        this.type = type;
    }
    jemit() {
        return { name: this.name, type: this.type };
    }
    static jparse(jobj) {
        return new MIRFunctionParameter(jobj.name, jobj.type);
    }
}
exports.MIRFunctionParameter = MIRFunctionParameter;
class MIRConstantDecl {
    constructor(enclosingDecl, cname, key, pragmas, sinfo, srcFile, declaredType, value) {
        this.enclosingDecl = enclosingDecl;
        this.cname = cname;
        this.key = key;
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;
        this.pragmas = pragmas;
        this.declaredType = declaredType;
        this.value = value;
    }
    jemit() {
        return { enclosingDecl: this.enclosingDecl, cname: this.cname, key: this.key, sinfo: jemitsinfo(this.sourceLocation), file: this.srcFile, pragmas: jemitpragmas(this.pragmas), declaredType: this.declaredType, value: this.value };
    }
    static jparse(jobj) {
        return new MIRConstantDecl(jobj.enclosingDecl, jobj.cname, jobj.key, jparsepragmas(jobj.pragmas), jparsesinfo(jobj.sinfo), jobj.file, jobj.declaredType, jobj.value);
    }
}
exports.MIRConstantDecl = MIRConstantDecl;
class MIRInvokeDecl {
    constructor(enclosingDecl, iname, key, attributes, recursive, pragmas, sinfo, srcFile, params, resultType, preconds, postconds) {
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
    static jparse(jobj) {
        if (jobj.body) {
            return new MIRInvokeBodyDecl(jobj.enclosingDecl, jobj.iname, jobj.key, jobj.attributes, jobj.recursive, jparsepragmas(jobj.pragmas), jparsesinfo(jobj.sinfo), jobj.file, jobj.params.map((p) => MIRFunctionParameter.jparse(p)), jobj.resultType, jobj.preconditions || undefined, jobj.postconditions || undefined, mir_ops_1.MIRBody.jparse(jobj.body));
        }
        else {
            let binds = new Map();
            jobj.binds.forEach((bind) => binds.set(bind[0], bind[1]));
            let pcodes = new Map();
            jobj.pcodes.forEach((pc) => pcodes.set(pc[0], pc[1]));
            return new MIRInvokePrimitiveDecl(jobj.enclosingDecl, jobj.iname, jobj.key, jobj.attributes, jobj.recursive, jparsepragmas(jobj.pragmas), jparsesinfo(jobj.sinfo), jobj.file, binds, jobj.params.map((p) => MIRFunctionParameter.jparse(p)), jobj.resultType, jobj.implkey, pcodes);
        }
    }
}
exports.MIRInvokeDecl = MIRInvokeDecl;
class MIRInvokeBodyDecl extends MIRInvokeDecl {
    constructor(enclosingDecl, iname, key, attributes, recursive, pragmas, sinfo, srcFile, params, resultType, preconds, postconds, body) {
        super(enclosingDecl, iname, key, attributes, recursive, pragmas, sinfo, srcFile, params, resultType, preconds, postconds);
        this.body = body;
    }
    jemit() {
        return { enclosingDecl: this.enclosingDecl, iname: this.iname, key: this.key, sinfo: jemitsinfo(this.sourceLocation), file: this.srcFile, attributes: this.attributes, recursive: this.recursive, pragmas: jemitpragmas(this.pragmas), params: this.params.map((p) => p.jemit()), resultType: this.resultType, preconditions: this.preconditions, postconditions: this.postconditions, body: this.body.jemit() };
    }
}
exports.MIRInvokeBodyDecl = MIRInvokeBodyDecl;
class MIRInvokePrimitiveDecl extends MIRInvokeDecl {
    constructor(enclosingDecl, iname, key, attributes, recursive, pragmas, sinfo, srcFile, binds, params, resultType, implkey, pcodes) {
        super(enclosingDecl, iname, key, attributes, recursive, pragmas, sinfo, srcFile, params, resultType, undefined, undefined);
        this.implkey = implkey;
        this.binds = binds;
        this.pcodes = pcodes;
    }
    jemit() {
        return { enclosingDecl: this.enclosingDecl, iname: this.iname, key: this.key, sinfo: jemitsinfo(this.sourceLocation), file: this.srcFile, attributes: this.attributes, recursive: this.recursive, pragmas: jemitpragmas(this.pragmas), params: this.params.map((p) => p.jemit()), resultType: this.resultType, implkey: this.implkey, binds: [...this.binds], pcodes: [...this.pcodes] };
    }
}
exports.MIRInvokePrimitiveDecl = MIRInvokePrimitiveDecl;
class MIRFieldDecl {
    constructor(enclosingDecl, attributes, fname, srcInfo, srcFile, fkey, pragmas, name, dtype, value) {
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
    jemit() {
        return { enclosingDecl: this.enclosingDecl, attributes: this.attributes, fname: this.fname, fkey: this.fkey, sinfo: jemitsinfo(this.sourceLocation), file: this.srcFile, pragmas: jemitpragmas(this.pragmas), name: this.name, declaredType: this.declaredType, value: this.value || null };
    }
    static jparse(jobj) {
        return new MIRFieldDecl(jobj.enclosingDecl, jobj.attributes, jobj.fname, jparsesinfo(jobj.sinfo), jobj.file, jobj.fkey, jparsepragmas(jobj.pragmas), jobj.name, jobj.declaredType, jobj.value || undefined);
    }
}
exports.MIRFieldDecl = MIRFieldDecl;
class MIROOTypeDecl {
    constructor(ooname, srcInfo, srcFile, tkey, attributes, pragmas, ns, name, terms, provides, invariants, fields) {
        this.invariants = [];
        this.fields = [];
        this.vcallMap = new Map();
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
    static jparse(jobj) {
        let terms = new Map();
        jobj.terms.forEach((t) => terms.set(t[0], MIRType.jparse(t[1])));
        if (jobj.isentity) {
            const entity = new MIREntityTypeDecl(jobj.ooname, jparsesinfo(jobj.sinfo), jobj.file, jobj.tkey, jobj.attributes, jparsepragmas(jobj.pragmas), jobj.ns, jobj.name, terms, jobj.provides, jobj.invariants, jobj.fields.map((f) => MIRFieldDecl.jparse(f)));
            jobj.vcallMap.forEach((vc) => entity.vcallMap.set(vc[0], vc[1]));
            return entity;
        }
        else {
            const concept = new MIRConceptTypeDecl(jobj.ooname, jparsesinfo(jobj.sinfo), jobj.file, jobj.tkey, jobj.attributes, jparsepragmas(jobj.pragmas), jobj.ns, jobj.name, terms, jobj.provides, jobj.invariants, jobj.fields.map((f) => MIRFieldDecl.jparse(f)));
            jobj.vcallMap.forEach((vc) => concept.vcallMap.set(vc[0], vc[1]));
            return concept;
        }
    }
}
exports.MIROOTypeDecl = MIROOTypeDecl;
class MIRConceptTypeDecl extends MIROOTypeDecl {
    constructor(ooname, srcInfo, srcFile, tkey, attributes, pragmas, ns, name, terms, provides, invariants, fields) {
        super(ooname, srcInfo, srcFile, tkey, attributes, pragmas, ns, name, terms, provides, invariants, fields);
    }
    jemit() {
        return { isentity: false, ooname: this.ooname, tkey: this.tkey, sinfo: jemitsinfo(this.sourceLocation), file: this.srcFile, attributes: this.attributes, pragmas: jemitpragmas(this.pragmas), ns: this.ns, name: this.name, terms: [...this.terms].map((t) => [t[0], t[1].jemit()]), provides: this.provides, invariants: this.invariants, fields: this.fields.map((f) => f.jemit()), vcallMap: [...this.vcallMap] };
    }
}
exports.MIRConceptTypeDecl = MIRConceptTypeDecl;
class MIREntityTypeDecl extends MIROOTypeDecl {
    constructor(ooname, srcInfo, srcFile, tkey, attributes, pragmas, ns, name, terms, provides, invariants, fields) {
        super(ooname, srcInfo, srcFile, tkey, attributes, pragmas, ns, name, terms, provides, invariants, fields);
    }
    jemit() {
        return { isentity: true, ooname: this.ooname, tkey: this.tkey, sinfo: jemitsinfo(this.sourceLocation), file: this.srcFile, attributes: this.attributes, pragmas: jemitpragmas(this.pragmas), ns: this.ns, name: this.name, terms: [...this.terms].map((t) => [t[0], t[1].jemit()]), provides: this.provides, invariants: this.invariants, fields: this.fields.map((f) => f.jemit()), vcallMap: [...this.vcallMap] };
    }
}
exports.MIREntityTypeDecl = MIREntityTypeDecl;
class MIRTypeOption {
    constructor(trkey) {
        this.trkey = trkey;
    }
    static jparse(jobj) {
        switch (jobj.kind) {
            case "entity":
                return MIREntityType.jparse(jobj);
            case "concept":
                return MIRConceptType.jparse(jobj);
            case "tuple":
                return MIRTupleType.jparse(jobj);
            case "record":
                return MIRRecordType.jparse(jobj);
            default:
                assert(jobj.kind === "ephemeral");
                return MIREphemeralListType.jparse(jobj);
        }
    }
}
exports.MIRTypeOption = MIRTypeOption;
class MIRNominalType extends MIRTypeOption {
    constructor(trkey) {
        super(trkey);
    }
}
exports.MIRNominalType = MIRNominalType;
class MIREntityType extends MIRNominalType {
    constructor(ekey) {
        super(ekey);
        this.ekey = ekey;
    }
    static create(ekey) {
        return new MIREntityType(ekey);
    }
    jemit() {
        return { kind: "entity", ekey: this.ekey };
    }
    static jparse(jobj) {
        return MIREntityType.create(jobj.ekey);
    }
}
exports.MIREntityType = MIREntityType;
class MIRConceptType extends MIRNominalType {
    constructor(trkey, ckeys) {
        super(trkey);
        this.ckeys = ckeys;
    }
    static create(ckeys) {
        const skeys = ckeys.sort();
        return new MIRConceptType(skeys.join(" & "), skeys);
    }
    jemit() {
        return { kind: "concept", ckeys: this.ckeys };
    }
    static jparse(jobj) {
        return MIRConceptType.create(jobj.ckeys);
    }
}
exports.MIRConceptType = MIRConceptType;
class MIRStructuralType extends MIRTypeOption {
    constructor(trkey) {
        super(trkey);
    }
}
exports.MIRStructuralType = MIRStructuralType;
class MIRTupleTypeEntry {
    constructor(type, isOpt) {
        this.isOptional = isOpt;
        this.type = type;
    }
    jemit() {
        return { type: this.type.jemit(), isOptional: this.isOptional };
    }
    static jparse(jobj) {
        return new MIRTupleTypeEntry(MIRType.jparse(jobj.type), jobj.isOptional);
    }
}
exports.MIRTupleTypeEntry = MIRTupleTypeEntry;
class MIRTupleType extends MIRStructuralType {
    constructor(trkey, entries) {
        super(trkey);
        this.entries = entries;
    }
    static create(entries) {
        let cvalue = entries.map((entry) => (entry.isOptional ? "?:" : "") + entry.type.trkey).join(", ");
        return new MIRTupleType("[" + cvalue + "]", [...entries]);
    }
    jemit() {
        return { kind: "tuple", entries: this.entries.map((e) => e.jemit()) };
    }
    static jparse(jobj) {
        return MIRTupleType.create(jobj.entries.map((e) => MIRTupleTypeEntry.jparse(e)));
    }
}
exports.MIRTupleType = MIRTupleType;
class MIRRecordTypeEntry {
    constructor(name, type, isOpt) {
        this.name = name;
        this.type = type;
        this.isOptional = isOpt;
    }
    jemit() {
        return { name: this.name, type: this.type.jemit(), isOptional: this.isOptional };
    }
    static jparse(jobj) {
        return new MIRRecordTypeEntry(jobj.name, MIRType.jparse(jobj.type), jobj.isOptional);
    }
}
exports.MIRRecordTypeEntry = MIRRecordTypeEntry;
class MIRRecordType extends MIRStructuralType {
    constructor(rstr, entries) {
        super(rstr);
        this.entries = entries;
    }
    static create(entries) {
        const rentries = [...entries].sort((a, b) => a.name.localeCompare(b.name));
        let cvalue = rentries.map((entry) => entry.name + (entry.isOptional ? "?:" : ":") + entry.type.trkey).join(", ");
        return new MIRRecordType("{" + cvalue + "}", rentries);
    }
    jemit() {
        return { kind: "record", entries: this.entries.map((e) => e.jemit()) };
    }
    static jparse(jobj) {
        return MIRRecordType.create(jobj.entries.map((e) => MIRRecordTypeEntry.jparse(e)));
    }
}
exports.MIRRecordType = MIRRecordType;
class MIREphemeralListType extends MIRTypeOption {
    constructor(trkey, entries) {
        super(trkey);
        this.entries = entries;
    }
    static create(entries) {
        let cvalue = entries.map((entry) => entry.trkey).join(", ");
        return new MIREphemeralListType("(|" + cvalue + "|)", [...entries]);
    }
    jemit() {
        return { kind: "ephemeral", entries: this.entries.map((e) => e.jemit()) };
    }
    static jparse(jobj) {
        return MIREphemeralListType.create(jobj.entries.map((e) => MIRType.jparse(e)));
    }
}
exports.MIREphemeralListType = MIREphemeralListType;
class MIRType {
    constructor(trkey, options) {
        this.trkey = trkey;
        this.options = options;
    }
    static createSingle(option) {
        return new MIRType(option.trkey, [option]);
    }
    static create(options) {
        if (options.length === 1) {
            return MIRType.createSingle(options[0]);
        }
        else {
            const trkey = [...options].sort().map((tk) => tk.trkey).join(" | ");
            return new MIRType(trkey, options);
        }
    }
    jemit() {
        return { options: this.options.map((opt) => opt.jemit()) };
    }
    static jparse(jobj) {
        return MIRType.create(jobj.options.map((opt) => MIRTypeOption.jparse(opt)));
    }
}
exports.MIRType = MIRType;
class PackageConfig {
    //TODO: package.config data
    jemit() {
        return {};
    }
    static jparse(jobj) {
        return new PackageConfig();
    }
}
exports.PackageConfig = PackageConfig;
class MIRAssembly {
    constructor(pckge, srcFiles, srcHash) {
        this.constantDecls = new Map();
        this.fieldDecls = new Map();
        this.entryPoints = [];
        this.invokeDecls = new Map();
        this.primitiveInvokeDecls = new Map();
        this.conceptDecls = new Map();
        this.entityDecls = new Map();
        this.typeMap = new Map();
        this.m_subtypeRelationMemo = new Map();
        this.m_atomSubtypeRelationMemo = new Map();
        this.package = pckge;
        this.srcFiles = srcFiles;
        this.srcHash = srcHash;
    }
    atomSubtypeOf_EntityEntity(t1, t2) {
        const t1e = this.entityDecls.get(t1.ekey);
        const t2e = this.entityDecls.get(t2.ekey);
        return (t1e.ns === t2e.ns && t1e.name === t2e.name);
    }
    atomSubtypeOf_EntityConcept(t1, t2) {
        const t1e = this.entityDecls.get(t1.ekey);
        const mcc = MIRType.createSingle(t2);
        return t1e.provides.some((provide) => this.subtypeOf(this.typeMap.get(provide), mcc));
    }
    atomSubtypeOf_ConceptConcept(t1, t2) {
        return t2.ckeys.every((c2t) => {
            return t1.ckeys.some((c1t) => {
                const c1 = this.conceptDecls.get(c1t);
                const c2 = this.conceptDecls.get(c2t);
                if (c1.ns === c2.ns && c1.name === c2.name) {
                    return true;
                }
                return c1.provides.some((provide) => this.subtypeOf(this.typeMap.get(provide), this.typeMap.get(c2t)));
            });
        });
    }
    checkAllTupleEntriesOfType(t1, t2) {
        return t1.entries.every((entry) => this.subtypeOf(entry.type, t2));
    }
    atomSubtypeOf_TupleConcept(t1, t2) {
        const tupleconcept = this.typeMap.get("NSCore::Tuple").options[0];
        if (this.atomSubtypeOf_ConceptConcept(tupleconcept, t2)) {
            return true;
        }
        const podconcept = this.typeMap.get("NSCore::PODType");
        const podconceptatom = podconcept.options[0];
        if (this.atomSubtypeOf_ConceptConcept(podconceptatom, t2) && this.checkAllTupleEntriesOfType(t1, podconcept)) {
            return true;
        }
        const apiconcept = this.typeMap.get("NSCore::APIType");
        const apiconceptatom = apiconcept.options[0];
        if (this.atomSubtypeOf_ConceptConcept(apiconceptatom, t2) && this.checkAllTupleEntriesOfType(t1, apiconcept)) {
            return true;
        }
        return false;
    }
    atomSubtypeOf_TupleTuple(t1, t2) {
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
    checkAllRecordEntriesOfType(t1, t2) {
        return t1.entries.every((entry) => this.subtypeOf(entry.type, t2));
    }
    atomSubtypeOf_RecordConcept(t1, t2) {
        const recordconcept = this.typeMap.get("NSCore::Record").options[0];
        if (this.atomSubtypeOf_ConceptConcept(recordconcept, t2)) {
            return true;
        }
        const podconcept = this.typeMap.get("NSCore::PODType");
        const podconceptatom = podconcept.options[0];
        if (this.atomSubtypeOf_ConceptConcept(podconceptatom, t2) && this.checkAllRecordEntriesOfType(t1, podconcept)) {
            return true;
        }
        const apiconcept = this.typeMap.get("NSCore::APIType");
        const apiconceptatom = apiconcept.options[0];
        if (this.atomSubtypeOf_ConceptConcept(apiconceptatom, t2) && this.checkAllRecordEntriesOfType(t1, apiconcept)) {
            return true;
        }
        return false;
    }
    atomSubtypeOf_RecordRecord(t1, t2) {
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
    atomSubtypeOf(t1, t2) {
        let memores = this.m_atomSubtypeRelationMemo.get(t1.trkey);
        if (memores === undefined) {
            this.m_atomSubtypeRelationMemo.set(t1.trkey, new Map());
            memores = this.m_atomSubtypeRelationMemo.get(t1.trkey);
        }
        let memoval = memores.get(t2.trkey);
        if (memoval !== undefined) {
            return memoval;
        }
        let res = false;
        if (t1.trkey === t2.trkey) {
            res = true;
        }
        else if (t1 instanceof MIREphemeralListType || t2 instanceof MIREphemeralListType) {
            //not eq from above so always false
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
    subtypeOf(t1, t2) {
        let memores = this.m_subtypeRelationMemo.get(t1.trkey);
        if (memores === undefined) {
            this.m_subtypeRelationMemo.set(t1.trkey, new Map());
            memores = this.m_subtypeRelationMemo.get(t1.trkey);
        }
        let memoval = memores.get(t2.trkey);
        if (memoval !== undefined) {
            return memoval;
        }
        const res = (t1.trkey === t2.trkey) || t1.options.every((t1opt) => t2.options.some((t2opt) => this.atomSubtypeOf(t1opt, t2opt)));
        memores.set(t2.trkey, res);
        return res;
    }
    registerUnionTypeIfNeeded(options) {
        const flatoptions = [].concat(...options.map((opt) => opt.options));
        //do a simplification based on A | B when A \Subtypeeq B is B
        let simplifiedTypes = [];
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
    jemit() {
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
    static jparse(jobj) {
        let masm = new MIRAssembly(PackageConfig.jparse(jobj.package), jobj.srcFiles, jobj.srcHash);
        jobj.constantDecls.forEach((cd) => masm.constantDecls.set(cd[0], MIRConstantDecl.jparse(cd[1])));
        jobj.fieldDecls.forEach((fd) => masm.fieldDecls.set(fd[0], MIRFieldDecl.jparse(fd[1])));
        jobj.entryPoints.forEach((ep) => masm.entryPoints.push(ep));
        jobj.invokeDecls.forEach((id) => masm.invokeDecls.set(id[0], MIRInvokeDecl.jparse(id[1])));
        jobj.primitiveInvokeDecls.forEach((id) => masm.primitiveInvokeDecls.set(id[0], MIRInvokeDecl.jparse(id[1])));
        jobj.conceptDecls.forEach((cd) => masm.conceptDecls.set(cd[0], MIROOTypeDecl.jparse(cd[1])));
        jobj.entityDecls.forEach((id) => masm.entityDecls.set(id[0], MIROOTypeDecl.jparse(id[1])));
        jobj.typeMap.forEach((t) => masm.typeMap.set(t[0], MIRType.jparse(t[1])));
        return masm;
    }
}
exports.MIRAssembly = MIRAssembly;
//# sourceMappingURL=mir_assembly.js.map