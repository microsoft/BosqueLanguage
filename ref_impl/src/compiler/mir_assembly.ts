//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo } from "../ast/parser";
import { MIRBody, MIRResolvedTypeKey, MIRTypeKey, MIRStaticKey, MIRConstKey, MIRFieldKey, MIRMethodKey, MIRVirtualMethodKey, MIRGlobalKey, MIRFunctionKey, MIRLambdaKey } from "./mir_ops";

class MIRFunctionParameter {
    readonly name: string;
    readonly type: MIRType;
    readonly isOptional: boolean;

    constructor(name: string, type: MIRType, isOpt: boolean) {
        this.name = name;
        this.type = type;
        this.isOptional = isOpt;
    }
}

class MIRInvokeDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly terms: Map<string, MIRType>;

    readonly params: MIRFunctionParameter[];
    readonly optRestName: string | undefined;
    readonly optRestType: MIREntityType | undefined;
    readonly resultType: MIRType;

    readonly preconditions: MIRBody[];
    readonly postconditions: MIRBody[];

    readonly isLambda: boolean;
    readonly captured: Map<string, MIRType>;
    readonly body: MIRBody | undefined;

    constructor(sinfo: SourceInfo, srcFile: string, terms: Map<string, MIRType>, params: MIRFunctionParameter[], optRestName: string | undefined, optRestType: MIREntityType | undefined, resultType: MIRType, preconds: MIRBody[], postconds: MIRBody[], isLambda: boolean, captured: Map<string, MIRType>, body: MIRBody | undefined) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

        this.terms = terms;

        this.params = params;
        this.optRestName = optRestName;
        this.optRestType = optRestType;
        this.resultType = resultType;

        this.preconditions = preconds;
        this.postconditions = postconds;

        this.isLambda = isLambda;
        this.captured = captured;
        this.body = body;
    }

    static createLambdaInvokeDecl(sinfo: SourceInfo, srcFile: string, params: MIRFunctionParameter[], optRestName: string | undefined, optRestType: MIREntityType | undefined, resultType: MIRType, captured: Map<string, MIRType>, body: MIRBody) {
        return new MIRInvokeDecl(sinfo, srcFile, new Map<string, MIRType>(), params, optRestName, optRestType, resultType, [], [], true, captured, body);
    }

    static createStaticInvokeDecl(sinfo: SourceInfo, srcFile: string, terms: Map<string, MIRType>, params: MIRFunctionParameter[], optRestName: string | undefined, optRestType: MIREntityType | undefined, resultType: MIRType, preconds: MIRBody[], postconds: MIRBody[], body: MIRBody | undefined) {
        return new MIRInvokeDecl(sinfo, srcFile, terms, params, optRestName, optRestType, resultType, preconds, postconds, false, new Map<string, MIRType>(), body);
    }

    static createMemberInvokeDecl(sinfo: SourceInfo, srcFile: string, terms: Map<string, MIRType>, params: MIRFunctionParameter[], optRestName: string | undefined, optRestType: MIREntityType | undefined, resultType: MIRType, preconds: MIRBody[], postconds: MIRBody[], body: MIRBody | undefined) {
        return new MIRInvokeDecl(sinfo, srcFile, terms, params, optRestName, optRestType, resultType, preconds, postconds, false, new Map<string, MIRType>(), body);
    }
}

abstract class MIROOMemberDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly name: string;

    readonly enclosingType: MIRTypeKey;

    constructor(srcInfo: SourceInfo, srcFile: string, attributes: string[], name: string, enclosingType: MIRTypeKey) {
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.name = name;
        this.enclosingType = enclosingType;
    }
}

class MIRConstDecl extends MIROOMemberDecl {
    readonly ckey: MIRConstKey;
    readonly declaredType: MIRType;
    readonly value: MIRBody | undefined;

    constructor(srcInfo: SourceInfo, srcFile: string, ckey: MIRConstKey, attributes: string[], name: string, enclosingType: MIRTypeKey, dtype: MIRType, value: MIRBody | undefined) {
        super(srcInfo, srcFile, attributes, name, enclosingType);

        this.ckey = ckey;
        this.declaredType = dtype;
        this.value = value;
    }
}

class MIRStaticDecl extends MIROOMemberDecl {
    readonly sfkey: MIRStaticKey;
    readonly invoke: MIRInvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, sfkey: MIRStaticKey, attributes: string[], name: string, enclosingType: MIRTypeKey, invoke: MIRInvokeDecl) {
        super(sinfo, srcFile, attributes, name, enclosingType);

        this.sfkey = sfkey;
        this.invoke = invoke;
    }
}

class MIRFieldDecl extends MIROOMemberDecl {
    readonly fkey: MIRFieldKey;
    readonly declaredType: MIRType;
    readonly value: MIRBody | undefined;

    constructor(srcInfo: SourceInfo, srcFile: string, fkey: MIRFieldKey, attributes: string[], name: string, enclosingType: MIRTypeKey, dtype: MIRType, value: MIRBody | undefined) {
        super(srcInfo, srcFile, attributes, name, enclosingType);

        this.fkey = fkey;
        this.declaredType = dtype;
        this.value = value;
    }
}

class MIRMethodDecl extends MIROOMemberDecl {
    readonly vkey: MIRVirtualMethodKey;
    readonly mkey: MIRMethodKey;
    readonly invoke: MIRInvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, vkey: MIRVirtualMethodKey, mkey: MIRMethodKey, attributes: string[], name: string, enclosingType: MIRTypeKey, invoke: MIRInvokeDecl) {
        super(sinfo, srcFile, attributes, name, enclosingType);

        this.vkey = vkey;
        this.mkey = mkey;
        this.invoke = invoke;
    }
}

class MIROOTypeDecl {
    readonly tkey: MIRTypeKey;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly ns: string;
    readonly name: string;

    readonly terms: Map<string, MIRType>;

    readonly provides: MIRTypeKey[];

    readonly isCollectionEntityType: boolean;
    readonly isMapEntityType: boolean;
    readonly declaredInvariants: MIRBody[];

    readonly memberMethods: MIRMethodDecl[] = [];
    readonly memberFields: MIRFieldDecl[];

    readonly invariants: MIRBody[] = [];
    readonly fieldMap: Map<string, MIRFieldDecl> = new Map<string, MIRFieldDecl>();
    readonly fieldLayout: string[] = [];
    readonly vcallMap: Map<MIRVirtualMethodKey, MIRMethodDecl> = new Map<string, MIRMethodDecl>();

    constructor(tkey: MIRTypeKey, srcFile: string, attributes: string[], ns: string, name: string, terms: Map<string, MIRType>, provides: MIRTypeKey[], isCollectionEntityType: boolean, isMapEntityType: boolean, declaredInvariants: MIRBody[], declaredFields: MIRFieldDecl[]) {
        this.tkey = tkey;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.ns = ns;
        this.name = name;
        this.terms = terms;
        this.provides = provides;
        this.isCollectionEntityType = isCollectionEntityType;
        this.isMapEntityType = isMapEntityType;
        this.declaredInvariants = declaredInvariants;
        this.memberFields = declaredFields;
    }

    static attributeSetContains(attr: string, attrSet: string[]): boolean {
        return attrSet.indexOf(attr) !== -1;
    }
}

class MIRConceptTypeDecl extends MIROOTypeDecl {
    constructor(tkey: MIRTypeKey, srcFile: string, attributes: string[], ns: string, name: string, terms: Map<string, MIRType>, provides: MIRTypeKey[], isCollectionEntityType: boolean, isMapEntityType: boolean, declaredInvariants: MIRBody[], declaredFields: MIRFieldDecl[]) {
        super(tkey, srcFile, attributes, ns, name, terms, provides, isCollectionEntityType, isMapEntityType, declaredInvariants, declaredFields);
    }
}

class MIREntityTypeDecl extends MIROOTypeDecl {
    readonly isEnum: boolean;
    readonly isKey: boolean;

    constructor(tkey: MIRTypeKey, srcFile: string, attributes: string[], ns: string, name: string, terms: Map<string, MIRType>, provides: MIRTypeKey[], isCollectionEntityType: boolean, isMapEntityType: boolean, declaredInvariants: MIRBody[], declaredFields: MIRFieldDecl[], isEnum: boolean, isKey: boolean) {
        super(tkey, srcFile, attributes, ns, name, terms, provides, isCollectionEntityType, isMapEntityType, declaredInvariants, declaredFields);

        this.isEnum = isEnum;
        this.isKey = isKey;
    }
}

abstract class MIRNSMemberDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly ns: string;
    readonly name: string;

    constructor(srcInfo: SourceInfo, srcFile: string, attributes: string[], ns: string, name: string) {
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;

        this.attributes = attributes;
        this.ns = ns;
        this.name = name;
    }
}

class MIRGlobalDecl extends MIRNSMemberDecl {
    readonly gkey: MIRGlobalKey;
    readonly declaredType: MIRType;
    readonly value: MIRBody;

    constructor(srcInfo: SourceInfo, srcFile: string, gkey: MIRGlobalKey, attributes: string[], ns: string, name: string, dtype: MIRType, value: MIRBody) {
        super(srcInfo, srcFile, attributes, ns, name);

        this.gkey = gkey;
        this.declaredType = dtype;
        this.value = value;
    }
}

class MIRFunctionDecl extends MIRNSMemberDecl {
    readonly fkey: MIRFunctionKey;
    readonly invoke: MIRInvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, fkey: MIRGlobalKey, attributes: string[], ns: string, name: string, invoke: MIRInvokeDecl) {
        super(sinfo, srcFile, attributes, ns, name);

        this.fkey = fkey;
        this.invoke = invoke;
    }
}

abstract class MIRTypeOption {
    readonly trkey: MIRResolvedTypeKey;

    constructor(trkey: MIRResolvedTypeKey) {
        this.trkey = trkey;
    }
}

abstract class MIRNominalType extends MIRTypeOption {
    constructor(trkey: MIRResolvedTypeKey) {
        super(trkey);
    }
}

class MIREntityType extends MIRNominalType {
    readonly ekey: MIRTypeKey;

    private constructor(ekey: MIRTypeKey) {
        super(ekey);
        this.ekey = ekey;
    }

    static create(ekey: MIRTypeKey): MIREntityType {
        return new MIREntityType(ekey);
    }
}

class MIRConceptType extends MIRNominalType {
    readonly ckeys: MIRTypeKey[];

    private constructor(trkey: MIRResolvedTypeKey, ckeys: MIRTypeKey[]) {
        super(trkey);
        this.ckeys = ckeys;
    }

    static create(ckeys: MIRTypeKey[]): MIRConceptType {
        const skeys = ckeys.sort();
        return new MIRConceptType(skeys.join(" & "), skeys);
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
}

class MIRTupleType extends MIRStructuralType {
    readonly entries: MIRTupleTypeEntry[];
    readonly isOpen: boolean;

    private constructor(trkey: MIRResolvedTypeKey, entries: MIRTupleTypeEntry[], isOpen: boolean) {
        super(trkey);
        this.entries = entries;
        this.isOpen = isOpen;
    }

    static create(isOpen: boolean, entries: MIRTupleTypeEntry[]): MIRTupleType {
        let cvalue = entries.map((entry) => (entry.isOptional ? "?:" : "") + entry.type.trkey).join(", ");
        if (isOpen) {
            cvalue += (entries.length !== 0 ? ", " : "") + "...";
        }

        return new MIRTupleType("[" + cvalue + "]", [...entries], isOpen);
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
}

class MIRRecordType extends MIRStructuralType {
    readonly entries: MIRRecordTypeEntry[];
    readonly isOpen: boolean;

    constructor(rstr: string, entries: MIRRecordTypeEntry[], isOpen: boolean) {
        super(rstr);
        this.entries = entries;
        this.isOpen = isOpen;
    }

    static create(isOpen: boolean, entries: MIRRecordTypeEntry[]): MIRRecordType {
        const rentries = [...entries].sort((a, b) => a.name.localeCompare(b.name));

        let cvalue = rentries.map((entry) => entry.name + (entry.isOptional ? "?:" : ":") + entry.type.trkey).join(", ");
        if (isOpen) {
            cvalue += (rentries.length !== 0 ? ", " : "") + "...";
        }

        return new MIRRecordType("{" + cvalue + "}", rentries, isOpen);
    }
}

class MIRFunctionTypeParam {
    readonly name: string;
    readonly isOptional: boolean;
    readonly type: MIRType;

    constructor(name: string, isOptional: boolean, type: MIRType) {
        this.name = name;
        this.isOptional = isOptional;
        this.type = type;
    }
}

class MIRFunctionType extends MIRStructuralType {
    readonly params: MIRFunctionTypeParam[];
    readonly optRestParamName: string | undefined;
    readonly optRestParamType: MIRType | undefined;
    readonly resultType: MIRType;

    readonly allParamNames: Set<string>;

    constructor(rstr: string, params: MIRFunctionTypeParam[], optRestParamName: string | undefined, optRestParamType: MIRType | undefined, resultType: MIRType, allParamNames: Set<string>) {
        super(rstr);
        this.params = params;
        this.optRestParamName = optRestParamName;
        this.optRestParamType = optRestParamType;
        this.resultType = resultType;

        this.allParamNames = new Set<string>();
    }

    static create(params: MIRFunctionTypeParam[], optRestParamName: string | undefined, optRestParamType: MIRType | undefined, resultType: MIRType): MIRFunctionType {
        let cvalues: string[] = [];
        let allNames = new Set<string>();
        params.forEach((param) => {
            if (param.name !== "_") {
                allNames.add(param.name);
            }
            cvalues.push(param.name + (param.isOptional ? "?: " : ": ") + param.type.trkey);
        });
        let cvalue = cvalues.join(", ");

        if (optRestParamName !== undefined && optRestParamType !== undefined) {
            cvalue += ((cvalues.length !== 0 ? ", " : "") + ("..." + optRestParamName + ": " + optRestParamType.trkey));
        }

        return new MIRFunctionType("(" + cvalue + ") -> " + resultType.trkey, params, optRestParamName, optRestParamType, resultType, allNames);
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
        const ropts = [...options].sort((a, b) => a.trkey.localeCompare(b.trkey));
        const trkey = ropts.map((opt) => opt.trkey).join(" | ");
        return new MIRType(trkey, ropts);
    }
}

class PackageConfig {
    //TODO: package.config data
}

class MIRAssembly {
    readonly package: PackageConfig;
    readonly srcFiles: { relativePath: string, contents: string }[];
    readonly srcHash: string;

    readonly globalDecls: Map<MIRGlobalKey, MIRGlobalDecl> = new Map<MIRGlobalKey, MIRGlobalDecl>();
    readonly constDecls: Map<MIRConstKey, MIRConstDecl> = new Map<MIRConstKey, MIRConstDecl>();

    readonly functionDecls: Map<MIRFunctionKey, MIRFunctionDecl> = new Map<MIRFunctionKey, MIRFunctionDecl>();
    readonly staticDecls: Map<MIRStaticKey, MIRStaticDecl> = new Map<MIRStaticKey, MIRStaticDecl>();
    readonly methodDecls: Map<MIRMethodKey, MIRMethodDecl> = new Map<MIRMethodKey, MIRMethodDecl>();
    readonly lambdaDecls: Map<MIRLambdaKey, MIRInvokeDecl> = new Map<MIRLambdaKey, MIRInvokeDecl>();

    readonly memberFields: Map<MIRFieldKey, MIRFieldDecl> = new Map<MIRFieldKey, MIRFieldDecl>();

    readonly conceptMap: Map<MIRTypeKey, MIRConceptTypeDecl> = new Map<MIRTypeKey, MIRConceptTypeDecl>();
    readonly entityMap: Map<MIRTypeKey, MIREntityTypeDecl> = new Map<MIRTypeKey, MIREntityTypeDecl>();

    readonly typeMap: Map<MIRResolvedTypeKey, MIRType> = new Map<MIRResolvedTypeKey, MIRType>();

    private m_subtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();
    private m_atomSubtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();

    private atomSubtypeOf_EntityEntity(t1: MIREntityType, t2: MIREntityType): boolean {
        const t1e = this.entityMap.get(t1.ekey) as MIREntityTypeDecl;
        const t2e = this.entityMap.get(t2.ekey) as MIREntityTypeDecl;
        if (t1e.ns !== t2e.ns || t1e.name !== t2e.name) {
            return false;
        }

        let allBindsOk = true;
        t1e.terms.forEach((v, k) => { allBindsOk = allBindsOk && this.subtypeOf(v, t2e.terms.get(k) as MIRType); });
        return allBindsOk;
    }

    private atomSubtypeOf_EntityConcept(t1: MIREntityType, t2: MIRConceptType): boolean {
        const t1e = this.entityMap.get(t1.ekey) as MIREntityTypeDecl;
        const t2type = MIRType.createSingle(t2);
        return t1e.provides.some((provide) => this.subtypeOf(this.typeMap.get(provide) as MIRType, t2type));
    }

    private atomSubtypeOf_ConceptConcept(t1: MIRConceptType, t2: MIRConceptType): boolean {
        return t1.ckeys.every((c1t) => {
            return t2.ckeys.some((c2t) => {
                const c1 = this.conceptMap.get(c1t) as MIRConceptTypeDecl;
                const c2 = this.conceptMap.get(c2t) as MIRConceptTypeDecl;

                if (c1.ns === c2.ns && c1.name === c2.name) {
                    let allBindsOk = true;
                    c1.terms.forEach((v, k) => { allBindsOk = allBindsOk && this.subtypeOf(v, c2.terms.get(k) as MIRType); });
                    return allBindsOk;
                }

                const t2type = MIRType.createSingle(MIRConceptType.create([c2t]));
                return c1.provides.some((provide) => this.subtypeOf(this.typeMap.get(provide) as MIRType, t2type));
            });
        });
    }

    private atomSubtypeOf_TupleTuple(t1: MIRTupleType, t2: MIRTupleType): boolean {
        //Then this is definitely not ok
        if (t1.isOpen && !t2.isOpen) {
            return false;
        }

        for (let i = 0; i < t1.entries.length; ++i) {
            const t1e = t1.entries[i];

            if (i >= t2.entries.length) {
                if (!t2.isOpen) {
                    return false;
                }
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
        //Then this is definitely not ok
        if (t1.isOpen && !t2.isOpen) {
            return false;
        }

        let badEntry = false;
        t1.entries.forEach((entry) => {
            const t2e = t2.entries.find((e) => e.name === entry.name);
            if (t2e === undefined) {
                if (!t2.isOpen) {
                    badEntry = badEntry || true;
                }
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

    private atomSubtypeOf_FunctionFunction(t1: MIRFunctionType, t2: MIRFunctionType): boolean {
        //Then this is definitely not ok
        if (t2.optRestParamType !== undefined && t1.optRestParamType === undefined) {
            return false;
        }

        if (t2.optRestParamType !== undefined && !this.subtypeOf(t2.optRestParamType, t1.optRestParamType as MIRType)) {
            return false;
        }

        for (let i = 0; i < t2.params.length; ++i) {
            const t2p = t2.params[i];

            if (i >= t1.params.length) {
                if (t1.optRestParamType !== undefined) {
                    return false;
                }
                else {
                    //TODO: we should type check that the type is assignable to the rest option
                }
            }
            else {
                const t1p = t1.params[i];
                if ((t2p.isOptional && !t1p.isOptional) || !this.subtypeOf(t2p.type, t1p.type)) {
                    return false;
                }
            }

            //check that if t2p is named then t1p has the same name
            if (t2.params[i].name !== "_") {
                if (t1.params.length <= i || t2.params[i].name === t1.params[i].name) {
                    return false;
                }
            }
        }

        //t1 has a required parameter that is not required in t2
        if (t1.params.length > t2.params.length && t1.params.slice(t2.params.length).some((param) => !param.isOptional)) {
            return false;
        }

        //co-variant is cool
        return this.subtypeOf(t1.resultType, t2.resultType);
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
        else if (t1 instanceof MIRConceptType && t2 instanceof MIRConceptType) {
            res = this.atomSubtypeOf_ConceptConcept(t1, t2);
        }
        else if (t1 instanceof MIRConceptType) {
            //res stays false
        }
        else if (t2 instanceof MIRConceptType) {
            if (t1 instanceof MIREntityType) {
                res = this.atomSubtypeOf_EntityConcept(t1, t2 as MIRConceptType);
            }
            else if (t1 instanceof MIRTupleType) {
                res = this.atomSubtypeOf_ConceptConcept(MIRConceptType.create(["NSCore::Tuple"]), t2 as MIRConceptType);
            }
            else if (t1 instanceof MIRRecordType) {
                res = this.atomSubtypeOf_ConceptConcept(MIRConceptType.create(["NSCore::Record"]), t2 as MIRConceptType);
            }
            else {
                res = this.atomSubtypeOf_ConceptConcept(MIRConceptType.create(["NSCore::Function"]), t2 as MIRConceptType);
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
            else if (t1 instanceof MIRFunctionType && t2 instanceof MIRFunctionType) {
                res = this.atomSubtypeOf_FunctionFunction(t1, t2);
            }
            else {
                //fall-through
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

    closeConceptDecl(cpt: MIRConceptTypeDecl) {
        cpt.provides.forEach((tkey) => {
            const ccdecl = this.conceptMap.get(tkey) as MIRConceptTypeDecl;
            this.closeConceptDecl(ccdecl);

            ccdecl.invariants.forEach((inv) => cpt.invariants.push(inv));
            ccdecl.fieldMap.forEach((fd, name) => cpt.fieldMap.set(name, fd));
            ccdecl.vcallMap.forEach((vcall, vcname) => cpt.vcallMap.set(vcname, vcall));
        });

        cpt.memberFields.forEach((fd) => {
            if (fd.attributes.indexOf("abstract") === -1) {
                cpt.fieldMap.set(fd.name, fd);
            }
        });

        cpt.memberMethods.forEach((vm) => {
            if (vm.attributes.indexOf("abstract") === -1) {
                cpt.vcallMap.set(vm.vkey, vm);
            }
        });
    }

    closeEntityDecl(entity: MIREntityTypeDecl) {
        entity.provides.forEach((tkey) => {
            const ccdecl = this.conceptMap.get(tkey) as MIRConceptTypeDecl;
            this.closeConceptDecl(ccdecl);

            ccdecl.invariants.forEach((inv) => entity.invariants.push(inv));
            ccdecl.fieldMap.forEach((fd, name) => entity.fieldMap.set(name, fd));
            ccdecl.vcallMap.forEach((vcall, vcname) => entity.vcallMap.set(vcname, vcall));
        });

        entity.memberFields.forEach((fd) => {
            entity.fieldMap.set(fd.name, fd);
        });

        entity.memberMethods.forEach((vm) => {
            entity.vcallMap.set(vm.vkey, vm);
        });

        entity.fieldMap.forEach((v, f) => entity.fieldLayout.push(f));
        entity.fieldLayout.sort();
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

        const res = t1.options.every((t1opt) => t2.options.some((t2opt) => this.atomSubtypeOf(t1opt, t2opt)));

        memores.set(t2.trkey, res);
        return res;
    }
}

export {
    MIRFunctionParameter, MIRInvokeDecl,
    MIROOMemberDecl, MIRConstDecl, MIRStaticDecl, MIRFieldDecl, MIRMethodDecl,
    MIROOTypeDecl, MIRConceptTypeDecl, MIREntityTypeDecl,
    MIRNSMemberDecl, MIRGlobalDecl, MIRFunctionDecl,
    MIRType, MIRTypeOption, MIRNominalType, MIREntityType, MIRConceptType,
    MIRStructuralType, MIRTupleTypeEntry, MIRTupleType, MIRRecordTypeEntry, MIRRecordType, MIRFunctionTypeParam, MIRFunctionType,
    PackageConfig, MIRAssembly
};
