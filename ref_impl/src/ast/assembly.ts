//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ResolvedType, ResolvedRecordAtomType, ResolvedTupleAtomType, ResolvedTupleAtomTypeEntry, ResolvedRecordAtomTypeEntry, ResolvedFunctionAtomTypeParam, ResolvedFunctionAtomType, ResolvedAtomType, ResolvedConceptAtomTypeEntry, ResolvedConceptAtomType, ResolvedEntityAtomType } from "./resolved_type";
import { TemplateTypeSignature, NominalTypeSignature, TypeSignature, TupleTypeSignature, RecordTypeSignature, FunctionTypeSignature, IntersectionTypeSignature, UnionTypeSignature, ParseErrorTypeSignature, AutoTypeSignature, FunctionParameter } from "./type_signature";
import { Expression, BodyImplementation } from "./body";
import { SourceInfo } from "./parser";

class TemplateTermDecl {
    readonly isUnique: boolean;
    readonly name: string;
    readonly ttype: TypeSignature;

    constructor(isUnique: boolean, name: string, ttype: TypeSignature) {
        this.isUnique = isUnique;
        this.name = name;
        this.ttype = ttype;
    }
}

class TemplateTermRestriction {
    readonly name: string;
    readonly ttype: TypeSignature;

    constructor(name: string, ttype: TypeSignature) {
        this.name = name;
        this.ttype = ttype;
    }
}

class InvokeDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly terms: TemplateTermDecl[];
    readonly termRestrictions: TemplateTermRestriction[];

    readonly params: FunctionParameter[];
    readonly optRestName: string | undefined;
    readonly optRestType: TypeSignature | undefined;
    readonly resultType: TypeSignature;

    readonly preconditions: Expression[];
    readonly postconditions: Expression[];

    readonly isLambda: boolean;
    readonly captureSet: Set<string>;
    readonly body: BodyImplementation | undefined;

    constructor(sinfo: SourceInfo, srcFile: string, terms: TemplateTermDecl[], termRestrictions: TemplateTermRestriction[], params: FunctionParameter[], optRestName: string | undefined, optRestType: TypeSignature | undefined, resultType: TypeSignature, preconds: Expression[], postconds: Expression[], isLambda: boolean, captureSet: Set<string>, body: BodyImplementation | undefined) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

        this.terms = terms;
        this.termRestrictions = termRestrictions;

        this.params = params;
        this.optRestName = optRestName;
        this.optRestType = optRestType;
        this.resultType = resultType;

        this.preconditions = preconds;
        this.postconditions = postconds;

        this.isLambda = isLambda;
        this.captureSet = captureSet;
        this.body = body;
    }

    generateSig(): TypeSignature {
        return new FunctionTypeSignature([...this.params], this.optRestName, this.optRestType, this.resultType);
    }

    static createLambdaInvokeDecl(sinfo: SourceInfo, srcFile: string, params: FunctionParameter[], optRestName: string | undefined, optRestType: TypeSignature | undefined, resultType: TypeSignature, captureSet: Set<string>, body: BodyImplementation) {
        return new InvokeDecl(sinfo, srcFile, [], [], params, optRestName, optRestType, resultType, [], [], true, captureSet, body);
    }

    static createStaticInvokeDecl(sinfo: SourceInfo, srcFile: string, terms: TemplateTermDecl[], termRestrictions: TemplateTermRestriction[], params: FunctionParameter[], optRestName: string | undefined, optRestType: TypeSignature | undefined, resultType: TypeSignature, preconds: Expression[], postconds: Expression[], body: BodyImplementation | undefined) {
        return new InvokeDecl(sinfo, srcFile, terms, termRestrictions, params, optRestName, optRestType, resultType, preconds, postconds, false, new Set<string>(), body);
    }

    static createMemberInvokeDecl(sinfo: SourceInfo, srcFile: string, terms: TemplateTermDecl[], termRestrictions: TemplateTermRestriction[], params: FunctionParameter[], optRestName: string | undefined, optRestType: TypeSignature | undefined, resultType: TypeSignature, preconds: Expression[], postconds: Expression[], body: BodyImplementation | undefined) {
        return new InvokeDecl(sinfo, srcFile, terms, termRestrictions, params, optRestName, optRestType, resultType, preconds, postconds, false, new Set<string>(), body);
    }
}

interface OOMemberDecl {
    getName(): string;
}

class StaticMemberDecl implements OOMemberDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly name: string;

    readonly declaredType: TypeSignature;
    readonly value: Expression | undefined;

    constructor(srcInfo: SourceInfo, srcFile: string, attributes: string[], ns: string, name: string, dtype: TypeSignature, value: Expression | undefined) {
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.name = name;
        this.declaredType = dtype;
        this.value = value;
    }

    getName(): string {
        return this.name;
    }
}

class StaticFunctionDecl implements OOMemberDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly name: string;

    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, attributes: string[], name: string, invoke: InvokeDecl) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.name = name;

        this.invoke = invoke;
    }

    getName(): string {
        return this.name;
    }
}

class MemberFieldDecl implements OOMemberDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly name: string;

    readonly declaredType: TypeSignature;
    readonly value: Expression | undefined;

    constructor(srcInfo: SourceInfo, srcFile: string, attributes: string[], name: string, dtype: TypeSignature, value: Expression | undefined) {
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.name = name;
        this.declaredType = dtype;
        this.value = value;
    }

    getName(): string {
        return this.name;
    }
}

class MemberMethodDecl implements OOMemberDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly name: string;

    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, attributes: string[], name: string, invoke: InvokeDecl) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.name = name;
        this.invoke = invoke;
    }

    getName(): string {
        return this.name;
    }
}

class OOPTypeDecl {
    readonly srcFile: string;

    readonly attributes: string[];
    readonly ns: string;
    readonly name: string;

    readonly terms: TemplateTermDecl[];

    readonly provides: TypeSignature[];

    readonly invariants: Expression[];

    readonly staticMembers: Map<string, StaticMemberDecl>;
    readonly staticFunctions: Map<string, StaticFunctionDecl>;
    readonly memberFields: Map<string, MemberFieldDecl>;
    readonly memberMethods: Map<string, MemberMethodDecl>;

    constructor(srcFile: string, attributes: string[], ns: string, name: string, terms: TemplateTermDecl[], provides: TypeSignature[],
        invariants: Expression[],
        staticMembers: Map<string, StaticMemberDecl>, staticFunctions: Map<string, StaticFunctionDecl>,
        memberFields: Map<string, MemberFieldDecl>, memberMethods: Map<string, MemberMethodDecl>) {
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.ns = ns;
        this.name = name;
        this.terms = terms;
        this.provides = provides;
        this.invariants = invariants;
        this.staticMembers = staticMembers;
        this.staticFunctions = staticFunctions;
        this.memberFields = memberFields;
        this.memberMethods = memberMethods;
    }

    isTypeACollectionEntity(): boolean {
        if (this.ns !== "NSCore") {
            return false;
        }

        return this.name === "List" || this.name === "HashSet";
    }

    isTypeAMapEntity(): boolean {
        if (this.ns !== "NSCore") {
            return false;
        }

        return this.name === "HashMap";
    }

    static attributeSetContains(attr: string, attrSet: string[]): boolean {
        return attrSet.indexOf(attr) !== -1;
    }
}

class ConceptTypeDecl extends OOPTypeDecl {
    constructor(srcFile: string, attributes: string[], ns: string, name: string, terms: TemplateTermDecl[], provides: TypeSignature[],
        invariants: Expression[],
        staticMembers: Map<string, StaticMemberDecl>, staticFunctions: Map<string, StaticFunctionDecl>,
        memberFields: Map<string, MemberFieldDecl>, memberMethods: Map<string, MemberMethodDecl>) {
        super(srcFile, attributes, ns, name, terms, provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods);
    }
}

class EntityTypeDecl extends OOPTypeDecl {
    readonly isEnum: boolean;
    readonly isKey: boolean;

    constructor(srcFile: string, attributes: string[], ns: string, name: string, terms: TemplateTermDecl[], provides: TypeSignature[],
        invariants: Expression[],
        staticMembers: Map<string, StaticMemberDecl>, staticFunctions: Map<string, StaticFunctionDecl>,
        memberFields: Map<string, MemberFieldDecl>, memberMethods: Map<string, MemberMethodDecl>,
        isEnum: boolean, isKey: boolean) {
        super(srcFile, attributes, ns, name, terms, provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods);
        this.isEnum = isEnum;
        this.isKey = isKey;
    }
}

class NamespaceConstDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly ns: string;
    readonly name: string;

    readonly declaredType: TypeSignature;
    readonly value: Expression;

    constructor(srcInfo: SourceInfo, srcFile: string, attributes: string[], ns: string, name: string, dtype: TypeSignature, value: Expression) {
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;

        this.attributes = attributes;
        this.ns = ns;
        this.name = name;

        this.declaredType = dtype;
        this.value = value;
    }
}

class NamespaceFunctionDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;
    readonly attributes: string[];

    readonly ns: string;
    readonly name: string;

    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, attributes: string[], ns: string, name: string, invoke: InvokeDecl) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

        this.attributes = attributes;
        this.ns = ns;
        this.name = name;

        this.invoke = invoke;
    }
}

class NamespaceTypedef {
    readonly ns: string;
    readonly name: string;
    readonly terms: TemplateTermDecl[];
    readonly boundType: TypeSignature;

    constructor(ns: string, name: string, terms: TemplateTermDecl[], btype: TypeSignature) {
        this.ns = ns;
        this.name = name;
        this.terms = terms;
        this.boundType = btype;
    }
}

class NamespaceUsing {
    readonly fromNamespace: string;
    readonly names: string[];

    constructor(from: string, names: string[]) {
        this.fromNamespace = from;
        this.names = names;
    }
}

class NamespaceDeclaration {
    readonly ns: string;

    usings: NamespaceUsing[];
    declaredNames: Set<string>;

    typeDefs: Map<string, NamespaceTypedef>;
    consts: Map<string, NamespaceConstDecl>;
    functions: Map<string, NamespaceFunctionDecl>;
    concepts: Map<string, ConceptTypeDecl>;
    objects: Map<string, EntityTypeDecl>;

    constructor(ns: string) {
        this.ns = ns;
        this.usings = [];
        this.declaredNames = new Set<string>();

        this.typeDefs = new Map<string, NamespaceTypedef>();
        this.consts = new Map<string, NamespaceConstDecl>();
        this.functions = new Map<string, NamespaceFunctionDecl>();
        this.concepts = new Map<string, ConceptTypeDecl>();
        this.objects = new Map<string, EntityTypeDecl>();
    }

    checkUsingNameClash(names: string[]): boolean {
        return names.some((name) => this.usings.some((usedecl) => usedecl.names.indexOf(name) !== -1));
    }

    checkDeclNameClash(ns: string, name: string): boolean {
        const rname = ns + "::" + name;
        return this.typeDefs.has(rname) || this.consts.has(rname) || this.functions.has(rname) || this.concepts.has(rname) || this.objects.has(rname) || this.usings.some((usedecl) => usedecl.names.indexOf(name) !== -1);
    }
}

class OOMemberLookupInfo {
    readonly contiainingType: OOPTypeDecl;
    readonly decl: OOMemberDecl;
    readonly binds: Map<string, ResolvedType>;

    constructor(contiainingType: OOPTypeDecl, decl: OOMemberDecl, binds: Map<string, ResolvedType>) {
        this.contiainingType = contiainingType;
        this.decl = decl;
        this.binds = binds;
    }
}

class Assembly {
    private m_specialTypeMap: Map<string, ResolvedType> = new Map<string, ResolvedType>();
    private m_namespaceMap: Map<string, NamespaceDeclaration> = new Map<string, NamespaceDeclaration>();
    private m_conceptMap: Map<string, ConceptTypeDecl> = new Map<string, ConceptTypeDecl>();
    private m_objectMap: Map<string, EntityTypeDecl> = new Map<string, EntityTypeDecl>();

    private m_subtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();
    private m_atomSubtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();

    private resolveTemplateBinds(declterms: TemplateTermDecl[], giventerms: TypeSignature[], binds: Map<string, ResolvedType>): Map<string, ResolvedType> {
        const fullbinds = new Map<string, ResolvedType>();

        for (let i = 0; i < declterms.length; ++i) {
            fullbinds.set(declterms[i].name, this.normalizeType(giventerms[i], binds));
        }

        return fullbinds;
    }

    private normalizeType_Template(t: TemplateTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        return binds.has(t.name) ? binds.get(t.name) as ResolvedType : ResolvedType.createEmpty();
    }

    private normalizeType_Nominal(t: NominalTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const [aliasResolvedType, aliasResolvedBinds] = this.lookupTypeDef(t, binds);
        if (aliasResolvedType === undefined) {
            return ResolvedType.createEmpty();
        }
        else if (!(aliasResolvedType instanceof NominalTypeSignature)) {
            return this.normalizeType(aliasResolvedType, aliasResolvedBinds);
        }
        else {
            const fconcept = this.tryGetConceptTypeForFullyResolvedName(aliasResolvedType.nameSpace + "::" + aliasResolvedType.baseName);
            if (fconcept !== undefined) {
                if (fconcept.terms.length !== aliasResolvedType.terms.length) {
                    return ResolvedType.createEmpty();
                }

                return ResolvedType.createSingle(this.createConceptTypeAtom(fconcept, aliasResolvedType, aliasResolvedBinds));
            }

            const fobject = this.tryGetObjectTypeForFullyResolvedName(aliasResolvedType.nameSpace + "::" + aliasResolvedType.baseName);
            if (fobject !== undefined) {
                if (fobject.terms.length !== aliasResolvedType.terms.length) {
                    return ResolvedType.createEmpty();
                }

                return ResolvedType.createSingle(this.createObjectTypeAtom(fobject, aliasResolvedType, aliasResolvedBinds));
            }

            return ResolvedType.createEmpty();
        }
    }

    private normalizeType_Tuple(t: TupleTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const entries = t.entries.map((entry) => new ResolvedTupleAtomTypeEntry(this.normalizeType(entry[0], binds), entry[1]));
        if (entries.some((e) => e.type.isEmptyType())) {
            return ResolvedType.createEmpty();
        }

        return ResolvedType.createSingle(ResolvedTupleAtomType.create(t.isOpen, entries));
    }

    private normalizeType_Record(t: RecordTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        let seenNames = new Set<string>();
        let entries: ResolvedRecordAtomTypeEntry[] = [];
        for (let i = 0; i < t.entries.length; ++i) {
            if (seenNames.has(t.entries[i][0])) {
                return ResolvedType.createEmpty();
            }

            entries.push(new ResolvedRecordAtomTypeEntry(t.entries[i][0], this.normalizeType(t.entries[i][1], binds), t.entries[i][2]));
        }
        if (entries.some((e) => e.type.isEmptyType())) {
            return ResolvedType.createEmpty();
        }

        return ResolvedType.createSingle(ResolvedRecordAtomType.create(t.isOpen, entries));
    }

    private normalizeType_Function(t: FunctionTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const params = t.params.map((param) => new ResolvedFunctionAtomTypeParam(param.name, param.isOptional, this.normalizeType(param.type, binds)));
        const optRestParamType = (t.optRestParamType !== undefined) ? this.normalizeType(t.optRestParamType, binds) : undefined;
        const resType = this.normalizeType(t.resultType, binds);

        if (params.some((p) => p.type.isEmptyType()) || (optRestParamType !== undefined && optRestParamType.isEmptyType()) || resType.isEmptyType()) {
            return ResolvedType.createEmpty();
        }

        return ResolvedType.createSingle(ResolvedFunctionAtomType.create(params, t.optRestParamName, optRestParamType, resType));
    }

    private normalizeType_Intersection(t: IntersectionTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        if (t.types.some((opt) => this.normalizeType(opt, binds).isEmptyType())) {
            return ResolvedType.createEmpty();
        }

        const ntypes: ResolvedAtomType[][] = t.types.map((opt) => this.normalizeType(opt, binds).options);
        const flattened: ResolvedAtomType[] = ([] as ResolvedAtomType[]).concat(...ntypes);

        if (flattened.some((ttype) => !(ttype instanceof ResolvedConceptAtomType))) {
            return ResolvedType.createEmpty();
        }

        const ctypes = flattened.map((arg) => (arg as ResolvedConceptAtomType).conceptTypes);
        const itypes = (([] as ResolvedConceptAtomTypeEntry[]).concat(...ctypes)).sort((cte1, cte2) => cte1.idStr.localeCompare(cte2.idStr));

        //do a simplification based on A & B when A \Subtypeeq B is A
        let simplifiedTypes: ResolvedConceptAtomTypeEntry[] = [];
        for (let i = 0; i < itypes.length; ++i) {
            let docopy = true;
            for (let j = 0; j < itypes.length; ++j) {
                if (i === j) {
                    continue; //ignore check on same element
                }

                //if \exists a Tj s.t. Ti \Subtypeeq Tj then we discard Tj
                if (this.atomSubtypeOf(ResolvedConceptAtomType.create([itypes[j]]), ResolvedConceptAtomType.create([itypes[i]]))) {
                    docopy = (itypes[i].idStr === itypes[j].idStr) && i < j; //if same type only keep one copy
                    break;
                }
            }

            if (docopy) {
                simplifiedTypes.push(itypes[i]);
            }
        }

        if (simplifiedTypes.length === 0) {
            return ResolvedType.createEmpty();
        }

        return ResolvedType.createSingle(ResolvedConceptAtomType.create(simplifiedTypes));
    }

    private normalizeType_Union(t: UnionTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        if (t.types.some((opt) => this.normalizeType(opt, binds).isEmptyType())) {
            return ResolvedType.createEmpty();
        }

        const utypes = t.types.map((opt) => this.normalizeType(opt, binds));
        return this.normalizeUnionList(utypes);
    }

    private normalizeUnionList(types: ResolvedType[]): ResolvedType {
        //flatten any union types
        const ntypes: ResolvedAtomType[][] = types.map((opt) => opt.options);
        const flattened: ResolvedAtomType[] = ([] as ResolvedAtomType[]).concat(...ntypes);

        //check for Some | None and add Any if needed
        if (flattened.some((atom) => atom.idStr === "NSCore::None") && flattened.some((atom) => atom.idStr === "NSCore::Some")) {
            flattened.push(this.getSpecialAnyType().options[0]);
        }
        const utypes = flattened.sort((cte1, cte2) => cte1.idStr.localeCompare(cte2.idStr));

        //do a simplification based on A | B when A \Subtypeeq B is B
        let simplifiedTypes: ResolvedAtomType[] = [];
        for (let i = 0; i < utypes.length; ++i) {
            let docopy = true;
            for (let j = 0; j < utypes.length; ++j) {
                if (i === j) {
                    continue; //ignore check on same element
                }

                //if \exists a Tj s.t. Ti \Subtypeeq Tj then we discard Ti
                if (this.atomSubtypeOf(utypes[i], utypes[j])) {
                    docopy = (utypes[i].idStr === utypes[j].idStr) && i < j; //if same type only keep one copy
                    break;
                }
            }

            if (docopy) {
                simplifiedTypes.push(utypes[i]);
            }
        }

        return ResolvedType.create(simplifiedTypes);
    }

    private atomSubtypeOf_EntityEntity(t1: ResolvedEntityAtomType, t2: ResolvedEntityAtomType): boolean {
        if (t1.object.ns !== t2.object.ns || t1.object.name !== t2.object.name) {
            return false;
        }

        let allBindsOk = true;
        t1.binds.forEach((v, k) => { allBindsOk = allBindsOk && this.subtypeOf(v, t2.binds.get(k) as ResolvedType); });
        return allBindsOk;
    }

    private atomSubtypeOf_EntityConcept(t1: ResolvedEntityAtomType, t2: ResolvedConceptAtomType): boolean {
        const t2type = ResolvedType.createSingle(t2);
        return t1.object.provides.some((provide) => {
            const tt = this.normalizeType(provide, t1.binds);
            return !tt.isEmptyType() && this.subtypeOf(tt, t2type);
        });
    }

    private atomSubtypeOf_ConceptConcept(t1: ResolvedConceptAtomType, t2: ResolvedConceptAtomType): boolean {
        return t1.conceptTypes.every((c1t) => {
            return t2.conceptTypes.some((c2t) => {
                if (c1t.concept.ns === c2t.concept.ns && c1t.concept.name === c2t.concept.name) {
                    let allBindsOk = true;
                    c1t.binds.forEach((v, k) => { allBindsOk = allBindsOk && this.subtypeOf(v, c2t.binds.get(k) as ResolvedType); });
                    return allBindsOk;
                }

                const t2type = ResolvedType.createSingle(ResolvedConceptAtomType.create([c2t]));
                return c1t.concept.provides.some((provide) => {
                    const tt = this.normalizeType(provide, c1t.binds);
                    return !tt.isEmptyType() && this.subtypeOf(tt, t2type);
                });
            });
        });
    }

    private atomSubtypeOf_TupleTuple(t1: ResolvedTupleAtomType, t2: ResolvedTupleAtomType): boolean {
        //Then this is definitely not ok
        if (t1.isOpen && !t2.isOpen) {
            return false;
        }

        for (let i = 0; i < t1.types.length; ++i) {
            const t1e = t1.types[i];

            if (i >= t2.types.length) {
                if (!t2.isOpen) {
                    return false;
                }
            }
            else {
                const t2e = t2.types[i];
                if ((t1e.isOptional && !t2e.isOptional) || !this.subtypeOf(t1e.type, t2e.type)) {
                    return false;
                }
            }
        }

        //t2 has a required entry that is not required in t1
        if (t2.types.length > t1.types.length && t2.types.slice(t1.types.length).some((entry) => !entry.isOptional)) {
            return false;
        }

        return true;
    }

    private atomSubtypeOf_RecordRecord(t1: ResolvedRecordAtomType, t2: ResolvedRecordAtomType): boolean {
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

    private atomSubtypeOf_FunctionFunction(t1: ResolvedFunctionAtomType, t2: ResolvedFunctionAtomType): boolean {
        if (t2.params.length !== t1.params.length) {
            return false; //need to have the same number of parameters
        }

        if ((t2.optRestParamType !== undefined) !== (t1.optRestParamType !== undefined)) {
            return false; //should both have rest or not
        }

        if (t2.optRestParamType !== undefined && !this.subtypeOf(t2.optRestParamType, t1.optRestParamType as ResolvedType)) {
            return false; //variance
        }

        for (let i = 0; i < t2.params.length; ++i) {
            const t2p = t2.params[i];
            const t1p = t1.params[i];
            if ((t2p.isOptional !== t1p.isOptional) || !this.subtypeOf(t2p.type, t1p.type)) {
                return false;
            }

            //check that if t2p is named then t1p has the same name
            if (t2.params[i].name !== "_") {
                if (t1.params.length <= i || t2.params[i].name === t1.params[i].name) {
                    return false;
                }
            }
        }

        //co-variant is cool
        return this.subtypeOf(t1.resultType, t2.resultType);
    }

    private internSpecialConceptType(name: string, terms?: TypeSignature[], binds?: Map<string, ResolvedType>): ResolvedType {
        if (this.m_specialTypeMap.has("NSCore::" + name)) {
            return this.m_specialTypeMap.get("NSCore::" + name) as ResolvedType;
        }

        const rsig = new NominalTypeSignature("NSCore", name, terms || [] as TypeSignature[]);
        const tconcept = this.createConceptTypeAtom(this.tryGetConceptTypeForFullyResolvedName("NSCore::" + name) as ConceptTypeDecl, rsig, binds || new Map<string, ResolvedType>());
        const rtype = ResolvedType.createSingle(tconcept);
        this.m_specialTypeMap.set("NSCore::" + name, rtype);

        return rtype;
    }

    private internSpecialObjectType(name: string, terms?: TypeSignature[], binds?: Map<string, ResolvedType>): ResolvedType {
        if (this.m_specialTypeMap.has("NSCore::" + name)) {
            return this.m_specialTypeMap.get("NSCore::" + name) as ResolvedType;
        }

        const rsig = new NominalTypeSignature("NSCore", name, terms || [] as TypeSignature[]);
        const tobject = this.createObjectTypeAtom(this.tryGetObjectTypeForFullyResolvedName("NSCore::" + name) as EntityTypeDecl, rsig, binds || new Map<string, ResolvedType>());
        const rtype = ResolvedType.createSingle(tobject);
        this.m_specialTypeMap.set("NSCore::" + name, rtype);

        return rtype;
    }

    getSpecialAnyType(): ResolvedType { return this.internSpecialConceptType("Any"); }
    getSpecialNoneType(): ResolvedType { return this.internSpecialObjectType("None"); }
    getSpecialSomeType(): ResolvedType { return this.internSpecialConceptType("Some"); }
    getSpecialBoolType(): ResolvedType { return this.internSpecialObjectType("Bool"); }
    getSpecialIntType(): ResolvedType { return this.internSpecialObjectType("Int"); }
    getSpecialFloatType(): ResolvedType { return this.internSpecialObjectType("Float"); }
    getSpecialRegexType(): ResolvedType { return this.internSpecialObjectType("Regex"); }
    getSpecialStringType(): ResolvedType { return this.internSpecialObjectType("String", [new TemplateTypeSignature("T")], new Map<string, ResolvedType>().set("T", this.getSpecialAnyType())); }
    getSpecialGUIDType(): ResolvedType { return this.internSpecialObjectType("GUID"); }

    getSpecialTupleConceptType(): ResolvedType { return this.internSpecialConceptType("Tuple"); }
    getSpecialRecordConceptType(): ResolvedType { return this.internSpecialConceptType("Record"); }
    getSpecialFunctionConceptType(): ResolvedType { return this.internSpecialConceptType("Function"); }
    getSpecialObjectConceptType(): ResolvedType { return this.internSpecialConceptType("Object"); }
    getSpecialEnumType(): ResolvedType { return this.internSpecialConceptType("Enum"); }
    getSpecialCustomKeyType(): ResolvedType { return this.internSpecialConceptType("CustomKey"); }

    getSpecialParsableConcept(): ResolvedType { return this.internSpecialConceptType("Parsable"); }
    getSpecialKeyedConcept(): ResolvedType { return this.internSpecialConceptType("Keyed"); }

    ensureTupleStructuralRepresentation(atom: ResolvedAtomType): ResolvedTupleAtomType {
        return (atom instanceof ResolvedTupleAtomType) ? atom : ResolvedTupleAtomType.createGenericOpen();
    }

    ensureRecordStructuralRepresentation(atom: ResolvedAtomType): ResolvedRecordAtomType {
        return (atom instanceof ResolvedRecordAtomType) ? atom : ResolvedRecordAtomType.createGenericOpen();
    }

    ensureNominalRepresentation(t: ResolvedType): ResolvedType {
        const opts = t.options.map((opt) => {
            if (opt instanceof ResolvedTupleAtomType) {
                return this.getSpecialTupleConceptType();
            }
            else if (opt instanceof ResolvedRecordAtomType) {
                return this.getSpecialRecordConceptType();
            }
            else if (opt instanceof ResolvedFunctionAtomType) {
                return this.getSpecialFunctionConceptType();
            }
            else {
                return ResolvedType.createSingle(opt);
            }
        });

        return this.typeUnion(opts);
    }

    tryGetConceptTypeForFullyResolvedName(name: string): ConceptTypeDecl | undefined {
        return this.m_conceptMap.get(name);
    }

    tryGetObjectTypeForFullyResolvedName(name: string): EntityTypeDecl | undefined {
        return this.m_objectMap.get(name);
    }

    hasNamespace(ns: string): boolean {
        return this.m_namespaceMap.has(ns);
    }

    getNamespace(ns: string): NamespaceDeclaration {
        return this.m_namespaceMap.get(ns) as NamespaceDeclaration;
    }

    ensureNamespace(ns: string): NamespaceDeclaration {
        if (!this.hasNamespace(ns)) {
            this.m_namespaceMap.set(ns, new NamespaceDeclaration(ns));
        }

        return this.getNamespace(ns);
    }

    getNamespaces(): NamespaceDeclaration[] {
        let decls: NamespaceDeclaration[] = [];
        this.m_namespaceMap.forEach((v, k) => {
            decls.push(v);
        });
        return decls;
    }

    addConceptDecl(resolvedName: string, concept: ConceptTypeDecl) {
        this.m_conceptMap.set(resolvedName, concept);
    }

    addObjectDecl(resolvedName: string, object: EntityTypeDecl) {
        this.m_objectMap.set(resolvedName, object);
    }

    ////
    //Type representation, normalization, and operations
    lookupTypeDef(t: NominalTypeSignature, binds: Map<string, ResolvedType>): [TypeSignature | undefined, Map<string, ResolvedType>] {
        if (!this.hasNamespace(t.nameSpace)) {
            return [undefined, new Map<string, ResolvedType>()];
        }

        const lname = t.nameSpace + "::" + t.baseName;
        const nsd = this.getNamespace(t.nameSpace);
        if (!nsd.typeDefs.has(lname)) {
            if (t.nameSpace === "NSCore" && t.baseName === "String" && t.terms.length === 0) {
                return [new NominalTypeSignature(t.nameSpace, t.baseName, [new TemplateTypeSignature("T")]), new Map<string, ResolvedType>(binds).set("T", this.getSpecialAnyType())];
            }
            else {
                return [t, new Map<string, ResolvedType>(binds)];
            }
        }

        //compute the bindings to use when resolving the RHS of the typedef alias
        const typealias = nsd.typeDefs.get(lname) as NamespaceTypedef;
        const updatedbinds = this.resolveTemplateBinds(typealias.terms, t.terms, binds);

        if (typealias.boundType instanceof NominalTypeSignature) {
            return this.lookupTypeDef(typealias.boundType, updatedbinds);
        }
        else {
            return [typealias.boundType, updatedbinds];
        }
    }

    createConceptTypeAtom(concept: ConceptTypeDecl, t: NominalTypeSignature, binds: Map<string, ResolvedType>): ResolvedConceptAtomType {
        const fullbinds = this.resolveTemplateBinds(concept.terms, t.terms, binds);
        return ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(concept, fullbinds)]);
    }

    createObjectTypeAtom(object: EntityTypeDecl, t: NominalTypeSignature, binds: Map<string, ResolvedType>): ResolvedEntityAtomType {
        const fullbinds = this.resolveTemplateBinds(object.terms, t.terms, binds);
        return ResolvedEntityAtomType.create(object, fullbinds);
    }

    getAllOOFields(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, fmap?: Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]>): Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]> {
        let declfields = fmap || new Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]>();
        ooptype.memberFields.forEach((mf, name) => {
            if (!OOPTypeDecl.attributeSetContains("abstract", mf.attributes) && !declfields.has(name)) {
                declfields.set(name, [ooptype, mf, binds]);
            }
        });

        ooptype.provides.forEach((provide) => {
            const tt = this.normalizeType(provide, binds);
            (tt.options[0] as ResolvedConceptAtomType).conceptTypes.forEach((concept) => {
                declfields = this.getAllOOFields(concept.concept, concept.binds, declfields);
            });
        });

        return declfields;
    }

    getAllOOInvariants(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, invs?: [Expression, Map<string, ResolvedType>][]): [Expression, Map<string, ResolvedType>][] {
        let declinvs: [Expression, Map<string, ResolvedType>][] = invs || [];
        ooptype.invariants.forEach((inv) => {
            declinvs.push([inv, binds]);
        });

        ooptype.provides.forEach((provide) => {
            const tt = this.normalizeType(provide, binds);
            (tt.options[0] as ResolvedConceptAtomType).conceptTypes.forEach((concept) => {
                declinvs = this.getAllOOInvariants(concept.concept, concept.binds, declinvs);
            });
        });

        return declinvs;
    }

    private tryGetOOMemberDeclThis(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, kind: "const" | "static" | "field" | "method", search: string): OOMemberLookupInfo | undefined {
        let decl: OOMemberDecl | undefined = undefined;
        if (kind === "const") {
            decl = ooptype.staticMembers.get(search);
        }
        else if (kind === "static") {
            decl = ooptype.staticFunctions.get(search);
        }
        else if (kind === "field") {
            decl = ooptype.memberFields.get(search);
        }
        else {
            decl = ooptype.memberMethods.get(search);
        }

        if (decl === undefined) {
            return undefined;
        }
        else {
            return new OOMemberLookupInfo(ooptype, decl, binds);
        }
    }

    private tryGetOOMemberDeclParent(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, kind: "const" | "static" | "field" | "method", search: string): OOMemberLookupInfo | undefined {
        for (let i = 0; i < ooptype.provides.length; ++i) {
            const tt = (this.normalizeType(ooptype.provides[i], binds).options[0] as ResolvedConceptAtomType).conceptTypes[0];
            const res = this.tryGetOOMemberDeclThis(tt.concept, tt.binds, kind, search) || this.tryGetOOMemberDeclParent(tt.concept, tt.binds, kind, search);
            if (res !== undefined) {
                return res;
            }
        }

        return undefined;
    }

    private tryGetOOMemberRootDeclarationOptions(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, kind: "const" | "static" | "field" | "method", search: string): OOMemberLookupInfo[] | undefined {
        const tdecl = this.tryGetOOMemberDeclThis(ooptype, binds, kind, search);
        const pdecl = this.tryGetOOMemberDeclParent(ooptype, binds, kind, search);
        if (tdecl === undefined && pdecl === undefined) {
            return undefined;
        }
        else if (tdecl !== undefined && pdecl === undefined) {
            return [tdecl];
        }
        else {
            let dopts: OOMemberLookupInfo[] = [];

            for (let i = 0; i < ooptype.provides.length; ++i) {
                const tt = (this.normalizeType(ooptype.provides[i], binds).options[0] as ResolvedConceptAtomType).conceptTypes[0];
                const copts = this.tryGetOOMemberRootDeclarationOptions(tt.concept, tt.binds, kind, search);
                if (copts !== undefined) {
                    dopts = dopts.concat(copts);
                }
            }

            return dopts;
        }
    }

    private ensureSingleDecl(opts: OOMemberLookupInfo[]): OOMemberLookupInfo | undefined {
        if (opts.length === 0) {
            return undefined;
        }
        else if (opts.length === 1) {
            return opts[0];
        }
        else {
            const opt1 = opts[0];
            const allSame = opts.every((opt) => {
                if (opt1.contiainingType.ns !== opt.contiainingType.ns || opt1.contiainingType.name !== opt.contiainingType.name) {
                    return false;
                }

                if (opt1.binds.size !== opt.binds.size) {
                    return false;
                }

                let bindsok = true;
                opt1.binds.forEach((v, k) => {
                    bindsok = bindsok && opt.binds.has(k) && v.idStr === (opt.binds.get(k) as ResolvedType).idStr;
                });

                return bindsok;
            });

            return allSame ? opt1 : undefined;
        }
    }

    tryGetOOMemberDeclUnique(tt: ResolvedType, kind: "const" | "static" | "field" | "method", search: string): OOMemberLookupInfo | undefined {
        const atom = ResolvedType.tryGetOOTypeInfo(this.ensureNominalRepresentation(tt));
        if (atom === undefined) {
            return undefined;
        }

        if (atom instanceof ResolvedEntityAtomType) {
            return this.tryGetOOMemberDeclThis(atom.object, atom.binds, kind, search) || this.tryGetOOMemberDeclParent(atom.object, atom.binds, kind, search);
        }
        else {
            const opts = atom.conceptTypes.map((opt) => this.tryGetOOMemberDeclThis(opt.concept, opt.binds, kind, search) || this.tryGetOOMemberDeclParent(opt.concept, opt.binds, kind, search));
            return this.ensureSingleDecl(opts.filter((opt) => opt !== undefined) as OOMemberLookupInfo[]);
        }
    }

    tryGetOOMemberDeclOptions(tt: ResolvedType, kind: "const" | "static" | "field" | "method", search: string): { decls: OOMemberLookupInfo[] | undefined, root: OOMemberLookupInfo | undefined } {
        const decls = this.ensureNominalRepresentation(tt).options.map((atom) => this.tryGetOOMemberDeclUnique(ResolvedType.createSingle(atom), kind, search));
        if (decls.some((opt) => opt === undefined)) {
            return { decls: undefined, root: undefined };
        }

        const ropts = (decls as OOMemberLookupInfo[]).map((info) => this.tryGetOOMemberRootDeclarationOptions(info.contiainingType, info.binds, kind, search) as OOMemberLookupInfo[]);
        const roots = ([] as OOMemberLookupInfo[]).concat(...ropts);
        return { decls: decls as OOMemberLookupInfo[], root: this.ensureSingleDecl(roots) };
    }

    resolveBindsForCall(declterms: TemplateTermDecl[], giventerms: TypeSignature[], implicitBinds: Map<string, ResolvedType>, callBinds: Map<string, ResolvedType>): Map<string, ResolvedType> | undefined {
        let fullbinds = new Map<string, ResolvedType>();
        implicitBinds.forEach((v, k) => {
            fullbinds.set(k, v);
        });

        //compute the bindings to use when resolving the RHS of the typedef alias
        for (let i = 0; i < declterms.length; ++i) {
            fullbinds.set(declterms[i].name, this.normalizeType(giventerms[i], callBinds));
        }

        return fullbinds;
    }

    normalizeType(t: TypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        if (t instanceof ParseErrorTypeSignature || t instanceof AutoTypeSignature) {
            return ResolvedType.createEmpty();
        }
        else if (t instanceof TemplateTypeSignature) {
            return this.normalizeType_Template(t as TemplateTypeSignature, binds);
        }
        else if (t instanceof NominalTypeSignature) {
            return this.normalizeType_Nominal(t as NominalTypeSignature, binds);
        }
        else if (t instanceof TupleTypeSignature) {
            return this.normalizeType_Tuple(t as TupleTypeSignature, binds);
        }
        else if (t instanceof RecordTypeSignature) {
            return this.normalizeType_Record(t as RecordTypeSignature, binds);
        }
        else if (t instanceof FunctionTypeSignature) {
            return this.normalizeType_Function(t as FunctionTypeSignature, binds);
        }
        else if (t instanceof IntersectionTypeSignature) {
            return this.normalizeType_Intersection(t as IntersectionTypeSignature, binds);
        }
        else {
            return this.normalizeType_Union(t as UnionTypeSignature, binds);
        }
    }

    normalizeToTupleRepresentation(t: ResolvedAtomType): ResolvedTupleAtomType {
        if (t.idStr === "NSCore::Tuple") {
            return ResolvedTupleAtomType.createGenericOpen();
        }
        else {
            return t as ResolvedTupleAtomType;
        }
    }

    normalizeToRecordRepresentation(t: ResolvedAtomType): ResolvedRecordAtomType {
        if (t.idStr === "NSCore::Record") {
            return ResolvedRecordAtomType.createGenericOpen();
        }
        else {
            return t as ResolvedRecordAtomType;
        }
    }

    normalizeToNominalRepresentation(t: ResolvedAtomType): ResolvedAtomType {
        if (t instanceof ResolvedTupleAtomType) {
            return this.getSpecialTupleConceptType();
        }
        else if (t instanceof ResolvedRecordAtomType) {
            return this.getSpecialRecordConceptType();
        }
        else if (t instanceof ResolvedFunctionAtomType) {
            return this.getSpecialFunctionConceptType();
        }
        else {
            return t;
        }
    }

    computeUnifiedFunctionType(funcs: ResolvedAtomType[], rootSig?: ResolvedFunctionAtomType): ResolvedFunctionAtomType | undefined {
        if (funcs.length === 0) {
            return undefined;
        }

        //if it is not limited to NSCore::Function
        if (funcs.some((atom) => atom instanceof ResolvedConceptAtomType)) {
            return undefined;
        }

        const fatoms = funcs as ResolvedFunctionAtomType[];
        if (fatoms.length === 1) {
            return fatoms[0];
        }
        else if (rootSig !== undefined) {
            if (funcs.some((ft) => !this.atomSubtypeOf_FunctionFunction(ft as ResolvedFunctionAtomType, rootSig))) {
                return undefined;
            }
            return rootSig;
        }
        else {
            //compute an approximate function type that we use for emit generation
            const ftypes = funcs.map((ft) => ft as ResolvedFunctionAtomType);

            let params: ResolvedFunctionAtomTypeParam[] = [];
            const minp = Math.min(...ftypes.map((ft) => ft.params.length));
            for (let i = 0; i < minp; ++i) {
                const allreq = ftypes.every((ft) => !ft.params[i].isOptional);

                let uniq = "_";
                let uniqok = true;
                ftypes.forEach((ft) => {
                    if (ft.params[i].name !== "_") {
                        uniqok = uniqok && (uniq === "_" || uniq === ft.params[i].name);
                        uniq = ft.params[i].name;
                    }
                });
                if (!uniqok) {
                    return undefined; //need to have same names in same positions in sig
                }

                //don't care about exact type since we will check the real options at call site
                params.push(new ResolvedFunctionAtomTypeParam(uniq, allreq, this.getSpecialAnyType()));
            }

            const allRest = ftypes.every((ft) => ft.optRestParamName !== undefined);
            const allFixed = ftypes.every((ft) => ft.optRestParamName === undefined);
            if (!allRest && !allFixed) {
                return undefined; //must all agree on rest vs fixed params
            }

            let restname = allRest ? "_" : undefined;
            let resttype: ResolvedType | undefined =  ftypes[0].optRestParamType;
            if (allRest) {
                let restok = true;
                ftypes.forEach((ft) => {
                    if (ft.optRestParamName !== "_") {
                        restok = restok && (restname === "_");
                        restok = restok && ((ft.optRestParamType as ResolvedType).idStr === (ft.optRestParamType as ResolvedType).idStr);

                        restname = ft.optRestParamName;
                    }
                });
                if (!restok) {
                    return undefined; //must agree on rest name and type
                }
            }

            return ResolvedFunctionAtomType.create(params, restname, resttype, this.getSpecialAnyType());
        }
    }

    restrictNone(from: ResolvedType): ResolvedType {
        const hasany = from.options.some((atom) => ResolvedType.createSingle(atom).isAnyType());
        const hasnone = from.options.some((atom) => ResolvedType.createSingle(atom).isNoneType());

        return (hasany || hasnone) ? this.getSpecialNoneType() : ResolvedType.createEmpty();
    }

    restrictSome(from: ResolvedType): ResolvedType {
        const hasany = from.options.some((atom) => ResolvedType.createSingle(atom).isAnyType());
        const sometypes = from.options.filter((atom) => this.subtypeOf(ResolvedType.createSingle(atom), this.getSpecialSomeType()));
        if (hasany) {
            return this.getSpecialSomeType();
        }
        else if (sometypes.length !== 0) {
            return ResolvedType.create(sometypes);
        }
        else {
            return ResolvedType.createEmpty();
        }
    }

    restrictT(from: ResolvedType, t: ResolvedType): ResolvedType {
        if (t.isNoneType()) {
            return this.restrictNone(from);
        }
        else if (t.isSomeType()) {
            return this.restrictSome(from);
        }
        else {
            return t;
        }
    }

    restrictNotT(from: ResolvedType, t: ResolvedType): ResolvedType {
        if (t.isNoneType()) {
            return this.restrictSome(from);
        }
        else if (t.isSomeType()) {
            return this.restrictNone(from);
        }
        else {
            const notttypes = from.options.filter((atom) => !this.subtypeOf(ResolvedType.createSingle(atom), t));
            return notttypes.length !== 0 ? ResolvedType.create(notttypes) : ResolvedType.createEmpty();
        }
    }

    typeUnion(types: ResolvedType[]): ResolvedType {
        return this.normalizeUnionList(types);
    }

    atomSubtypeOf(t1: ResolvedAtomType, t2: ResolvedAtomType): boolean {
        let memores = this.m_atomSubtypeRelationMemo.get(t1.idStr);
        if (memores === undefined) {
            this.m_atomSubtypeRelationMemo.set(t1.idStr, new Map<string, boolean>());
            memores = this.m_atomSubtypeRelationMemo.get(t1.idStr) as Map<string, boolean>;
        }

        let memoval = memores.get(t2.idStr);
        if (memoval !== undefined) {
            return memoval;
        }

        let res = false;

        if (t1.idStr === t2.idStr) {
            res = true;
        }
        else if (t1 instanceof ResolvedConceptAtomType && t2 instanceof ResolvedConceptAtomType) {
            res = this.atomSubtypeOf_ConceptConcept(t1, t2);
        }
        else if (t1 instanceof ResolvedConceptAtomType) {
            //res stays false
        }
        else if (t2 instanceof ResolvedConceptAtomType) {
            if (t1 instanceof ResolvedEntityAtomType) {
                res = this.atomSubtypeOf_EntityConcept(t1, t2 as ResolvedConceptAtomType);
            }
            else if (t1 instanceof ResolvedTupleAtomType) {
                res = this.atomSubtypeOf_ConceptConcept(this.getSpecialTupleConceptType().options[0] as ResolvedConceptAtomType, t2 as ResolvedConceptAtomType);
            }
            else if (t1 instanceof ResolvedRecordAtomType) {
                res = this.atomSubtypeOf_ConceptConcept(this.getSpecialRecordConceptType().options[0] as ResolvedConceptAtomType, t2 as ResolvedConceptAtomType);
            }
            else {
                res = this.atomSubtypeOf_ConceptConcept(this.getSpecialFunctionConceptType().options[0] as ResolvedConceptAtomType, t2 as ResolvedConceptAtomType);
            }
        }
        else {
            if (t1 instanceof ResolvedEntityAtomType && t2 instanceof ResolvedEntityAtomType) {
                res = this.atomSubtypeOf_EntityEntity(t1, t2);
            }
            else if (t1 instanceof ResolvedTupleAtomType && t2 instanceof ResolvedTupleAtomType) {
                res = this.atomSubtypeOf_TupleTuple(t1, t2);
            }
            else if (t1 instanceof ResolvedRecordAtomType && t2 instanceof ResolvedRecordAtomType) {
                res = this.atomSubtypeOf_RecordRecord(t1, t2);
            }
            else if (t1 instanceof ResolvedFunctionAtomType && t2 instanceof ResolvedFunctionAtomType) {
                res = this.atomSubtypeOf_FunctionFunction(t1, t2);
            }
            else {
                //fall-through
            }
        }

        memores.set(t2.idStr, res);
        return res;
    }

    subtypeOf(t1: ResolvedType, t2: ResolvedType): boolean {
        let memores = this.m_subtypeRelationMemo.get(t1.idStr);
        if (memores === undefined) {
            this.m_subtypeRelationMemo.set(t1.idStr, new Map<string, boolean>());
            memores = this.m_subtypeRelationMemo.get(t1.idStr) as Map<string, boolean>;
        }

        let memoval = memores.get(t2.idStr);
        if (memoval !== undefined) {
            return memoval;
        }

        const res = t1.options.every((t1opt) => t2.options.some((t2opt) => this.atomSubtypeOf(t1opt, t2opt)));

        memores.set(t2.idStr, res);
        return res;
    }
}

export {
    TemplateTermDecl, TemplateTermRestriction, InvokeDecl,
    OOMemberDecl, StaticMemberDecl, StaticFunctionDecl, MemberFieldDecl, MemberMethodDecl, OOPTypeDecl, ConceptTypeDecl, EntityTypeDecl,
    NamespaceConstDecl, NamespaceFunctionDecl, NamespaceTypedef, NamespaceUsing, NamespaceDeclaration,
    OOMemberLookupInfo, Assembly
};
