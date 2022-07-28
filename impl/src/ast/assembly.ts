//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ResolvedType, ResolvedRecordAtomType, ResolvedTupleAtomType, ResolvedAtomType, ResolvedFunctionTypeParam, ResolvedFunctionType, ResolvedConceptAtomTypeEntry, ResolvedConceptAtomType, ResolvedEntityAtomType, ResolvedEphemeralListType, ResolvedTemplateUnifyType } from "./resolved_type";
import { TemplateTypeSignature, NominalTypeSignature, TypeSignature, TupleTypeSignature, RecordTypeSignature, FunctionTypeSignature, UnionTypeSignature, ParseErrorTypeSignature, AutoTypeSignature, FunctionParameter, ProjectTypeSignature, EphemeralListTypeSignature, PlusTypeSignature, AndTypeSignature } from "./type_signature";
import { Expression, BodyImplementation, LiteralIntegralExpression, LiteralFloatPointExpression, LiteralRationalExpression, AccessStaticFieldExpression, AccessNamespaceConstantExpression, ConstantExpressionValue, LiteralNumberinoExpression, LiteralTypedStringExpression, LiteralTypedPrimitiveConstructorExpression, LiteralNoneExpression, LiteralNothingExpression, LiteralBoolExpression, LiteralStringExpression } from "./body";
import { SourceInfo } from "./parser";

import * as assert from "assert";
import { BSQRegex } from "./bsqregex";

enum BuildApplicationMode {
    Executable,
    FunctionalizedExecutable,
    ModelChecker,
    TypeChecker
}

type BuildLevel = "doc" | "spec" | "debug" | "test" | "release";

function isBuildLevelEnabled(check: BuildLevel, enabled: BuildLevel): boolean {
    if(check === "doc") {
        return false;
    }

    if(enabled === "spec") {
        return true;
    }
    else if(enabled === "debug") {
        return check === "debug" || check === "test" || check === "release";
    }
    else if(enabled === "test") {
        return check === "test" || check === "release";
    }
    else {
        return check === "release";
    }
}

class TemplateTermDecl {
    readonly name: string;
    readonly isunique: boolean;
    readonly isgrounded: boolean;
    readonly tconstraint: TypeSignature;
    readonly isInfer: boolean;
    readonly defaultType: TypeSignature | undefined;

    constructor(name: string, isunique: boolean, isgrounded: boolean, tconstraint: TypeSignature, isinfer: boolean, defaulttype: TypeSignature | undefined) {
        this.name = name;
        this.isunique = isunique;
        this.isgrounded = isgrounded;
        this.tconstraint = tconstraint;
        this.isInfer = isinfer;
        this.defaultType = defaulttype;
    }
}

class TemplateTypeRestriction {
    readonly t: TypeSignature;
    readonly isunique: boolean;
    readonly isgrounded: boolean;
    readonly tconstraint: TypeSignature;

    constructor(t: TypeSignature, isunique: boolean, isgrounded: boolean, tconstraint: TypeSignature) {
        this.t = t;
        this.isunique = isunique;
        this.isgrounded = isgrounded;
        this.tconstraint = tconstraint;
    }
}

class TypeConditionRestriction {
    readonly constraints: TemplateTypeRestriction[];

    constructor(constraints: TemplateTypeRestriction[]) {
        this.constraints = constraints;
    }
}

class PreConditionDecl {
    readonly sinfo: SourceInfo;
    readonly isvalidate: boolean;
    readonly level: BuildLevel;
    readonly exp: Expression;
    readonly err: Expression | undefined;

    constructor(sinfo: SourceInfo, isvalidate: boolean, level: BuildLevel, exp: Expression, err: Expression | undefined) {
        this.sinfo = sinfo;
        this.isvalidate = isvalidate;
        this.level = level;
        this.exp = exp;
        this.err = err;
    }
}

class PostConditionDecl {
    readonly sinfo: SourceInfo;
    readonly level: BuildLevel;
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, level: BuildLevel, exp: Expression) {
        this.sinfo = sinfo;
        this.level = level;
        this.exp = exp;
    }
}

class InvariantDecl {
    readonly sinfo: SourceInfo;
    readonly level: BuildLevel;
    readonly exp: ConstantExpressionValue;

    constructor(sinfo: SourceInfo, level: BuildLevel, exp: ConstantExpressionValue) {
        this.sinfo = sinfo;
        this.level = level;
        this.exp = exp;
    }
}

class ValidateDecl {
    readonly sinfo: SourceInfo;
    readonly exp: ConstantExpressionValue;

    constructor(sinfo: SourceInfo, exp: ConstantExpressionValue) {
        this.sinfo = sinfo;
        this.exp = exp;
    }
}

class InvokeDecl {
    readonly namespace: string;
    readonly startSourceLocation: SourceInfo;
    readonly endSourceLocation: SourceInfo;
    readonly srcFile: string;
    readonly bodyID: string;

    readonly attributes: string[];
    readonly recursive: "yes" | "no" | "cond";

    readonly terms: TemplateTermDecl[];
    readonly termRestrictions: TypeConditionRestriction | undefined;

    readonly params: FunctionParameter[];
    readonly optRestName: string | undefined;
    readonly optRestType: TypeSignature | undefined;

    readonly resultType: TypeSignature;

    readonly preconditions: PreConditionDecl[];
    readonly postconditions: PostConditionDecl[];

    readonly isPCodeFn: boolean;
    readonly isPCodePred: boolean;
    readonly captureSet: Set<string>;
    readonly body: BodyImplementation | undefined;

    constructor(ns: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, bodyID: string, srcFile: string, attributes: string[], recursive: "yes" | "no" | "cond", terms: TemplateTermDecl[], termRestrictions: TypeConditionRestriction | undefined, params: FunctionParameter[], optRestName: string | undefined, optRestType: TypeSignature | undefined, resultType: TypeSignature, preconds: PreConditionDecl[], postconds: PostConditionDecl[], isPCodeFn: boolean, isPCodePred: boolean, captureSet: Set<string>, body: BodyImplementation | undefined) {
        this.namespace = ns;
        this.startSourceLocation = sinfoStart;
        this.endSourceLocation = sinfoEnd;
        this.srcFile = srcFile;
        this.bodyID = bodyID;

        this.attributes = attributes;
        this.recursive = recursive;

        this.terms = terms;
        this.termRestrictions = termRestrictions;

        this.params = params;
        this.optRestName = optRestName;
        this.optRestType = optRestType;

        this.resultType = resultType;

        this.preconditions = preconds;
        this.postconditions = postconds;

        this.isPCodeFn = isPCodeFn;
        this.isPCodePred = isPCodePred;
        this.captureSet = captureSet;
        this.body = body;
    }

    generateSig(): TypeSignature {
        return new FunctionTypeSignature(this.recursive, [...this.params], this.optRestName, this.optRestType, this.resultType, this.isPCodePred);
    }

    static createPCodeInvokeDecl(namespce: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, bodyID: string, srcFile: string, attributes: string[], recursive: "yes" | "no" | "cond", params: FunctionParameter[], optRestName: string | undefined, optRestType: TypeSignature | undefined, resultInfo: TypeSignature, captureSet: Set<string>, body: BodyImplementation, isPCodeFn: boolean, isPCodePred: boolean) {
        return new InvokeDecl(namespce, sinfoStart, sinfoEnd, bodyID, srcFile, attributes, recursive, [], undefined, params, optRestName, optRestType, resultInfo, [], [], isPCodeFn, isPCodePred, captureSet, body);
    }

    static createStandardInvokeDecl(namespace: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, bodyID: string, srcFile: string, attributes: string[], recursive: "yes" | "no" | "cond", terms: TemplateTermDecl[], termRestrictions: TypeConditionRestriction | undefined, params: FunctionParameter[], optRestName: string | undefined, optRestType: TypeSignature | undefined, resultInfo: TypeSignature, preconds: PreConditionDecl[], postconds: PostConditionDecl[], body: BodyImplementation | undefined) {
        return new InvokeDecl(namespace, sinfoStart, sinfoEnd, bodyID, srcFile, attributes, recursive, terms, termRestrictions, params, optRestName, optRestType, resultInfo, preconds, postconds, false, false, new Set<string>(), body);
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
    readonly value: ConstantExpressionValue | undefined;

    constructor(srcInfo: SourceInfo, srcFile: string, attributes: string[], name: string, dtype: TypeSignature, value: ConstantExpressionValue | undefined) {
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

    readonly name: string;

    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, name: string, invoke: InvokeDecl) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;
        this.name = name;

        this.invoke = invoke;
    }

    getName(): string {
        return this.name;
    }
}

class StaticOperatorDecl implements OOMemberDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly isPrefix: boolean;
    readonly isInfix: boolean;
    readonly isDynamic: boolean;
    readonly name: string;

    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, name: string, invoke: InvokeDecl) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;
        this.isPrefix = invoke.attributes.includes("prefix");
        this.isInfix = invoke.attributes.includes("infix");
        this.isDynamic = invoke.attributes.includes("dynamic");
        this.name = name;

        this.invoke = invoke;
    }

    getName(): string {
        return this.name;
    }

    doesKindTagMatch(tag: "prefix" | "infix" | "std"): boolean {
        return (tag === "prefix" && this.isPrefix) || (tag === "infix" && this.isInfix) || (tag === "std" && !this.isPrefix && !this.isInfix);
    }
}

class MemberFieldDecl implements OOMemberDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly name: string;

    readonly declaredType: TypeSignature;
    readonly value: ConstantExpressionValue | undefined;

    constructor(srcInfo: SourceInfo, srcFile: string, attributes: string[], name: string, dtype: TypeSignature, value: ConstantExpressionValue | undefined) {
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

    readonly name: string;
    readonly refRcvr: boolean;

    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, name: string, refrcvr: boolean, invoke: InvokeDecl) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;
        this.refRcvr = refrcvr;
        this.name = name;
        this.invoke = invoke;
    }

    getName(): string {
        return this.name;
    }
}

class OOPTypeDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly ns: string;
    readonly name: string;

    readonly terms: TemplateTermDecl[];

    readonly provides: [TypeSignature, TypeConditionRestriction | undefined][];

    readonly invariants: InvariantDecl[];
    readonly validates: ValidateDecl[];

    readonly staticMembers: StaticMemberDecl[];
    readonly staticFunctions: StaticFunctionDecl[];
    readonly staticOperators: StaticOperatorDecl[];
    readonly memberFields: MemberFieldDecl[];
    readonly memberMethods: MemberMethodDecl[];

    readonly nestedEntityDecls: Map<string, EntityTypeDecl>;

    constructor(sourceLocation: SourceInfo, srcFile: string, attributes: string[], ns: string, name: string, terms: TemplateTermDecl[], provides: [TypeSignature, TypeConditionRestriction | undefined][],
        invariants: InvariantDecl[], validates: ValidateDecl[],
        staticMembers: StaticMemberDecl[], staticFunctions: StaticFunctionDecl[], staticOperators: StaticOperatorDecl[],
        memberFields: MemberFieldDecl[], memberMethods: MemberMethodDecl[],
        nestedEntityDecls: Map<string, EntityTypeDecl>) {
        this.sourceLocation = sourceLocation;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.ns = ns;
        this.name = name;
        this.terms = terms;
        this.provides = provides;
        this.invariants = invariants;
        this.validates = validates;
        this.staticMembers = staticMembers;
        this.staticFunctions = staticFunctions;
        this.staticOperators = staticOperators;
        this.memberFields = memberFields;
        this.memberMethods = memberMethods;
        this.nestedEntityDecls = nestedEntityDecls;
    }

    isTypeAnExpandoableCollection(): boolean {
        return ["__list_type", "__stack_type", "__queue_type", "__set_type", "__map_type"].some((otype) => OOPTypeDecl.attributeSetContains(otype, this.attributes));
    }

    isListType(): boolean {
        return OOPTypeDecl.attributeSetContains("__list_type", this.attributes);
    }

    isStackType(): boolean {
        return OOPTypeDecl.attributeSetContains("__stack_type", this.attributes);
    }

    isQueueType(): boolean {
        return OOPTypeDecl.attributeSetContains("__queue_type", this.attributes);
    }

    isSetType(): boolean {
        return OOPTypeDecl.attributeSetContains("__set_type", this.attributes);
    }

    isMapType(): boolean {
        return OOPTypeDecl.attributeSetContains("__map_type", this.attributes);
    }

    isInternalType(): boolean { 
        return this.attributes.includes("__internal"); 
    }
    
    isUniversalConceptType(): boolean { 
        return this.attributes.includes("__universal"); 
    }

    isSpecialConstructableEntity(): boolean {
        return this.attributes.includes("__constructable"); 
    }

    static attributeSetContains(attr: string, attrSet: string[]): boolean {
        return attrSet.indexOf(attr) !== -1;
    }
}

class ConceptTypeDecl extends OOPTypeDecl {
    constructor(sourceLocation: SourceInfo, srcFile: string, attributes: string[], ns: string, name: string, terms: TemplateTermDecl[], provides: [TypeSignature, TypeConditionRestriction | undefined][],
        invariants: InvariantDecl[], validates: ValidateDecl[],
        staticMembers: StaticMemberDecl[], staticFunctions: StaticFunctionDecl[], staticOperators: StaticOperatorDecl[],
        memberFields: MemberFieldDecl[], memberMethods: MemberMethodDecl[],
        nestedEntityDecls: Map<string, EntityTypeDecl>) {
        super(sourceLocation, srcFile, attributes, ns, name, terms, provides, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, nestedEntityDecls);
    }
}

class EntityTypeDecl extends OOPTypeDecl {
    constructor(sourceLocation: SourceInfo, srcFile: string, attributes: string[], ns: string, name: string, terms: TemplateTermDecl[], provides: [TypeSignature, TypeConditionRestriction | undefined][],
        invariants: InvariantDecl[], validates: ValidateDecl[],
        staticMembers: StaticMemberDecl[], staticFunctions: StaticFunctionDecl[], staticOperators: StaticOperatorDecl[],
        memberFields: MemberFieldDecl[], memberMethods: MemberMethodDecl[],
        nestedEntityDecls: Map<string, EntityTypeDecl>) {
        super(sourceLocation, srcFile, attributes, ns, name, terms, provides, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, nestedEntityDecls);
    }
}

class NamespaceConstDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly ns: string;
    readonly name: string;

    readonly declaredType: TypeSignature;
    readonly value: ConstantExpressionValue;

    constructor(srcInfo: SourceInfo, srcFile: string, attributes: string[], ns: string, name: string, dtype: TypeSignature, value: ConstantExpressionValue) {
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

    readonly ns: string;
    readonly name: string;

    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, ns: string, name: string, invoke: InvokeDecl) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

        this.ns = ns;
        this.name = name;

        this.invoke = invoke;
    }
}

class NamespaceOperatorDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;
    readonly isPrefix: boolean;
    readonly isInfix: boolean;
    readonly isDynamic: boolean;
    readonly level: number;

    readonly ns: string;
    readonly name: string;

    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, ns: string, name: string, invoke: InvokeDecl, level: number) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

        this.isPrefix = invoke.attributes.includes("prefix");
        this.isInfix = invoke.attributes.includes("infix");
        this.isDynamic = invoke.attributes.includes("dynamic");
        this.level = level;
        this.ns = ns;
        this.name = name;

        this.invoke = invoke;
    }

    doesKindTagMatch(tag: "prefix" | "infix" | "std"): boolean {
        return (tag === "prefix" && this.isPrefix) || (tag === "infix" && this.isInfix) || (tag === "std" && !this.isPrefix && !this.isInfix);
    }
}

class NamespaceTypedef {
    readonly attributes: string[];

    readonly ns: string;
    readonly name: string;
    readonly terms: TemplateTermDecl[];
    readonly boundType: TypeSignature;

    constructor(attributes: string[], ns: string, name: string, terms: TemplateTermDecl[], btype: TypeSignature) {
        this.attributes = attributes;

        this.ns = ns;
        this.name = name;
        this.terms = terms;
        this.boundType = btype;
    }
}

class NamespaceUsing {
    readonly fromns: string;
    readonly asns: string;
    readonly names: string[];

    constructor(fromns: string, asns: string, names: string[]) {
        this.fromns = fromns;
        this.asns = asns;
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
    operators: Map<string, NamespaceOperatorDecl[]>;
    concepts: Map<string, ConceptTypeDecl>;
    objects: Map<string, EntityTypeDecl>;

    constructor(ns: string) {
        this.ns = ns;
        this.usings = [];
        this.declaredNames = new Set<string>();

        this.typeDefs = new Map<string, NamespaceTypedef>();
        this.consts = new Map<string, NamespaceConstDecl>();
        this.functions = new Map<string, NamespaceFunctionDecl>();
        this.operators = new Map<string, NamespaceOperatorDecl[]>();
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

class OOMemberLookupInfo<T> {
    readonly contiainingType: OOPTypeDecl;
    readonly decl: T;
    readonly binds: Map<string, ResolvedType>;

    constructor(contiainingType: OOPTypeDecl, decl: T, binds: Map<string, ResolvedType>) {
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

    private m_literalRegexs: BSQRegex[] = [];
    private m_validatorRegexs: Map<string, BSQRegex> = new Map<string, BSQRegex>();

    private m_subtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();
    private m_atomSubtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();

    private m_typedeclResolutions: Map<string, ResolvedType> = new Map<string, ResolvedType>();

    private resolveTemplateBinds(declterms: TemplateTermDecl[], giventerms: TypeSignature[], binds: Map<string, ResolvedType>): Map<string, ResolvedType> | undefined {
        let fullbinds = new Map<string, ResolvedType>();

        for (let i = 0; i < declterms.length; ++i) {
            if (giventerms.length <= i) {
                if (declterms[i].defaultType !== undefined) {
                    fullbinds.set(declterms[i].name, this.normalizeTypeOnly(declterms[i].defaultType as TypeSignature, new Map<string, ResolvedType>()));
                }
                else {
                    return undefined;
                }
            }
            else {
                fullbinds.set(declterms[i].name, this.normalizeTypeOnly(giventerms[i], binds));
            }
        }

        if([...fullbinds].some((bb) => bb[1].isEmptyType())) {
            return undefined;
        }
        else {
            return fullbinds;
        }
    }

    processNumberinoExpressionIntoTypedExpression(exp: LiteralNumberinoExpression, infertype: ResolvedType): Expression | undefined {
        //We will do bounds checking later so just make sure general format is ok here
        const isfpnum = exp.value.includes(".");

        if(infertype.isSameType(this.getSpecialIntType())) {
            return !isfpnum ? new LiteralIntegralExpression(exp.sinfo, exp.value + "i", new NominalTypeSignature("Core", ["Int"])) : undefined;
        }
        else if(infertype.isSameType(this.getSpecialNatType())) {
            return !isfpnum ? new LiteralIntegralExpression(exp.sinfo, exp.value + "n", new NominalTypeSignature("Core", ["Nat"])) : undefined;
        }
        else if(infertype.isSameType(this.getSpecialBigIntType())) {
            return !isfpnum ? new LiteralIntegralExpression(exp.sinfo, exp.value + "I", new NominalTypeSignature("Core", ["BigInt"])) : undefined;
        }
        else if(infertype.isSameType(this.getSpecialBigNatType())) {
            return !isfpnum ? new LiteralIntegralExpression(exp.sinfo, exp.value + "N", new NominalTypeSignature("Core", ["BigNat"])) : undefined;
        }
        else if(infertype.isSameType(this.getSpecialFloatType())) {
            return new LiteralFloatPointExpression(exp.sinfo, exp.value + "f", new NominalTypeSignature("Core", ["Float"]));
        }
        else if(infertype.isSameType(this.getSpecialDecimalType())) {
            return new LiteralFloatPointExpression(exp.sinfo, exp.value + "d", new NominalTypeSignature("Core", ["Decimal"]));
        }
        else if(infertype.isSameType(this.getSpecialRationalType())) {
            return new LiteralRationalExpression(exp.sinfo, exp.value + "/1R", new NominalTypeSignature("Core", ["Rational"]));
        }
        else {
            if(!infertype.isUniqueCallTargetType() || !infertype.getUniqueCallTargetType().object.attributes.includes("__typedprimitive")) {
                return undefined;
            }

            const tt = (infertype.getUniqueCallTargetType().object.memberMethods.find((mmf) => mmf.name === "value") as MemberMethodDecl).invoke.resultType;
            const rtt = this.normalizeTypeOnly(tt, new Map<string, ResolvedType>());

            const le = this.processNumberinoExpressionIntoTypedExpression(exp, rtt);
            if (le === undefined) {
                return undefined;
            }

            if (le instanceof LiteralIntegralExpression) {
                return new LiteralTypedPrimitiveConstructorExpression(exp.sinfo, le.value, le.itype, tt);
            }
            else if (le instanceof LiteralFloatPointExpression) {
                return new LiteralTypedPrimitiveConstructorExpression(exp.sinfo, le.value, le.fptype, tt);
            }
            else {
                const re = le as LiteralRationalExpression;
                return new LiteralTypedPrimitiveConstructorExpression(exp.sinfo, re.value, re.rtype, tt);
            }
        }
    }

    compileTimeReduceConstantExpression(exp: Expression, binds: Map<string, ResolvedType>, infertype: ResolvedType | undefined): Expression | undefined {
        if(exp.isCompileTimeInlineValue()) {
            if(exp instanceof LiteralNumberinoExpression && infertype !== undefined) {
                return this.processNumberinoExpressionIntoTypedExpression(exp, infertype);
            }
            else {
                if(exp instanceof LiteralTypedStringExpression) {
                    const oftype = this.normalizeTypeOnly(exp.stype, binds);
                    if(oftype.isUniqueCallTargetType() && oftype.getUniqueCallTargetType().object.attributes.includes("__validator_type")) {
                        return exp;
                    }
                    else {
                        return undefined;
                    }
                }
                else {
                    return exp;
                }
            }
        }
        else if (exp instanceof AccessNamespaceConstantExpression) {
            if (!this.hasNamespace(exp.ns)) {
                return undefined;
            }
            const nsdecl = this.getNamespace(exp.ns);

            if (!nsdecl.consts.has(exp.name)) {
                return undefined;
            }

            const cdecl = nsdecl.consts.get(exp.name) as NamespaceConstDecl;
            return this.compileTimeReduceConstantExpression(cdecl.value.exp, binds, this.normalizeTypeOnly(cdecl.declaredType, new Map<string, ResolvedType>()));
        }
        else if (exp instanceof AccessStaticFieldExpression) {
            const oftype = this.normalizeTypeOnly(exp.stype, binds);
            const cdecltry = this.tryGetConstMemberUniqueDeclFromType(oftype, exp.name);
            if(cdecltry === undefined) {
                return undefined;
            }
    
            const cdecl = cdecltry as OOMemberLookupInfo<StaticMemberDecl>;
            if(cdecl.contiainingType.attributes.includes("__enum_type")) {
                return exp;
            }
            else {
                return cdecl.decl.value !== undefined ? this.compileTimeReduceConstantExpression(cdecl.decl.value.exp, cdecl.binds, this.normalizeTypeOnly(cdecl.decl.declaredType, cdecl.binds)) : undefined;
            }
        }
        else {
            return undefined;
        }
    }

    reduceLiteralValueToCanonicalForm(exp: Expression, binds: Map<string, ResolvedType>, infertype: ResolvedType | undefined): [Expression, ResolvedType, string] | undefined {
        const cexp = this.compileTimeReduceConstantExpression(exp, binds, infertype);
        if(cexp === undefined) {
            return undefined;
        }

        if(cexp instanceof AccessStaticFieldExpression) {
            const stype = this.normalizeTypeOnly(cexp.stype, new Map<string, ResolvedType>());
            return [cexp, stype, `${stype.typeID}::${cexp.name}`];
        }
        else {
            assert(cexp.isLiteralValueExpression());

            if (cexp instanceof LiteralNoneExpression) {
                return [cexp, this.getSpecialNoneType(), "none"];
            }
            else if (cexp instanceof LiteralNothingExpression) {
                return [cexp, this.getSpecialNothingType(), "nothing"];
            }
            else if (cexp instanceof LiteralBoolExpression) {
                return [cexp, this.getSpecialBoolType(), `${cexp.value}`];
            }
            else if (cexp instanceof LiteralIntegralExpression) {
                const itype = this.normalizeTypeOnly(cexp.itype, new Map<string, ResolvedType>());
                return [cexp, itype, cexp.value];
            }
            else if (cexp instanceof LiteralStringExpression) {
                return [cexp, this.getSpecialStringType(), cexp.value];
            }
            else if (cexp instanceof LiteralTypedStringExpression) {
                const oftype = this.normalizeTypeOnly(cexp.stype, binds);
                return [cexp, oftype, `${cexp.value}#${oftype.typeID}`];
            }
            else {
                assert(cexp instanceof LiteralTypedPrimitiveConstructorExpression);
                const lexp = cexp as LiteralTypedPrimitiveConstructorExpression;

                const vtype = this.normalizeTypeOnly(lexp.vtype, binds);
                const vv = (/.*[inINfdR]$/.test(lexp.value)) ? lexp.value.slice(0, lexp.value.length - 1) : lexp.value;

                return [lexp, vtype, `${vv}#${vtype.typeID}`];
            }
        }
    }

    private splitConceptTypes(ofc: ResolvedConceptAtomType, withc: ResolvedConceptAtomType): {tp: ResolvedType | undefined, fp: ResolvedType | undefined} {
        if (ofc.typeID === "Any" && withc.typeID === "Some") {
            return { tp: ResolvedType.createSingle(withc), fp: this.getSpecialNoneType() };
        }
        else if (ofc.typeID.startsWith("Option<") && withc.typeID === "ISomething") {
            const somthingres = ResolvedEntityAtomType.create(this.tryGetObjectTypeForFullyResolvedName("Something") as EntityTypeDecl, ofc.conceptTypes[0].binds)
            return { tp: ResolvedType.createSingle(somthingres), fp: this.getSpecialNothingType() };
        }
        else if (ofc.typeID === "IOption" && withc.typeID === "ISomething") {
            return { tp: ResolvedType.createSingle(withc), fp: this.getSpecialNothingType() };
        }
        else {
            return { tp: ResolvedType.createSingle(withc), fp: ResolvedType.createSingle(ofc) };
        }
    }

    private splitConceptEntityTypes(ofc: ResolvedConceptAtomType, withe: ResolvedEntityAtomType): { tp: ResolvedType | undefined, fp: ResolvedType | undefined } {
        const somethingdecl = this.tryGetObjectTypeForFullyResolvedName("Something") as EntityTypeDecl;
        const okdecl = this.tryGetObjectTypeForFullyResolvedName("Result::Ok") as EntityTypeDecl;
        const errdecl = this.tryGetObjectTypeForFullyResolvedName("Result::Err") as EntityTypeDecl;

        //
        //TODO: we may want to handle some ISomething, Something, Option, Nothing situations more precisely if they can arise
        //

        if (ofc.typeID === "Any" && withe.typeID === "None") {
            return { tp: ResolvedType.createSingle(withe), fp: this.getSpecialSomeConceptType() };
        }
        else if (ofc.typeID.startsWith("Option<") && withe.typeID === "Nothing") {
            return { tp: ResolvedType.createSingle(withe), fp: ResolvedType.createSingle(ResolvedEntityAtomType.create(somethingdecl, ofc.conceptTypes[0].binds)) };
        }
        else if (ofc.typeID.startsWith("Option<") && withe.typeID === "Something<") {
            return { tp: ResolvedType.createSingle(withe), fp: this.getSpecialNothingType() };
        }
        else if (ofc.typeID.startsWith("Result<") && withe.typeID.startsWith("Result::Ok<")) {
            return { tp: ResolvedType.createSingle(withe), fp: ResolvedType.createSingle(ResolvedEntityAtomType.create(errdecl, ofc.conceptTypes[0].binds)) };
        }
        else if (ofc.typeID.startsWith("Result<") && withe.typeID.startsWith("Result::Err<")) {
            return { tp: ResolvedType.createSingle(withe), fp: ResolvedType.createSingle(ResolvedEntityAtomType.create(okdecl, ofc.conceptTypes[0].binds)) };
        }
        else if(this.atomSubtypeOf(withe, ofc)) {
            if(ofc.conceptTypes.length === 1 && ofc.conceptTypes[0].concept.attributes.includes("__adt_concept_type")) {
                const splits = [...this.m_objectMap]
                    .filter((tt) => tt[1].terms.length === 0)
                    .map((tt) => ResolvedEntityAtomType.create(tt[1], new Map<string, ResolvedType>()))
                    .filter((tt) => { 
                        const issubtype = this.atomSubtypeOf(tt, ofc);
                        const notwithe = tt.typeID !== withe.typeID;

                        return issubtype && notwithe;
                    });
                
                return { tp: ResolvedType.createSingle(withe), fp: ResolvedType.create(splits) };
            }
            else {
                return { tp: ResolvedType.createSingle(withe), fp: ResolvedType.createSingle(ofc) };
            }
        }
        else {
            return { tp: undefined, fp: ResolvedType.createSingle(ofc) };
        }
    }

    private getConceptsProvidedByTuple(tt: ResolvedTupleAtomType): ResolvedConceptAtomType {
        let tci: ResolvedConceptAtomTypeEntry[] = [...(this.getSpecialTupleConceptType().options[0] as ResolvedConceptAtomType).conceptTypes];

        if (tt.types.every((ttype) => this.subtypeOf(ttype, this.getSpecialAPITypeConceptType()))) {
            tci.push(...(this.getSpecialAPITypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
        }
        else {
            if (tt.types.every((ttype) => this.subtypeOf(ttype, this.getSpecialTestableTypeConceptType()))) {
                tci.push(...(this.getSpecialTestableTypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
            }
        }

        return ResolvedConceptAtomType.create(tci);
    }

    private getConceptsProvidedByRecord(rr: ResolvedRecordAtomType): ResolvedConceptAtomType {
        let tci: ResolvedConceptAtomTypeEntry[] = [...(this.getSpecialSomeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes];
        
        if (rr.entries.every((entry) => this.subtypeOf(entry.ptype, this.getSpecialAPITypeConceptType()))) {
            tci.push(...(this.getSpecialAPITypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
        }
        else {
            if (rr.entries.every((entry) => this.subtypeOf(entry.ptype, this.getSpecialTestableTypeConceptType()))) {
                tci.push(...(this.getSpecialTestableTypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
            } 
        }

        return ResolvedConceptAtomType.create(tci);
    }

    private splitConceptTuple(ofc: ResolvedConceptAtomType, witht: ResolvedTupleAtomType): { tp: ResolvedType | undefined, fp: ResolvedType | undefined } {
        const withc = this.getConceptsProvidedByTuple(witht);
        if (this.atomSubtypeOf(withc, ofc)) {
            return { tp: ResolvedType.createSingle(witht), fp: ResolvedType.createSingle(ofc) };
        }
        else {
            return { tp: undefined, fp: ResolvedType.createSingle(ofc) };
        }
    }

    private splitConceptRecord(ofc: ResolvedConceptAtomType, withr: ResolvedRecordAtomType): { tp: ResolvedType | undefined, fp: ResolvedType | undefined } {
        const withc = this.getConceptsProvidedByRecord(withr);
        if (this.atomSubtypeOf(withc, ofc)) {
            return { tp: ResolvedType.createSingle(withr), fp: ResolvedType.createSingle(ofc) };
        }
        else {
            return { tp: undefined, fp: ResolvedType.createSingle(ofc) };
        }
    }

    private splitAtomTypes(ofa: ResolvedAtomType, witha: ResolvedAtomType): { tp: ResolvedType | undefined, fp: ResolvedType | undefined } {
        if (this.atomSubtypeOf(ofa, witha)) {
            return { tp: ResolvedType.createSingle(ofa), fp: undefined };
        }

        if(ofa instanceof ResolvedConceptAtomType) {
            if (witha instanceof ResolvedEntityAtomType) {
                return this.splitConceptEntityTypes(ofa, witha);
            }
            else if(witha instanceof ResolvedConceptAtomType) {
                return this.splitConceptTypes(ofa, witha);
            }
            else if (witha instanceof ResolvedTupleAtomType) {
                return this.splitConceptTuple(ofa, witha);
            }
            else if (witha instanceof ResolvedRecordAtomType) {
                return this.splitConceptRecord(ofa, witha);
            }
            else {
                return { tp: undefined, fp: ResolvedType.createSingle(ofa) };
            }
        }
        else if (ofa instanceof ResolvedTupleAtomType) {
            if (witha instanceof ResolvedTupleAtomType) {
                if(ofa.typeID === witha.typeID) {
                    return { tp: ResolvedType.createSingle(witha), fp: undefined };
                }
                else {
                    return { tp: undefined, fp: ResolvedType.createSingle(ofa) };
                }
            }
            else {
                return { tp: undefined, fp: ResolvedType.createSingle(ofa) };
            }
        }
        else if (ofa instanceof ResolvedRecordAtomType) {
            if (witha instanceof ResolvedRecordAtomType) {
                if(ofa.typeID === witha.typeID) {
                    return { tp: ResolvedType.createSingle(witha), fp: undefined };
                }
                else {
                    return { tp: undefined, fp: ResolvedType.createSingle(ofa) };
                }
            }
            else {
                return { tp: undefined, fp: ResolvedType.createSingle(ofa) };
            }
        }
        else {
            return { tp: undefined, fp: ResolvedType.createSingle(ofa) };
        }
    }

    private splitAtomWithType(ofa: ResolvedAtomType, witht: ResolvedType): { tp: ResolvedType[], fp: ResolvedType[] } {
        let tp: ResolvedType[] = [];
        let fp: ResolvedType[] = [];
        witht.options
            .map((opt) => this.splitAtomTypes(ofa, opt))
            .forEach((rr) => {
                if(rr.tp !== undefined) {
                    tp.push(rr.tp);
                }
                if(rr.fp !== undefined) {
                    fp.push(rr.fp);
                }
            });

        return { tp: tp, fp: fp };
    }

    splitTypes(oft: ResolvedType, witht: ResolvedType): { tp: ResolvedType, fp: ResolvedType } {
        if (oft.isEmptyType() || witht.isEmptyType()) {
            return { tp: ResolvedType.createEmpty(), fp: ResolvedType.createEmpty() };
        }

        if (oft.typeID === witht.typeID) {
            return { tp: oft, fp: ResolvedType.createEmpty() };
        }

        const paths = oft.options.map((opt) => this.splitAtomWithType(opt, witht));
        let tp = ([] as ResolvedType[]).concat(...paths.map((pp) => pp.tp));
        let fp = ([] as ResolvedType[]).concat(...paths.map((pp) => pp.fp));

        return {tp: this.typeUpperBound(tp), fp: this.typeUpperBound(fp)};
    }

    splitIndex(oft: ResolvedType, idx: number): { tp: ResolvedType, fp: ResolvedType } {
        if (oft.isEmptyType()) {
            return { tp: ResolvedType.createEmpty(), fp: ResolvedType.createEmpty() };
        }

        let tpp: ResolvedTupleAtomType[] = [];
        let fpp: ResolvedTupleAtomType[] = [];
        for(let i = 0; i < oft.options.length; ++i) {
            const opt = oft.options[i] as ResolvedTupleAtomType;

            if(idx < opt.types.length) {
                tpp.push(opt);
            }
            else {
                fpp.push(opt);
            }
        }

        return {tp: ResolvedType.create(tpp), fp: ResolvedType.create(fpp)};
    }

    splitProperty(oft: ResolvedType, pname: string): { tp: ResolvedType, fp: ResolvedType } {
        if (oft.isEmptyType()) {
            return { tp: ResolvedType.createEmpty(), fp: ResolvedType.createEmpty() };
        }

        let tpp: ResolvedRecordAtomType[] = [];
        let fpp: ResolvedRecordAtomType[] = [];
        for(let i = 0; i < oft.options.length; ++i) {
            const opt = oft.options[i] as ResolvedRecordAtomType;

            const entry = opt.entries.find((ee) => ee.pname === pname);
            if(entry !== undefined) {
                tpp.push(opt);
            }
            else {
                fpp.push(opt);
            }
        }

        return {tp: ResolvedType.create(tpp), fp: ResolvedType.create(fpp)};
    }

    getDerivedTypeProjection(fromtype: ResolvedType, oftype: ResolvedType): ResolvedType {
        if(oftype.typeID === "Some") {
            return this.splitTypes(fromtype, this.getSpecialNoneType()).fp;
        }
        else if(oftype.typeID === "IOptionT") {
            if(oftype.options.length === 1 && oftype.typeID.startsWith("Option<")) {
                return (oftype.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds.get("T") as ResolvedType;
            }
            else {
                return ResolvedType.createEmpty();
            }
        }
        else if(oftype.typeID === "IResultT") {
            if(oftype.options.length === 1 && oftype.typeID.startsWith("Result<")) {
                return (oftype.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds.get("T") as ResolvedType;
            }
            else {
                return ResolvedType.createEmpty();
            }
        }
        else if(oftype.typeID === "IResultE") {
            if(oftype.options.length === 1 && oftype.typeID.startsWith("Result<")) {
                return (oftype.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds.get("E") as ResolvedType;
            }
            else {
                return ResolvedType.createEmpty();
            }
        }
        else {
            return ResolvedType.createEmpty();
        }
    }

    private normalizeType_Template(t: TemplateTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        return binds.has(t.name) ? binds.get(t.name) as ResolvedType : ResolvedType.createEmpty();
    }

    private normalizeType_Nominal(t: NominalTypeSignature, binds: Map<string, ResolvedType>): ResolvedType | ResolvedFunctionType {
        const [aliasResolvedType, aliasResolvedBinds, isresolution] = this.lookupTypeDef(t, binds);

        let rtype: ResolvedType | ResolvedFunctionType = ResolvedType.createEmpty(); 
        if (aliasResolvedType === undefined) {
            ;
        }
        else if (!(aliasResolvedType instanceof NominalTypeSignature)) {
            rtype = this.normalizeTypeGeneral(aliasResolvedType, aliasResolvedBinds);
        }
        else {
            const ttname = (aliasResolvedType.nameSpace !== "Core" ? (aliasResolvedType.nameSpace + "::") : "") + aliasResolvedType.computeResolvedName();

            const fconcept = this.tryGetConceptTypeForFullyResolvedName(ttname);
            if (fconcept !== undefined) {
                const cta = this.createConceptTypeAtom(fconcept, aliasResolvedType, aliasResolvedBinds);
                rtype = cta !== undefined ? ResolvedType.createSingle(cta) : ResolvedType.createEmpty();
            }

            const fobject = this.tryGetObjectTypeForFullyResolvedName(ttname);
            if (fobject !== undefined) {
                const ota = this.createObjectTypeAtom(fobject, aliasResolvedType, aliasResolvedBinds);
                rtype = ota !== undefined ? ResolvedType.createSingle(ota) : ResolvedType.createEmpty();
            }
        }

        if(isresolution) {
            let sstr = (t.nameSpace !== "Core" ? (t.nameSpace + "::") : "") + t.computeResolvedName();

            if(t.terms.length !== 0) {
                sstr += "<" + t.terms.map((t) => this.normalizeTypeOnly(t, binds).typeID).join(", ") + ">";
            }

            this.m_typedeclResolutions.set(sstr, rtype as ResolvedType);
        }

        return rtype;
    }


    private normalizeType_Tuple(t: TupleTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const entries = t.entries.map((entry) => this.normalizeTypeOnly(entry, binds));
        if (entries.some((e) => e.isEmptyType())) {
            return ResolvedType.createEmpty();
        }

        return ResolvedType.createSingle(ResolvedTupleAtomType.create(entries));
    }

    private normalizeType_Record(t: RecordTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        let seenNames = new Set<string>();
        let entries: {pname: string, ptype: ResolvedType}[] = [];
        for (let i = 0; i < t.entries.length; ++i) {
            if (seenNames.has(t.entries[i][0])) {
                return ResolvedType.createEmpty();
            }

            entries.push({pname: t.entries[i][0], ptype: this.normalizeTypeOnly(t.entries[i][1], binds)});
        }
        if (entries.some((e) => e.ptype.isEmptyType())) {
            return ResolvedType.createEmpty();
        }

        return ResolvedType.createSingle(ResolvedRecordAtomType.create(entries));
    }

    private normalizeType_EphemeralList(t: EphemeralListTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const entries = t.entries.map((entry) => this.normalizeTypeOnly(entry, binds));
        if (entries.some((e) => e.isEmptyType())) {
            return ResolvedType.createEmpty();
        }

        return ResolvedType.createSingle(ResolvedEphemeralListType.create(entries));
    }

    private normalizeType_Projection(t: ProjectTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const fromt = this.normalizeTypeOnly(t.fromtype, binds);
        const oft = this.normalizeTypeOnly(t.oftype, binds);

        if(fromt.isEmptyType() || oft.isEmptyType()) {
            return ResolvedType.createEmpty();
        }

        return this.getDerivedTypeProjection(fromt, oft);
    }

    private normalizeType_Plus(t: PlusTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const ccs = t.types.map((tt) => this.normalizeTypeOnly(tt, binds));
        assert(ccs.length !== 0);

        if(ccs.some((tt) => tt.isEmptyType)) {
            return ResolvedType.createEmpty();
        }

        if(ccs.every((tt) => tt.isUniqueTupleTargetType())) {
            let tte: ResolvedType[][] = [];
            for(let i = 0; i < ccs.length; ++i) {
                const rte = ccs[i].options[0] as ResolvedTupleAtomType;
                tte.push(rte.types);
            }

            const fte = ([] as ResolvedType[]).concat(...tte);
            return ResolvedType.createSingle(ResolvedTupleAtomType.create(fte));
        }
        else if(ccs.every((tt) => tt.isRecordTargetType())) {
            let tte: {pname: string, ptype: ResolvedType}[][] = [];
            let names = new Set<string>();
            for(let i = 0; i < ccs.length; ++i) {
                const rre = ccs[i].options[0] as ResolvedRecordAtomType;

                const allnamegroups = rre.entries.map((entry) => entry.pname);
                const allnames = [...new Set<string>(([] as string[]).concat(...allnamegroups))].sort();

                if (allnames.some((pname) => names.has(pname))) {
                    return ResolvedType.createEmpty();
                }

                tte.push(rre.entries);
            }

            const fte = ([] as {pname: string, ptype: ResolvedType}[]).concat(...tte);
            return ResolvedType.createSingle(ResolvedRecordAtomType.create(fte));
        }
        else {
            return ResolvedType.createEmpty();
        }
    }

    private normalizeType_And(t: AndTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        if (t.types.some((opt) => this.normalizeTypeOnly(opt, binds).isEmptyType())) {
            return ResolvedType.createEmpty();
        }

        const ntypes: ResolvedAtomType[][] = t.types.map((opt) => this.normalizeTypeOnly(opt, binds).options);
        const flattened: ResolvedAtomType[] = ([] as ResolvedAtomType[]).concat(...ntypes);

        if (flattened.some((ttype) => !(ttype instanceof ResolvedConceptAtomType))) {
            return ResolvedType.createEmpty();
        }

        const ctypes = flattened.map((arg) => (arg as ResolvedConceptAtomType).conceptTypes);
        const itypes = (([] as ResolvedConceptAtomTypeEntry[]).concat(...ctypes)).sort((cte1, cte2) => cte1.typeID.localeCompare(cte2.typeID));

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
                    docopy = (itypes[i].typeID === itypes[j].typeID) && i < j; //if same type only keep one copy
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
        if (t.types.some((opt) => this.normalizeTypeOnly(opt, binds).isEmptyType())) {
            return ResolvedType.createEmpty();
        }

        const utypes = t.types.map((opt) => this.normalizeTypeOnly(opt, binds));
        return this.normalizeUnionList(utypes);
    }

    private normalizeEphemerals(ephemerals: ResolvedEphemeralListType[]): ResolvedEphemeralListType | undefined {
        const lidx = Math.max(...ephemerals.map((tt) => tt.types.length));
        const uidx = Math.min(...ephemerals.map((tt) => tt.types.length));
        if(lidx !== uidx) {
            return undefined; //can't have different lengths!!!
        }

        let nte: ResolvedType[] = [];
        for (let i = 0; i < lidx; ++i) {
            const ttypes = ephemerals.map((tt) => tt.types[i]);
            const ttype = this.typeUpperBound(ttypes);
            if(ephemerals.some((tt) => !tt.types[i].isSameType(ttype))) {
                return undefined; //can't have different types
            }

            nte.push(ttype);
        }

        return ResolvedEphemeralListType.create(nte);
    }

    private normalizeUnionList(types: ResolvedType[]): ResolvedType {
        //flatten any union types
        const ntypes: ResolvedAtomType[][] = types.map((opt) => opt.options);
        let flattened: ResolvedAtomType[] = ([] as ResolvedAtomType[]).concat(...ntypes);

        //check for Some | None and add Any if needed
        if (flattened.some((atom) => atom.typeID === "None") && flattened.some((atom) => atom.typeID === "Some")) {
            flattened.push(this.getSpecialAnyConceptType().options[0]);
        }

        //check for Something<T> | Nothing and add Option<T> if needed
        if (flattened.some((atom) => atom.typeID === "Nothing") && flattened.some((atom) => atom.typeID.startsWith("Something<"))) {
            const copt = this.m_conceptMap.get("Option") as ConceptTypeDecl;

            const nopts = flattened
                .filter((atom) => atom.typeID.startsWith("Something<"))
                .map((atom) => ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(copt, (atom as ResolvedEntityAtomType).binds)]));

            flattened.push(...nopts);
        }

        //check for Ok<T, E> | Err<T, E> and add Result<T> if needed
        if (flattened.some((atom) => atom.typeID.startsWith("Result::Ok<")) && flattened.some((atom) => atom.typeID.startsWith("Result::Err<"))) {
            const ropt = this.m_conceptMap.get("Result") as ConceptTypeDecl;

            const okopts =  flattened.filter((atom) => atom.typeID.startsWith("Result::Ok<"));
            const erropts =  flattened.filter((atom) => atom.typeID.startsWith("Result::Err<"));

            const bothopts = okopts.filter((okatom) => erropts.some((erratom) => {
                const okbinds = (okatom as ResolvedEntityAtomType).binds;
                const errbinds = (erratom as ResolvedEntityAtomType).binds;
                return (okbinds.get("T") as ResolvedType).typeID === (errbinds.get("T") as ResolvedType).typeID && (okbinds.get("E") as ResolvedType).typeID === (errbinds.get("E") as ResolvedType).typeID;
            }));

            const nopts = bothopts.map((atom) => ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(ropt, (atom as ResolvedEntityAtomType).binds)]));

            flattened.push(...nopts);
        }

        const teph = flattened.filter((tt) => tt instanceof ResolvedEphemeralListType) as ResolvedEphemeralListType[];
        let merged = flattened.filter((tt) => !(tt instanceof ResolvedEphemeralListType));

        if (teph.length !== 0) {
            const eet = this.normalizeEphemerals(teph);
            if (eet === undefined || merged.length !== 0) {
                return ResolvedType.createEmpty();
            }
            else {
                merged.push(eet);
            }
        }

        const utypes = merged.sort((cte1, cte2) => cte1.typeID.localeCompare(cte2.typeID));

        //do a simplification based on A | B when A \Subtypeeq B is B
        let simplifiedTypes: ResolvedAtomType[] = [];
        for (let i = 0; i < utypes.length; ++i) {
            const tt = utypes[i];

            //see if there is a type that is a strict supertype
            if (utypes.some((ott) => ott.typeID !== tt.typeID && this.atomSubtypeOf(tt, ott))) {
                continue;
            }

            //see if this is the first occourence of the type
            const idx = utypes.findIndex((ott) => ott.typeID === tt.typeID);
            if (idx < i) {
                continue;
            }

            simplifiedTypes.push(utypes[i]);
        }

        return ResolvedType.create(simplifiedTypes);
    }

    private normalizeType_Function(t: FunctionTypeSignature, binds: Map<string, ResolvedType>): ResolvedFunctionType | undefined {
        const params = t.params.map((param) => {
            let ttl = this.normalizeTypeGeneral(param.type, binds);
            let llpv: string | undefined = undefined;
            if(param.litexp !== undefined) {
                const lei = this.reduceLiteralValueToCanonicalForm(param.litexp.exp, binds, ttl as ResolvedType);
                if(lei === undefined) {
                    ttl = ResolvedType.createEmpty();
                }
                else {
                    llpv = lei[2];
                }
            }

            return new ResolvedFunctionTypeParam(param.name, ttl, param.isOptional, param.refKind, llpv);
        });
        const optRestParamType = (t.optRestParamType !== undefined) ? this.normalizeTypeOnly(t.optRestParamType, binds) : undefined;
        const rtype = this.normalizeTypeOnly(t.resultType, binds);

        if (params.some((p) => p.type instanceof ResolvedType && p.type.isEmptyType()) || params.some((p) => p.isOptional && (p.refKind !== undefined)) || (optRestParamType !== undefined && optRestParamType.isEmptyType()) || rtype.isEmptyType()) {
            return undefined;
        }

        if(t.isPred && rtype.typeID !== "Bool") {
            return undefined; //pred must have Bool result type
        }

        return ResolvedFunctionType.create(t.recursive, params, t.optRestParamName, optRestParamType, rtype, t.isPred);
    }

    private atomSubtypeOf_EntityConcept(t1: ResolvedEntityAtomType, t2: ResolvedConceptAtomType): boolean {
        if(t1.object.attributes.includes("__nothing_type") && t2.conceptTypes.some((cpt) => cpt.concept.attributes.includes("__option_type"))) {
            return true;
        }
        else {
            const t2type = ResolvedType.createSingle(t2);
            return this.resolveProvides(t1.object, t1.binds).some((provide) => {
                const tt = this.normalizeTypeOnly(provide, t1.binds);
                return !tt.isEmptyType() && this.subtypeOf(tt, t2type);
            });
        }
    }

    private atomSubtypeOf_TupleConcept(t1: ResolvedTupleAtomType, t2: ResolvedConceptAtomType): boolean {
        const tt = this.getConceptsProvidedByTuple(t1);
        return this.subtypeOf(ResolvedType.createSingle(tt), ResolvedType.createSingle(t2));
    }

    private atomSubtypeOf_RecordConcept(t1: ResolvedRecordAtomType, t2: ResolvedConceptAtomType): boolean {
        const tr = this.getConceptsProvidedByRecord(t1);
        return this.subtypeOf(ResolvedType.createSingle(tr), ResolvedType.createSingle(t2));
    }

    private atomSubtypeOf_ConceptConcept(t1: ResolvedConceptAtomType, t2: ResolvedConceptAtomType, ): boolean {
        return t2.conceptTypes.every((c2t) => {
            return t1.conceptTypes.some((c1t) => {
                if (c1t.concept.ns === c2t.concept.ns && c1t.concept.name === c2t.concept.name) {
                    let allBindsOk = true;
                    c1t.binds.forEach((v, k) => (allBindsOk = allBindsOk && v.typeID === (c2t.binds.get(k) as ResolvedType).typeID));
                    return allBindsOk;
                }

                const t2type = ResolvedType.createSingle(ResolvedConceptAtomType.create([c2t]));
                return this.resolveProvides(c1t.concept, c1t.binds).some((provide) => {
                    const tt = this.normalizeTypeOnly(provide, c1t.binds);
                    return !tt.isEmptyType() && this.subtypeOf(tt, t2type);
                });
            });
        });
    }

    private unifyResolvedEntityAtomType(witht: ResolvedEntityAtomType, atom: ResolvedEntityAtomType, umap: Map<string, ResolvedType | undefined>) {
        if(witht.object.ns !== atom.object.ns || witht.object.name !== atom.object.name) {
            return;
        }

        if(witht.binds.size !== atom.binds.size) {
            return;
        }

        witht.binds.forEach((v, k) => {
            this.typeUnify(v, atom.binds.get(k) as ResolvedType, umap);
        });
    }

    private unifyResolvedConceptAtomType(witht: ResolvedConceptAtomType, atom: ResolvedConceptAtomType, umap: Map<string, ResolvedType | undefined>) {
        if(witht.conceptTypes.length !== atom.conceptTypes.length) {
            return;
        }

        for(let i = 0; i < witht.conceptTypes.length; ++i) {
            const withcc = witht.conceptTypes[i];
            const atomcc = atom.conceptTypes[i];

            if(withcc.concept.ns !== atomcc.concept.ns || withcc.concept.name !== atomcc.concept.name) {
                return;
            }
    
            if(withcc.binds.size !== atomcc.binds.size) {
                return;
            }
    
            withcc.binds.forEach((v, k) => {
                this.typeUnify(v, atomcc.binds.get(k) as ResolvedType, umap);
            });
        }
    }

    private unifyResolvedTupleAtomType(witht: ResolvedTupleAtomType, atom: ResolvedTupleAtomType, umap: Map<string, ResolvedType | undefined>) {
        if(witht.types.length !== atom.types.length) {
            return;
        }

        for(let i = 0; i < witht.types.length; ++i) {
            this.typeUnify(witht.types[i], atom.types[i], umap);
        }
    }

    private unifyResolvedRecordAtomType(witht: ResolvedRecordAtomType, atom: ResolvedRecordAtomType, umap: Map<string, ResolvedType | undefined>) {
        if(witht.entries.length !== atom.entries.length) {
            return;
        }

        for(let i = 0; i < witht.entries.length; ++i) {
            const withe = witht.entries[i];
            const atome = atom.entries[i];

            if(withe.pname !== atome.pname) {
                return;
            }

            this.typeUnify(withe.ptype, atome.ptype, umap);
        }
    }

    private internSpecialConceptType(names: [string], terms?: TypeSignature[], binds?: Map<string, ResolvedType>): ResolvedType {
        if (this.m_specialTypeMap.has(names.join("::"))) {
            return this.m_specialTypeMap.get(names.join("::")) as ResolvedType;
        }

        const rsig = new NominalTypeSignature("Core", names, terms || [] as TypeSignature[]);
        const tconcept = this.createConceptTypeAtom(this.tryGetConceptTypeForFullyResolvedName(names.join("::")) as ConceptTypeDecl, rsig, binds || new Map<string, ResolvedType>());
        const rtype = ResolvedType.createSingle(tconcept as ResolvedAtomType);
        this.m_specialTypeMap.set(names.join("::"), rtype);

        return rtype;
    }

    private internSpecialObjectType(names: string[], terms?: TypeSignature[], binds?: Map<string, ResolvedType>): ResolvedType {
        if (this.m_specialTypeMap.has(names.join("::"))) {
            return this.m_specialTypeMap.get(names.join("::")) as ResolvedType;
        }

        const rsig = new NominalTypeSignature("Core", names, terms || [] as TypeSignature[]);
        const tobject = this.createObjectTypeAtom(this.tryGetObjectTypeForFullyResolvedName(names.join("::")) as EntityTypeDecl, rsig, binds || new Map<string, ResolvedType>());
        const rtype = ResolvedType.createSingle(tobject as ResolvedAtomType);
        this.m_specialTypeMap.set(names.join("::"), rtype);

        return rtype;
    }

    getSpecialNoneType(): ResolvedType { return this.internSpecialObjectType(["None"]); }
    getSpecialBoolType(): ResolvedType { return this.internSpecialObjectType(["Bool"]); }
    getSpecialIntType(): ResolvedType { return this.internSpecialObjectType(["Int"]); }
    getSpecialNatType(): ResolvedType { return this.internSpecialObjectType(["Nat"]); }
    getSpecialBigIntType(): ResolvedType { return this.internSpecialObjectType(["BigInt"]); }
    getSpecialBigNatType(): ResolvedType { return this.internSpecialObjectType(["BigNat"]); }
    getSpecialRationalType(): ResolvedType { return this.internSpecialObjectType(["Rational"]); }
    getSpecialFloatType(): ResolvedType { return this.internSpecialObjectType(["Float"]); }
    getSpecialDecimalType(): ResolvedType { return this.internSpecialObjectType(["Decimal"]); }
    getSpecialStringType(): ResolvedType { return this.internSpecialObjectType(["String"]); }
    getSpecialBufferFormatType(): ResolvedType { return this.internSpecialObjectType(["BufferFormat"]); }
    getSpecialBufferCompressionType(): ResolvedType { return this.internSpecialObjectType(["BufferCompression"]); }
    getSpecialByteBufferType(): ResolvedType { return this.internSpecialObjectType(["ByteBuffer"]); }
    getSpecialDateTimeType(): ResolvedType { return this.internSpecialObjectType(["DateTime"]); }
    getSpecialUTCDateTimeType(): ResolvedType { return this.internSpecialObjectType(["UTCDateTime"]); }
    getSpecialCalendarDateType(): ResolvedType { return this.internSpecialObjectType(["CalendarDate"]); }
    getSpecialRelativeTimeType(): ResolvedType { return this.internSpecialObjectType(["RelativeTime"]); }
    getSpecialTickTimeType(): ResolvedType { return this.internSpecialObjectType(["TickTime"]); }
    getSpecialLogicalTimeType(): ResolvedType { return this.internSpecialObjectType(["LogicalTime"]); }
    getSpecialISOTimeStampType(): ResolvedType { return this.internSpecialObjectType(["ISOTimeStamp"]); }
    getSpecialUUID4Type(): ResolvedType { return this.internSpecialObjectType(["UUID4"]); }
    getSpecialUUID7Type(): ResolvedType { return this.internSpecialObjectType(["UUID7"]); }
    getSpecialSHAContentHashType(): ResolvedType { return this.internSpecialObjectType(["SHAContentHash"]); }
    getSpecialLatLongCoordinateType(): ResolvedType { return this.internSpecialObjectType(["LatLongCoordinate"]); }
    getSpecialRegexType(): ResolvedType { return this.internSpecialObjectType(["Regex"]); }
    getSpecialNothingType(): ResolvedType { return this.internSpecialObjectType(["Nothing"]); }

    getSpecialHavocType(): ResolvedType { return this.internSpecialObjectType(["HavocSequence"]); }

    getSpecialAnyConceptType(): ResolvedType { return this.internSpecialConceptType(["Any"]); }
    getSpecialSomeConceptType(): ResolvedType { return this.internSpecialConceptType(["Some"]); }

    getSpecialKeyTypeConceptType(): ResolvedType { return this.internSpecialConceptType(["KeyType"]); }
    getSpecialValidatorConceptType(): ResolvedType { return this.internSpecialConceptType(["Validator"]); }
    getSpecialParsableConceptType(): ResolvedType { return this.internSpecialConceptType(["Parsable"]); }
    getSpecialBufferParsableConceptType(): ResolvedType { return this.internSpecialConceptType(["BufferParsable"]); }
    getSpecialTestableTypeConceptType(): ResolvedType { return this.internSpecialConceptType(["TestableType"]); }
    getSpecialAPITypeConceptType(): ResolvedType { return this.internSpecialConceptType(["APIType"]); }
    getSpecialAlgebraicConceptType(): ResolvedType { return this.internSpecialConceptType(["Algebraic"]); }
    getSpecialOrderableConceptType(): ResolvedType { return this.internSpecialConceptType(["Orderable"]); }

    getSpecialTupleConceptType(): ResolvedType { return this.internSpecialConceptType(["Tuple"]); }
    getSpecialRecordConceptType(): ResolvedType { return this.internSpecialConceptType(["Record"]); }

    getSpecialISomethingConceptType(): ResolvedType { return this.internSpecialConceptType(["ISomething"]); }
    getSpecialIOptionConceptType(): ResolvedType { return this.internSpecialConceptType(["IOption"]); }
    getSpecialIOptionTConceptType(): ResolvedType { return this.internSpecialConceptType(["IOptionT"]); }

    getSpecialIResultConceptType(): ResolvedType { return this.internSpecialConceptType(["IResult"]); }
    getSpecialIOkConceptType(): ResolvedType { return this.internSpecialConceptType(["IOk"]); }
    getSpecialIErrTConceptType(): ResolvedType { return this.internSpecialConceptType(["IErr"]); }
    getSpecialIResultTConceptType(): ResolvedType { return this.internSpecialConceptType(["IResultT"]); }
    getSpecialIResultEConceptType(): ResolvedType { return this.internSpecialConceptType(["IResultE"]); }

    getSpecialObjectConceptType(): ResolvedType { return this.internSpecialConceptType(["Object"]); }

    getStringOfType(t: ResolvedType): ResolvedType { return ResolvedType.createSingle(ResolvedEntityAtomType.create(this.m_objectMap.get("StringOf") as EntityTypeDecl, new Map<string, ResolvedType>().set("T", t))); }
    getDataStringType(t: ResolvedType): ResolvedType { return ResolvedType.createSingle(ResolvedEntityAtomType.create(this.m_objectMap.get("DataString") as EntityTypeDecl, new Map<string, ResolvedType>().set("T", t))); }
    getDataBufferType(t: ResolvedType): ResolvedType { return ResolvedType.createSingle(ResolvedEntityAtomType.create(this.m_objectMap.get("DataBuffer") as EntityTypeDecl, new Map<string, ResolvedType>().set("T", t))); }

    getSomethingType(t: ResolvedType): ResolvedType { return ResolvedType.createSingle(ResolvedEntityAtomType.create(this.m_objectMap.get("Something") as EntityTypeDecl, new Map<string, ResolvedType>().set("T", t))); }
    getOkType(t: ResolvedType, e: ResolvedType): ResolvedType { return ResolvedType.createSingle(ResolvedEntityAtomType.create(this.m_objectMap.get("Result::Ok") as EntityTypeDecl, new Map<string, ResolvedType>().set("T", t).set("E", e))); }
    getErrType(t: ResolvedType, e: ResolvedType): ResolvedType { return ResolvedType.createSingle(ResolvedEntityAtomType.create(this.m_objectMap.get("Result::Err") as EntityTypeDecl, new Map<string, ResolvedType>().set("T", t).set("E", e))); }

    getOptionConceptType(t: ResolvedType): ResolvedType { return ResolvedType.createSingle(ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(this.m_conceptMap.get("Option") as ConceptTypeDecl, new Map<string, ResolvedType>().set("T", t))])); }
    getResultConceptType(t: ResolvedType, e: ResolvedType): ResolvedType { return ResolvedType.createSingle(ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(this.m_conceptMap.get("Result") as ConceptTypeDecl, new Map<string, ResolvedType>().set("T", t).set("E", e))])); }
    
    isExpandoableType(ty: ResolvedAtomType): boolean { return ty.typeID.startsWith("Expandoable<"); }

    ensureNominalRepresentation(t: ResolvedType): ResolvedType {
        const opts = t.options.map((opt) => {
            if (opt instanceof ResolvedTupleAtomType) {
                return this.getSpecialTupleConceptType();
            }
            else if (opt instanceof ResolvedRecordAtomType) {
                return this.getSpecialRecordConceptType();
            }
            else {
                return ResolvedType.createSingle(opt);
            }
        });

        return this.typeUpperBound(opts);
    }

    tryGetConceptTypeForFullyResolvedName(name: string): ConceptTypeDecl | undefined {
        return this.m_conceptMap.get(name);
    }

    tryGetObjectTypeForFullyResolvedName(name: string): EntityTypeDecl | undefined {
        return this.m_objectMap.get(name);
    }

    tryGetValidatorForFullyResolvedName(name: string): BSQRegex | undefined {
        return this.m_validatorRegexs.get(name);
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

    addValidatorRegex(resolvedName: string, validator: BSQRegex) {
        let ere = this.m_literalRegexs.findIndex((lre) => lre.restr === validator.restr);
        if(ere === -1) {
            ere = this.m_literalRegexs.length;
            this.m_literalRegexs.push(validator);
        }

        this.m_validatorRegexs.set(resolvedName, this.m_literalRegexs[ere]);
    }

    addLiteralRegex(re: BSQRegex) {
        const ere = this.m_literalRegexs.findIndex((lre) => lre.restr === re.restr);
        if(ere !== -1) {
            this.m_literalRegexs.push(re);
        }
    }

    getAllLiteralRegexs(): BSQRegex[] {
        return this.m_literalRegexs;
    }

    getAllValidators(): [ResolvedEntityAtomType, BSQRegex][] {
        return [...this.m_validatorRegexs].map((vre) => {
            const ve = ResolvedEntityAtomType.create(this.m_objectMap.get(vre[0]) as EntityTypeDecl, new Map<string, ResolvedType>());
            return [ve, vre[1]];
        });
    } 

    getTypedefRemap(): Map<string, ResolvedType> {
        return this.m_typedeclResolutions;
    }

    ////
    //Type representation, normalization, and operations
    lookupTypeDef(t: NominalTypeSignature, binds: Map<string, ResolvedType>): [TypeSignature | undefined, Map<string, ResolvedType>, boolean] {
        if (!this.hasNamespace(t.nameSpace)) {
            return [undefined, new Map<string, ResolvedType>(), false];
        }

        const lname = (t.nameSpace !== "Core" ? (t.nameSpace + "::") : "") + t.tnames.join("::");
        const nsd = this.getNamespace(t.nameSpace);
        if (!nsd.typeDefs.has(lname)) {
            return [t, new Map<string, ResolvedType>(binds), false];
        }

        //compute the bindings to use when resolving the RHS of the typedef alias
        const typealias = nsd.typeDefs.get(lname) as NamespaceTypedef;
        const updatedbinds = this.resolveTemplateBinds(typealias.terms, t.terms, binds);
        if(updatedbinds === undefined) {
            return [undefined, new Map<string, ResolvedType>(), false];
        }

        if (typealias.boundType instanceof NominalTypeSignature) {
            return this.lookupTypeDef(typealias.boundType, updatedbinds);
        }
        else {
            return [typealias.boundType, updatedbinds, true];
        }
    }

    createConceptTypeAtom(concept: ConceptTypeDecl, t: NominalTypeSignature, binds: Map<string, ResolvedType>): ResolvedConceptAtomType | undefined {
        const fullbinds = this.resolveTemplateBinds(concept.terms, t.terms, binds);
        if(fullbinds === undefined) {
            return undefined;
        }

        return ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(concept, fullbinds)]);
    }

    createObjectTypeAtom(object: EntityTypeDecl, t: NominalTypeSignature, binds: Map<string, ResolvedType>): ResolvedEntityAtomType | undefined {
        const fullbinds = this.resolveTemplateBinds(object.terms, t.terms, binds);
        if(fullbinds === undefined) {
            return undefined;
        }

        return ResolvedEntityAtomType.create(object, fullbinds);
    }

    getAllOOFieldsConstructors(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, fmap?: { req: Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]>, opt: Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]> }): { req: Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]>, opt: Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]> } {
        assert(!ooptype.isSpecialConstructableEntity(), "Needs to be handled as special case");

        let declfields = fmap || { req: new Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]>(), opt: new Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]>() };

        //Important to do traversal in Left->Right Topmost traversal order

        this.resolveProvides(ooptype, binds).forEach((provide) => {
            const tt = this.normalizeTypeOnly(provide, binds);
            (tt.options[0] as ResolvedConceptAtomType).conceptTypes.forEach((concept) => {
                declfields = this.getAllOOFieldsConstructors(concept.concept, concept.binds, declfields);
            });
        });

        ooptype.memberFields.forEach((mf) => {
            if(mf.value === undefined) {
                if(!declfields.req.has(mf.name)) {
                    declfields.req.set(mf.name, [ooptype, mf, binds]);
                }
            }
            else {
                if (!declfields.opt.has(mf.name) && !OOPTypeDecl.attributeSetContains("derived", mf.attributes)) {
                    declfields.opt.set(mf.name, [ooptype, mf, binds]);
                }
            }
        });

        return declfields;
    }

    getAllOOFieldsLayout(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, fmap?: Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]>): Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]> {
        assert(!ooptype.isSpecialConstructableEntity(), "Needs to be handled as special case");
        
        let declfields = fmap || new Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]>();

        //Important to do traversal in Left->Right Topmost traversal order

        this.resolveProvides(ooptype, binds).forEach((provide) => {
            const tt = this.normalizeTypeOnly(provide, binds);
            (tt.options[0] as ResolvedConceptAtomType).conceptTypes.forEach((concept) => {
                declfields = this.getAllOOFieldsLayout(concept.concept, concept.binds, declfields);
            });
        });

        ooptype.memberFields.forEach((mf) => {
            if (!declfields.has(mf.name)) {
                declfields.set(mf.name, [ooptype, mf, binds]);
            }
        });

        return declfields;
    }

    getExpandoProvides(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>): ResolvedType | undefined {
        if(ooptype.ns === "Core" && ooptype.name === "Expandoable") {
            return ResolvedType.createSingle(ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(ooptype as ConceptTypeDecl, binds)]));
        }

        const rtypes = this.resolveProvides(ooptype, binds);
        for(let i = 0; i < rtypes.length; ++i) {
            const tt = this.normalizeTypeOnly(rtypes[i], binds);
            const ct = (tt.options[0] as ResolvedConceptAtomType).conceptTypes[0];
            const ep = this.getExpandoProvides(ct.concept, ct.binds);
            if(ep !== undefined) {
                return ep;
            }
        }
        
        return undefined;
    }

    getAllInvariantProvidingTypes(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, invprovs?: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][]): [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][] {
        let declinvs:  [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][] = [...(invprovs || [])];

        this.resolveProvides(ooptype, binds).forEach((provide) => {
            const tt = this.normalizeTypeOnly(provide, binds);
            (tt.options[0] as ResolvedConceptAtomType).conceptTypes.forEach((concept) => {
                declinvs = this.getAllInvariantProvidingTypes(concept.concept, concept.binds, declinvs);
            });
        });

        const ttype = ResolvedType.createSingle(ooptype instanceof EntityTypeDecl ? ResolvedEntityAtomType.create(ooptype, binds) : ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(ooptype as ConceptTypeDecl, binds)]));
        if(declinvs.find((dd) => dd[0].typeID === ttype.typeID)) {
            return declinvs;
        }
        else {
            if(ooptype.invariants.length !== 0 || ooptype.validates.length !== 0) {
                declinvs.push([ttype, ooptype, binds]);
            }

            return declinvs;
        }
    }

    getAbstractPrePostConds(fname: string, ooptype: OOPTypeDecl, oobinds: Map<string, ResolvedType>, callbinds: Map<string, ResolvedType>): {pre: [PreConditionDecl[], Map<string, ResolvedType>], post: [PostConditionDecl[], Map<string, ResolvedType>] } | undefined {
        const rprovides = this.resolveProvides(ooptype, oobinds);
        for (let i = 0; i < rprovides.length; ++i) {
            const provide = rprovides[i];
            const tt = this.normalizeTypeOnly(provide, oobinds);
            for (let j = 0; j < (tt.options[0] as ResolvedConceptAtomType).conceptTypes.length; ++j) {
                const concept = (tt.options[0] as ResolvedConceptAtomType).conceptTypes[j];
                const pc = this.getAbstractPrePostConds(fname, concept.concept, concept.binds, callbinds);
                if (pc !== undefined) {
                    return pc;
                }
            }
        }

        const mmdecl = ooptype.memberMethods.find((mmd) => mmd.name === fname);
        if (mmdecl !== undefined && (mmdecl.invoke.attributes.includes("abstract") || mmdecl.invoke.attributes.includes("virtual"))) {
            let newbinds = new Map<string, ResolvedType>();
            oobinds.forEach((v, k) => newbinds.set(k, v));
            mmdecl.invoke.terms.forEach((term) => newbinds.set(term.name, callbinds.get(term.name) as ResolvedType));

            return {pre: [mmdecl.invoke.preconditions, newbinds], post: [mmdecl.invoke.postconditions, newbinds]};
        }

        const sfdecl = ooptype.staticFunctions.find((sfd) => sfd.name === fname);
        if (sfdecl !== undefined && !(sfdecl.invoke.attributes.includes("abstract") || sfdecl.invoke.attributes.includes("virtual"))) {
            let newbinds = new Map<string, ResolvedType>();
            oobinds.forEach((v, k) => newbinds.set(k, v));
            sfdecl.invoke.terms.forEach((term) => newbinds.set(term.name, callbinds.get(term.name) as ResolvedType));

            return {pre: [sfdecl.invoke.preconditions, newbinds], post: [sfdecl.invoke.postconditions, newbinds]};
        }

        return undefined;
    }

    private tryGetMemberConstDecl(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, name: string): OOMemberLookupInfo<StaticMemberDecl> | undefined {
        const sdecl = ooptype.staticMembers.find((sm) => sm.name === name);
        if(sdecl === undefined) {
            return undefined;
        }

        return new OOMemberLookupInfo<StaticMemberDecl>(ooptype, sdecl, binds);
    }

    private tryGetMemberConstDeclParent(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, name: string): OOMemberLookupInfo<StaticMemberDecl> | undefined {
        const rprovides = this.resolveProvides(ooptype, binds);
        for (let i = 0; i < rprovides.length; ++i) {
            const tt = (this.normalizeTypeOnly(rprovides[i], binds).options[0] as ResolvedConceptAtomType).conceptTypes[0];
            const res = this.tryGetMemberConstDecl(tt.concept, tt.binds, name) || this.tryGetMemberConstDeclParent(tt.concept, tt.binds, name);
            if (res !== undefined) {
                return res;
            }
        }

        return undefined;
    }

    private tryGetMemberFunctionDecl(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, name: string): OOMemberLookupInfo<StaticFunctionDecl> | undefined {
        const sfdecl = ooptype.staticFunctions.find((sfd) => sfd.name === name);
        if(sfdecl === undefined) {
            return undefined;
        }

        return new OOMemberLookupInfo<StaticFunctionDecl>(ooptype, sfdecl, binds);
    }

    private tryGetMemberFunctionDeclParent(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, name: string): OOMemberLookupInfo<StaticFunctionDecl> | undefined {
        const rprovides = this.resolveProvides(ooptype, binds);
        for (let i = 0; i < rprovides.length; ++i) {
            const tt = (this.normalizeTypeOnly(rprovides[i], binds).options[0] as ResolvedConceptAtomType).conceptTypes[0];
            const res = this.tryGetMemberFunctionDecl(tt.concept, tt.binds, name,) || this.tryGetMemberFunctionDeclParent(tt.concept, tt.binds, name);
            if (res !== undefined) {
                return res;
            }
        }

        return undefined;
    }

    private tryGetMemberOperatorDecl(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, name: string): OOMemberLookupInfo<StaticOperatorDecl[]> | undefined {
        const sodecl = ooptype.staticOperators.filter((so) => so.name === name);
        if(sodecl.length === 0) {
            return undefined;
        }

        return new OOMemberLookupInfo<StaticOperatorDecl[]>(ooptype, sodecl, binds);
    }

    private tryGetMemberOperatorDeclParent(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, name: string): OOMemberLookupInfo<StaticOperatorDecl[]> | undefined {
        const rprovides = this.resolveProvides(ooptype, binds);
        for (let i = 0; i < rprovides.length; ++i) {
            const tprovide = this.normalizeTypeOnly(rprovides[i], binds).options[0] as ResolvedConceptAtomType;
            const tt = tprovide.conceptTypes[0];
            const res = this.tryGetMemberOperatorDecl(tt.concept, tt.binds, name,) || this.tryGetMemberOperatorDeclParent(tt.concept, tt.binds, name);
            if (res !== undefined) {
                return res;
            }
        }

        return undefined;
    }

    private tryGetMemberFieldDecl(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, name: string): OOMemberLookupInfo<MemberFieldDecl> | undefined {
        const mfdecl = ooptype.memberFields.find((mf) => mf.name === name);
        if(mfdecl === undefined) {
            return undefined;
        }

        return new OOMemberLookupInfo<MemberFieldDecl>(ooptype, mfdecl, binds);
    }

    private tryGetMemberFieldDeclParent(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, name: string): OOMemberLookupInfo<MemberFieldDecl> | undefined {
        const rprovides = this.resolveProvides(ooptype, binds);
        for (let i = 0; i < rprovides.length; ++i) {
            const tt = (this.normalizeTypeOnly(rprovides[i], binds).options[0] as ResolvedConceptAtomType).conceptTypes[0];
            const res = this.tryGetMemberFieldDecl(tt.concept, tt.binds, name) || this.tryGetMemberFieldDeclParent(tt.concept, tt.binds, name);
            if (res !== undefined) {
                return res;
            }
        }

        return undefined;
    }

    private tryGetMemberMethodDecl(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, name: string, skipoverride: boolean): OOMemberLookupInfo<MemberMethodDecl[]> | undefined {
        const mmdecls = ooptype.memberMethods.filter((mm) => {
            if(skipoverride && OOPTypeDecl.attributeSetContains("override", mm.invoke.attributes)) {
                return false;
            }

            return mm.name === name;
        });

        if(mmdecls.length === 0) {
            return undefined;
        }

        return new OOMemberLookupInfo<MemberMethodDecl[]>(ooptype, mmdecls, binds);
    }

    private tryGetMemberMethodDeclParent(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, name: string, skipoverride: boolean): OOMemberLookupInfo<MemberMethodDecl[]> | undefined {
        const rprovides = this.resolveProvides(ooptype, binds);
        for (let i = 0; i < rprovides.length; ++i) {
            const tt = (this.normalizeTypeOnly(rprovides[i], binds).options[0] as ResolvedConceptAtomType).conceptTypes[0];
            const res = this.tryGetMemberMethodDecl(tt.concept, tt.binds, name, skipoverride) || this.tryGetMemberMethodDeclParent(tt.concept, tt.binds, name, skipoverride);
            if (res !== undefined) {
                return res;
            }
        }

        return undefined;
    }

    tryGetNestedEntityDecl(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, name: string): OOMemberLookupInfo<EntityTypeDecl> | undefined {
        if(!ooptype.nestedEntityDecls.has(name)) {
            return undefined;
        }

        return new OOMemberLookupInfo<EntityTypeDecl>(ooptype, ooptype.nestedEntityDecls.get(name) as EntityTypeDecl, binds);
    }

    private ensureSingleDecl_Helper<T>(opts: OOMemberLookupInfo<T>[]): OOMemberLookupInfo<T> | undefined {
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
                    bindsok = bindsok && opt.binds.has(k) && v.typeID === (opt.binds.get(k) as ResolvedType).typeID;
                });

                return bindsok;
            });

            return allSame ? opt1 : undefined;
        }
    }

    tryGetConstMemberUniqueDeclFromType(tt: ResolvedType, fname: string): OOMemberLookupInfo<StaticMemberDecl> | undefined {
        const ntype = this.ensureNominalRepresentation(tt);
        const ttopts = ntype.options.map((ttopt) => {
            if(ttopt instanceof ResolvedEntityAtomType) {
                return this.tryGetMemberConstDecl(ttopt.object, ttopt.binds, fname) || this.tryGetMemberConstDeclParent(ttopt.object, ttopt.binds, fname);
            }
            else {
                const copts = (ttopt as ResolvedConceptAtomType).conceptTypes.map((ccopt) => {
                    return this.tryGetMemberConstDecl(ccopt.concept, ccopt.binds, fname) || this.tryGetMemberConstDeclParent(ccopt.concept, ccopt.binds, fname);
                });
                return this.ensureSingleDecl_Helper<StaticMemberDecl>(copts.filter((ccopt) => ccopt !== undefined) as OOMemberLookupInfo<StaticMemberDecl>[]);
            }
        });

        if(ttopts.some((topt) => topt === undefined)) {
            return undefined;
        }
        else {
            return this.ensureSingleDecl_Helper<StaticMemberDecl>(ttopts as OOMemberLookupInfo<StaticMemberDecl>[]);
        }
    }

    tryGetFunctionUniqueDeclFromType(tt: ResolvedType, fname: string): OOMemberLookupInfo<StaticFunctionDecl> | undefined {
        const ntype = this.ensureNominalRepresentation(tt);
        const ttopts = ntype.options.map((ttopt) => {
            if(ttopt instanceof ResolvedEntityAtomType) {
                return this.tryGetMemberFunctionDecl(ttopt.object, ttopt.binds, fname) || this.tryGetMemberFunctionDeclParent(ttopt.object, ttopt.binds, fname);
            }
            else {
                const copts = (ttopt as ResolvedConceptAtomType).conceptTypes.map((ccopt) => {
                    return this.tryGetMemberFunctionDecl(ccopt.concept, ccopt.binds, fname) || this.tryGetMemberFunctionDeclParent(ccopt.concept, ccopt.binds, fname);
                });
                return this.ensureSingleDecl_Helper<StaticFunctionDecl>(copts.filter((ccopt) => ccopt !== undefined) as OOMemberLookupInfo<StaticFunctionDecl>[]);
            }
        });

        if(ttopts.some((topt) => topt === undefined)) {
            return undefined;
        }
        else {
            return this.ensureSingleDecl_Helper<StaticFunctionDecl>(ttopts as OOMemberLookupInfo<StaticFunctionDecl>[]);
        }
    }

    tryGetOperatorUniqueDeclFromType(tt: ResolvedType, fname: string): OOMemberLookupInfo<StaticOperatorDecl[]> | undefined {
        const ntype = this.ensureNominalRepresentation(tt);
        const ttopts = ntype.options.map((ttopt) => {
            if(ttopt instanceof ResolvedEntityAtomType) {
                return this.tryGetMemberOperatorDecl(ttopt.object, ttopt.binds, fname) || this.tryGetMemberOperatorDeclParent(ttopt.object, ttopt.binds, fname);
            }
            else {
                const copts = (ttopt as ResolvedConceptAtomType).conceptTypes.map((ccopt) => {
                    return this.tryGetMemberOperatorDecl(ccopt.concept, ccopt.binds, fname) || this.tryGetMemberOperatorDeclParent(ccopt.concept, ccopt.binds, fname);
                });
                return this.ensureSingleDecl_Helper<StaticOperatorDecl[]>(copts.filter((ccopt) => ccopt !== undefined) as OOMemberLookupInfo<StaticOperatorDecl[]>[]);
            }
        });

        if(ttopts.some((topt) => topt === undefined)) {
            return undefined;
        }
        else {
            return this.ensureSingleDecl_Helper<StaticOperatorDecl[]>(ttopts as OOMemberLookupInfo<StaticOperatorDecl[]>[]);
        }
    }

    tryGetFieldUniqueDeclFromType(tt: ResolvedType, fname: string): OOMemberLookupInfo<MemberFieldDecl> | undefined {
        const ntype = this.ensureNominalRepresentation(tt);
        const ttopts = ntype.options.map((ttopt) => {
            if(ttopt instanceof ResolvedEntityAtomType) {
                assert(!ttopt.object.isSpecialConstructableEntity(), "Needs to be handled as special case");

                return this.tryGetMemberFieldDecl(ttopt.object, ttopt.binds, fname) || this.tryGetMemberFieldDeclParent(ttopt.object, ttopt.binds, fname);
            }
            else {
                const copts = (ttopt as ResolvedConceptAtomType).conceptTypes.map((ccopt) => {
                    return this.tryGetMemberFieldDecl(ccopt.concept, ccopt.binds, fname) || this.tryGetMemberFieldDeclParent(ccopt.concept, ccopt.binds, fname);
                });
                return this.ensureSingleDecl_Helper<MemberFieldDecl>(copts.filter((ccopt) => ccopt !== undefined) as OOMemberLookupInfo<MemberFieldDecl>[]);
            }
        });

        if(ttopts.some((topt) => topt === undefined)) {
            return undefined;
        }
        else {
            return this.ensureSingleDecl_Helper<MemberFieldDecl>(ttopts as OOMemberLookupInfo<MemberFieldDecl>[]);
        }
    }

    //Given a type find, if possible, the single static method that every possibility resolves to -- if not then this needs to be a virtual call
    tryGetMethodUniqueConcreteDeclFromType(tt: ResolvedType, fname: string): OOMemberLookupInfo<MemberMethodDecl[]> | undefined {
        const ntype = this.ensureNominalRepresentation(tt);
        const ttopts = ntype.options.map((ttopt) => {
            if(ttopt instanceof ResolvedEntityAtomType) {
                return this.tryGetMemberMethodDecl(ttopt.object, ttopt.binds, fname, false) || this.tryGetMemberMethodDeclParent(ttopt.object, ttopt.binds, fname, false);
            }
            else {
                const copts = (ttopt as ResolvedConceptAtomType).conceptTypes.map((ccopt) => {
                    return this.tryGetMemberMethodDecl(ccopt.concept, ccopt.binds, fname, false) || this.tryGetMemberMethodDeclParent(ccopt.concept, ccopt.binds, fname, false);
                });
                return this.ensureSingleDecl_Helper<MemberMethodDecl[]>(copts.filter((ccopt) => ccopt !== undefined) as OOMemberLookupInfo<MemberMethodDecl[]>[]);
            }
        });

        if(ttopts.some((topt) => topt === undefined)) {
            return undefined;
        }
        else {
            const sdecl = this.ensureSingleDecl_Helper<MemberMethodDecl[]>(ttopts as OOMemberLookupInfo<MemberMethodDecl[]>[]);
            if(sdecl === undefined) {
                return undefined;
            }

            if(tt.isUniqueCallTargetType()) {
                const isundef = sdecl.decl.some((sd) => OOPTypeDecl.attributeSetContains("abstract", sd.invoke.attributes));
                if (isundef) {
                    return undefined;
                }
                else {
                    return sdecl;
                }
            }
            else {
                const isoveridable = sdecl.decl.some((sd) => OOPTypeDecl.attributeSetContains("override", sd.invoke.attributes) || OOPTypeDecl.attributeSetContains("virtual", sd.invoke.attributes) || OOPTypeDecl.attributeSetContains("abstract", sd.invoke.attributes));
                if (isoveridable) {
                    return undefined;
                }
                else {
                    return sdecl;
                }
            }
        }
    }

    //Given a type find the single virtual method root decl that every possible resoltions derives from -- should exist or it is an error
    tryGetMethodUniqueRootDeclFromType(tt: ResolvedType, fname: string): OOMemberLookupInfo<MemberMethodDecl[]> | undefined {
        const ntype = this.ensureNominalRepresentation(tt);
        const ttopts = ntype.options.map((ttopt) => {
            if(ttopt instanceof ResolvedEntityAtomType) {
                return this.tryGetMemberMethodDecl(ttopt.object, ttopt.binds, fname, true) || this.tryGetMemberMethodDeclParent(ttopt.object, ttopt.binds, fname, true);
            }
            else {
                const copts = (ttopt as ResolvedConceptAtomType).conceptTypes.map((ccopt) => {
                    return this.tryGetMemberMethodDecl(ccopt.concept, ccopt.binds, fname, true) || this.tryGetMemberMethodDeclParent(ccopt.concept, ccopt.binds, fname, true);
                });
                return this.ensureSingleDecl_Helper<MemberMethodDecl[]>(copts.filter((ccopt) => ccopt !== undefined) as OOMemberLookupInfo<MemberMethodDecl[]>[]);
            }
        });

        if(ttopts.some((topt) => topt === undefined)) {
            return undefined;
        }
        else {
            return this.ensureSingleDecl_Helper<MemberMethodDecl[]>(ttopts as OOMemberLookupInfo<MemberMethodDecl[]>[]);
        }
    }

    tryGetUniqueStaticOperatorResolve(args: ResolvedType[], opsig: ResolvedFunctionType[]): number {
        const ppairs = opsig.map((sig, idx) => { return {sig: sig, idx: idx}; }).filter((spp) => {
            let j = 0;
            for(let i = 0; i < args.length; ++i) {
                while(spp.sig.params[j].type instanceof ResolvedFunctionType) {
                    j++;
                }

                if(!this.subtypeOf(args[i], spp.sig.params[j].type as ResolvedType)) {
                    return false;
                }
                j++;
            }
            return true;
        });

        const rrsigs: {sig: ResolvedFunctionType, idx: number}[] = [];
        for(let i = 0; i < ppairs.length; ++i) {
            const isig = ppairs[i].sig;
            let nomorespecific = true;

            for(let j = 0; j < ppairs.length; ++j) {
                if(i == j) {
                    continue;
                }

                const jsig = ppairs[j].sig;
                let morespecific = false;
                for(let k = 0; k < isig.params.length; ++ k) {
                    if(isig.params[k] instanceof ResolvedFunctionType) {
                        continue;
                    }

                    if(this.subtypeOf(jsig.params[k].type as ResolvedType, isig.params[k].type as ResolvedType)) {
                        morespecific = true;
                        break;
                    } 
                }

                if(morespecific) {
                    nomorespecific = false;
                    break;
                }
            }

            if(nomorespecific) {
                rrsigs.push(ppairs[i]);
            }
        }

        if(rrsigs.length !== 1) {
            return -1;
        }
        else {
            return rrsigs[0].idx;
        }
    }

    resolveBindsForCallComplete(declterms: TemplateTermDecl[], giventerms: TypeSignature[], implicitBinds: Map<string, ResolvedType>, callBinds: Map<string, ResolvedType>, inferBinds: Map<string, ResolvedType>): Map<string, ResolvedType> | undefined {
        let fullbinds = new Map<string, ResolvedType>();
        implicitBinds.forEach((v, k) => {
            fullbinds.set(k, v);
        });

        for (let i = 0; i < declterms.length; ++i) {
            if(giventerms.length <= i) {
                if(declterms[i].defaultType !== undefined) {
                    fullbinds.set(declterms[i].name, this.normalizeTypeOnly(declterms[i].defaultType as TypeSignature, implicitBinds));
                }
                else if (declterms[i].isInfer) {
                    if(!inferBinds.has(declterms[i].name)) {
                        return undefined;
                    }
                    else {
                        fullbinds.set(declterms[i].name, inferBinds.get(declterms[i].name) as ResolvedType);
                    }
                }
                else {
                    return undefined;
                }
            }
            else {
                fullbinds.set(declterms[i].name, this.normalizeTypeOnly(giventerms[i], callBinds));
            }
        }

        return fullbinds;
    }

    resolveBindsForCallWithInfer(declterms: TemplateTermDecl[], giventerms: TypeSignature[], implicitBinds: Map<string, ResolvedType>, callBinds: Map<string, ResolvedType>): [Map<string, ResolvedType> | undefined, string[]] {
        let fullbinds = new Map<string, ResolvedType>();
        let inferbinds: string[] = [];
        implicitBinds.forEach((v, k) => {
            fullbinds.set(k, v);
        });

        for (let i = 0; i < declterms.length; ++i) {
            if(giventerms.length <= i) {
                if(declterms[i].defaultType !== undefined) {
                    fullbinds.set(declterms[i].name, this.normalizeTypeOnly(declterms[i].defaultType as TypeSignature, implicitBinds));
                }
                else if (declterms[i].isInfer) {
                    inferbinds.push(declterms[i].name);
                    fullbinds.set(declterms[i].name, ResolvedType.createSingle(ResolvedTemplateUnifyType.create(declterms[i].name)));
                }
                else {
                    return [undefined, inferbinds];
                }
            }
            else {
                fullbinds.set(declterms[i].name, this.normalizeTypeOnly(giventerms[i], callBinds));
            }
        }

        return [fullbinds, inferbinds];
    }

    normalizeTypeOnly(t: TypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const res = this.normalizeTypeGeneral(t, binds);
        if (res instanceof ResolvedFunctionType) {
            return ResolvedType.createEmpty();
        }
        else {
            return res;
        }
    }

    normalizeTypeFunction(t: TypeSignature, binds: Map<string, ResolvedType>): ResolvedFunctionType | undefined {
        if (t instanceof ParseErrorTypeSignature || t instanceof AutoTypeSignature) {
            return undefined;
        }
        else {
            return this.normalizeType_Function(t as FunctionTypeSignature, binds);
        }
    }

    normalizeTypeGeneral(t: TypeSignature, binds: Map<string, ResolvedType>): ResolvedType | ResolvedFunctionType {
        if (t instanceof ParseErrorTypeSignature || t instanceof AutoTypeSignature) {
            return ResolvedType.createEmpty();
        }
        else if (t instanceof FunctionTypeSignature) {
            return this.normalizeTypeFunction(t, binds) || ResolvedType.createEmpty();
        }
        else if (t instanceof TemplateTypeSignature) {
            return this.normalizeType_Template(t, binds);
        }
        else if (t instanceof NominalTypeSignature) {
            return this.normalizeType_Nominal(t, binds);
        }
        else if (t instanceof TupleTypeSignature) {
            return this.normalizeType_Tuple(t, binds);
        }
        else if (t instanceof RecordTypeSignature) {
            return this.normalizeType_Record(t, binds);
        }
        else if (t instanceof EphemeralListTypeSignature) {
            return this.normalizeType_EphemeralList(t, binds);
        }
        else if(t instanceof ProjectTypeSignature) {
            return this.normalizeType_Projection(t, binds);
        }
        else if (t instanceof PlusTypeSignature) {
            return this.normalizeType_Plus(t, binds);
        }
        else if (t instanceof AndTypeSignature) {
            return this.normalizeType_And(t, binds);
        }
        else {
            return this.normalizeType_Union(t as UnionTypeSignature, binds);
        }
    }

    normalizeToNominalRepresentation(t: ResolvedAtomType): ResolvedAtomType {
        if (t instanceof ResolvedTupleAtomType) {
            return this.getSpecialTupleConceptType();
        }
        else if (t instanceof ResolvedRecordAtomType) {
            return this.getSpecialRecordConceptType();
        }
        else {
            return t;
        }
    }

    restrictNone(from: ResolvedType): { tp: ResolvedType, fp: ResolvedType } {
        return this.splitTypes(from, this.getSpecialNoneType());
    }

    restrictSome(from: ResolvedType): { tp: ResolvedType, fp: ResolvedType } {
        return this.splitTypes(from, this.getSpecialSomeConceptType());
    }

    restrictNothing(from: ResolvedType): { tp: ResolvedType, fp: ResolvedType } {
        return this.splitTypes(from, this.getSpecialNothingType());
    }

    restrictSomething(from: ResolvedType): { tp: ResolvedType, fp: ResolvedType } {
        return this.splitTypes(from, this.getSpecialISomethingConceptType());
    }

    restrictT(from: ResolvedType, t: ResolvedType): { tp: ResolvedType, fp: ResolvedType } {
        return this.splitTypes(from, t);
    }

    typeUpperBound(types: ResolvedType[]): ResolvedType {
        if(types.length === 0) {
            return ResolvedType.createEmpty();
        }
        else {
            return this.normalizeUnionList(types);
        }
    }

    atomSubtypeOf(t1: ResolvedAtomType, t2: ResolvedAtomType): boolean {
        let memores = this.m_atomSubtypeRelationMemo.get(t1.typeID);
        if (memores === undefined) {
            this.m_atomSubtypeRelationMemo.set(t1.typeID, new Map<string, boolean>());
            memores = this.m_atomSubtypeRelationMemo.get(t1.typeID) as Map<string, boolean>;
        }

        let memoval = memores.get(t2.typeID);
        if (memoval !== undefined) {
            return memoval;
        }

        let res = false;

        if (t1.typeID === t2.typeID) {
            res = true;
        }
        else if (t1 instanceof ResolvedConceptAtomType && t2 instanceof ResolvedConceptAtomType) {
            res = this.atomSubtypeOf_ConceptConcept(t1, t2);
        }
        else if (t2 instanceof ResolvedConceptAtomType) {
            if (t1 instanceof ResolvedEntityAtomType) {
                res = this.atomSubtypeOf_EntityConcept(t1, t2);
            }
            else if (t1 instanceof ResolvedTupleAtomType) {
                res = this.atomSubtypeOf_TupleConcept(t1, t2);
            }
            else if (t1 instanceof ResolvedRecordAtomType) {
                res = this.atomSubtypeOf_RecordConcept(t1, t2);
            }
            else {
                //fall-through
            }
        }
        else {
            //fall-through
        }

        memores.set(t2.typeID, res);
        return res;
    }

    subtypeOf(t1: ResolvedType, t2: ResolvedType): boolean {
        let memores = this.m_subtypeRelationMemo.get(t1.typeID);
        if (memores === undefined) {
            this.m_subtypeRelationMemo.set(t1.typeID, new Map<string, boolean>());
            memores = this.m_subtypeRelationMemo.get(t1.typeID) as Map<string, boolean>;
        }

        let memoval = memores.get(t2.typeID);
        if (memoval !== undefined) {
            return memoval;
        }

        const res = (t1.typeID === t2.typeID) || t1.options.every((t1opt) => t2.options.some((t2opt) => this.atomSubtypeOf(t1opt, t2opt)));

        memores.set(t2.typeID, res);
        return res;
    }
 
    atomUnify(t1: ResolvedAtomType, t2: ResolvedAtomType, umap: Map<string, ResolvedType | undefined>) {
        if(t1 instanceof ResolvedTemplateUnifyType) {
            if(umap.has(t1.typeID)) {
                if(umap.get(t1.typeID) === undefined || (umap.get(t1.typeID) as ResolvedType).typeID === t2.typeID) {
                    //leave it
                }
                else {
                    umap.set(t1.typeID, undefined);
                }
            }
            else {
                umap.set(t1.typeID, ResolvedType.createSingle(t2));
            }
        }
        else if(t1 instanceof ResolvedEntityAtomType && t2 instanceof ResolvedEntityAtomType) {
            this.unifyResolvedEntityAtomType(t1, t2, umap);
        }
        else if(t1 instanceof ResolvedConceptAtomType && t2 instanceof ResolvedConceptAtomType) {
            this.unifyResolvedConceptAtomType(t1, t2, umap);
        }
        else if(t1 instanceof ResolvedTupleAtomType && t2 instanceof ResolvedTupleAtomType) {
            this.unifyResolvedTupleAtomType(t1, t2, umap);
        }
        else if(t1 instanceof ResolvedRecordAtomType && t2 instanceof ResolvedRecordAtomType) {
            this.unifyResolvedRecordAtomType(t1, t2, umap);
        }
        else {
            //nothing -- types might mismatch but we don't care as typecheck will catch this later
        }
    }

    typeUnify(t1: ResolvedType, t2: ResolvedType, umap: Map<string, ResolvedType | undefined>) {
        //TODO: we may want to try and strip matching types in any options -- T | None ~~ Int | None should unify T -> Int

        if (t1.options.length === 1 && t1.options[0] instanceof ResolvedTemplateUnifyType) {
            if (umap.has(t1.typeID)) {
                if (umap.get(t1.typeID) === undefined || (umap.get(t1.typeID) as ResolvedType).typeID === t2.typeID) {
                    //leave it
                }
                else {
                    umap.set(t1.typeID, undefined);
                }
            }
            else {
                if (t2.options.length !== 1) {
                    //if multiple options unify with the | 
                    umap.set(t1.typeID, t2); 
                }
                else {
                    //otherwise expand and try unifying with the individual type
                    this.atomUnify(t1.options[0], t2.options[0], umap);
                }
            }
        }

        if(t1.options.length === 1 && t1.options[0] instanceof ResolvedEntityAtomType && t1.options[0].object.attributes.includes("__list_type")
            && t2.options.length === 1 && t2.options[0] instanceof ResolvedEntityAtomType && t2.options[0].object.attributes.includes("__list_type")) {
                this.typeUnify(t1.options[0].binds.get("T") as ResolvedType, t2.options[0].binds.get("T") as ResolvedType, umap);
        }

        //otherwise we do nothing and will fail subtype check later 
    }

    resolveProvides(tt: OOPTypeDecl, binds: Map<string, ResolvedType>): TypeSignature[] {
        let oktypes: TypeSignature[] = [];
        
        for (let i = 0; i < tt.provides.length; ++i) {
            const psig = tt.provides[i][0];
            const pcond = tt.provides[i][1];
            
            if(pcond === undefined) {
                oktypes.push(psig);
            }
            else {
                const allok = pcond.constraints.every((consinfo) => {
                    const constype = this.normalizeTypeOnly(consinfo.t, binds)
                    return this.subtypeOf(constype, this.normalizeTypeOnly(consinfo.tconstraint, binds));
                });

                if(allok) {
                    oktypes.push(psig);
                }
            }
        }

        return oktypes;
    }

    private functionSubtypeOf_helper(t1: ResolvedFunctionType, t2: ResolvedFunctionType): boolean {
        if (t2.isPred !== t1.isPred) {
            return false; //need to have same pred spec
        }

        if (t2.params.length !== t1.params.length) {
            return false; //need to have the same number of parameters
        }

        if ((t2.optRestParamType !== undefined) !== (t1.optRestParamType !== undefined)) {
            return false; //should both have rest or not
        }

        if (t2.optRestParamType !== undefined && t2.optRestParamType.typeID !== (t1.optRestParamType as ResolvedType).typeID) {
            return false; //variance
        }

        for (let i = 0; i < t2.params.length; ++i) {
            const t2p = t2.params[i];
            const t1p = t1.params[i];
            if ((t2p.isOptional !== t1p.isOptional) || (t2p.refKind !== t1p.refKind)) {
                return false;
            }

            if(t2p.litexp !== undefined && t2p.litexp !== t1p.litexp) {
                return false;
            }

            //We want the argument types to be the same for all cases -- no clear reason to overload to more general types
            if (t2p.type instanceof ResolvedFunctionType && t1p.type instanceof ResolvedFunctionType) {
                if (t2p.type.typeID !== t1p.type.typeID) {
                    return false;
                }
            }
            else if (t2p.type instanceof ResolvedType && t1p.type instanceof ResolvedType) {
                if (t2p.type.typeID !== t1p.type.typeID) {
                    return false;
                }
            }
            else {
                return false;
            }

            //check that if t2p is named then t1p has the same name
            if (t2.params[i].name !== "_") {
                if (t2.params[i].name !== t1.params[i].name) {
                    return false;
                }
            }
        }

        if(t1.resultType.typeID !== t2.resultType.typeID) {
            return false;
        }

        return true;
    }

    //Only used for pcode checking
    functionSubtypeOf(t1: ResolvedFunctionType, t2: ResolvedFunctionType): boolean {
        let memores = this.m_subtypeRelationMemo.get(t1.typeID);
        if (memores === undefined) {
            this.m_subtypeRelationMemo.set(t1.typeID, new Map<string, boolean>());
            memores = this.m_subtypeRelationMemo.get(t1.typeID) as Map<string, boolean>;
        }

        let memoval = memores.get(t2.typeID);
        if (memoval !== undefined) {
            return memoval;
        }

        const res = this.functionSubtypeOf_helper(t1, t2);

        memores.set(t2.typeID, res);
        return res;
    }
}

export {
    BuildApplicationMode, BuildLevel, isBuildLevelEnabled,
    TemplateTermDecl, TemplateTypeRestriction, TypeConditionRestriction, PreConditionDecl, PostConditionDecl, InvokeDecl,
    OOMemberDecl, InvariantDecl, ValidateDecl, StaticMemberDecl, StaticFunctionDecl, StaticOperatorDecl, MemberFieldDecl, MemberMethodDecl, OOPTypeDecl, ConceptTypeDecl, EntityTypeDecl,
    NamespaceConstDecl, NamespaceFunctionDecl, NamespaceOperatorDecl, NamespaceTypedef, NamespaceUsing, NamespaceDeclaration,
    OOMemberLookupInfo, Assembly
};
