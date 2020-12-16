//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ResolvedType, ResolvedRecordAtomType, ResolvedTupleAtomType, ResolvedTupleAtomTypeEntry, ResolvedRecordAtomTypeEntry, ResolvedAtomType, ResolvedFunctionTypeParam, ResolvedFunctionType, ResolvedConceptAtomTypeEntry, ResolvedConceptAtomType, ResolvedEntityAtomType, ResolvedEphemeralListType, ResolvedLiteralAtomType, ResolvedTemplateUnifyType } from "./resolved_type";
import { TemplateTypeSignature, NominalTypeSignature, TypeSignature, TupleTypeSignature, RecordTypeSignature, FunctionTypeSignature, UnionTypeSignature, ParseErrorTypeSignature, AutoTypeSignature, FunctionParameter, ProjectTypeSignature, EphemeralListTypeSignature, LiteralTypeSignature, PlusTypeSignature, AndTypeSignature } from "./type_signature";
import { Expression, BodyImplementation, LiteralBoolExpression, LiteralIntegralExpression, LiteralFloatPointExpression, LiteralRationalExpression, AccessStaticFieldExpression, AccessNamespaceConstantExpression, PrefixNotOp, CallNamespaceFunctionOrOperatorExpression, LiteralTypedNumericConstructorExpression, LiteralParamerterValueExpression, ConstantExpressionValue, LiteralNumberinoExpression, LiteralTypedStringExpression } from "./body";
import { SourceInfo } from "./parser";

import * as assert from "assert";
import { BSQRegex } from "./bsqregex";

type BuildLevel = "debug" | "test" | "release";

function isBuildLevelEnabled(check: BuildLevel, enabled: BuildLevel): boolean {
    if(enabled === "debug") {
        return true;
    }
    else if(enabled === "test") {
        return check === "test" || check === "release";
    }
    else {
        return check === "release";
    }
}

enum TemplateTermSpecialRestriction {
    Parsable, //implies unique
    Validator, //implies unique
    Struct, //modifies entity constructable
    Entity, //implies unique and constructable
    Grounded
}

class TemplateTermDecl {
    readonly name: string;
    readonly specialRestrictions: Set<TemplateTermSpecialRestriction>;
    readonly tconstraint: TypeSignature;
    readonly isInfer: boolean;
    readonly defaultType: TypeSignature | undefined;

    constructor(name: string, specialRestrictions: Set<TemplateTermSpecialRestriction>, tconstraint: TypeSignature, isinfer: boolean, defaulttype: TypeSignature | undefined) {
        this.name = name;
        this.specialRestrictions = specialRestrictions;
        this.tconstraint = tconstraint;
        this.isInfer = isinfer;
        this.defaultType = defaulttype;
    }
}

class TemplateTypeRestriction {
    readonly t: TypeSignature;
    readonly tconstraint: TypeSignature;

    constructor(t: TypeSignature, tconstraint: TypeSignature) {
        this.t = t;
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

class InvokeDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

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

    readonly isLambda: boolean;
    readonly captureSet: Set<string>;
    readonly body: BodyImplementation | undefined;

    constructor(sinfo: SourceInfo, srcFile: string, attributes: string[], recursive: "yes" | "no" | "cond", terms: TemplateTermDecl[], termRestrictions: TypeConditionRestriction | undefined, params: FunctionParameter[], optRestName: string | undefined, optRestType: TypeSignature | undefined, resultType: TypeSignature, preconds: PreConditionDecl[], postconds: PostConditionDecl[], isLambda: boolean, captureSet: Set<string>, body: BodyImplementation | undefined) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

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

        this.isLambda = isLambda;
        this.captureSet = captureSet;
        this.body = body;
    }

    generateSig(): TypeSignature {
        return new FunctionTypeSignature(this.recursive, [...this.params], this.optRestName, this.optRestType, this.resultType);
    }

    static createPCodeInvokeDecl(sinfo: SourceInfo, srcFile: string, attributes: string[], recursive: "yes" | "no" | "cond", params: FunctionParameter[], optRestName: string | undefined, optRestType: TypeSignature | undefined, resultInfo: TypeSignature, captureSet: Set<string>, body: BodyImplementation) {
        return new InvokeDecl(sinfo, srcFile, attributes, recursive, [], undefined, params, optRestName, optRestType, resultInfo, [], [], true, captureSet, body);
    }

    static createStandardInvokeDecl(sinfo: SourceInfo, srcFile: string, attributes: string[], recursive: "yes" | "no" | "cond", terms: TemplateTermDecl[], termRestrictions: TypeConditionRestriction | undefined, params: FunctionParameter[], optRestName: string | undefined, optRestType: TypeSignature | undefined, resultInfo: TypeSignature, preconds: PreConditionDecl[], postconds: PostConditionDecl[], body: BodyImplementation | undefined) {
        return new InvokeDecl(sinfo, srcFile, attributes, recursive, terms, termRestrictions, params, optRestName, optRestType, resultInfo, preconds, postconds, false, new Set<string>(), body);
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

enum SpecialTypeCategory {
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

class OOPTypeDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly specialDecls: Set<SpecialTypeCategory>;
    readonly ns: string;
    readonly name: string;

    readonly terms: TemplateTermDecl[];

    readonly provides: [TypeSignature, TypeConditionRestriction | undefined][];

    readonly invariants: InvariantDecl[];

    readonly staticMembers: Map<string, StaticMemberDecl>;
    readonly staticFunctions: Map<string, StaticFunctionDecl>;
    readonly staticOperators = new Map<string, StaticOperatorDecl[]>();
    readonly memberFields: Map<string, MemberFieldDecl>;
    readonly memberMethods: Map<string, MemberMethodDecl>;

    readonly nestedEntityDecls: Map<string, EntityTypeDecl>;

    constructor(sourceLocation: SourceInfo, srcFile: string, attributes: string[], specialDecls: SpecialTypeCategory[], ns: string, name: string, terms: TemplateTermDecl[], provides: [TypeSignature, TypeConditionRestriction | undefined][],
        invariants: InvariantDecl[],
        staticMembers: Map<string, StaticMemberDecl>, staticFunctions: Map<string, StaticFunctionDecl>, staticOperators: Map<string, StaticOperatorDecl[]>,
        memberFields: Map<string, MemberFieldDecl>, memberMethods: Map<string, MemberMethodDecl>,
        nestedEntityDecls: Map<string, EntityTypeDecl>) {
        this.sourceLocation = sourceLocation;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.specialDecls = new Set<SpecialTypeCategory>(specialDecls);
        this.ns = ns;
        this.name = name;
        this.terms = terms;
        this.provides = provides;
        this.invariants = invariants;
        this.staticMembers = staticMembers;
        this.staticFunctions = staticFunctions;
        this.staticOperators = staticOperators;
        this.memberFields = memberFields;
        this.memberMethods = memberMethods;
        this.nestedEntityDecls = nestedEntityDecls;
    }

    isTypeAnExpandoableCollection(): boolean {
        return this.isTypeAListEntity() || this.isTypeASetEntity() || this.isTypeAMapEntity();
    }

    isTypeAListEntity(): boolean {
        return this.specialDecls.has(SpecialTypeCategory.VectorTypeDecl) || this.specialDecls.has(SpecialTypeCategory.ListTypeDecl);
    }

    isTypeAQueueEntity(): boolean {
        return this.specialDecls.has(SpecialTypeCategory.QueueTypeDecl);
    }

    isTypeAStackEntity(): boolean {
        return this.specialDecls.has(SpecialTypeCategory.StackTypeDecl);
    }

    isTypeASetEntity(): boolean {
        return this.specialDecls.has(SpecialTypeCategory.SetTypeDecl) || this.specialDecls.has(SpecialTypeCategory.DynamicSetTypeDecl);
    }

    isTypeAMapEntity(): boolean {
        return this.specialDecls.has(SpecialTypeCategory.MapTypeDecl) || this.specialDecls.has(SpecialTypeCategory.DynamicMapTypeDecl);
    }

    isTypeGrounded(): boolean {
        return this.specialDecls.has(SpecialTypeCategory.GroundedTypeDecl);
    }

    static attributeSetContains(attr: string, attrSet: string[]): boolean {
        return attrSet.indexOf(attr) !== -1;
    }
}

class ConceptTypeDecl extends OOPTypeDecl {
    constructor(sourceLocation: SourceInfo, srcFile: string, attributes: string[], specialDecls: SpecialTypeCategory[], ns: string, name: string, terms: TemplateTermDecl[], provides: [TypeSignature, TypeConditionRestriction | undefined][],
        invariants: InvariantDecl[],
        staticMembers: Map<string, StaticMemberDecl>, staticFunctions: Map<string, StaticFunctionDecl>, staticOperators: Map<string, StaticOperatorDecl[]>,
        memberFields: Map<string, MemberFieldDecl>, memberMethods: Map<string, MemberMethodDecl>,
        nestedEntityDecls: Map<string, EntityTypeDecl>) {
        super(sourceLocation, srcFile, attributes, specialDecls, ns, name, terms, provides, invariants, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, nestedEntityDecls);
    }
}

class EntityTypeDecl extends OOPTypeDecl {
    constructor(sourceLocation: SourceInfo, srcFile: string, attributes: string[], specialDecls: SpecialTypeCategory[], ns: string, name: string, terms: TemplateTermDecl[], provides: [TypeSignature, TypeConditionRestriction | undefined][],
        invariants: InvariantDecl[],
        staticMembers: Map<string, StaticMemberDecl>, staticFunctions: Map<string, StaticFunctionDecl>, staticOperators: Map<string, StaticOperatorDecl[]>,
        memberFields: Map<string, MemberFieldDecl>, memberMethods: Map<string, MemberMethodDecl>,
        nestedEntityDecls: Map<string, EntityTypeDecl>) {
        super(sourceLocation, srcFile, attributes, specialDecls, ns, name, terms, provides, invariants, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, nestedEntityDecls);
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

    constructor(sinfo: SourceInfo, srcFile: string, ns: string, name: string, invoke: InvokeDecl, level?: number) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

        this.isPrefix = invoke.attributes.includes("prefix");
        this.isInfix = invoke.attributes.includes("infix");
        this.isDynamic = invoke.attributes.includes("dynamic");
        this.level = level || -1;
        this.ns = ns;
        this.name = name;

        this.invoke = invoke;
    }

    doesKindTagMatch(tag: "prefix" | "infix" | "std"): boolean {
        return (tag === "prefix" && this.isPrefix) || (tag === "infix" && this.isInfix) || (tag === "std" && !this.isPrefix && !this.isInfix);
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

        return fullbinds;
    }

    processNumberinoExpressionIntoTypedExpression(exp: LiteralNumberinoExpression, infertype: ResolvedType): Expression | undefined {
        //We will do bounds checking later so just make sure general format is ok here
        const isfpnum = exp.value.includes(".");

        if(infertype.isSameType(this.getSpecialIntType())) {
            return !isfpnum ? new LiteralIntegralExpression(exp.sinfo, exp.value + "i", this.getSpecialIntType()) : undefined;
        }
        else if(infertype.isSameType(this.getSpecialNatType())) {
            return !isfpnum ? new LiteralIntegralExpression(exp.sinfo, exp.value + "n", this.getSpecialNatType()) : undefined;
        }
        else if(infertype.isSameType(this.getSpecialBigIntType())) {
            return !isfpnum ? new LiteralIntegralExpression(exp.sinfo, exp.value + "I", this.getSpecialBigIntType()) : undefined;
        }
        else if(infertype.isSameType(this.getSpecialBigNatType())) {
            return !isfpnum ? new LiteralIntegralExpression(exp.sinfo, exp.value + "N", this.getSpecialBigNatType()) : undefined;
        }
        else if(infertype.isSameType(this.getSpecialFloatType())) {
            return new LiteralFloatPointExpression(exp.sinfo, exp.value + "f", this.getSpecialFloatType());
        }
        else if(infertype.isSameType(this.getSpecialDecimalType())) {
            return new LiteralFloatPointExpression(exp.sinfo, exp.value + "d", this.getSpecialDecimalType());
        }
        else if(infertype.isSameType(this.getSpecialRationalType())) {
            return new LiteralRationalExpression(exp.sinfo, exp.value + "/1R", this.getSpecialRationalType());
        }
        else {
            if(!infertype.isUniqueCallTargetType() || !infertype.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.TypeDeclNumeric)) {
                return undefined;
            }

            const tt = (infertype.getUniqueCallTargetType().object.memberFields.get("value") as MemberFieldDecl).declaredType;
            const rtt = this.normalizeTypeOnly(tt, new Map<string, ResolvedType>());

            const le = this.processNumberinoExpressionIntoTypedExpression(exp, rtt);
            if (le === undefined) {
                return undefined;
            }

            if (le instanceof LiteralIntegralExpression) {
                return new LiteralTypedNumericConstructorExpression(exp.sinfo, le.value, le.itype, infertype);
            }
            else if (le instanceof LiteralFloatPointExpression) {
                return new LiteralTypedNumericConstructorExpression(exp.sinfo, le.value, le.fptype, infertype);
            }
            else {
                const re = le as LiteralRationalExpression;
                return new LiteralTypedNumericConstructorExpression(exp.sinfo, re.value, re.rtype, infertype);
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
                    if(oftype.isUniqueCallTargetType() && oftype.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.ValidatorTypeDecl)) {
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
        else if (exp instanceof LiteralParamerterValueExpression) {
            const vv = (binds.get(exp.ltype.name) as ResolvedType).options[0] as ResolvedLiteralAtomType;
            return vv.vexp;
        }
        else if (exp instanceof PrefixNotOp) {
            const earg = this.compileTimeReduceConstantExpression(exp.exp, binds, undefined);
            if (earg === undefined) {
                return undefined;
            }

            if (earg instanceof LiteralBoolExpression) {
                return new LiteralBoolExpression(exp.sinfo, !earg.value);
            }
            else {
                return undefined;
            }
        }
        else if (exp instanceof CallNamespaceFunctionOrOperatorExpression) {
            if(exp.opkind !== "prefix") {
                return undefined;
            }

            if(exp.name !== "+" && exp.name !== "-") {
                return undefined;
            }

            const earg = this.compileTimeReduceConstantExpression(exp.args.argList[0].value, binds, infertype);
            if (earg === undefined) {
                return undefined;
            }

            const nsdecl = this.m_namespaceMap.get("NSMain") as NamespaceDeclaration;
            if (earg instanceof LiteralIntegralExpression || earg instanceof LiteralFloatPointExpression || earg instanceof LiteralRationalExpression) {
                if(exp.name === "+") {
                    return earg;
                }
                else {
                    if(earg instanceof LiteralIntegralExpression) {
                        return new LiteralIntegralExpression(earg.sinfo, earg.value.startsWith("-") ? earg.value.slice(1) : ("-" + earg.value), earg.itype);
                    }
                    else if (earg instanceof LiteralFloatPointExpression) {
                        return new LiteralFloatPointExpression(earg.sinfo, earg.value.startsWith("-") ? earg.value.slice(1) : ("-" + earg.value), earg.fptype);
                    }
                    else {
                        return new LiteralRationalExpression(earg.sinfo, earg.value.startsWith("-") ? earg.value.slice(1) : ("-" + earg.value), earg.rtype);
                    }
                }
            }
            else if(earg instanceof LiteralTypedNumericConstructorExpression) {
                const opdecls = (nsdecl.operators.get(exp.name) as NamespaceOperatorDecl[]).filter((nso) => !OOPTypeDecl.attributeSetContains("abstract", nso.invoke.attributes));

                const isigs = opdecls.map((opd) => this.normalizeTypeFunction(opd.invoke.generateSig(), new Map<string, ResolvedType>()) as ResolvedFunctionType);
                const opidx = this.tryGetUniqueStaticOperatorResolve([this.normalizeTypeOnly(earg.ntype, new Map<string, ResolvedType>())], isigs);
                if (opidx === -1 || (opdecls[opidx].invoke.body as BodyImplementation).body !== undefined) {
                    return undefined;
                }

                if(exp.name === "+") {
                    return earg;
                }
                else {
                    return new LiteralTypedNumericConstructorExpression(earg.sinfo, earg.value.startsWith("-") ? earg.value.slice(1) : ("-" + earg.value), earg.ntype, earg.vtype);
                }
            }
            else {
                return undefined;
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
            if(cdecl.contiainingType.specialDecls.has(SpecialTypeCategory.EnumTypeDecl)) {
                return (cdecl.decl.value as ConstantExpressionValue).exp //must be an enum which cannot have template terms so don't care about binds;
            }
            else {
                return cdecl.decl.value !== undefined ? this.compileTimeReduceConstantExpression(cdecl.decl.value.exp, cdecl.binds, this.normalizeTypeOnly(cdecl.decl.declaredType, cdecl.binds)) : undefined;
            }
        }
        else {
            return undefined;
        }
    }

    reduceLiteralValueToCanonicalForm(exp: Expression, binds: Map<string, ResolvedType>, infertype: ResolvedType | undefined): [Expression, ResolvedType, string, boolean | number | undefined] | undefined {
        const cexp = this.compileTimeReduceConstantExpression(exp, binds, infertype);
        if(cexp === undefined) {
            return undefined;
        }

        if(cexp instanceof LiteralBoolExpression) {
            return [cexp, this.getSpecialBoolType(), `${cexp.value}`, cexp.value];
        }
        else if(cexp instanceof LiteralIntegralExpression) {
            if(this.getSpecialIntType().isSameType(this.normalizeTypeOnly(cexp.itype, new Map<string, ResolvedType>()))) {
                return [cexp, this.normalizeTypeOnly(cexp.itype, new Map<string, ResolvedType>()), cexp.value, Number.parseInt(cexp.value.slice(0, cexp.value.length - 1))];
            }
            else if(this.getSpecialNatType().isSameType(this.normalizeTypeOnly(cexp.itype, new Map<string, ResolvedType>()))) {
                return [cexp, this.normalizeTypeOnly(cexp.itype, new Map<string, ResolvedType>()), cexp.value, Number.parseInt(cexp.value.slice(0, cexp.value.length - 1))];
            }
            else {
                return undefined;
            }
        }
        else if(cexp instanceof LiteralTypedNumericConstructorExpression) {
            if(this.getSpecialIntType().isSameType(this.normalizeTypeOnly(cexp.ntype, new Map<string, ResolvedType>()))) {
                return [cexp, this.normalizeTypeOnly(cexp.vtype, new Map<string, ResolvedType>()), cexp.value, undefined];
            }
            else if(this.getSpecialNatType().isSameType(this.normalizeTypeOnly(cexp.ntype, new Map<string, ResolvedType>()))) {
                return [cexp, this.normalizeTypeOnly(cexp.vtype, new Map<string, ResolvedType>()), cexp.value, undefined];
            }
            else {
                return undefined;
            }
        }
        else if(cexp instanceof AccessStaticFieldExpression) {
            const stype = this.normalizeTypeOnly(cexp.stype, new Map<string, ResolvedType>());
            return [cexp, stype, `${stype.idStr}::${cexp.name}`, undefined];
        }
        else {
            return undefined;
        }

    }

    private checkTuplesMustDisjoint(t1: ResolvedTupleAtomType, t2: ResolvedTupleAtomType): boolean {
        if(t1.isvalue !== t2.isvalue) {
            return true;
        }

        for(let i = 0; i < t1.types.length; ++i) {
            if(t1.types[i].isOptional) {
                break;
            }

            if(i <= t2.types.length || !t1.types[i].type.isSameType(t2.types[i].type)) {
                return true;
            }
        }

        for(let i = 0; i < t2.types.length; ++i) {
            if(t2.types[i].isOptional) {
                break;
            }

            if(i <= t1.types.length || !t2.types[i].type.isSameType(t1.types[i].type)) {
                return true;
            }
        }

        return false;
    }

    private checkRecordsMustDisjoint(r1: ResolvedRecordAtomType, r2: ResolvedRecordAtomType): boolean {
        if(r1.isvalue !== r2.isvalue) {
            return true;
        }

        for(let i = 0; i < r1.entries.length; ++i) {
            if(r1.entries[i].isOptional) {
                break;
            }

            const r2e = r2.entries.find((entry) => entry.name === r1.entries[i].name);
            if(r2e === undefined || !r1.entries[i].type.isSameType(r2e.type)) {
                return true;
            }
        }

        for(let i = 0; i < r2.entries.length; ++i) {
            if(r2.entries[i].isOptional) {
                break;
            }

            const r1e = r1.entries.find((entry) => entry.name === r2.entries[i].name);
            if(r1e === undefined || !r2.entries[i].type.isSameType(r1e.type)) {
                return true;
            }
        }

        return false;
    }

    private checkAllTupleEntriesOfType(tt: ResolvedTupleAtomType, t2: ResolvedType): boolean {
        return tt.types.every((entry) => this.subtypeOf(entry.type, t2));
    }

    private getConceptsProvidedByTuple(tt: ResolvedTupleAtomType): ResolvedConceptAtomType {
        let tci: ResolvedConceptAtomTypeEntry[] = [...(this.getSpecialSomeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes];
        if (tt.grounded) {
            if (tt.isvalue && this.checkAllTupleEntriesOfType(tt, this.getSpecialKeyTypeConceptType())) {
                tci.push(...(this.getSpecialKeyTypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
            }
            if (this.checkAllTupleEntriesOfType(tt, this.getSpecialAPITypeConceptType())) {
                if (this.checkAllTupleEntriesOfType(tt, this.getSpecialPODTypeConceptType())) {
                    tci.push(...(this.getSpecialPODTypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
                }
                else {
                    tci.push(...(this.getSpecialAPITypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
                }
            }
        }

        return ResolvedConceptAtomType.create(tci);
    }

    private checkAllRecordEntriesOfType(rr: ResolvedRecordAtomType, t2: ResolvedType): boolean {
        return rr.entries.every((entry) => this.subtypeOf(entry.type, t2));
    }

    private getConceptsProvidedByRecord(rr: ResolvedRecordAtomType): ResolvedConceptAtomType {
        let tci: ResolvedConceptAtomTypeEntry[] = [...(this.getSpecialSomeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes];
        if (rr.grounded) {
            if (rr.isvalue && this.checkAllRecordEntriesOfType(rr, this.getSpecialKeyTypeConceptType())) {
                tci.push(...(this.getSpecialKeyTypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
            }
            if (this.checkAllRecordEntriesOfType(rr, this.getSpecialAPITypeConceptType())) {
                if (this.checkAllRecordEntriesOfType(rr, this.getSpecialPODTypeConceptType())) {
                    tci.push(...(this.getSpecialPODTypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
                }
                else {
                    tci.push(...(this.getSpecialAPITypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
                }
            }
        }

        return ResolvedConceptAtomType.create(tci);
    }

    private splitConceptTypes(ofc: ResolvedConceptAtomType, withc: ResolvedConceptAtomType): {tp: ResolvedAtomType | undefined, fp: ResolvedAtomType | undefined} {
        if (ofc.idStr === "NSCore::Any" && withc.idStr === "NSCore::Some") {
            return { tp: withc, fp: this.getSpecialNoneType() };
        }
        else {
            const itypes = [...ofc.conceptTypes, ...withc.conceptTypes].sort((cte1, cte2) => cte1.idStr.localeCompare(cte2.idStr));

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

            const tpt = ResolvedConceptAtomType.create(simplifiedTypes);

            return { tp: tpt, fp: ofc };
        }
    }

    private splitConceptEntityTypes(ofc: ResolvedConceptAtomType, withe: ResolvedEntityAtomType): { tp: ResolvedAtomType | undefined, fp: ResolvedAtomType | undefined } {
        if (ofc.idStr === "NSCore::Any" && withe.idStr === "NSCore::None") {
            return { tp: withe, fp: this.getSpecialSomeConceptType() };
        }
        else if(ofc.idStr.startsWith("NSCore::Result<")) {
            const okdecl = this.tryGetObjectTypeForFullyResolvedName("NSCore::Result::Ok") as EntityTypeDecl;
            const okt = ResolvedEntityAtomType.create(okdecl, ofc.conceptTypes[0].binds);

            const errdecl = this.tryGetObjectTypeForFullyResolvedName("NSCore::Result::Err") as EntityTypeDecl;
            const errt = ResolvedEntityAtomType.create(errdecl, ofc.conceptTypes[0].binds);

            if(withe.idStr === ofc.idStr.replace("NSCore::Result", "NSCore::Result::Ok")) {
                return { tp: okt, fp: errt };
            }
            else if (withe.idStr === ofc.idStr.replace("NSCore::Result", "NSCore::Result::Err")) {
                return { tp: errt, fp: okt };
            }
            else {
                return { tp: withe, fp: ofc };
            }
        }
        else if(this.atomSubtypeOf(withe, ofc)) {
            return { tp: withe, fp: ofc };
        }
        else {
            return { tp: undefined, fp: ofc };
        }
    }

    private splitConceptTuple(ofc: ResolvedConceptAtomType, witht: ResolvedTupleAtomType): { tp: ResolvedAtomType | undefined, fp: ResolvedAtomType | undefined } {
        if (this.atomSubtypeOf(this.getConceptsProvidedByTuple(witht), ofc)) {
            return { tp: witht, fp: ofc };
        }
        else {
            return { tp: undefined, fp: ofc };
        }
    }

    private splitConceptRecord(ofc: ResolvedConceptAtomType, withr: ResolvedRecordAtomType): { tp: ResolvedAtomType | undefined, fp: ResolvedAtomType | undefined } {
        if (this.atomSubtypeOf(this.getConceptsProvidedByRecord(withr), ofc)) {
            return { tp: withr, fp: ofc };
        }
        else {
            return { tp: undefined, fp: ofc };
        }
    }

    private splitAtomTypes(ofa: ResolvedAtomType, witha: ResolvedAtomType): { tp: ResolvedAtomType | undefined, fp: ResolvedAtomType | undefined } {
        if (this.atomSubtypeOf(ofa, witha)) {
            return { tp: ofa, fp: undefined };
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
                return { tp: undefined, fp: ofa };
            }
        }
        else if (ofa instanceof ResolvedTupleAtomType) {
            if (witha instanceof ResolvedTupleAtomType && !this.checkTuplesMustDisjoint(ofa, witha)) {
                return { tp: witha, fp: ofa };
            }
            else {
                return { tp: undefined, fp: ofa };
            }
        }
        else if (ofa instanceof ResolvedRecordAtomType) {
            if (witha instanceof ResolvedRecordAtomType && !this.checkRecordsMustDisjoint(ofa, witha)) {
                return { tp: witha, fp: ofa };
            }
            else {
                return { tp: undefined, fp: ofa };
            }
        }
        else {
            return { tp: undefined, fp: ofa };
        }
    }

    private splitAtomWithType(ofa: ResolvedAtomType, witht: ResolvedType): { tp: ResolvedType[], fp: ResolvedType[] } {
        let tp: ResolvedType[] = [];
        let fp: ResolvedType[] = [];
        witht.options
            .map((opt) => this.splitAtomTypes(ofa, opt))
            .forEach((rr) => {
                if(rr.tp !== undefined) {
                    tp.push(ResolvedType.createSingle(rr.tp));
                }
                if(rr.fp !== undefined) {
                    fp.push(ResolvedType.createSingle(rr.fp));
                }
            });

        return { tp: tp, fp: fp };
    }

    splitTypes(oft: ResolvedType, witht: ResolvedType): { tp: ResolvedType, fp: ResolvedType } {
        if (oft.isEmptyType() || witht.isEmptyType()) {
            return { tp: ResolvedType.createEmpty(), fp: ResolvedType.createEmpty() };
        }

        if (oft.idStr === witht.idStr) {
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

            if(idx < opt.types.length && !opt.types[idx].isOptional) {
                tpp.push(opt);
            }
            else if (opt.types.length <= idx) {
                fpp.push(opt);
            }
            else {
                let ttypes: ResolvedTupleAtomTypeEntry[] = [];
                let ftypes: ResolvedTupleAtomTypeEntry[] = [];
                for(let j = 0; j < opt.types.length; ++i) {
                    if(j < idx) {
                        ttypes.push(new ResolvedTupleAtomTypeEntry(opt.types[j].type, false));
                        ftypes.push(opt.types[j]);
                    }
                    else if (j === idx) {
                        ttypes.push(new ResolvedTupleAtomTypeEntry(opt.types[j].type, false));
                    }
                    else {
                        ttypes.push(opt.types[j]);
                    }
                }

                tpp.push(ResolvedTupleAtomType.create(opt.isvalue, ttypes));
                fpp.push(ResolvedTupleAtomType.create(opt.isvalue, ftypes));
            }
        }

        return {tp: ResolvedType.create(tpp), fp: ResolvedType.create(fpp)};
    }

    restrictTupleBaseOnMatch(oftype: ResolvedType, isvalue: boolean, reqcount: number, optcount: number): ResolvedType {
        let topts = (oftype.options.filter((opt) => {
            if(!(opt instanceof ResolvedTupleAtomType) || opt.isvalue !== isvalue) {
                return false;
            }

            if(opt.types.length < reqcount) {
                return false;
            }

            if(opt.types.length > optcount && !opt.types[optcount].isOptional) {
                return false;
            }

            return true;
        }) as ResolvedTupleAtomType[])
        .map((opt) => {
            return ResolvedTupleAtomType.create(opt.isvalue, opt.types.slice(0, optcount));
        });

        return ResolvedType.create(topts);
    }

    splitProperty(oft: ResolvedType, pname: string): { tp: ResolvedType, fp: ResolvedType } {
        if (oft.isEmptyType()) {
            return { tp: ResolvedType.createEmpty(), fp: ResolvedType.createEmpty() };
        }

        let tpp: ResolvedRecordAtomType[] = [];
        let fpp: ResolvedRecordAtomType[] = [];
        for(let i = 0; i < oft.options.length; ++i) {
            const opt = oft.options[i] as ResolvedRecordAtomType;

            const entry = opt.entries.find((ee) => ee.name === pname);
            if(entry !== undefined && !entry.isOptional) {
                tpp.push(opt);
            }
            else if (entry === undefined) {
                fpp.push(opt);
            }
            else {
                let ttypes: ResolvedRecordAtomTypeEntry[] = [];
                let ftypes: ResolvedRecordAtomTypeEntry[] = [];
                for(let j = 0; j < opt.entries.length; ++i) {
                    if (opt.entries[j].name === pname) {
                        ttypes.push(new ResolvedRecordAtomTypeEntry(pname, opt.entries[j].type, false));
                    }
                    else {
                        ttypes.push(opt.entries[j]);
                        ftypes.push(opt.entries[j])
                    }
                }

                tpp.push(ResolvedRecordAtomType.create(opt.isvalue, ttypes));
                fpp.push(ResolvedRecordAtomType.create(opt.isvalue, ftypes));
            }
        }

        return {tp: ResolvedType.create(tpp), fp: ResolvedType.create(fpp)};
    }

    restrictRecordBaseOnMatch(oftype: ResolvedType, isvalue: boolean, reqnames: Set<string>, optnames: Set<string>): ResolvedType {
        let topts = (oftype.options.filter((opt) => {
            if(!(opt instanceof ResolvedRecordAtomType) || opt.isvalue !== isvalue) {
                return false;
            }

            if(opt.entries.length < reqnames.size) {
                return false;
            }

            if(opt.entries.some((entry) => !entry.isOptional && !reqnames.has(entry.name) && !optnames.has(entry.name))) {
                return false;
            }

            return true;
        }) as ResolvedRecordAtomType[])
        .map((opt) => {
            const fentries = opt.entries.filter((entry) => reqnames.has(entry.name) || optnames.has(entry.name));
            return ResolvedTupleAtomType.create(opt.isvalue, fentries);
        });

        return ResolvedType.create(topts);
    }

    getDerivedTypeProjection(fromtype: ResolvedType, oftype: ResolvedType): ResolvedType {
        if(oftype.idStr === "NSCore::Record") {
            //
            //NOT IMPLEMENTED YET
            //
            assert(false);
            return ResolvedType.createEmpty();
        }
        else if(oftype.idStr === "NSCore::KeyType") {
            //
            //NOT IMPLEMENTED YET
            //
            assert(false);
            return ResolvedType.createEmpty();
        }
        else if(oftype.idStr === "NSCore::APIType") {
            //
            //NOT IMPLEMENTED YET
            //
            assert(false);
            return ResolvedType.createEmpty();
        }
        else {
            return ResolvedType.createEmpty();
        }
    }

    private normalizeType_Template(t: TemplateTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        return binds.has(t.name) ? binds.get(t.name) as ResolvedType : ResolvedType.createEmpty();
    }

    private normalizeType_Nominal(t: NominalTypeSignature, binds: Map<string, ResolvedType>): ResolvedType | ResolvedFunctionType {
        const [aliasResolvedType, aliasResolvedBinds] = this.lookupTypeDef(t, binds);
        if (aliasResolvedType === undefined) {
            return ResolvedType.createEmpty();
        }
        else if (!(aliasResolvedType instanceof NominalTypeSignature)) {
            return this.normalizeTypeGeneral(aliasResolvedType, aliasResolvedBinds);
        }
        else {
            const fconcept = this.tryGetConceptTypeForFullyResolvedName(aliasResolvedType.nameSpace + "::" + aliasResolvedType.computeResolvedName());
            if (fconcept !== undefined) {
                if (fconcept.terms.length !== aliasResolvedType.terms.length) {
                    return ResolvedType.createEmpty();
                }

                const cta = this.createConceptTypeAtom(fconcept, aliasResolvedType, aliasResolvedBinds);
                return cta !== undefined ? ResolvedType.createSingle(cta) : ResolvedType.createEmpty();
            }

            const fobject = this.tryGetObjectTypeForFullyResolvedName(aliasResolvedType.nameSpace + "::" + aliasResolvedType.computeResolvedName());
            if (fobject !== undefined) {
                if (fobject.terms.length !== aliasResolvedType.terms.length) {
                    return ResolvedType.createEmpty();
                }

                const ota = this.createObjectTypeAtom(fobject, aliasResolvedType, aliasResolvedBinds);
                return ota !== undefined ? ResolvedType.createSingle(ota) : ResolvedType.createEmpty();
            }

            return ResolvedType.createEmpty();
        }
    }

    private normalizeType_Literal(l: LiteralTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const cform = this.reduceLiteralValueToCanonicalForm(l.typevalue.exp, binds, undefined);
        if(cform === undefined || cform[1].isEmptyType()) {
            return ResolvedType.createEmpty();
        }

        let ltype = cform[1];
        let tval = cform[0];

        return ResolvedType.createSingle(ResolvedLiteralAtomType.create(ltype, tval, cform[2], cform[3]));
    }

    private normalizeType_Tuple(t: TupleTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const entries = t.entries.map((entry) => new ResolvedTupleAtomTypeEntry(this.normalizeTypeOnly(entry[0], binds), entry[1]));
        if (entries.some((e) => e.type.isEmptyType())) {
            return ResolvedType.createEmpty();
        }

        let seenreq = false;
        for (let i = entries.length - 1; i >= 0; --i) {
            seenreq = seenreq || !entries[i].isOptional;
            if (entries[i].isOptional && seenreq) {
                return ResolvedType.createEmpty();
            }
        }

        return ResolvedType.createSingle(ResolvedTupleAtomType.create(t.isvalue, entries));
    }

    private normalizeType_Record(t: RecordTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        let seenNames = new Set<string>();
        let entries: ResolvedRecordAtomTypeEntry[] = [];
        for (let i = 0; i < t.entries.length; ++i) {
            if (seenNames.has(t.entries[i][0])) {
                return ResolvedType.createEmpty();
            }

            entries.push(new ResolvedRecordAtomTypeEntry(t.entries[i][0], this.normalizeTypeOnly(t.entries[i][1], binds), t.entries[i][2]));
        }
        if (entries.some((e) => e.type.isEmptyType())) {
            return ResolvedType.createEmpty();
        }

        return ResolvedType.createSingle(ResolvedRecordAtomType.create(t.isvalue, entries));
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
            let tte: ResolvedTupleAtomTypeEntry[][] = [];
            let allvals = (ccs[ccs.length -1].options[0] as ResolvedTupleAtomType).isvalue;
            let allrefs = !(ccs[ccs.length -1].options[0] as ResolvedTupleAtomType).isvalue;
            for(let i = 0; i < ccs.length - 1; ++i) {
                const rte = ccs[i].options[0] as ResolvedTupleAtomType;
                if(rte.types.some((entry) => entry.isOptional)) {
                    return ResolvedType.createEmpty();
                }

                tte.push(rte.types);
                allvals = allvals && rte.isvalue;
                allrefs = allrefs && !rte.isvalue;
            }

            tte.push((ccs[ccs.length -1].options[0] as ResolvedTupleAtomType).types);

            if(!allvals && !allrefs) {
                return ResolvedType.createEmpty();
            }

            const fte = ([] as ResolvedTupleAtomTypeEntry[]).concat(...tte);
            return ResolvedType.createSingle(ResolvedTupleAtomType.create(allvals, fte));
        }
        else if(ccs.every((tt) => tt.isRecordTargetType())) {
            let tte: ResolvedRecordAtomTypeEntry[][] = [];
            let names = new Set<string>();
            let allvals = true;
            let allrefs = true;
            for(let i = 0; i < ccs.length; ++i) {
                const allnamegroups = ccs[i].options.map((opt) => (opt as ResolvedRecordAtomType).entries.map((entry) => entry.name));
                const allnames = [...new Set<string>(([] as string[]).concat(...allnamegroups))].sort();

                if (allnames.some((pname) => names.has(pname))) {
                    return ResolvedType.createEmpty();
                }

                allvals = allvals && ccs[i].options.every((opt) => (opt as ResolvedRecordAtomType).isvalue);
                allrefs = allrefs && ccs[i].options.every((opt) => !(opt as ResolvedRecordAtomType).isvalue);
                    
                const ecc = allnames.map((pname) => {
                    names.add(pname);
                    
                    const isopt = ccs[i].options.some((opt) => {
                        const entry = (opt as ResolvedRecordAtomType).entries.find((ee) => ee.name === pname);
                        return entry === undefined || entry.isOptional;
                    });

                    const ttypes = ccs[i].options
                        .filter((opt) => (opt as ResolvedRecordAtomType).entries.find((ee) => ee.name === pname) !== undefined)
                        .map((opt) => ((opt as ResolvedRecordAtomType).entries.find((ee) => ee.name === pname) as ResolvedRecordAtomTypeEntry).type);

                    return new ResolvedRecordAtomTypeEntry(pname, this.typeUpperBound(ttypes), isopt);
                });

                tte.push(ecc);
            }

            if(!allvals && !allrefs) {
                return ResolvedType.createEmpty();
            }

            const fte = ([] as ResolvedRecordAtomTypeEntry[]).concat(...tte);
            return ResolvedType.createSingle(ResolvedTupleAtomType.create(allvals, fte));
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
        if (flattened.some((atom) => atom.idStr === "NSCore::None") && flattened.some((atom) => atom.idStr === "NSCore::Some")) {
            flattened.push(this.getSpecialAnyConceptType().options[0]);
        }

        //Check for Result::Ok and Result::Err => replace with Result
        let nresults: ResolvedConceptAtomType[] = [];
        for (let i = 0; i < flattened.length; ++i) {
            const tt = flattened[i];
            if(tt.idStr.startsWith("NSCore::Result::Ok<")) {
                const ttn = tt.idStr.replace("NSCore::Result::Ok", "NSCore::Result::Err");
                if(flattened.some((ot) => ot.idStr === ttn)) {
                    const rrt = this.tryGetConceptTypeForFullyResolvedName("NSCore::Result") as ConceptTypeDecl;
                    const rra = ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(rrt, (tt as ResolvedEntityAtomType).binds)]);
                    nresults.push(rra);
                }
            }
        }
        flattened = [...flattened, ...nresults];

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

        const utypes = merged.sort((cte1, cte2) => cte1.idStr.localeCompare(cte2.idStr));

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

    private normalizeType_Function(t: FunctionTypeSignature, binds: Map<string, ResolvedType>): ResolvedFunctionType | undefined {
        const params = t.params.map((param) => {
            let ttl = this.normalizeTypeGeneral(param.type, binds);
            let llpv: string | undefined = undefined;
            if(param.litexp !== undefined) {
                const lnv = this.reduceLiteralValueToCanonicalForm(param.litexp.exp, new Map<string, ResolvedType>(), ttl as ResolvedType);
                if(lnv === undefined) {
                    return new ResolvedFunctionTypeParam(param.name, ResolvedType.createEmpty(), false, undefined, undefined);
                }
                llpv = lnv[2];
            }

            return new ResolvedFunctionTypeParam(param.name, ttl, param.isOptional, param.refKind, llpv);
        });
        const optRestParamType = (t.optRestParamType !== undefined) ? this.normalizeTypeOnly(t.optRestParamType, binds) : undefined;
        const rtype = this.normalizeTypeOnly(t.resultType, binds);

        if (params.some((p) => p.type instanceof ResolvedType && p.type.isEmptyType()) || params.some((p) => p.isOptional && (p.refKind !== undefined)) || (optRestParamType !== undefined && optRestParamType.isEmptyType()) || rtype.isEmptyType()) {
            return undefined;
        }

        return ResolvedFunctionType.create(t.recursive, params, t.optRestParamName, optRestParamType, rtype);
    }

    private atomSubtypeOf_EntityConcept(t1: ResolvedEntityAtomType, t2: ResolvedConceptAtomType): boolean {
        const t2type = ResolvedType.createSingle(t2);
        return this.resolveProvides(t1.object, t1.binds).some((provide) => {
            const tt = this.normalizeTypeOnly(provide, t1.binds);
            return !tt.isEmptyType() && this.subtypeOf(tt, t2type);
        });
    }

    private atomSubtypeOf_TupleConcept(t1: ResolvedTupleAtomType, t2: ResolvedConceptAtomType): boolean {
        return this.subtypeOf(ResolvedType.createSingle(this.getConceptsProvidedByTuple(t1)), ResolvedType.createSingle(t2));
    }

    private atomSubtypeOf_RecordConcept(t1: ResolvedRecordAtomType, t2: ResolvedConceptAtomType): boolean {
        return this.subtypeOf(ResolvedType.createSingle(this.getConceptsProvidedByRecord(t1)), ResolvedType.createSingle(t2));
    }

    private atomSubtypeOf_ConceptConcept(t1: ResolvedConceptAtomType, t2: ResolvedConceptAtomType, ): boolean {
        return t2.conceptTypes.every((c2t) => {
            return t1.conceptTypes.some((c1t) => {
                if (c1t.concept.ns === c2t.concept.ns && c1t.concept.name === c2t.concept.name) {
                    let allBindsOk = true;
                    c1t.binds.forEach((v, k) => (allBindsOk = allBindsOk && v.idStr === (c2t.binds.get(k) as ResolvedType).idStr));
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

    private atomSubtypeOf_TupleTuple(t1: ResolvedTupleAtomType, t2: ResolvedTupleAtomType): boolean {
        if(t1.isvalue !== t2.isvalue) {
            return false;
        }

       for (let i = 0; i < t1.types.length; ++i) {
            const t1e = t1.types[i];

           if (i >= t2.types.length) {
               return false;
           }
           else {
               const t2e = t2.types[i];
               if ((t1e.isOptional && !t2e.isOptional) || t1e.type.idStr !== t2e.type.idStr) {
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
                if ((entry.isOptional && !t2e.isOptional) || entry.type.idStr !== t2e.type.idStr) {
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
        if(witht.isvalue !== atom.isvalue || witht.types.length !== atom.types.length) {
            return;
        }

        for(let i = 0; i < witht.types.length; ++i) {
            const withe = witht.types[i];
            const atome = atom.types[i];

            if(withe.isOptional !== atome.isOptional) {
                return;
            }

            this.typeUnify(withe.type, atome.type, umap);
        }
    }

    private unifyResolvedRecordAtomType(witht: ResolvedRecordAtomType, atom: ResolvedRecordAtomType, umap: Map<string, ResolvedType | undefined>) {
        if(witht.isvalue !== atom.isvalue || witht.entries.length !== atom.entries.length) {
            return;
        }

        for(let i = 0; i < witht.entries.length; ++i) {
            const withe = witht.entries[i];
            const atome = atom.entries[i];

            if(withe.name !== atome.name || withe.isOptional !== atome.isOptional) {
                return;
            }

            this.typeUnify(withe.type, atome.type, umap);
        }
    }

    private internSpecialConceptType(names: [string], terms?: TypeSignature[], binds?: Map<string, ResolvedType>): ResolvedType {
        if (this.m_specialTypeMap.has("NSCore::" + names.join("::"))) {
            return this.m_specialTypeMap.get("NSCore::" + names.join("::")) as ResolvedType;
        }

        const rsig = new NominalTypeSignature("NSCore", names, terms || [] as TypeSignature[]);
        const tconcept = this.createConceptTypeAtom(this.tryGetConceptTypeForFullyResolvedName("NSCore::" + names.join("::")) as ConceptTypeDecl, rsig, binds || new Map<string, ResolvedType>());
        const rtype = ResolvedType.createSingle(tconcept as ResolvedAtomType);
        this.m_specialTypeMap.set("NSCore::" + names.join("::"), rtype);

        return rtype;
    }

    private internSpecialObjectType(names: string[], terms?: TypeSignature[], binds?: Map<string, ResolvedType>): ResolvedType {
        if (this.m_specialTypeMap.has("NSCore::" + names.join("::"))) {
            return this.m_specialTypeMap.get("NSCore::" + names.join("::")) as ResolvedType;
        }

        const rsig = new NominalTypeSignature("NSCore", names, terms || [] as TypeSignature[]);
        const tobject = this.createObjectTypeAtom(this.tryGetObjectTypeForFullyResolvedName("NSCore::" + names.join("::")) as EntityTypeDecl, rsig, binds || new Map<string, ResolvedType>());
        const rtype = ResolvedType.createSingle(tobject as ResolvedAtomType);
        this.m_specialTypeMap.set("NSCore::" + names.join("::"), rtype);

        return rtype;
    }

    getSpecialNoneType(): ResolvedType { return this.internSpecialObjectType(["None"]); }
    getSpecialBoolType(): ResolvedType { return this.internSpecialObjectType(["Bool"]); }
    getSpecialIntType(): ResolvedType { return this.internSpecialObjectType(["Int"]); }
    getSpecialNatType(): ResolvedType { return this.internSpecialObjectType(["Nat"]); }
    getSpecialBigIntType(): ResolvedType { return this.internSpecialObjectType(["BigInt"]); }
    getSpecialBigNatType(): ResolvedType { return this.internSpecialObjectType(["BigNat"]); }
    getSpecialRationalType(): ResolvedType { return this.internSpecialObjectType(["Rational"]); }
    getSpecialComplexType(): ResolvedType { return this.internSpecialObjectType(["Complex"]); }
    getSpecialFloatType(): ResolvedType { return this.internSpecialObjectType(["Float"]); }
    getSpecialDecimalType(): ResolvedType { return this.internSpecialObjectType(["Decimal"]); }
    getSpecialStringType(): ResolvedType { return this.internSpecialObjectType(["String"]); }
    getSpecialBufferFormatType(): ResolvedType { return this.internSpecialObjectType(["BufferFormat"]); }
    getSpecialBufferEncodingType(): ResolvedType { return this.internSpecialObjectType(["BufferEncoding"]); }
    getSpecialBufferCompressionType(): ResolvedType { return this.internSpecialObjectType(["BufferCompression"]); }
    getSpecialByteBufferType(): ResolvedType { return this.internSpecialObjectType(["ByteBuffer"]); }
    getSpecialUUIDType(): ResolvedType { return this.internSpecialObjectType(["UUID"]); }
    getSpecialCryptoHashType(): ResolvedType { return this.internSpecialObjectType(["CryptoHash"]); }
    getSpecialRegexType(): ResolvedType { return this.internSpecialObjectType(["Regex"]); }
    getSpecialRegexMatchType(): ResolvedType { return this.internSpecialObjectType(["RegexMatch"]); }

    getSpecialAnyConceptType(): ResolvedType { return this.internSpecialConceptType(["Any"]); }
    getSpecialSomeConceptType(): ResolvedType { return this.internSpecialConceptType(["Some"]); }
    getSpecialKeyTypeConceptType(): ResolvedType { return this.internSpecialConceptType(["KeyType"]); }
    getSpecialPODTypeConceptType(): ResolvedType { return this.internSpecialConceptType(["PODType"]); }
    getSpecialAPIValueConceptType(): ResolvedType { return this.internSpecialConceptType(["APIValue"]); }
    getSpecialAPITypeConceptType(): ResolvedType { return this.internSpecialConceptType(["APIType"]); }

    getSpecialObjectConceptType(): ResolvedType { return this.internSpecialConceptType(["Object"]); }

    isExpandoableType(ty: ResolvedAtomType): boolean { return ty.idStr.startsWith("NSCore::Expandoable<"); }

    ensureNominalRepresentation(t: ResolvedType): ResolvedType {
        const opts = t.options.map((opt) => {
            if (opt instanceof ResolvedTupleAtomType) {
                return ResolvedType.createSingle(this.getConceptsProvidedByTuple(opt));
            }
            else if (opt instanceof ResolvedRecordAtomType) {
                return ResolvedType.createSingle(this.getConceptsProvidedByRecord(opt));
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
        if(ere !== -1) {
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

    ////
    //Type representation, normalization, and operations
    lookupTypeDef(t: NominalTypeSignature, binds: Map<string, ResolvedType>): [TypeSignature | undefined, Map<string, ResolvedType>] {
        if (!this.hasNamespace(t.nameSpace)) {
            return [undefined, new Map<string, ResolvedType>()];
        }

        const lname = t.nameSpace + "::" + t.tnames.join("::");
        const nsd = this.getNamespace(t.nameSpace);
        if (!nsd.typeDefs.has(lname)) {
            return [t, new Map<string, ResolvedType>(binds)];
        }

        //compute the bindings to use when resolving the RHS of the typedef alias
        const typealias = nsd.typeDefs.get(lname) as NamespaceTypedef;
        const updatedbinds = this.resolveTemplateBinds(typealias.terms, t.terms, binds);
        if(updatedbinds === undefined) {
            return [undefined, new Map<string, ResolvedType>()];
        }

        if (typealias.boundType instanceof NominalTypeSignature) {
            return this.lookupTypeDef(typealias.boundType, updatedbinds);
        }
        else {
            return [typealias.boundType, updatedbinds];
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
        let declfields = fmap || { req: new Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]>(), opt: new Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]>() };

        //Important to do traversal in Left->Right Topmost traversal order

        this.resolveProvides(ooptype, binds).forEach((provide) => {
            const tt = this.normalizeTypeOnly(provide, binds);
            (tt.options[0] as ResolvedConceptAtomType).conceptTypes.forEach((concept) => {
                declfields = this.getAllOOFieldsConstructors(concept.concept, concept.binds, declfields);
            });
        });

        ooptype.memberFields.forEach((mf, name) => {
            if(mf.value === undefined) {
                if(!declfields.req.has(name)) {
                    declfields.req.set(name, [ooptype, mf, binds]);
                }
            }
            else {
                if (!declfields.opt.has(name) && !OOPTypeDecl.attributeSetContains("derived", mf.attributes)) {
                    declfields.opt.set(name, [ooptype, mf, binds]);
                }
            }
        });

        return declfields;
    }

    getAllOOFieldsLayout(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, fmap?: Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]>): Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]> {
        let declfields = fmap || new Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]>();

        //Important to do traversal in Left->Right Topmost traversal order

        this.resolveProvides(ooptype, binds).forEach((provide) => {
            const tt = this.normalizeTypeOnly(provide, binds);
            (tt.options[0] as ResolvedConceptAtomType).conceptTypes.forEach((concept) => {
                declfields = this.getAllOOFieldsLayout(concept.concept, concept.binds, declfields);
            });
        });

        ooptype.memberFields.forEach((mf, name) => {
            if (!declfields.has(name)) {
                declfields.set(name, [ooptype, mf, binds]);
            }
        });

        return declfields;
    }

    getExpandoProvides(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>): ResolvedType | undefined {
        if(ooptype.ns === "NSCore" && ooptype.name === "Expandoable") {
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
        if(declinvs.find((dd) => dd[0].idStr === ttype.idStr)) {
            return declinvs;
        }
        else {
            if(ooptype.invariants.length !== 0) {
                declinvs.push([ttype, ooptype, binds]);
            }

            return declinvs;
        }
    }

    hasInvariants(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>): boolean {
        return this.getAllInvariantProvidingTypes(ooptype, binds).length !== 0;
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

        if (ooptype.memberMethods.has(fname) && !(ooptype.memberMethods.get(fname) as MemberMethodDecl).invoke.attributes.includes("override")) {
            let newbinds = new Map<string, ResolvedType>();
            oobinds.forEach((v, k) => newbinds.set(k, v));
            (ooptype.memberMethods.get(fname) as MemberMethodDecl).invoke.terms.forEach((term) => newbinds.set(term.name, callbinds.get(term.name) as ResolvedType));

            return {pre: [(ooptype.memberMethods.get(fname) as MemberMethodDecl).invoke.preconditions, newbinds], post: [(ooptype.memberMethods.get(fname) as MemberMethodDecl).invoke.postconditions, newbinds]};
        }

        if (ooptype.staticFunctions.has(fname) && !(ooptype.staticFunctions.get(fname) as StaticFunctionDecl).invoke.attributes.includes("override")) {
            let newbinds = new Map<string, ResolvedType>();
            oobinds.forEach((v, k) => newbinds.set(k, v));
            (ooptype.staticFunctions.get(fname) as StaticFunctionDecl).invoke.terms.forEach((term) => newbinds.set(term.name, callbinds.get(term.name) as ResolvedType));

            return {pre: [(ooptype.staticFunctions.get(fname) as StaticFunctionDecl).invoke.preconditions, newbinds], post: [(ooptype.staticFunctions.get(fname) as StaticFunctionDecl).invoke.postconditions, newbinds]};
        }

        return undefined;
    }

    private tryGetMemberConstDecl(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, name: string): OOMemberLookupInfo<StaticMemberDecl> | undefined {
        if(!ooptype.staticMembers.has(name)) {
            return undefined;
        }

        return new OOMemberLookupInfo<StaticMemberDecl>(ooptype, ooptype.staticMembers.get(name) as StaticMemberDecl, binds);
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
        if(!ooptype.staticFunctions.has(name)) {
            return undefined;
        }

        return new OOMemberLookupInfo<StaticFunctionDecl>(ooptype, ooptype.staticFunctions.get(name) as StaticFunctionDecl, binds);
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
        if(!ooptype.staticOperators.has(name)) {
            return undefined;
        }

        return new OOMemberLookupInfo<StaticOperatorDecl[]>(ooptype, ooptype.staticOperators.get(name) as StaticOperatorDecl[], binds);
    }

    private tryGetMemberOperatorDeclParent(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, name: string): OOMemberLookupInfo<StaticOperatorDecl[]> | undefined {
        const rprovides = this.resolveProvides(ooptype, binds);
        for (let i = 0; i < rprovides.length; ++i) {
            const tt = (this.normalizeTypeOnly(rprovides[i], binds).options[0] as ResolvedConceptAtomType).conceptTypes[0];
            const res = this.tryGetMemberOperatorDecl(tt.concept, tt.binds, name,) || this.tryGetMemberOperatorDeclParent(tt.concept, tt.binds, name);
            if (res !== undefined) {
                return res;
            }
        }

        return undefined;
    }

    private tryGetMemberFieldDecl(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, name: string): OOMemberLookupInfo<MemberFieldDecl> | undefined {
        if(!ooptype.memberFields.has(name)) {
            return undefined;
        }

        return new OOMemberLookupInfo<MemberFieldDecl>(ooptype, ooptype.memberFields.get(name) as MemberFieldDecl, binds);
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

    private tryGetMemberMethodDecl(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, name: string, findspecific: boolean): OOMemberLookupInfo<MemberMethodDecl> | undefined {
        if(!ooptype.memberMethods.has(name)) {
            return undefined;
        }

        const mmd = ooptype.memberMethods.get(name) as MemberMethodDecl;
        if(!findspecific && OOPTypeDecl.attributeSetContains("override", mmd.invoke.attributes)) {
            return undefined;
        }

        return new OOMemberLookupInfo<MemberMethodDecl>(ooptype, mmd, binds);
    }

    private tryGetMemberMethodDeclParent(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, name: string, findspecific: boolean): OOMemberLookupInfo<MemberMethodDecl> | undefined {
        const rprovides = this.resolveProvides(ooptype, binds);
        for (let i = 0; i < rprovides.length; ++i) {
            const tt = (this.normalizeTypeOnly(rprovides[i], binds).options[0] as ResolvedConceptAtomType).conceptTypes[0];
            const res = this.tryGetMemberMethodDecl(tt.concept, tt.binds, name, findspecific) || this.tryGetMemberMethodDeclParent(tt.concept, tt.binds, name, findspecific);
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
                    bindsok = bindsok && opt.binds.has(k) && v.idStr === (opt.binds.get(k) as ResolvedType).idStr;
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
    tryGetMethodUniqueConcreteDeclFromType(tt: ResolvedType, fname: string): OOMemberLookupInfo<MemberMethodDecl> | undefined {
        const ntype = this.ensureNominalRepresentation(tt);
        const ttopts = ntype.options.map((ttopt) => {
            if(ttopt instanceof ResolvedEntityAtomType) {
                return this.tryGetMemberMethodDecl(ttopt.object, ttopt.binds, fname, true) || this.tryGetMemberMethodDeclParent(ttopt.object, ttopt.binds, fname, true);
            }
            else {
                const copts = (ttopt as ResolvedConceptAtomType).conceptTypes.map((ccopt) => {
                    return this.tryGetMemberMethodDecl(ccopt.concept, ccopt.binds, fname, true) || this.tryGetMemberMethodDeclParent(ccopt.concept, ccopt.binds, fname, true);
                });
                return this.ensureSingleDecl_Helper<MemberMethodDecl>(copts.filter((ccopt) => ccopt !== undefined) as OOMemberLookupInfo<MemberMethodDecl>[]);
            }
        });

        if(ttopts.some((topt) => topt === undefined)) {
            return undefined;
        }
        else {
            const sdecl = this.ensureSingleDecl_Helper<MemberMethodDecl>(ttopts as OOMemberLookupInfo<MemberMethodDecl>[]);
            if(sdecl === undefined) {
                return undefined;
            }

            if(OOPTypeDecl.attributeSetContains("override", sdecl.decl.invoke.attributes) || OOPTypeDecl.attributeSetContains("virtual", sdecl.decl.invoke.attributes) || OOPTypeDecl.attributeSetContains("abstract", sdecl.decl.invoke.attributes)) {
                return undefined;
            }
            else {
                return sdecl;
            }
        }
    }

    //Given a type find the single virtual method root decl that every possible resoltions derives from -- should exist or it is an error
    tryGetMethodUniqueRootDeclFromType(tt: ResolvedType, fname: string): OOMemberLookupInfo<MemberMethodDecl> | undefined {
        const ntype = this.ensureNominalRepresentation(tt);
        const ttopts = ntype.options.map((ttopt) => {
            if(ttopt instanceof ResolvedEntityAtomType) {
                return this.tryGetMemberMethodDecl(ttopt.object, ttopt.binds, fname, false) || this.tryGetMemberMethodDeclParent(ttopt.object, ttopt.binds, fname, false);
            }
            else {
                const copts = (ttopt as ResolvedConceptAtomType).conceptTypes.map((ccopt) => {
                    return this.tryGetMemberMethodDecl(ccopt.concept, ccopt.binds, fname, false) || this.tryGetMemberMethodDeclParent(ccopt.concept, ccopt.binds, fname, false);
                });
                return this.ensureSingleDecl_Helper<MemberMethodDecl>(copts.filter((ccopt) => ccopt !== undefined) as OOMemberLookupInfo<MemberMethodDecl>[]);
            }
        });

        if(ttopts.some((topt) => topt === undefined)) {
            return undefined;
        }
        else {
            return this.ensureSingleDecl_Helper<MemberMethodDecl>(ttopts as OOMemberLookupInfo<MemberMethodDecl>[]);
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
            }
            return true;
        });

        const rrsigs: {sig: ResolvedFunctionType, idx: number}[] = [];
        for(let i = 0; i < ppairs.length; ++i) {
            const isig = ppairs[i].sig;
            let nomorespecific = false;

            for(let j = 0; j < ppairs.length; ++j) {
                if(i == j) {
                    continue;
                }

                const jsig = ppairs[j].sig;
                let morespecific = true;
                for(let k = 0; k < isig.params.length; ++ k) {
                    if(isig.params[k] instanceof ResolvedFunctionType) {
                        continue;
                    }

                    if(!this.subtypeOf(jsig.params[k].type as ResolvedType, isig.params[k].type as ResolvedType)) {
                        morespecific = false;
                        break;
                    } 
                }

                if(morespecific) {
                    nomorespecific = true;
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
        else if (t instanceof LiteralTypeSignature) {
            return this.normalizeType_Literal(t, binds);
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
            return this.getSpecialSomeConceptType();
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
            if (t1 instanceof ResolvedTupleAtomType && t2 instanceof ResolvedTupleAtomType) {
                res = this.atomSubtypeOf_TupleTuple(t1, t2);
            }
            else if (t1 instanceof ResolvedRecordAtomType && t2 instanceof ResolvedRecordAtomType) {
                res = this.atomSubtypeOf_RecordRecord(t1, t2);
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

        const res = (t1.idStr === t2.idStr) || t1.options.every((t1opt) => t2.options.some((t2opt) => this.atomSubtypeOf(t1opt, t2opt)));

        memores.set(t2.idStr, res);
        return res;
    }
 
    atomUnify(t1: ResolvedAtomType, t2: ResolvedAtomType, umap: Map<string, ResolvedType | undefined>) {
        if(t1 instanceof ResolvedTemplateUnifyType) {
            if(umap.has(t1.idStr)) {
                if(umap.get(t1.idStr) === undefined || (umap.get(t1.idStr) as ResolvedType).idStr === t2.idStr) {
                    //leave it
                }
                else {
                    umap.set(t1.idStr, undefined);
                }
            }
            else {
                umap.set(t1.idStr, ResolvedType.createSingle(t2));
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
            if (umap.has(t1.idStr)) {
                if (umap.get(t1.idStr) === undefined || (umap.get(t1.idStr) as ResolvedType).idStr === t2.idStr) {
                    //leave it
                }
                else {
                    umap.set(t1.idStr, undefined);
                }
            }
            else {
                if (t2.options.length !== 1) {
                    //if multiple options unify with the | 
                    umap.set(t1.idStr, t2); 
                }
                else {
                    //otherwise expand and try unifying with the individual type
                    this.atomUnify(t1.options[0], t2.options[0], umap);
                }
            }
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
        if (t2.params.length !== t1.params.length) {
            return false; //need to have the same number of parameters
        }

        if ((t2.optRestParamType !== undefined) !== (t1.optRestParamType !== undefined)) {
            return false; //should both have rest or not
        }

        if (t2.optRestParamType !== undefined && t2.optRestParamType.idStr !== (t1.optRestParamType as ResolvedType).idStr) {
            return false; //variance
        }

        for (let i = 0; i < t2.params.length; ++i) {
            const t2p = t2.params[i];
            const t1p = t1.params[i];
            if ((t2p.isOptional !== t1p.isOptional) || (t2p.refKind !== t1p.refKind) || (t2p.litexp !== t1p.litexp)) {
                return false;
            }

            //We want the argument types to be the same for all cases -- no clear reason to overload to more general types
            if (t2p.type instanceof ResolvedFunctionType && t1p.type instanceof ResolvedFunctionType) {
                if (t2p.type.idStr !== t1p.type.idStr) {
                    return false;
                }
            }
            else if (t2p.type instanceof ResolvedType && t1p.type instanceof ResolvedType) {
                if (t2p.type.idStr !== t1p.type.idStr) {
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

        if(t1.resultType.idStr !== t2.resultType.idStr) {
            return false;
        }

        return true;
    }

    //Only used for pcode checking
    functionSubtypeOf(t1: ResolvedFunctionType, t2: ResolvedFunctionType): boolean {
        let memores = this.m_subtypeRelationMemo.get(t1.idStr);
        if (memores === undefined) {
            this.m_subtypeRelationMemo.set(t1.idStr, new Map<string, boolean>());
            memores = this.m_subtypeRelationMemo.get(t1.idStr) as Map<string, boolean>;
        }

        let memoval = memores.get(t2.idStr);
        if (memoval !== undefined) {
            return memoval;
        }

        const res = this.functionSubtypeOf_helper(t1, t2);

        memores.set(t2.idStr, res);
        return res;
    }
}

export {
    BuildLevel, isBuildLevelEnabled,
    TemplateTermSpecialRestriction, TemplateTermDecl, TemplateTypeRestriction, TypeConditionRestriction, PreConditionDecl, PostConditionDecl, InvokeDecl,
    SpecialTypeCategory, OOMemberDecl, InvariantDecl, StaticMemberDecl, StaticFunctionDecl, StaticOperatorDecl, MemberFieldDecl, MemberMethodDecl, OOPTypeDecl, ConceptTypeDecl, EntityTypeDecl,
    NamespaceConstDecl, NamespaceFunctionDecl, NamespaceOperatorDecl, NamespaceTypedef, NamespaceUsing, NamespaceDeclaration,
    OOMemberLookupInfo, Assembly
};
