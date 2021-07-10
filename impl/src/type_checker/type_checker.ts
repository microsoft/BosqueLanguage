//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ResolvedType, ResolvedTupleAtomType, ResolvedEntityAtomType, ResolvedTupleAtomTypeEntry, ResolvedRecordAtomType, ResolvedRecordAtomTypeEntry, ResolvedConceptAtomType, ResolvedFunctionType, ResolvedEphemeralListType, ResolvedConceptAtomTypeEntry, ResolvedLiteralAtomType } from "../ast/resolved_type";
import { Assembly, NamespaceConstDecl, OOPTypeDecl, StaticMemberDecl, EntityTypeDecl, StaticFunctionDecl, InvokeDecl, MemberFieldDecl, NamespaceFunctionDecl, TemplateTermDecl, OOMemberLookupInfo, MemberMethodDecl, BuildLevel, isBuildLevelEnabled, PreConditionDecl, PostConditionDecl, TypeConditionRestriction, ConceptTypeDecl, SpecialTypeCategory, TemplateTermSpecialRestriction, NamespaceOperatorDecl, StaticOperatorDecl } from "../ast/assembly";
import { TypeEnvironment, VarInfo, FlowTypeTruthValue, StructuredAssignmentPathStep, StructuredAssignmentCheck, ValueType } from "./type_environment";
import { TypeSignature, TemplateTypeSignature, NominalTypeSignature, AutoTypeSignature, FunctionParameter, TupleTypeSignature, FunctionTypeSignature } from "../ast/type_signature";
import { Expression, ExpressionTag, LiteralTypedStringExpression, LiteralTypedStringConstructorExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, NamedArgument, ConstructorPrimaryExpression, ConstructorPrimaryWithFactoryExpression, ConstructorTupleExpression, ConstructorRecordExpression, Arguments, PositionalArgument, CallNamespaceFunctionOrOperatorExpression, CallStaticFunctionOrOperatorExpression, PostfixOp, PostfixOpTag, PostfixAccessFromIndex, PostfixProjectFromIndecies, PostfixAccessFromName, PostfixProjectFromNames, PostfixInvoke, PostfixModifyWithIndecies, PostfixModifyWithNames, PrefixNotOp, LiteralNoneExpression, BinLogicExpression, NonecheckExpression, CoalesceExpression, SelectExpression, VariableDeclarationStatement, VariableAssignmentStatement, IfElseStatement, Statement, StatementTag, BlockStatement, ReturnStatement, LiteralBoolExpression, LiteralStringExpression, BodyImplementation, AssertStatement, CheckStatement, DebugStatement, StructuredVariableAssignmentStatement, StructuredAssignment, RecordStructuredAssignment, IgnoreTermStructuredAssignment, ConstValueStructuredAssignment, VariableDeclarationStructuredAssignment, VariableAssignmentStructuredAssignment, TupleStructuredAssignment, MatchStatement, MatchGuard, WildcardMatchGuard, TypeMatchGuard, StructureMatchGuard, AbortStatement, YieldStatement, IfExpression, MatchExpression, BlockStatementExpression, ConstructorPCodeExpression, PCodeDirectInvokeExpression, PCodeInvokeExpression, ExpOrExpression, LiteralRegexExpression, ConstructorEphemeralValueList, VariablePackDeclarationStatement, VariablePackAssignmentStatement, NominalStructuredAssignment, ValueListStructuredAssignment, NakedCallStatement, ValidateStatement, IfElse, CondBranchEntry, MapEntryConstructorExpression, SpecialConstructorExpression, RecursiveAnnotation, PostfixIs, PostfixHasIndex, PostfixHasProperty, PostfixAs, LiteralParamerterValueExpression, LiteralTypedNumericConstructorExpression, OfTypeConvertExpression, LiteralIntegralExpression, LiteralRationalExpression, LiteralFloatPointExpression, LiteralExpressionValue, PostfixGetIndexOrNone, PostfixGetIndexTry, PostfixGetPropertyOrNone, PostfixGetPropertyTry, ConstantExpressionValue, LiteralNumberinoExpression, BinKeyExpression, TemplateArguments, CombinatorPCodeExpression } from "../ast/body";
import { PCode, MIREmitter, MIRKeyGenerator } from "../compiler/mir_emitter";
import { MIRArgument, MIRConstantNone, MIRVirtualMethodKey, MIRInvokeKey, MIRResolvedTypeKey, MIRFieldKey, MIRConstantString, MIRRegisterArgument, MIRConstantInt, MIRConstantNat, MIRConstantBigNat, MIRConstantBigInt, MIRConstantRational, MIRConstantDecimal, MIRConstantFloat, MIRGlobalKey, MIRGlobalVariable, MIRBody, MIRMaskGuard, MIRArgGuard, MIRStatmentGuard, MIRConstantFalse } from "../compiler/mir_ops";
import { SourceInfo, unescapeLiteralString } from "../ast/parser";
import { MIREntityTypeDecl, MIRConceptTypeDecl, MIRFieldDecl, MIRInvokeDecl, MIRFunctionParameter, MIRType, MIRConstantDecl, MIRPCode, MIRInvokePrimitiveDecl, MIRInvokeBodyDecl, MIRSpecialTypeCategory } from "../compiler/mir_assembly";
import { BSQRegex } from "../ast/bsqregex";

import * as assert from "assert";

class TypeError extends Error {
    readonly file: string;
    readonly line: number;

    constructor(file: string, line: number, message?: string) {
        super(`Type error on ${line} -- ${message}`);
        Object.setPrototypeOf(this, new.target.prototype);

        this.file = file;
        this.line = line;
    }
}

type ExpandedArgument = {
    name: string | undefined,
    argtype: ValueType | ResolvedFunctionType,
    expando: boolean,
    ref: ["ref" | "out" | "out?", MIRRegisterArgument] | undefined,
    pcode: PCode | undefined,
    treg: MIRRegisterArgument | undefined
};

type FilledLocation = {
    vtype: ValueType | ResolvedFunctionType,
    mustDef: boolean,
    fflagchk: boolean,
    ref: ["ref" | "out" | "out?", MIRRegisterArgument] | undefined,
    pcode: PCode | undefined,
    trgt: MIRArgument | undefined
};

function createTupleStructuredAssignmentPathStep(fromtype: ResolvedType, t: ResolvedType, ival: number): StructuredAssignmentPathStep {
    return { fromtype: fromtype, t: t, step: "tuple", ival: ival, nval: "[empty]" };
}

function createRecordStructuredAssignmentPathStep(fromtype: ResolvedType, t: ResolvedType, nval: string): StructuredAssignmentPathStep {
    return { fromtype: fromtype, t: t, step: "record", ival: -1, nval: nval };
}

function createEphemeralStructuredAssignmentPathStep(fromtype: ResolvedType, t: ResolvedType, ival: number): StructuredAssignmentPathStep {
    return { fromtype: fromtype, t: t, step: "elist", ival: ival, nval: "[empty]" };
}

function createNominalStructuredAssignmentPathStep(fromtype: ResolvedType, t: ResolvedType, nval: string): StructuredAssignmentPathStep {
    return { fromtype: fromtype, t: t, step: "nominal", ival: -1, nval: nval };
}

function createTerminalEqCheck(srctype: ResolvedType, exp: ConstantExpressionValue): StructuredAssignmentCheck {
    return { action: "eqchk", srctype: srctype, oftype: undefined, isoptional: false, eqvalue: exp };
}

function createOfTypeCheck(srctype: ResolvedType, oftype: ResolvedType, isoptional: boolean): StructuredAssignmentCheck {
    return { action: "typechk", srctype: srctype, oftype: oftype, isoptional: isoptional, eqvalue: undefined };
}

abstract class InitializerEvaluationAction {
    readonly deps: string[];

    constructor(deps: string[]) {
        this.deps = deps;
    }
}

class InitializerEvaluationLiteralExpression extends InitializerEvaluationAction {
    readonly constexp: Expression;

    constructor(constexp: Expression) {
        super([]);
        this.constexp = constexp;
    }
}

class InitializerEvaluationConstantLoad extends InitializerEvaluationAction {
    readonly gkey: MIRGlobalKey;

    constructor(gkey: MIRGlobalKey) {
        super([]);

        this.gkey = gkey;
    }
}

class InitializerEvaluationCallAction extends InitializerEvaluationAction {
    readonly ikey: MIRInvokeKey;
    readonly args: MIRArgument[];

    constructor(ikey: MIRInvokeKey, args: MIRArgument[]) {
        super(args.map((arg) => arg.nameID));

        this.ikey = ikey;
        this.args = args;
    }
}

class TypeChecker {
    private readonly m_assembly: Assembly;

    private readonly m_buildLevel: BuildLevel;

    private m_file: string;
    private m_errors: [string, number, string][];

    private readonly m_emitter: MIREmitter;

    constructor(assembly: Assembly, emitter: MIREmitter, buildlevel: BuildLevel) {
        this.m_assembly = assembly;

        this.m_buildLevel = buildlevel;

        this.m_file = "[No File]";
        this.m_errors = [];

        this.m_emitter = emitter;
    }

    private raiseError(sinfo: SourceInfo, msg?: string) {
        this.m_emitter.setEmitEnabled(false);

        this.m_errors.push([this.m_file, sinfo.line, msg || "Type error"]);
        throw new TypeError(this.m_file, sinfo.line, msg || "Type error");
    }

    private raiseErrorIf(sinfo: SourceInfo, cond: boolean, msg?: string) {
        if (cond) {
            this.raiseError(sinfo, msg);
        }
    }

    getErrorList(): [string, number, string][] {
        return this.m_errors;
    }

    private resolveAndEnsureTypeOnly(sinfo: SourceInfo, ttype: TypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const rtype = this.m_assembly.normalizeTypeOnly(ttype, binds);
        this.raiseErrorIf(sinfo, rtype.isEmptyType(), "Bad type signature");

        this.m_emitter.registerResolvedTypeReference(rtype);
        return rtype;
    }

    private resolveOOTypeFromDecls(oodecl: OOPTypeDecl, oobinds: Map<string, ResolvedType>): ResolvedType {
        if(oodecl instanceof EntityTypeDecl) {
            return ResolvedType.createSingle(ResolvedEntityAtomType.create(oodecl, oobinds));
        }
        else {
            return ResolvedType.createSingle(ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(oodecl as ConceptTypeDecl, oobinds)]));
        }
    }

    private isConstructorTypeOfValue(ctype: ResolvedType): boolean {
        const ootd = (ctype.options[0] as ResolvedEntityAtomType).object;
        return OOPTypeDecl.attributeSetContains("struct", ootd.attributes);
    }

    private getResultSubtypes(rtype: ResolvedType): [ResolvedType, ResolvedType] {
        const binds = (rtype.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds;
        const okentity = this.m_assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Result::Ok") as EntityTypeDecl;
        const errentity = this.m_assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Result::Err") as EntityTypeDecl;

        return [
            ResolvedType.createSingle(ResolvedEntityAtomType.create(okentity, binds)),
            ResolvedType.createSingle(ResolvedEntityAtomType.create(errentity, binds))
        ];
    }

    private getResultBinds(rtype: ResolvedType): { T: ResolvedType, E: ResolvedType } {
        const binds = (rtype.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds;
        return { T: binds.get("T") as ResolvedType, E: binds.get("E") as ResolvedType };
    }

    private emitInlineConvertIfNeeded<T extends MIRArgument>(sinfo: SourceInfo, src: T, srctype: ValueType, trgttype: ResolvedType): T | MIRRegisterArgument {
        if(srctype.layout.isSameType(trgttype)) {
            return src;
        }

        this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(srctype.flowtype, trgttype), `Cannot convert type ${srctype.flowtype.idStr} into ${trgttype.idStr}`);

        const mirsrclayouttype = this.m_emitter.registerResolvedTypeReference(srctype.layout);
        const mirsrcflowtype = this.m_emitter.registerResolvedTypeReference(srctype.flowtype);
        const mirintotype = this.m_emitter.registerResolvedTypeReference(trgttype);

        const rr = this.m_emitter.generateTmpRegister();
        this.m_emitter.emitConvert(sinfo, mirsrclayouttype, mirsrcflowtype, mirintotype, src, rr, undefined);

        return rr;
    }

    private emitCheckedInlineConvertIfNeeded<T extends MIRArgument>(sinfo: SourceInfo, src: T, srctype: ValueType, trgttype: ResolvedType, guard: MIRStatmentGuard): T | MIRRegisterArgument {
        if(srctype.layout.isSameType(trgttype)) {
            return src;
        }

        this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(srctype.flowtype, trgttype), `Cannot convert type ${srctype.flowtype.idStr} into ${trgttype.idStr}`);

        const mirsrclayouttype = this.m_emitter.registerResolvedTypeReference(srctype.layout);
        const mirsrcflowtype = this.m_emitter.registerResolvedTypeReference(srctype.flowtype);
        const mirintotype = this.m_emitter.registerResolvedTypeReference(trgttype);

        const rr = this.m_emitter.generateTmpRegister();
        this.m_emitter.emitConvert(sinfo, mirsrclayouttype, mirsrcflowtype, mirintotype, src, rr, guard);

        return rr;
    }

    private emitInlineConvertToFlow<T extends MIRArgument>(sinfo: SourceInfo, src: T, srctype: ValueType): T | MIRRegisterArgument {
        return this.emitInlineConvertIfNeeded<T>(sinfo, src, srctype, srctype.flowtype);
    }

    private checkTemplateTypes(sinfo: SourceInfo, terms: TemplateTermDecl[], binds: Map<string, ResolvedType>, optTypeRestrict?: TypeConditionRestriction) {
        for(let i = 0; i < terms.length; ++i) {
            const terminfo = terms[i];
            const termtype = binds.get(terminfo.name) as ResolvedType;

            const termconstraint = this.resolveAndEnsureTypeOnly(sinfo, terminfo.tconstraint, new Map<string, ResolvedType>());
            const boundsok = this.m_assembly.subtypeOf(termtype, termconstraint);
            this.raiseErrorIf(sinfo, !boundsok, `Template instantiation does not satisfy specified bounds -- not subtype of ${termconstraint.idStr}`);

            if (terminfo.specialRestrictions.size !== 0) {
                terminfo.specialRestrictions.forEach((srv) => {
                    switch (srv) {
                        case TemplateTermSpecialRestriction.Literal: {
                            this.raiseErrorIf(sinfo, termtype.options.length !== 1 || !(termtype.options[0] instanceof ResolvedLiteralAtomType), "Not a literal type");
                            break;
                        }
                        case TemplateTermSpecialRestriction.Validator: {
                            const isunique = termtype.isUniqueCallTargetType();
                            this.raiseErrorIf(sinfo, !isunique, "Validator types must be unique");
                            const isvalidator = termtype.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.ValidatorTypeDecl);
                            this.raiseErrorIf(sinfo, !isvalidator, "Not a valid validator type");
                            break;
                        }
                        case TemplateTermSpecialRestriction.Parsable:  {
                            const isunique = termtype.isUniqueCallTargetType();
                            this.raiseErrorIf(sinfo, !isunique, "Parsable types must be unique");
                            const isparsable = termtype.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.ParsableTypeDecl);
                            this.raiseErrorIf(sinfo, !isparsable, "Not a valid parsable type");
                            break;
                        }
                        case TemplateTermSpecialRestriction.Grounded: {
                            this.raiseErrorIf(sinfo, !termtype.isGroundedType(), "Type is not grounded");
                            break;
                        }
                        case TemplateTermSpecialRestriction.Entity: {
                            const isuniqueentity = termtype.isUniqueCallTargetType();
                            this.raiseErrorIf(sinfo, !isuniqueentity, "entity types must be of a single entity declared type");
                            break;
                        }
                        case TemplateTermSpecialRestriction.Struct: {
                            const isuniqueentity = termtype.isUniqueCallTargetType();
                            this.raiseErrorIf(sinfo, !isuniqueentity, "struct types must be of a single entity declared type");
                            const isstruct = OOPTypeDecl.attributeSetContains("struct", termtype.getUniqueCallTargetType().object.attributes);
                            this.raiseErrorIf(sinfo, !isstruct, "struct types must have decl with struct attribute");
                            break;
                        }
                    }
                });
            }
        }

        if (optTypeRestrict !== undefined) {
            for (let i = 0; i < optTypeRestrict.constraints.length; ++i) {
                const consinfo = optTypeRestrict.constraints[i];
                const constype = this.resolveAndEnsureTypeOnly(sinfo, consinfo.t, binds)

                const constrainttype = this.resolveAndEnsureTypeOnly(sinfo, consinfo.tconstraint, binds);
                const boundsok = this.m_assembly.subtypeOf(constype, constrainttype);
                this.raiseErrorIf(sinfo, !boundsok, `Template instantiation does not satisfy specified restriction -- not subtype of ${constrainttype.idStr}`);
            }
        }
    }

    private doConstantExpressionTypeInferNoEmit(env: TypeEnvironment, srcFile: string, cexp: Expression, args: Map<string, VarInfo>): ValueType {
        const oldenable = this.m_emitter.getEmitEnabled();
        this.m_emitter.setEmitEnabled(false);

        const ccall = `ConstExprEval@@${srcFile}#${cexp.sinfo.pos}`;
        const cenv = TypeEnvironment.createInitialEnvForCall(ccall, new Map<string, ResolvedType>(env.terms), new Map<string, { pcode: PCode, captured: string[] }>(), args, undefined);

        const junkreg = this.m_emitter.generateTmpRegister();
        const etype = this.checkExpression(cenv, cexp, junkreg, undefined).getExpressionResult().valtype;

        this.m_emitter.setEmitEnabled(oldenable);

        return etype;
    }

    private isPCodeTypedExpression(e: Expression, env: TypeEnvironment): boolean {
        if(e instanceof CombinatorPCodeExpression || e instanceof ConstructorPCodeExpression) {
            return true;
        }
        else if (e instanceof AccessVariableExpression) {
            return env.pcodes.has(e.name);
        }
        else {
            return false;
        }
    }

    private checkInvokeDecl(sinfo: SourceInfo, invoke: InvokeDecl, invokeBinds: Map<string, ResolvedType>, pcodes: PCode[]) {
        this.raiseErrorIf(sinfo, invoke.optRestType !== undefined && invoke.params.some((param) => param.isOptional), "Cannot have optional and rest parameters in an invocation signature");

        this.raiseErrorIf(sinfo, invoke.recursive === "no" && pcodes.some((pc) => pc.code.recursive === "yes"), "Recursive decl does not match use");

        const allNames = new Set<string>();
        if (invoke.optRestName !== undefined && invoke.optRestName !== "_") {
            allNames.add(invoke.optRestName);
        }
        for (let i = 0; i < invoke.params.length; ++i) {
            if (invoke.params[i].name !== "_") {
                this.raiseErrorIf(sinfo, allNames.has(invoke.params[i].name), `Duplicate name in invocation signature paramaters "${invoke.params[i].name}"`);
                allNames.add(invoke.params[i].name);
            }
            const rtype = this.m_assembly.normalizeTypeGeneral(invoke.params[i].type, invokeBinds);
            this.raiseErrorIf(sinfo, rtype instanceof ResolvedType && rtype.isEmptyType(), "Bad type signature");
        }

        const firstOptIndex = invoke.params.findIndex((param) => param.isOptional);
        if (firstOptIndex === -1) {
            return;
        }

        for (let i = firstOptIndex; i < invoke.params.length; ++i) {
            this.raiseErrorIf(sinfo, !invoke.params[i].isOptional, "Cannot have required paramaters following optional parameters");
        }

        if (invoke.optRestType !== undefined) {
            this.resolveAndEnsureTypeOnly(sinfo, invoke.optRestType, invokeBinds);
        }

        const rtype = this.resolveAndEnsureTypeOnly(sinfo, invoke.resultType, invokeBinds);
        this.raiseErrorIf(sinfo, rtype.isEmptyType(), "Bad type signature");
    }

    private checkPCodeDecl(sinfo: SourceInfo, fsig: ResolvedFunctionType, rec: "yes" | "no" | "cond") {
        this.raiseErrorIf(sinfo, fsig.optRestParamType !== undefined && fsig.params.some((param) => param.isOptional), "Cannot have optional and rest parameters in an invocation signature");
        this.raiseErrorIf(sinfo, rec === "no" && fsig.recursive === "yes", "Recursive decl does not match use");

        const allNames = new Set<string>();
        if (fsig.optRestParamName !== undefined && fsig.optRestParamName !== "_") {
            allNames.add(fsig.optRestParamName);
        }
        for (let i = 0; i < fsig.params.length; ++i) {
            if (fsig.params[i].name !== "_") {
                this.raiseErrorIf(sinfo, allNames.has(fsig.params[i].name), `Duplicate name in invocation signature paramaters "${fsig.params[i].name}"`);
                allNames.add(fsig.params[i].name);
            }
        
            const rtype = fsig.params[i].type;
            this.raiseErrorIf(sinfo, rtype instanceof ResolvedFunctionType, "Cannot have nested function type param");
        }

        const firstOptIndex = fsig.params.findIndex((param) => param.isOptional);
        if (firstOptIndex === -1) {
            return;
        }

        for (let i = firstOptIndex; i < fsig.params.length; ++i) {
            this.raiseErrorIf(sinfo, !fsig.params[i].isOptional, "Cannot have required paramaters following optional parameters");
        }
    }

    private checkRecursion(sinfo: SourceInfo, fsig: ResolvedFunctionType, pcodes: PCode[], crec: "yes" | "no" | "cond") {
        if ((fsig.recursive === "no" && crec === "no") || (fsig.recursive === "yes" && crec === "yes")) {
            return;
        }

        let sigr = fsig.recursive;
        if (sigr === "cond") {
            sigr = pcodes.some((pc) => pc.code.recursive === "yes") ? "yes" : "no";
        }

        let callr = crec;
        if (callr === "cond") {
            callr = pcodes.some((pc) => pc.code.recursive === "yes") ? "yes" : "no";
        }

        this.raiseErrorIf(sinfo, (sigr === "yes" && callr === "no") || (sigr === "no" && callr === "yes"), "Mismatched recursive annotations on call");
    }

    private checkValueEq(lhsexp: Expression, lhs: ResolvedType, rhsexp: Expression, rhs: ResolvedType): "err" | "truealways" | "falsealways" | "lhsnone" | "rhsnone" | "lhssomekey" | "rhssomekey" | "stdkey" {
        if (lhsexp instanceof LiteralNoneExpression && rhsexp instanceof LiteralNoneExpression) {
            return "truealways";
        }

        if (lhsexp instanceof LiteralNoneExpression) {
            return rhs.options.some((opt) => opt.idStr === "NSCore::None") ? "lhsnone" : "falsealways";
        }

        if (rhsexp instanceof LiteralNoneExpression) {
            return lhs.options.some((opt) => opt.idStr === "NSCore::None") ? "rhsnone" : "falsealways";
        }
        
        //we want T | None === T or T === T | None so at most 3 options are ok
        if(lhs.options.length + rhs.options.length > 3) {
            return "err";
        }

        const simplelhsopts = lhs.options.filter((opt) => opt.idStr !== "NSCore::None");
        const simplerhsopts = rhs.options.filter((opt) => opt.idStr !== "NSCore::None");

        if(simplelhsopts.length === 0 && simplerhsopts.length === 0) {
            return "truealways";
        }
        else if (simplelhsopts.length === 0) {
            return rhs.options.some((opt) => opt.idStr === "NSCore::None") ? "lhsnone" : "falsealways";
        }
        else if (simplerhsopts.length === 0) {
            return lhs.options.some((opt) => opt.idStr === "NSCore::None") ? "rhsnone" : "falsealways";
        }
        else {
            //should be 1 non-none type on each side then -- so 1 less than the orig number of types
            if (simplelhsopts.length + simplerhsopts.length !== 2) {
                return "err";
            }

            if(lhs.options.length === 1 && rhs.options.length === 1) {
                return lhs.options[0].idStr === rhs.options[0].idStr ? "stdkey" : "falsealways";
            }
            else {
                if (simplelhsopts[0].idStr !== simplerhsopts[0].idStr) {
                    return "falsealways";
                }
                else {
                    return lhs.options.length === 2 ? "lhssomekey" : "rhssomekey";
                }
            }
        }
    }

    private getInfoForHasIndex(sinfo: SourceInfo, rtype: ResolvedType, idx: number): "yes" | "no" | "maybe" {
        this.raiseErrorIf(sinfo, rtype.options.some((atom) => !(atom instanceof ResolvedTupleAtomType)), "Can only load indecies from Tuples");

        const yhas = rtype.options.every((atom) => {
            const tatom = atom as ResolvedTupleAtomType;
            return (idx < tatom.types.length) && !tatom.types[idx].isOptional;
        });

        const yno = rtype.options.every((atom) => {
            const tatom = atom as ResolvedTupleAtomType;
            return (idx >= tatom.types.length);
        });

        if(yhas) {
            return "yes";
        }
        else if(yno) {
            return "no";
        }
        else {
            return "maybe";
        }
    }

    private getInfoForLoadFromSafeIndex(sinfo: SourceInfo, rtype: ResolvedType, idx: number): ResolvedType {
        this.raiseErrorIf(sinfo, this.getInfoForHasIndex(sinfo, rtype, idx) !== "yes");
        return this.m_assembly.typeUpperBound(rtype.options.map((atom) => (atom as ResolvedTupleAtomType).types[idx].type));
    }

    private getInfoForLoadFromSafeIndexOnly(sinfo: SourceInfo, rtype: ResolvedType, idx: number): ResolvedType {
        this.raiseErrorIf(sinfo, this.getInfoForHasIndex(sinfo, rtype, idx) === "no");
        return this.m_assembly.typeUpperBound(rtype.options
            .filter((atom) => (atom as ResolvedTupleAtomType).types.length > idx)
            .map((atom) => (atom as ResolvedTupleAtomType).types[idx].type)
        );
    }

    private getInfoForHasProperty(sinfo: SourceInfo, rtype: ResolvedType, pname: string): "yes" | "no" | "maybe" {
        this.raiseErrorIf(sinfo, rtype.options.some((atom) => !(atom instanceof ResolvedRecordAtomType)), "Can only load properties from Records");

        const yhas = rtype.options.every((atom) => {
            const tatom = atom as ResolvedRecordAtomType;
            const eidx = tatom.entries.findIndex((entry) => entry.name === pname);
            return (eidx !== -1) && !tatom.entries[eidx].isOptional;
        });

        const yno = rtype.options.every((atom) => {
            const tatom = atom as ResolvedRecordAtomType;
            const eidx = tatom.entries.findIndex((entry) => entry.name === pname);
            return (eidx === -1);
        });

        if(yhas) {
            return "yes";
        }
        else if(yno) {
            return "no";
        }
        else {
            return "maybe";
        }
    }

    private getInfoForLoadFromSafeProperty(sinfo: SourceInfo, rtype: ResolvedType, pname: string): ResolvedType {
        this.raiseErrorIf(sinfo, this.getInfoForHasProperty(sinfo, rtype, pname) !== "yes");
        return this.m_assembly.typeUpperBound(rtype.options.map((atom) => ((atom as ResolvedRecordAtomType).entries.find((re) => re.name === pname) as ResolvedRecordAtomTypeEntry).type));
    }

    private getInfoForLoadFromSafePropertyOnly(sinfo: SourceInfo, rtype: ResolvedType, pname: string): ResolvedType {
        this.raiseErrorIf(sinfo, this.getInfoForHasProperty(sinfo, rtype, pname) === "no");
        return this.m_assembly.typeUpperBound(rtype.options
            .filter((atom) => (atom as ResolvedRecordAtomType).entries.find((re) => re.name === pname) !== undefined)
            .map((atom) => ((atom as ResolvedRecordAtomType).entries.find((re) => re.name === pname) as ResolvedRecordAtomTypeEntry).type)
        );
    }

    private checkTypeOkForTupleExpando(sinfo: SourceInfo, rtype: ResolvedType): [number, number] {
        const tslist = rtype.options.map((opt) => {
            this.raiseErrorIf(sinfo, !(opt instanceof ResolvedTupleAtomType), "Can only expando into positional arguments with Tuple");
            return opt as ResolvedTupleAtomType;
        });
        const reqlen = tslist.reduce((acc, v) => Math.min(acc, v.types.filter((te) => !te.isOptional).length), Number.MAX_SAFE_INTEGER);
        const tlen = tslist.reduce((acc, v) => Math.max(acc, v.types.length), 0);

        return [reqlen, tlen];
    }

    private checkTypeOkForRecordExpando(sinfo: SourceInfo, rtype: ResolvedType): [Set<string>, Set<string>] {
        const rslist = rtype.options.map((opt) => {
            this.raiseErrorIf(sinfo, !(opt instanceof ResolvedRecordAtomType), "Can only expando into named arguments with Record");
            return opt as ResolvedRecordAtomType;
        });

        let allNames = new Set<string>();
        let reqNames = new Set<string>();
        rslist.forEach((opt) => {
            opt.entries.forEach((re) => {
                allNames.add(re.name);

                if (re.isOptional) {
                    reqNames.add(re.name);
                }
            });
        });

        return [reqNames, allNames];
    }

    private checkPCodeExpressionInfer(env: TypeEnvironment, exp: CombinatorPCodeExpression | ConstructorPCodeExpression, cbinds: Map<string, ResolvedType>, expectedFunction: ResolvedFunctionType | undefined): ResolvedType {
        if (exp instanceof CombinatorPCodeExpression) {
            return this.m_assembly.getSpecialBoolType();
        }
        else {
            this.raiseErrorIf(exp.sinfo, exp.isAuto && expectedFunction === undefined, "Could not infer auto function type");

            if (exp.invoke.isPCodePred) {
                return this.m_assembly.getSpecialBoolType();
            }

            const ltypetry = exp.isAuto ? expectedFunction : this.m_assembly.normalizeTypeFunction(exp.invoke.generateSig(), cbinds);
            this.raiseErrorIf(exp.sinfo, ltypetry === undefined, "Invalid lambda type");

            this.raiseErrorIf(exp.sinfo, exp.invoke.params.length !== (ltypetry as ResolvedFunctionType).params.length, "Mismatch in expected parameter count and provided function parameter count");

            const fsig = ltypetry as ResolvedFunctionType;
            let refNames: string[] = [];
            let cargs = new Map<string, VarInfo>();

            for (let i = 0; i < exp.invoke.params.length; ++i) {
                const p = fsig.params[i];
                cargs.set(exp.invoke.params[i].name, new VarInfo(p.type as ResolvedType, p.refKind === undefined, false, true, p.type as ResolvedType));

                if (p.refKind !== undefined) {
                    refNames.push(p.name);
                }
            }
            if (fsig.optRestParamType !== undefined) {
                cargs.set(exp.invoke.optRestName as string, new VarInfo(fsig.optRestParamType, true, false, true, fsig.optRestParamType));
            }

            exp.invoke.captureSet.forEach((v) => {
                if (v === "%this_captured" && env.lookupVar(v) === null) {
                    const vinfo = env.lookupVar("this") as VarInfo;
                    cargs.set(v, vinfo);
                }
                else {
                    const vinfo = env.lookupVar(v) as VarInfo;
                    this.raiseErrorIf(exp.sinfo, vinfo.declaredType instanceof ResolvedFunctionType, "Cannot capture function typed argument");
                    cargs.set(v, vinfo);
                }
            });

            const ikey = MIRKeyGenerator.generatePCodeKey(exp.invoke);
            const pcenv = TypeEnvironment.createInitialEnvForCall(ikey, new Map<string, ResolvedType>(cbinds), new Map<string, { pcode: PCode, captured: string[] }>(), cargs, undefined);

            if (exp.invoke.body instanceof Expression) {
                const dummyreg = this.m_emitter.generateTmpRegister();
                const evalue = this.checkExpression(pcenv, exp.invoke.body, dummyreg, undefined);
                return evalue.getExpressionResult().valtype.flowtype;
            }
            else {
                const renv = this.checkBlock(pcenv, (exp.invoke.body as BodyImplementation).body as BlockStatement);

                this.raiseErrorIf(exp.sinfo, renv.hasNormalFlow(), "Not all flow paths return a value!");
                return renv.returnResult as ResolvedType;
            }
        }
    }

    private checkArgumentsEvaluationWSigInfer(sinfo: SourceInfo, env: TypeEnvironment, ptypes: FunctionParameter[], args: Arguments, hasself: boolean, ibinds: Map<string, ResolvedType>, infer: string[]): Map<string, ResolvedType> {
        let resbinds = new Map<string, ResolvedType | undefined>();

        //
        //TODO: assumes a simple signature and call layout -- no optional, no rest, no named, no spread, no ref
        //      if we want to support some/all of this we will need to split the checking like we do for the real thing
        //

        const pidx = hasself ? 1 : 0;
        
        for (let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i];
            const ptype = this.m_assembly.normalizeTypeGeneral(ptypes[pidx + i].type, ibinds);
            
            if (arg.value instanceof CombinatorPCodeExpression || arg.value instanceof ConstructorPCodeExpression) {
                this.raiseErrorIf(arg.value.sinfo, !(ptype instanceof ResolvedFunctionType), "Must have function type for function arg");
                
                const pcrtype = this.checkPCodeExpressionInfer(env, arg.value, ibinds, ptype as ResolvedFunctionType | undefined);
                this.m_assembly.typeUnify((ptype as ResolvedFunctionType).resultType, pcrtype, resbinds);
            }
            else if (arg.value instanceof AccessVariableExpression && env.pcodes.has(arg.value.name)) {
                this.raiseErrorIf(arg.value.sinfo, !(ptype instanceof ResolvedFunctionType), "Must have function type for function arg");

                const pcode =  (env.pcodes.get(arg.value.name) as { pcode: PCode, captured: string[] }).pcode;
                this.m_assembly.typeUnify((ptype as ResolvedFunctionType).resultType, pcode.ftype.resultType, resbinds);
            }
            else {
                this.raiseErrorIf(arg.value.sinfo, !(ptype instanceof ResolvedType), "Must have non-function type for non-function arg");
                const dummyreg = this.m_emitter.generateTmpRegister();

                const etype = this.checkExpression(env, arg.value, dummyreg, undefined).getExpressionResult().valtype.flowtype;
                this.m_assembly.typeUnify((ptype as ResolvedType), etype, resbinds);
            }
        }

        this.raiseErrorIf(sinfo, infer.some((ii) => !resbinds.has(ii)), "Could not compute bind for all needed variables");
        this.raiseErrorIf(sinfo, [...resbinds].some((bb) => bb[1] === undefined), "Binds were ambig for inference");

        let fbinds = new Map<string, ResolvedType>();
        resbinds.forEach((v, k) => fbinds.set(k, v as ResolvedType));
        return fbinds;
    }

    private checkPCodeExpression(env: TypeEnvironment, exp: CombinatorPCodeExpression | ConstructorPCodeExpression, cbinds: Map<string, ResolvedType>, expectedFunction: ResolvedFunctionType | undefined): PCode {
        if(exp instanceof CombinatorPCodeExpression) {
            if(exp.cexp instanceof PrefixNotOp) {
                return this.checkPrefixNotOpAsCombinator(env, exp.cexp as PrefixNotOp, cbinds, expectedFunction);
            }
            else {
                return this.checkBinLogicAsCombinator(env, exp.cexp as BinLogicExpression, cbinds, expectedFunction);
            }
        }
        else {
            this.raiseErrorIf(exp.sinfo, exp.isAuto && expectedFunction === undefined, "Could not infer auto function type");

            const ltypetry = exp.isAuto ? expectedFunction : this.m_assembly.normalizeTypeFunction(exp.invoke.generateSig(), cbinds);
            this.raiseErrorIf(exp.sinfo, ltypetry === undefined, "Invalid lambda type");

            this.raiseErrorIf(exp.sinfo, exp.invoke.params.length !== (ltypetry as ResolvedFunctionType).params.length, "Mismatch in expected parameter count and provided function parameter count");
            this.raiseErrorIf(exp.sinfo, expectedFunction !== undefined && !this.m_assembly.functionSubtypeOf(ltypetry as ResolvedFunctionType, expectedFunction), "Mismatch in expected and provided function signature");

            let capturedMap: Map<string, ResolvedType> = new Map<string, ResolvedType>();

            let captures: string[] = [];
            exp.invoke.captureSet.forEach((v) => captures.push(v));
            captures.sort();

            captures.forEach((v) => {
                if (v === "%this_captured" && env.lookupVar(v) === null) {
                    const vinfo = env.lookupVar("this") as VarInfo;

                    capturedMap.set(v, vinfo.flowType);
                }
                else {
                    const vinfo = env.lookupVar(v) as VarInfo;
                    this.raiseErrorIf(exp.sinfo, vinfo.declaredType instanceof ResolvedFunctionType, "Cannot capture function typed argument");

                    capturedMap.set(v, vinfo.flowType);
                }
            });

            this.m_emitter.registerPCode(exp.invoke, ltypetry as ResolvedFunctionType, cbinds, [...capturedMap].sort((a, b) => a[0].localeCompare(b[0])));

            return { code: exp.invoke, scope: env.scope, captured: capturedMap, ftype: ltypetry as ResolvedFunctionType };
        }
    }

    private checkArgumentsEvaluationWSig(sinfo: SourceInfo, env: TypeEnvironment, sig: ResolvedFunctionType, sigbinds: Map<string, ResolvedType>, args: Arguments, optSelfValue: [ValueType, string | undefined, MIRRegisterArgument] | undefined, refallowed: boolean): ExpandedArgument[] {
        let eargs: ExpandedArgument[] = [];

        if (optSelfValue !== undefined) {
            if(optSelfValue[1] === undefined) {
                eargs.push({ name: undefined, argtype: optSelfValue[0], ref: undefined, expando: false, pcode: undefined, treg: optSelfValue[2] });
            }
            else {
                const rvname = optSelfValue[1];
                this.raiseErrorIf(sinfo, env.lookupVar(rvname) === null, "Variable name is not defined");

                const earg = (env.lookupVar(rvname) as VarInfo);
                const eargval = new ValueType(earg.declaredType, earg.flowType);
                eargs.push({ name: undefined, argtype: eargval, ref: ["ref", new MIRRegisterArgument(rvname)], expando: false, pcode: undefined, treg: optSelfValue[2] });
            }
        }

        const ridx = optSelfValue !== undefined ? 1 : 0;
        const noExpando = args.argList.every((arg) => !(arg instanceof PositionalArgument) || !arg.isSpread);
        
        this.raiseErrorIf(sinfo, !refallowed && ((optSelfValue !== undefined && optSelfValue[1] !== undefined) || args.argList.some((arg) => arg.ref !== undefined)), "Cannot use ref params in this call position");

        //
        //TODO: we only end up doing type inference for calls that are simple (no expandos)
        //      we may want to fix this by augmenting our template type inference to do more!!!
        //

        if (noExpando) {
            let fillednames = new Set<string>();

            for (let i = 0; i < args.argList.length; ++i) {
                const isref = args.argList[i].ref !== undefined;
                this.raiseErrorIf(args.argList[i].value.sinfo, isref && !refallowed, "Cannot use ref params in this call position");

                if (args.argList[i] instanceof PositionalArgument) {
                    continue;
                }
                const narg = args.argList[i] as NamedArgument;
                fillednames.add(narg.name);

                const paramIdx = sig.params.findIndex((p) => p.name === narg.name);
                this.raiseErrorIf(narg.value.sinfo, paramIdx === -1 || eargs[paramIdx] !== undefined, "Named argument does not match parameter or is multiply defined");
                const param = sig.params[paramIdx];

                const treg = this.m_emitter.generateTmpRegister();
                if (narg.value instanceof CombinatorPCodeExpression || narg.value instanceof ConstructorPCodeExpression) {
                    this.raiseErrorIf(narg.value.sinfo, !(param.type instanceof ResolvedFunctionType), "Must have function type for function arg");
                    this.raiseErrorIf(narg.value.sinfo, isref, "Cannot use ref params on function argument");

                    const pcode = this.checkPCodeExpression(env, narg.value, sigbinds, param.type as ResolvedFunctionType);
                    eargs[i + ridx] = { name: narg.name, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg };
                }
                else if (narg.value instanceof AccessVariableExpression && env.pcodes.has(narg.value.name)) {
                    this.raiseErrorIf(narg.value.sinfo, !(param.type instanceof ResolvedFunctionType), "Must have function type for function arg");
                    this.raiseErrorIf(narg.value.sinfo, isref, "Cannot use ref params on function argument");

                    const pcode = (env.pcodes.get(narg.value.name) as { pcode: PCode, captured: string[] }).pcode;
                    eargs[i + ridx] = { name: narg.name, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg };
                }
                else {
                    if (isref) {
                        this.raiseErrorIf(narg.value.sinfo, !(narg.value instanceof AccessVariableExpression), "Can only ref on variable names");

                        const rvname = (narg.value as AccessVariableExpression).name;
                        this.raiseErrorIf(narg.value.sinfo, env.lookupVar(rvname) === null, "Variable name is not defined");

                        let refreg: MIRRegisterArgument | undefined = undefined;
                        if(narg.ref === "ref") {
                            this.checkExpression(env, narg.value, treg, param.type as ResolvedType);
                            refreg = treg;
                        }

                        const earg = (env.lookupVar(rvname) as VarInfo);
                        const eargval = new ValueType(earg.declaredType, earg.declaredType); //it is a ref so we need to use the declared type
                        const refv = new MIRRegisterArgument(rvname);

                        eargs[i + ridx] = { name: narg.name, argtype: eargval, ref: [narg.ref as "ref" | "out" | "out?", refv], expando: false, pcode: undefined, treg: refreg };
                    }
                    else {
                        const earg = this.checkExpression(env, narg.value, treg, param.type as ResolvedType).getExpressionResult();
                        eargs[i + ridx] = { name: narg.name, argtype: earg.valtype, ref: undefined, expando: false, pcode: undefined, treg: treg };
                    }
                }
            }

            let sigidx = ridx;
            for (let i = 0; i < args.argList.length; ++i) {
                if (args.argList[i] instanceof NamedArgument) {
                    continue;
                }
                const parg = args.argList[i] as PositionalArgument;
                const isref = parg.ref !== undefined;

                while(sigidx < sig.params.length && fillednames.has(sig.params[sigidx].name)) {
                    sigidx++;
                }

                const oftypett = (sigidx < sig.params.length) 
                    ? sig.params[sigidx].type 
                    : (sig.optRestParamType !== undefined ? (sig.optRestParamType as ResolvedType).getCollectionContentsType() : undefined);
                
                this.raiseErrorIf(sinfo, oftypett === undefined, "Too many parameters for call");
                const oftype = oftypett as ResolvedFunctionType | ResolvedType;

                const treg = this.m_emitter.generateTmpRegister();
                if (parg.value instanceof CombinatorPCodeExpression || parg.value instanceof ConstructorPCodeExpression) {
                    this.raiseErrorIf(parg.value.sinfo, !(oftype instanceof ResolvedFunctionType), "Must have function type for function arg");
                    this.raiseErrorIf(parg.value.sinfo, isref, "Cannot use ref params on function argument");

                    const pcode = this.checkPCodeExpression(env, parg.value, sigbinds, oftype as ResolvedFunctionType);
                    eargs[i + ridx] = { name: undefined, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg };
                }
                else if (parg.value instanceof AccessVariableExpression && env.pcodes.has(parg.value.name)) {
                    this.raiseErrorIf(parg.value.sinfo, !(oftype instanceof ResolvedFunctionType), "Must have function type for function arg");
                    this.raiseErrorIf(parg.value.sinfo, isref, "Cannot use ref params on function argument");

                    const pcode = (env.pcodes.get(parg.value.name) as { pcode: PCode, captured: string[] }).pcode;
                    eargs[i + ridx] = { name: undefined, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg };
                }
                else {
                    if (isref) {
                        this.raiseErrorIf(parg.value.sinfo, !(parg.value instanceof AccessVariableExpression), "Can only ref on variable names");

                        const rvname = (parg.value as AccessVariableExpression).name;
                        this.raiseErrorIf(parg.value.sinfo, env.lookupVar(rvname) === null, "Variable name is not defined");

                        this.checkExpression(env, parg.value, treg, oftype as ResolvedType);

                        let refreg: MIRRegisterArgument | undefined = undefined;
                        if(parg.ref === "ref") {
                            this.checkExpression(env, parg.value, treg, oftype as ResolvedType);
                            refreg = treg;
                        }

                        const earg = (env.lookupVar(rvname) as VarInfo);
                        const eargval = new ValueType(earg.declaredType, earg.declaredType); //it is a ref so we need to use the declared type
                        const refv = new MIRRegisterArgument(rvname);

                        eargs[i + ridx] = { name: undefined, argtype: eargval, ref: [parg.ref as "ref" | "out" | "out?", refv], expando: false, pcode: undefined, treg: refreg };
                    }
                    else {
                        const earg = this.checkExpression(env, parg.value, treg, oftype as ResolvedType).getExpressionResult();
                        eargs[i + ridx] = { name: undefined, argtype: earg.valtype, ref: undefined, expando: false, pcode: undefined, treg: treg };
                    }
                }

                ++sigidx;
            }
        }
        else {
            for (let i = 0; i < args.argList.length; ++i) {
                const arg = args.argList[i];
                const isref = arg.ref !== undefined;

                const treg = this.m_emitter.generateTmpRegister();

                this.raiseErrorIf(arg.value.sinfo, isref && !refallowed, "Cannot use ref params in this call position");
                this.raiseErrorIf(arg.value.sinfo, isref && arg instanceof PositionalArgument && arg.isSpread, "Cannot use ref on spread argument");

                if (arg.value instanceof CombinatorPCodeExpression || arg.value instanceof ConstructorPCodeExpression) {
                    this.raiseErrorIf(arg.value.sinfo, isref, "Cannot use ref params on function argument");

                    const pcode = this.checkPCodeExpression(env, arg.value, sigbinds, undefined);

                    if (arg instanceof NamedArgument) {
                        eargs.push({ name: arg.name, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                    }
                    else {
                        this.raiseErrorIf(arg.value.sinfo, (arg as PositionalArgument).isSpread, "Cannot have spread on pcode argument");

                        eargs.push({ name: undefined, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                    }
                }
                else if (arg.value instanceof AccessVariableExpression && env.pcodes.has(arg.value.name)) {
                    this.raiseErrorIf(arg.value.sinfo, isref, "Cannot use ref params on function argument");

                    const pcode = (env.pcodes.get(arg.value.name) as { pcode: PCode, captured: string[] }).pcode;

                    if (arg instanceof NamedArgument) {
                        eargs.push({ name: arg.name, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                    }
                    else {
                        this.raiseErrorIf(arg.value.sinfo, (arg as PositionalArgument).isSpread, "Cannot have spread on pcode argument");

                        eargs.push({ name: undefined, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                    }
                }
                else {
                    if (isref) {
                        this.raiseErrorIf(arg.value.sinfo, !(arg.value instanceof AccessVariableExpression), "Can only ref on variable names");

                        const rvname = (arg.value as AccessVariableExpression).name;
                        this.raiseErrorIf(arg.value.sinfo, env.lookupVar(rvname) === null, "Variable name is not defined");

                        this.checkExpression(env, arg.value, treg, undefined);

                        let refreg: MIRRegisterArgument | undefined = undefined;
                        if(arg.ref === "ref") {
                            this.checkExpression(env, arg.value, treg, undefined);
                            refreg = treg;
                        }

                        const earg = (env.lookupVar(rvname) as VarInfo);
                        const eargval = new ValueType(earg.declaredType, earg.declaredType); //it is a ref so we need to use the declared type
                        const refv = new MIRRegisterArgument(rvname);

                        if (arg instanceof NamedArgument) {
                            eargs.push({ name: arg.name, argtype: eargval, ref: [arg.ref as "ref" | "out" | "out?", refv], expando: false, pcode: undefined, treg: refreg });
                        }
                        else {
                            eargs.push({ name: undefined, argtype: eargval, ref: [arg.ref as "ref" | "out" | "out?", refv], expando: false, pcode: undefined, treg: refreg });
                        }
                    }
                    else {
                        if (arg instanceof NamedArgument) {
                            const earg = this.checkExpression(env, arg.value, treg, undefined).getExpressionResult();
                            eargs.push({ name: arg.name, argtype: earg.valtype, ref: undefined, expando: false, pcode: undefined, treg: treg });
                        }
                        else {
                            const earg = this.checkExpression(env, arg.value, treg, undefined).getExpressionResult();
                            eargs.push({ name: undefined, argtype: earg.valtype, ref: undefined, expando: (arg as PositionalArgument).isSpread, pcode: undefined, treg: treg });
                        }
                    }
                }
            }
        }

        return eargs;
    }

    private inferAndCheckArguments(sinfo: SourceInfo, env: TypeEnvironment, args: Arguments, invk: InvokeDecl, giventerms: TypeSignature[], implicitBinds: Map<string, ResolvedType>, callBinds: Map<string, ResolvedType>, optSelfValue: [ValueType, string | undefined, MIRRegisterArgument] | undefined, refallowed: boolean): [ResolvedFunctionType, Map<string, ResolvedType>, ExpandedArgument[]] {
        const oldenable = this.m_emitter.getEmitEnabled();
        this.m_emitter.setEmitEnabled(false);
        let rrbinds = new Map<string, ResolvedType>();

        const [ibinds, iterms] = this.m_assembly.resolveBindsForCallWithInfer(invk.terms, giventerms, implicitBinds, callBinds);
        this.raiseErrorIf(sinfo, ibinds === undefined, "Template instantiation failure");

        //Do checking and infer any template params that we need
        rrbinds = ibinds as Map<string, ResolvedType>;
        if (iterms.length !== 0) {
            const fbinds = this.checkArgumentsEvaluationWSigInfer(sinfo, env, invk.params, args, optSelfValue !== undefined, rrbinds, iterms);

            const binds = this.m_assembly.resolveBindsForCallComplete(invk.terms, giventerms, implicitBinds, callBinds, fbinds);
            this.raiseErrorIf(sinfo, binds === undefined, "Call bindings could not be resolved");

            rrbinds = binds as Map<string, ResolvedType>;
        }

        this.m_emitter.setEmitEnabled(oldenable);

        this.checkTemplateTypes(sinfo, invk.terms, rrbinds);

        const fsig = this.m_assembly.normalizeTypeFunction(invk.generateSig(), rrbinds);
        this.raiseErrorIf(sinfo, fsig === undefined, "Invalid function signature");

        const eargs = this.checkArgumentsEvaluationWSig(sinfo, env, fsig as ResolvedFunctionType, rrbinds, args, optSelfValue, refallowed);

        return [fsig as ResolvedFunctionType, rrbinds, eargs];
    }

    private checkArgumentsEvaluationWOperator(sinfo: SourceInfo, env: TypeEnvironment, binds: Map<string, ResolvedType>, args: Arguments, refallowed: boolean): ExpandedArgument[] {
        let eargs: ExpandedArgument[] = [];
        
        this.raiseErrorIf(sinfo, !refallowed && args.argList.some((arg) => arg.ref !== undefined), "Cannot use ref params in this call position");

        for (let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i];
            const isref = arg.ref !== undefined;

            const treg = this.m_emitter.generateTmpRegister();

            this.raiseErrorIf(arg.value.sinfo, isref && !refallowed, "Cannot use ref params in this call position");
            this.raiseErrorIf(arg.value.sinfo, isref && arg instanceof PositionalArgument && arg.isSpread, "Cannot use ref on spread argument");

            if (arg.value instanceof CombinatorPCodeExpression || arg.value instanceof ConstructorPCodeExpression) {
                this.raiseErrorIf(arg.value.sinfo, isref, "Cannot use ref params on function argument");

                const pcode = this.checkPCodeExpression(env, arg.value, binds, undefined);

                if (arg instanceof NamedArgument) {
                    eargs.push({ name: arg.name, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                }
                else {
                    this.raiseErrorIf(arg.value.sinfo, (arg as PositionalArgument).isSpread, "Cannot have spread on pcode argument");

                    eargs.push({ name: undefined, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                }
            }
            else if (arg.value instanceof AccessVariableExpression && env.pcodes.has(arg.value.name)) {
                this.raiseErrorIf(arg.value.sinfo, isref, "Cannot use ref params on function argument");

                const pcode = (env.pcodes.get(arg.value.name) as { pcode: PCode, captured: string[] }).pcode;

                if (arg instanceof NamedArgument) {
                    eargs.push({ name: arg.name, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                }
                else {
                    this.raiseErrorIf(arg.value.sinfo, (arg as PositionalArgument).isSpread, "Cannot have spread on pcode argument");

                    eargs.push({ name: undefined, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                }
            }
            else {
                if (isref) {
                    this.raiseErrorIf(arg.value.sinfo, !(arg.value instanceof AccessVariableExpression), "Can only ref on variable names");

                    const rvname = (arg.value as AccessVariableExpression).name;
                    this.raiseErrorIf(arg.value.sinfo, env.lookupVar(rvname) === null, "Variable name is not defined");

                    let refreg: MIRRegisterArgument | undefined = undefined;
                    if(arg.ref === "ref") {
                        this.checkExpression(env, arg.value, treg, undefined);
                        refreg = treg;
                    }

                    const earg = (env.lookupVar(rvname) as VarInfo);
                    const eargval = new ValueType(earg.declaredType, earg.declaredType); //it is a ref so we need to use the declared type
                    const refv = new MIRRegisterArgument(rvname);

                    if (arg instanceof NamedArgument) {
                        eargs.push({ name: arg.name, argtype: eargval, ref: [arg.ref as "ref" | "out" | "out?", refv], expando: false, pcode: undefined, treg: refreg });
                    }
                    else {
                        eargs.push({ name: undefined, argtype: eargval, ref: [arg.ref as "ref" | "out" | "out?", refv], expando: false, pcode: undefined, treg: refreg });
                    }
                }
                else {
                    if (arg instanceof NamedArgument) {
                        const earg = this.checkExpression(env, arg.value, treg, undefined).getExpressionResult();
                        eargs.push({ name: arg.name, argtype: earg.valtype, ref: undefined, expando: false, pcode: undefined, treg: treg });
                    }
                    else {
                        const earg = this.checkExpression(env, arg.value, treg, undefined).getExpressionResult();
                        eargs.push({ name: undefined, argtype: earg.valtype, ref: undefined, expando: (arg as PositionalArgument).isSpread, pcode: undefined, treg: treg });
                    }
                }
            }
        }

        return eargs;
    }

    private checkArgumentsEvaluationTuple(env: TypeEnvironment, args: Arguments, itype: ResolvedTupleAtomType | undefined): [ResolvedType, MIRRegisterArgument][] {
        let eargs: [ResolvedType, MIRRegisterArgument][] = [];

        for (let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i];
            this.raiseErrorIf(arg.value.sinfo, arg.ref !== undefined, "Cannot use ref params in this call position");
            this.raiseErrorIf(arg.value.sinfo, this.isPCodeTypedExpression(arg.value, env), "Cannot use function in this call position");

            this.raiseErrorIf(arg.value.sinfo, !(arg instanceof PositionalArgument), "Only positional arguments allowed in tuple constructor");
            this.raiseErrorIf(arg.value.sinfo, (arg as PositionalArgument).isSpread, "Expando parameters are not allowed in Tuple constructor");

            const treg = this.m_emitter.generateTmpRegister();
            let etype: ResolvedType | undefined = undefined;
            if(itype !== undefined && i < itype.types.length) {
                etype = itype.types[i].type;
            }

            const earg = this.checkExpression(env, arg.value, treg, etype).getExpressionResult();
            const ttype = etype || earg.valtype.flowtype;
            this.raiseErrorIf(arg.value.sinfo, ttype.options.some((opt) => opt instanceof ResolvedEphemeralListType), "Cannot store ephemeral lists");
            this.raiseErrorIf(arg.value.sinfo, !this.m_assembly.subtypeOf(earg.valtype.flowtype, ttype), "Argument not of expected type");

            eargs.push([ttype, this.emitInlineConvertIfNeeded(arg.value.sinfo, treg, earg.valtype, ttype)]);
        }

        return eargs;
    }

    private checkArgumentsTupleConstructor(sinfo: SourceInfo, isvalue: boolean, args: [ResolvedType, MIRRegisterArgument][], trgt: MIRRegisterArgument): ResolvedType {
        const tupleatom = ResolvedTupleAtomType.create(isvalue, args.map((targ) => new ResolvedTupleAtomTypeEntry(targ[0], false)));
        const rtuple = ResolvedType.createSingle(tupleatom);

        const regs = args.map((e) => e[1]);
        const tupkey = this.m_emitter.registerResolvedTypeReference(rtuple);
        this.m_emitter.emitConstructorTuple(sinfo, tupkey, regs, trgt);

        return rtuple;
    }

    private checkArgumentsEvaluationRecord(env: TypeEnvironment, args: Arguments, itype: ResolvedRecordAtomType | undefined): [string, ResolvedType, MIRRegisterArgument][] {
        let eargs: [string, ResolvedType, MIRRegisterArgument][] = [];

        for (let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i];
            this.raiseErrorIf(arg.value.sinfo, arg.ref !== undefined, "Cannot use ref params in this call position");
            this.raiseErrorIf(arg.value.sinfo, this.isPCodeTypedExpression(arg.value, env), "Cannot use function in this call position");

            this.raiseErrorIf(arg.value.sinfo, !(arg instanceof NamedArgument), "Only named arguments allowed in record constructor");

            const treg = this.m_emitter.generateTmpRegister();
            let etype: ResolvedType | undefined = undefined;
            if(itype !== undefined && itype.entries.findIndex((entry) => entry.name === (arg as NamedArgument).name) !== -1) {
                etype = (itype.entries.find((entry) => entry.name === (arg as NamedArgument).name) as ResolvedRecordAtomTypeEntry).type;
            }
            
            const earg = this.checkExpression(env, arg.value, treg, etype).getExpressionResult();
            const ttype = etype || earg.valtype.flowtype;
            this.raiseErrorIf(arg.value.sinfo, ttype.options.some((opt) => opt instanceof ResolvedEphemeralListType), "Cannot store ephemeral lists");
            this.raiseErrorIf(arg.value.sinfo, !this.m_assembly.subtypeOf(earg.valtype.flowtype, ttype), "Argument not of expected type");

            eargs.push([(arg as NamedArgument).name, ttype, this.emitInlineConvertIfNeeded(arg.value.sinfo, treg, earg.valtype, ttype)]);
        }

        return eargs;
    }

    private checkArgumentsRecordConstructor(sinfo: SourceInfo, isvalue: boolean, args: [string, ResolvedType, MIRRegisterArgument][], trgt: MIRRegisterArgument): ResolvedType {
        let rargs: [string, ResolvedType][] = [];

        const seenNames = new Set<string>();
        for (let i = 0; i < args.length; ++i) {
            this.raiseErrorIf(sinfo, seenNames.has(args[i][0] as string), "Duplicate argument name in Record constructor");

            rargs.push([args[i][0] as string, args[i][1] as ResolvedType]);
        }

        const rentries = rargs.map((targ) => new ResolvedRecordAtomTypeEntry(targ[0], targ[1], false));
        const recordatom = ResolvedRecordAtomType.create(isvalue, rentries);
        const rrecord = ResolvedType.createSingle(recordatom);

        const regs = args.map<[string, MIRRegisterArgument]>((e) => [e[0] as string, e[2]]).sort((a, b) => a[0].localeCompare(b[0]));
        const regkey = this.m_emitter.registerResolvedTypeReference(rrecord);
        this.m_emitter.emitConstructorRecord(sinfo, regkey, regs, trgt);

        return rrecord;
    }

    private checkArgumentsEvaluationValueList(env: TypeEnvironment, args: Arguments, itype: ResolvedEphemeralListType | undefined): [ResolvedType, MIRRegisterArgument][] {
        let eargs: [ResolvedType, MIRRegisterArgument][] = [];

        for (let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i];
            this.raiseErrorIf(arg.value.sinfo, arg.ref !== undefined, "Cannot use ref params in this call position");
            this.raiseErrorIf(arg.value.sinfo, this.isPCodeTypedExpression(arg.value, env), "Cannot use function in this call position");

            this.raiseErrorIf(arg.value.sinfo, !(arg instanceof PositionalArgument), "Only positional arguments allowed in tuple constructor");
            this.raiseErrorIf(arg.value.sinfo, (arg as PositionalArgument).isSpread, "Expando parameters are not allowed in Tuple constructor");

            const treg = this.m_emitter.generateTmpRegister();
            let etype: ResolvedType | undefined = undefined;
            if(itype !== undefined && i < itype.types.length) {
                etype = itype.types[i];
            }

            const earg = this.checkExpression(env, arg.value, treg, etype).getExpressionResult();
            const ttype = etype || earg.valtype.flowtype;
            this.raiseErrorIf(arg.value.sinfo, ttype.options.some((opt) => opt instanceof ResolvedEphemeralListType), "Cannot store ephemeral lists");
            this.raiseErrorIf(arg.value.sinfo, !this.m_assembly.subtypeOf(earg.valtype.flowtype, ttype), "Argument not of expected type");

            eargs.push([ttype, this.emitInlineConvertIfNeeded(arg.value.sinfo, treg, earg.valtype, ttype)]);
        }

        return eargs;
    }

    private checkArgumentsValueListConstructor(sinfo: SourceInfo, args: [ResolvedType, MIRRegisterArgument][], trgt: MIRRegisterArgument): ResolvedType {
        let targs: ResolvedType[] = [];

        for (let i = 0; i < args.length; ++i) {
            targs.push(args[i][0] as ResolvedType);
        }

        const vlatom = ResolvedEphemeralListType.create(targs);
        const rvl = ResolvedType.createSingle(vlatom);

        const regs = args.map((e) => e[1]);
        const vlkey = this.m_emitter.registerResolvedTypeReference(rvl);
        this.m_emitter.emitConstructorValueList(sinfo, vlkey, regs, trgt);

        return rvl;
    }

    private getExpandoType(sinfo: SourceInfo, eatom: ResolvedEntityAtomType): ResolvedType {
        const ep = this.m_assembly.getExpandoProvides(eatom.object, eatom.binds);
        this.raiseErrorIf(sinfo, ep === undefined, "Not an expandoable type");

        return ep as ResolvedType;
    }

    private checkArgumentsEvaluationCollection(env: TypeEnvironment, args: Arguments, contentstype: ResolvedType): [ResolvedType, boolean, MIRRegisterArgument][] {
        let eargs: [ResolvedType, boolean, MIRRegisterArgument][] = [];

        for (let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i];
            this.raiseErrorIf(arg.value.sinfo, arg.ref !== undefined, "Cannot use ref params in this call position");
            this.raiseErrorIf(arg.value.sinfo, this.isPCodeTypedExpression(arg.value, env), "Cannot use function in this call position");
            this.raiseErrorIf(arg.value.sinfo, arg instanceof NamedArgument, "Cannot use named arguments in constructor");

            const treg = this.m_emitter.generateTmpRegister();
            if ((arg as PositionalArgument).isSpread) {
                const earg = this.checkExpression(env, arg.value, treg, undefined).getExpressionResult().valtype;
                const ttype = earg.flowtype;
            
                eargs.push([ttype, true, this.emitInlineConvertIfNeeded(arg.value.sinfo, treg, earg, ttype)]);
            }
            else {
                const earg = this.checkExpression(env, arg.value, treg, contentstype).getExpressionResult().valtype;
                const ttype = contentstype;
                this.raiseErrorIf(arg.value.sinfo, ttype.options.some((opt) => opt instanceof ResolvedEphemeralListType), "Cannot store ephemeral lists");
                this.raiseErrorIf(arg.value.sinfo, !this.m_assembly.subtypeOf(earg.flowtype, ttype), "Argument not of expected type");

                eargs.push([ttype, false, this.emitInlineConvertIfNeeded(arg.value.sinfo, treg, earg, ttype)]);
            }
        }

        return eargs;
    }

    private checkExpandoType(sinfo: SourceInfo, oftype: ResolvedEntityAtomType, argtype: ResolvedType): boolean {
        const oftexpando = this.getExpandoType(sinfo, oftype);
        const oftexpandoT = (oftexpando.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds.get("T") as ResolvedType;

        this.raiseErrorIf(sinfo, argtype.options.length !== 1, "Must be unique type to use in collection expando");
        const opt = argtype.options[0];
            
        this.raiseErrorIf(sinfo, !(opt instanceof ResolvedEntityAtomType), "Can only expand other container types in container constructor");
        this.raiseErrorIf(sinfo, !(opt as ResolvedEntityAtomType).object.isTypeAnExpandoableCollection(), "Can only expand other container types in container constructor");
            
        const texpando = this.getExpandoType(sinfo, opt as ResolvedEntityAtomType);
        const texpandoT = (texpando.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds.get("T") as ResolvedType;

        return texpandoT.isSameType(oftexpandoT);
    }

    private checkArgumentsCollectionConstructor(sinfo: SourceInfo, oftype: ResolvedEntityAtomType, entrytype: ResolvedType, args: [ResolvedType, boolean, MIRRegisterArgument][], trgt: MIRRegisterArgument): ResolvedType {
        for (let i = 0; i < args.length; ++i) {
            const arg = args[i];

            if (!arg[1]) {
                this.raiseErrorIf(sinfo, !arg[0].isSameType(entrytype));
            }
            else {
                this.raiseErrorIf(sinfo, !this.checkExpandoType(sinfo, oftype, arg[0]), "Container contents not of matching expando type");
            }
        }

        const resulttype = ResolvedType.createSingle(oftype);

        const tkey = this.m_emitter.registerResolvedTypeReference(resulttype).trkey;
        this.m_emitter.registerResolvedTypeReference(entrytype);
        if (args.length === 0) {
            this.m_emitter.emitConstructorPrimaryCollectionEmpty(sinfo, tkey, trgt);
        }
        else {
            if (args.every((v) => !v[1])) {
                this.m_emitter.emitConstructorPrimaryCollectionSingletons(sinfo, tkey, args.map<[MIRType, MIRArgument]>((arg) => [this.m_emitter.registerResolvedTypeReference(arg[0]), arg[2]]), trgt);
            }
            else if (args.every((v) => v[1])) {
                if(args.length === 1 && args[0][0].isSameType(resulttype)) {
                    //special case where we expand a (say) List<Int> into a List<Int>
                    this.m_emitter.emitRegisterStore(sinfo, args[0][2], trgt, this.m_emitter.registerResolvedTypeReference(args[0][0]), undefined);
                }
                else {
                    this.m_emitter.emitConstructorPrimaryCollectionCopies(sinfo, tkey, args.map<[MIRType, MIRArgument]>((arg) => [this.m_emitter.registerResolvedTypeReference(arg[0]), arg[2]]), trgt);
                }
            }
            else {
                this.m_emitter.emitConstructorPrimaryCollectionMixed(sinfo, tkey, args.map<[boolean, MIRType, MIRArgument]>((arg) => [arg[1], this.m_emitter.registerResolvedTypeReference(arg[0]), arg[2]]), trgt);
            }
        }

        return resulttype;
    }

    private checkArgumentsEvaluationEntity(sinfo: SourceInfo, env: TypeEnvironment, oftype: ResolvedEntityAtomType, args: Arguments): ExpandedArgument[] {
        const rrfinfo = this.m_assembly.getAllOOFieldsConstructors(oftype.object, oftype.binds);
        const fieldinfo = [...rrfinfo.req, ...rrfinfo.opt];
        let eargs: ExpandedArgument[] = [];

        const noExpando = args.argList.every((arg) => !(arg instanceof PositionalArgument) || !arg.isSpread);
        if (noExpando) {
            let fillednames = new Set<string>();
            for (let i = 0; i < args.argList.length; ++i) {
                this.raiseErrorIf(args.argList[i].value.sinfo, args.argList[i].ref !== undefined, "Cannot use ref params in this call position");

                if (args.argList[i] instanceof PositionalArgument) {
                    continue;
                }
                const narg = args.argList[i] as NamedArgument;
                fillednames.add(narg.name);

                const fieldIdx = fieldinfo.findIndex((p) => p[0] === narg.name);
                this.raiseErrorIf(narg.value.sinfo, fieldIdx === -1 || eargs[fieldIdx] !== undefined, "Named argument does not match any field name or is multiply defined");
                const field = fieldinfo[fieldIdx];
                const ftype = this.resolveAndEnsureTypeOnly(sinfo, field[1][1].declaredType, field[1][2]);

                const treg = this.m_emitter.generateTmpRegister();
                const earg = this.checkExpression(env, narg.value, treg, ftype).getExpressionResult();
                eargs[i] = { name: narg.name, argtype: earg.valtype, ref: undefined, expando: false, pcode: undefined, treg: treg };
            }

            let fidx = 0;
            for (let i = 0; i < args.argList.length; ++i) {
                if (args.argList[i] instanceof NamedArgument) {
                    continue;
                }
                const parg = args.argList[i] as PositionalArgument;

                while (fidx < fieldinfo.length && fillednames.has(fieldinfo[i][0])) {
                    fidx++;
                }

                const field = fieldinfo[fidx];
                const ftype = this.resolveAndEnsureTypeOnly(sinfo, field[1][1].declaredType, field[1][2]);

                const treg = this.m_emitter.generateTmpRegister();

                const earg = this.checkExpression(env, parg.value, treg, ftype).getExpressionResult();
                eargs[i] = { name: undefined, argtype: earg.valtype, ref: undefined, expando: false, pcode: undefined, treg: treg };

                ++fidx;
            }
        }
        else {
            for (let i = 0; i < args.argList.length; ++i) {
                const arg = args.argList[i];
                this.raiseErrorIf(arg.value.sinfo, arg.ref !== undefined, "Cannot use ref params in this call position");

                const treg = this.m_emitter.generateTmpRegister();

                if (arg instanceof NamedArgument) {
                    const earg = this.checkExpression(env, arg.value, treg, undefined).getExpressionResult();
                    eargs.push({ name: arg.name, argtype: earg.valtype, ref: undefined, expando: false, pcode: undefined, treg: treg });
                }
                else {
                    const earg = this.checkExpression(env, arg.value, treg, undefined).getExpressionResult();
                    eargs.push({ name: undefined, argtype: earg.valtype, ref: undefined, expando: (arg as PositionalArgument).isSpread, pcode: undefined, treg: treg });
                }
            }
        }

        return eargs;
    }

    private checkArgumentsEntityConstructor(sinfo: SourceInfo, oftype: ResolvedEntityAtomType, args: ExpandedArgument[], trgt: MIRRegisterArgument): ResolvedType {
        const fieldInfo = this.m_assembly.getAllOOFieldsConstructors(oftype.object, oftype.binds);
        const flatfinfo = [...fieldInfo.req, ...fieldInfo.opt].map((ff) => ff[1]);
        const fields = flatfinfo.map((ff) => ff[1].name);

        const optcount = flatfinfo.filter((fi) => fi[1].value !== undefined).length;
        const optfirst = flatfinfo.findIndex((fi) => fi[1].value !== undefined);
        const fflag = this.m_emitter.emitGuardFlagLocation(sinfo, oftype.object.name, optcount);

        let filledLocations: { vtype: ValueType, mustDef: boolean, fflagchk: boolean, trgt: MIRArgument }[] = [];

        //figure out named parameter mapping first
        for (let i = 0; i < args.length; ++i) {
            const arg = args[i];
            this.raiseErrorIf(sinfo, args[i].ref !== undefined, "Cannot use ref params in this call position");

            if (arg.name !== undefined) {
                const fidx = fields.indexOf(arg.name);
                this.raiseErrorIf(sinfo, fidx === -1, `Entity ${oftype.idStr} does not have field named "${arg.name}"`);
                this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${arg.name}"`);

                filledLocations[fidx] = { vtype: arg.argtype as ValueType, mustDef: true, fflagchk: false, trgt: arg.treg as MIRRegisterArgument };
                if(flatfinfo[fidx][1].value !== undefined) {
                    this.m_emitter.emitSetGuardFlagConstant(sinfo, fflag as string, fidx - optfirst, true);
                }
            }
            else if (arg.expando && (arg.argtype as ValueType).flowtype.isRecordTargetType()) {
                const expandInfo = this.checkTypeOkForRecordExpando(sinfo, (arg.argtype as ValueType).flowtype);

                expandInfo[1].forEach((pname) => {
                    const fidx = fields.indexOf(pname);
                    this.raiseErrorIf(sinfo, fidx === -1, `Entity ${oftype.idStr} does not have field named "${pname}"`);
                    this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${pname}"`);

                    this.raiseErrorIf(sinfo, flatfinfo[fidx][1].value !== undefined && !expandInfo[0].has(pname), `Constructor requires "${pname}" but it is provided as an optional argument`);

                    const etreg = this.m_emitter.generateTmpRegister();
                    const lvtype = this.getInfoForLoadFromSafeProperty(sinfo, (arg.argtype as ValueType).flowtype, pname);
                    const ptype = this.m_emitter.registerResolvedTypeReference(lvtype);

                    if(expandInfo[0].has(pname)) {
                        this.m_emitter.emitLoadProperty(sinfo, arg.treg as MIRRegisterArgument, this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).layout), this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).flowtype), pname, !(arg.argtype as ValueType).flowtype.isUniqueRecordTargetType(), ptype, etreg);
                        filledLocations[fidx] = { vtype: ValueType.createUniform(lvtype), mustDef: true, fflagchk: false, trgt: etreg };
                    }
                    else {
                        const field = flatfinfo[fidx][1];
                        this.raiseErrorIf(sinfo, field.value === undefined, `Field "${fields[fidx]}" is required and must be assigned a value in constructor`);
                        
                        this.m_emitter.emitLoadUninitVariableValue(sinfo, ptype, etreg);
                        this.m_emitter.emitLoadRecordPropertySetGuard(sinfo, arg.treg as MIRRegisterArgument, this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).layout), this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).flowtype), pname, !(arg.argtype as ValueType).flowtype.isUniqueRecordTargetType(), ptype, etreg, new MIRMaskGuard(fflag as string, fidx - optfirst, optcount));
                        filledLocations[fidx] = { vtype: ValueType.createUniform(lvtype), mustDef: false, fflagchk: true, trgt: etreg };
                    }
                });
            }
            else {
                //nop
            }
        }

        //now fill in positional parameters
        let apos = args.findIndex((ae) => ae.name === undefined && !(ae.expando && (ae.argtype as ValueType).flowtype.isRecordTargetType()));
        if (apos === -1) {
            apos = args.length;
        }

        let ii = 0;
        while (ii < fields.length && apos < args.length) {
            if (filledLocations[ii] !== undefined) {
                this.raiseErrorIf(sinfo, !filledLocations[ii].mustDef, `We have an potentially ambigious binding of an optional field "${fields[ii]}"`);
                ++ii;
                continue;
            }

            const arg = args[apos];
            if (!arg.expando) {
                filledLocations[ii] = { vtype: arg.argtype as ValueType, mustDef: true, fflagchk: false, trgt: arg.treg as MIRRegisterArgument };
                if(flatfinfo[ii][1].value !== undefined) {
                    this.m_emitter.emitSetGuardFlagConstant(sinfo, fflag as string, ii - optfirst, true);
                }
                
                ++ii;
            }
            else {
                this.raiseErrorIf(sinfo, !((arg.argtype as ValueType).flowtype).isTupleTargetType(), "Only Tuple types can be expanded as positional arguments");
                const expandInfo = this.checkTypeOkForTupleExpando(sinfo, (arg.argtype as ValueType).flowtype);

                for (let ectr = 0; ectr < expandInfo[1]; ++ectr) {
                    this.raiseErrorIf(sinfo, ii >= fields.length, "Too many arguments as part of tuple expando");
                    this.raiseErrorIf(sinfo, flatfinfo[ii][1].value !== undefined && ectr >= expandInfo[0], `Constructor requires "${fields[ii]}" but it is provided as an optional argument as part of tuple expando`);

                    const etreg = this.m_emitter.generateTmpRegister();
                    const lvtype = this.getInfoForLoadFromSafeIndex(sinfo, (arg.argtype as ValueType).flowtype, ectr);
                    const itype = this.m_emitter.registerResolvedTypeReference(lvtype);
                   
                    if(ectr < expandInfo[0]) {
                        this.m_emitter.emitLoadTupleIndex(sinfo, arg.treg as MIRRegisterArgument, this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).layout), this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).flowtype), ectr, !(arg.argtype as ValueType).flowtype.isUniqueTupleTargetType(), itype, etreg);
                        filledLocations[ii] = { vtype: ValueType.createUniform(lvtype), mustDef: true, fflagchk: false, trgt: etreg };
                    }
                    else {
                        const field = flatfinfo[ii][1];
                        this.raiseErrorIf(sinfo, field.value === undefined, `Field "${fields[ii]}" is required and must be assigned a value in constructor`);

                        this.m_emitter.emitLoadUninitVariableValue(sinfo, itype, etreg);
                        this.m_emitter.emitLoadTupleIndexSetGuard(sinfo, arg.treg as MIRRegisterArgument, this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).layout), this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).flowtype), ectr, !(arg.argtype as ValueType).flowtype.isUniqueTupleTargetType(), itype, etreg, new MIRMaskGuard(fflag as string, ii - optfirst, optcount));
                        filledLocations[ii] = { vtype: ValueType.createUniform(lvtype), mustDef: false, fflagchk: true, trgt: etreg };
                    }

                    while (filledLocations[ii] !== undefined) {
                        this.raiseErrorIf(sinfo, !filledLocations[ii].mustDef, `We have an potentially ambigious binding of an optional field "${fields[ii]}"`);
                        ii++;
                    }
                }
            }

            apos++;
            while (apos < args.length && (args[apos].name !== undefined || (args[apos].expando && (args[apos].argtype as ValueType).flowtype.isRecordTargetType()))) {
                apos++;
            }
        }

        //go through arguments and type coearce as needed
        let cargs: MIRArgument[] = [];
        for (let i = 0; i < fields.length; ++i) {
            const field = flatfinfo[i];
            const fieldtype = this.resolveAndEnsureTypeOnly(sinfo, field[1].declaredType, field[2]);

            if (filledLocations[i] === undefined) {
                this.raiseErrorIf(sinfo, field[1].value === undefined, `Field ${field[1].name} is required and must be assigned a value in constructor`);

                const emptyreg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitLoadUninitVariableValue(sinfo, this.m_emitter.registerResolvedTypeReference(fieldtype), emptyreg);
                this.m_emitter.emitSetGuardFlagConstant(sinfo, fflag as string, i - optfirst, false);
                filledLocations[i] = { vtype: ValueType.createUniform(fieldtype), mustDef: false, fflagchk: true, trgt: emptyreg };
            }

            if(filledLocations[i].fflagchk) {
                cargs.push(this.emitCheckedInlineConvertIfNeeded(sinfo, filledLocations[i].trgt, filledLocations[i].vtype, fieldtype, new MIRStatmentGuard(new MIRMaskGuard(fflag as string, i - optfirst, optcount), "defaultonfalse", undefined)));
            }
            else {
                cargs.push(this.emitInlineConvertIfNeeded(sinfo, filledLocations[i].trgt, filledLocations[i].vtype, fieldtype));
            }
        }

        const constype = ResolvedType.createSingle(oftype);
        const rtype = this.m_emitter.registerResolvedTypeReference(constype);

        const ikey = MIRKeyGenerator.generateFunctionKey(MIRKeyGenerator.generateTypeKey(constype), "@@constructor", new Map<string, ResolvedType>(), []);
        this.m_emitter.emitInvokeFixedFunction(sinfo, ikey, cargs, fflag, rtype, trgt);
        return constype;
    }

    private checkArgumentsSignature(sinfo: SourceInfo, env: TypeEnvironment, name: string, sig: ResolvedFunctionType, args: ExpandedArgument[]): { args: MIRArgument[], fflag: string | undefined, refs: ["ref" | "out" | "out?", MIRRegisterArgument, ResolvedType][], pcodes: PCode[], cinfo: [string, ResolvedType][] } {
        const optcount = sig.params.filter((p) => p.isOptional).length;
        const optfirst = sig.params.findIndex((p) => p.isOptional);
        const fflag = this.m_emitter.emitGuardFlagLocation(sinfo, name, optcount);

        let filledLocations: FilledLocation[] = [];

        //figure out named parameter mapping first
        for (let j = 0; j < args.length; ++j) {
            const arg = args[j];
            if (arg.name !== undefined) {
                const fidx = sig.params.findIndex((param) => param.name === arg.name);
                this.raiseErrorIf(sinfo, fidx === -1, `Call does not have parameter named "${arg.name}"`);
                this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name ${arg.name}`);

                filledLocations[fidx] = { vtype: arg.argtype, mustDef: true, fflagchk: false, ref: arg.ref, pcode: arg.pcode, trgt: arg.treg };
                if(sig.params[fidx].isOptional) {
                    this.m_emitter.emitSetGuardFlagConstant(sinfo, fflag as string, fidx - optfirst, true);
                }
            }
            else if (arg.expando && (arg.argtype as ValueType).flowtype.isRecordTargetType()) {
                const expandInfo = this.checkTypeOkForRecordExpando(sinfo, (arg.argtype as ValueType).flowtype);

                expandInfo[1].forEach((pname) => {
                    const fidx = sig.params.findIndex((param) => param.name === pname);
                    this.raiseErrorIf(sinfo, fidx === -1, `Call does not have parameter named "${pname}"`);
                    this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${pname}"`);

                    this.raiseErrorIf(sinfo, !sig.params[fidx].isOptional && !expandInfo[0].has(pname), `Call requires "${pname}" but it is provided as an optional argument`);

                    const etreg = this.m_emitter.generateTmpRegister();
                    const lvtype =  this.getInfoForLoadFromSafeProperty(sinfo, (arg.argtype as ValueType).flowtype, pname);
                    const ptype = this.m_emitter.registerResolvedTypeReference(lvtype);

                    if(expandInfo[0].has(pname)) {
                        this.m_emitter.emitLoadProperty(sinfo, arg.treg as MIRRegisterArgument, this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).layout), this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).flowtype), pname, !(arg.argtype as ValueType).flowtype.isUniqueRecordTargetType(), ptype, etreg);
                        filledLocations[fidx] = { vtype: ValueType.createUniform(lvtype), mustDef: true, fflagchk: false, ref: undefined, pcode: undefined, trgt: etreg };
                    }
                    else {
                        const param = sig.params[fidx];
                        this.raiseErrorIf(sinfo, !param.isOptional, `Parameter "${param.name}" is required and must be assigned a value in call`);

                        this.m_emitter.emitLoadUninitVariableValue(sinfo, ptype, etreg);
                        this.m_emitter.emitLoadRecordPropertySetGuard(sinfo, arg.treg as MIRRegisterArgument, this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).layout), this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).flowtype), pname, !(arg.argtype as ValueType).flowtype.isUniqueRecordTargetType(), ptype, etreg, new MIRMaskGuard(fflag as string, fidx - optfirst, optcount));
                        filledLocations[fidx] = { vtype: ValueType.createUniform(lvtype), mustDef: false, fflagchk: true, ref: undefined, pcode: undefined, trgt: etreg };
                    }
                });
            }
            else {
                //nop
            }
        }

        //now fill in positional parameters
        let apos = args.findIndex((ae) => ae.name === undefined && !(ae.expando && (ae.argtype as ValueType).flowtype.isRecordTargetType()));
        if (apos === -1) {
            apos = args.length;
        }

        let ii = 0;
        while (ii < sig.params.length && apos < args.length) {
            if (filledLocations[ii] !== undefined) {
                this.raiseErrorIf(sinfo, !filledLocations[ii].mustDef, `We have an potentially ambigious binding of an optional parameter "${sig.params[ii].name}"`);
                ++ii;
                continue;
            }

            const arg = args[apos];
            if (!arg.expando) {
                filledLocations[ii] = { vtype: arg.argtype, mustDef: true, fflagchk: false, ref: arg.ref, pcode: arg.pcode, trgt: arg.treg };
                if(sig.params[ii].isOptional) {
                    this.m_emitter.emitSetGuardFlagConstant(sinfo, fflag as string, ii - optfirst, true);
                }

                ++ii;
            }
            else {
                this.raiseErrorIf(sinfo, !(arg.argtype as ValueType).flowtype.isTupleTargetType(), "Only Tuple types can be expanded as positional arguments");
                const expandInfo = this.checkTypeOkForTupleExpando(sinfo, (arg.argtype as ValueType).flowtype);

                for (let ectr = 0; ectr < expandInfo[1]; ++ectr) {
                    this.raiseErrorIf(sinfo, ii >= sig.params.length, "Too many arguments as part of tuple expando and/or cannot split tuple expando (between arguments and rest)");
                    this.raiseErrorIf(sinfo, !sig.params[ii].isOptional && ectr >= expandInfo[0], `Call requires "${sig.params[ii].name}" but it is provided as an optional argument as part of tuple expando`);

                    const etreg = this.m_emitter.generateTmpRegister();
                    const lvtype = this.getInfoForLoadFromSafeIndex(sinfo, (arg.argtype as ValueType).flowtype, ectr);
                    const itype = this.m_emitter.registerResolvedTypeReference(lvtype);
                   
                    if(ectr < expandInfo[0]) {
                        this.m_emitter.emitLoadTupleIndex(sinfo, arg.treg as MIRRegisterArgument, this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).layout), this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).flowtype), ectr, !(arg.argtype as ValueType).flowtype.isUniqueTupleTargetType(), itype, etreg);
                        filledLocations[ii] = { vtype: ValueType.createUniform(lvtype), mustDef: true, fflagchk: false, ref: undefined, pcode: undefined, trgt: etreg };
                    }
                    else {
                        const param = sig.params[ii];
                        this.raiseErrorIf(sinfo, !param.isOptional, `Parameter "${param.name}" is required and must be assigned a value in call`);

                        this.m_emitter.emitLoadUninitVariableValue(sinfo, itype, etreg);
                        this.m_emitter.emitLoadTupleIndexSetGuard(sinfo, arg.treg as MIRRegisterArgument, this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).layout), this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).flowtype), ectr, !(arg.argtype as ValueType).flowtype.isUniqueTupleTargetType(), itype, etreg, new MIRMaskGuard(fflag as string, ii - optfirst, optcount));
                        filledLocations[ii] = { vtype: ValueType.createUniform(lvtype), mustDef: false, fflagchk: true, ref: undefined, pcode: undefined, trgt: etreg };
                    }

                    while (filledLocations[ii] !== undefined) {
                        this.raiseErrorIf(sinfo, !filledLocations[ii].mustDef, `We have an potentially ambigious binding of an optional parameter "${sig.params[ii].name}"`);
                        ii++;
                    }
                }
            }

            apos++;
            while (apos < args.length && (args[apos].name !== undefined || (args[apos].expando && (args[apos].argtype as ValueType).flowtype.isRecordTargetType()))) {
                apos++;
            }
        }

        while (filledLocations[ii] !== undefined) {
            this.raiseErrorIf(sinfo, !filledLocations[ii].mustDef, `We have an potentially ambigious binding of an optional parameter "${sig.params[ii].name}"`);
            ii++;
        }

        while (apos < args.length && (args[apos].name !== undefined || (args[apos].expando && (args[apos].argtype as ValueType).flowtype.isRecordTargetType()))) {
            apos++;
        }

        if (ii < sig.params.length) {
            this.raiseErrorIf(sinfo, !sig.params[ii].isOptional, `Insufficient number of parameters -- missing value for ${sig.params[ii].name}`);
        }
        else {
            this.raiseErrorIf(sinfo, apos !== args.length && sig.optRestParamType === undefined, "Too many arguments for call");
        }

        //go through names and fill out info for any that should use the default value -- raise error if any are missing
        //check ref, pcode, and regular arg types -- plus build up emit data
        let margs: MIRArgument[] = [];
        let pcodes: PCode[] = [];
        let refs: ["ref" | "out" | "out?", MIRRegisterArgument, ResolvedType][] = [];
        for (let j = 0; j < sig.params.length; ++j) {
            const paramtype = sig.params[j].type;

            if (filledLocations[j] === undefined) {
                this.raiseErrorIf(sinfo, !sig.params[j].isOptional, `Parameter ${sig.params[j].name} is required and must be assigned a value in constructor`);

                const emptyreg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitLoadUninitVariableValue(sinfo, this.m_emitter.registerResolvedTypeReference(paramtype as ResolvedType), emptyreg);
                this.m_emitter.emitSetGuardFlagConstant(sinfo, fflag as string, j - optfirst, false);
                filledLocations[j] = { vtype: ValueType.createUniform(paramtype as ResolvedType), mustDef: false, fflagchk: true, ref: undefined, pcode: undefined, trgt: emptyreg };
            }

            if (sig.params[j].type instanceof ResolvedFunctionType) {
                this.raiseErrorIf(sinfo, filledLocations[j].pcode === undefined, `Parameter ${sig.params[j].name} expected a function`);
                this.raiseErrorIf(sinfo, !this.m_assembly.functionSubtypeOf(filledLocations[j].vtype as ResolvedFunctionType, paramtype as ResolvedFunctionType), `Parameter ${sig.params[j].name} expected function of type ${paramtype.idStr}`);

                pcodes.push(filledLocations[j].pcode as PCode);
            }
            else {
                this.raiseErrorIf(sinfo, filledLocations[j].pcode !== undefined, `Parameter ${sig.params[j].name} cannot take a function`);

                if (sig.params[j].refKind !== undefined) {
                    this.raiseErrorIf(sinfo, filledLocations[j].ref === undefined, `Parameter ${sig.params[j].name} expected reference parameter`);
                    this.raiseErrorIf(sinfo, !(filledLocations[j].vtype as ValueType).layout.isSameType(paramtype as ResolvedType), `Parameter ${sig.params[j].name} expected argument of type ${paramtype.idStr}`);

                    refs.push([...(filledLocations[j].ref as ["ref" | "out" | "out?", MIRRegisterArgument]), (filledLocations[j].vtype as ValueType).layout] as ["ref" | "out" | "out?", MIRRegisterArgument, ResolvedType]);
                }
                else {
                    this.raiseErrorIf(sinfo, filledLocations[j].ref !== undefined, `Parameter ${sig.params[j].name} reference parameter is not allowed in this position`);
                    this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf((filledLocations[j].vtype as ValueType).flowtype, paramtype as ResolvedType), `Parameter ${sig.params[j].name} expected argument of type ${paramtype.idStr}`);
                }

                if (sig.params[j].refKind === undefined || sig.params[j].refKind === "ref") {
                    let narg = filledLocations[j].trgt as MIRArgument;
                    if (filledLocations[j].fflagchk) {
                        narg = this.emitCheckedInlineConvertIfNeeded(sinfo, narg, filledLocations[j].vtype as ValueType, sig.params[j].type as ResolvedType, new MIRStatmentGuard(new MIRMaskGuard(fflag as string, j - optfirst, optcount), "defaultonfalse", undefined));
                    }
                    else {
                        narg = this.emitInlineConvertIfNeeded(sinfo, narg, filledLocations[j].vtype as ValueType, sig.params[j].type as ResolvedType);
                    }

                    margs.push(narg);
                }
            }
        }

        //if this has a rest parameter check it
        if (sig.optRestParamType !== undefined) {
            const objtype = ResolvedType.tryGetOOTypeInfo(sig.optRestParamType);
            this.raiseErrorIf(sinfo, objtype === undefined || !(objtype instanceof ResolvedEntityAtomType), "Invalid rest type");

            const etype = sig.optRestParamType.getCollectionContentsType();
            const oodecl = (objtype as ResolvedEntityAtomType).object;
            const oobinds = (objtype as ResolvedEntityAtomType).binds;
            const oftype = ResolvedEntityAtomType.create(oodecl, oobinds);

            const rargs = args.slice(apos).filter((arg) => arg.name === undefined);
            const cargs = rargs.map((ca) => {
                if (ca.expando) {
                    return [(ca.argtype as ValueType).flowtype, true, this.emitInlineConvertToFlow<MIRRegisterArgument>(sinfo, ca.treg as MIRRegisterArgument, ca.argtype as ValueType)];
                }
                else {
                    return [etype, false, this.emitInlineConvertIfNeeded<MIRRegisterArgument>(sinfo, ca.treg as MIRRegisterArgument, ca.argtype as ValueType, etype)];
                }
            }) as [ResolvedType, boolean, MIRRegisterArgument][];

            const rtreg = this.m_emitter.generateTmpRegister();
            this.checkArgumentsCollectionConstructor(sinfo, oftype, etype, cargs, rtreg);

            margs.push(rtreg);
        }

        //take all the pcodes and pass the "captured" variables in as arguments in alpha order
        let cinfo: [string, ResolvedType][] = [];
        if (pcodes.length !== 0) {
            let allcaptured = new Set<string>();
            pcodes.forEach((pc) => pc.captured.forEach((v, k) => allcaptured.add(k)));

            const cnames = [...allcaptured].sort();
            for (let i = 0; i < cnames.length; ++i) {
                const vinfo = env.lookupVar(cnames[i]);
                if(vinfo === null) {
                    //This is the first place we capture $$this_captured so we sould pass "this" as the arg for it
                    const tinfo = env.lookupVar("this") as VarInfo;
                    margs.push(new MIRRegisterArgument("this"));

                    cinfo.push([cnames[i], tinfo.flowType]);
                }
                else {
                    if(env.getLocalVarInfo(cnames[i]) !== undefined) {
                        margs.push(new MIRRegisterArgument(cnames[i]));
                    }
                    else {
                        margs.push(new MIRRegisterArgument(vinfo.isCaptured ? this.m_emitter.generateCapturedVarName(cnames[i]) : cnames[i]));
                    }

                    cinfo.push([cnames[i], vinfo.flowType]);
                }
            }
        }

        return { args: margs, fflag: fflag, refs: refs, pcodes: pcodes, cinfo: cinfo };
    }

    private checkArgumentsWOperator(sinfo: SourceInfo, env: TypeEnvironment, opnames: string[], hasrest: boolean, args: ExpandedArgument[]): { args: MIRArgument[], types: ValueType[], refs: ["ref" | "out" | "out?", MIRRegisterArgument, ResolvedType][], pcodes: PCode[], cinfo: [string, ResolvedType][] } {
        let filledLocations: FilledLocation[] = [];

        //figure out named parameter mapping first
        for (let j = 0; j < args.length; ++j) {
            const arg = args[j];
            if (arg.name !== undefined) {
                const fidx = opnames.findIndex((name) => name === arg.name);
                this.raiseErrorIf(sinfo, fidx === -1, `Operator does not have parameter named "${arg.name}"`);
                this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name ${arg.name}`);

                filledLocations[fidx] = { vtype: arg.argtype, mustDef: true, fflagchk: false, ref: arg.ref, pcode: arg.pcode, trgt: arg.treg };
            }
            else if (arg.expando && (arg.argtype as ValueType).flowtype.isRecordTargetType()) {
                const expandInfo = this.checkTypeOkForRecordExpando(sinfo, (arg.argtype as ValueType).flowtype);
                this.raiseErrorIf(sinfo, expandInfo[0].size !== expandInfo[1].size, "Cannot have optional arguments on operator");

                expandInfo[1].forEach((pname) => {
                    const fidx = opnames.findIndex((name) => name === pname);
                    this.raiseErrorIf(sinfo, fidx === -1, `Operator does not have parameter named "${pname}"`);
                    this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${pname}"`);

                    const etreg = this.m_emitter.generateTmpRegister();
                    const lvtype =  this.getInfoForLoadFromSafeProperty(sinfo, (arg.argtype as ValueType).flowtype, pname);
                    const ptype = this.m_emitter.registerResolvedTypeReference(lvtype);

                    this.m_emitter.emitLoadProperty(sinfo, arg.treg as MIRRegisterArgument, this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).layout), this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).flowtype), pname, !(arg.argtype as ValueType).flowtype.isUniqueRecordTargetType(), ptype, etreg);
                    filledLocations[fidx] = { vtype: ValueType.createUniform(lvtype), mustDef: true, fflagchk: false, ref: undefined, pcode: undefined, trgt: etreg };
                });
            }
            else {
                //nop
            }
        }

        //now fill in positional parameters
        let apos = args.findIndex((ae) => ae.name === undefined && !(ae.expando && (ae.argtype as ValueType).flowtype.isRecordTargetType()));
        if (apos === -1) {
            apos = args.length;
        }

        let ii = 0;
        while (ii < opnames.length && apos < args.length) {
            if (filledLocations[ii] !== undefined) {
                ++ii;
                continue;
            }

            const arg = args[apos];
            if (!arg.expando) {
                filledLocations[ii] = { vtype: arg.argtype, mustDef: true, fflagchk: false, ref: arg.ref, pcode: arg.pcode, trgt: arg.treg };
                ++ii;
            }
            else {
                this.raiseErrorIf(sinfo, !(arg.argtype as ValueType).flowtype.isTupleTargetType(), "Only Tuple types can be expanded as positional arguments");
                const expandInfo = this.checkTypeOkForTupleExpando(sinfo, (arg.argtype as ValueType).flowtype);
                this.raiseErrorIf(sinfo, expandInfo[0] !== expandInfo[1], "Cannot have optional arguments on operator");

                for (let ectr = 0; ectr < expandInfo[1]; ++ectr) {
                    this.raiseErrorIf(sinfo, ii >= opnames.length, "Too many arguments as part of tuple expando and/or cannot split tuple expando (between arguments and rest)");
                    
                    const etreg = this.m_emitter.generateTmpRegister();
                    const lvtype = this.getInfoForLoadFromSafeIndex(sinfo, (arg.argtype as ValueType).flowtype, ectr);
                    const itype = this.m_emitter.registerResolvedTypeReference(lvtype);
                   
                    this.m_emitter.emitLoadTupleIndex(sinfo, arg.treg as MIRRegisterArgument, this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).layout), this.m_emitter.registerResolvedTypeReference((arg.argtype as ValueType).flowtype), ectr, !(arg.argtype as ValueType).flowtype.isUniqueTupleTargetType(), itype, etreg);
                    filledLocations[ii] = { vtype: ValueType.createUniform(lvtype), mustDef: true, fflagchk: false, ref: undefined, pcode: undefined, trgt: etreg };

                    while (filledLocations[ii] !== undefined) {
                        ii++;
                    }
                }
            }

            apos++;
            while (apos < args.length && (args[apos].name !== undefined || (args[apos].expando && (args[apos].argtype as ValueType).flowtype.isRecordTargetType()))) {
                apos++;
            }
        }

        while (apos < args.length && (args[apos].name !== undefined || (args[apos].expando && (args[apos].argtype as ValueType).flowtype.isRecordTargetType()))) {
            apos++;
        }

        this.raiseErrorIf(sinfo, ii < opnames.length, `Insufficient number of parameters -- missing value for ${opnames[ii]}`);
        this.raiseErrorIf(sinfo, !hasrest && apos !== args.length, "Too many arguments for operator");

        //check ref, pcode, and regular arg types -- plus build up emit data
        let margs: MIRArgument[] = [];
        let mtypes: ValueType[] = [];
        let pcodes: PCode[] = [];
        let refs: ["ref" | "out" | "out?", MIRRegisterArgument, ResolvedType][] = [];
        for (let j = 0; j < opnames.length; ++j) {
            this.raiseErrorIf(sinfo, filledLocations[j] === undefined, `Parameter ${opnames[j]} was not provided`);

            if (filledLocations[j].vtype instanceof ResolvedFunctionType) {
                pcodes.push(filledLocations[j].pcode as PCode);
            }
            else {
                this.raiseErrorIf(sinfo, filledLocations[j].pcode !== undefined, `Parameter ${opnames[j]} cannot take a function`);

                if (filledLocations[j].ref !== undefined) {
                    this.raiseErrorIf(sinfo, (filledLocations[j].ref as ["ref" | "out" | "out?", MIRRegisterArgument])[0] !== "ref" , "'out' and 'out?' refs are not supported on operators (yet)");

                    refs.push([...(filledLocations[j].ref as ["ref" | "out" | "out?", MIRRegisterArgument]), (filledLocations[j].vtype as ValueType).layout] as ["ref" | "out" | "out?", MIRRegisterArgument, ResolvedType]);
                }

                margs.push(filledLocations[j].trgt as MIRArgument);
                mtypes.push(filledLocations[j].vtype as ValueType);
            }
        }

        //if this has a rest parameter check it
        if (hasrest) {
            //
            //TODO: we may want to distinguish List, Set, Map options
            //
            const rargs = args.slice(apos).filter((arg) => arg.name === undefined);
            const cargs = rargs.map((ca) => [(ca.argtype as ValueType).flowtype, ca.expando, this.emitInlineConvertToFlow<MIRRegisterArgument>(sinfo, ca.treg as MIRRegisterArgument, ca.argtype as ValueType)] as [ResolvedType, boolean, MIRRegisterArgument]);

            const etype = this.m_assembly.typeUpperBound(cargs.map((aa) => {
                if(!aa[1]) {
                    return aa[0];
                }
                else {
                    this.raiseErrorIf(sinfo, aa[0].isUniqueCallTargetType(), "Expected unique expandoable collection type in expando position");

                    const oftexpando = this.getExpandoType(sinfo, aa[0].getUniqueCallTargetType());
                    return ResolvedType.createSingle(oftexpando);
                }
            }));

            const lentity = this.m_assembly.tryGetObjectTypeForFullyResolvedName("NSCore::List") as EntityTypeDecl;
            const oftype = ResolvedEntityAtomType.create(lentity, new Map<string, ResolvedType>().set("T", etype));

            const rtreg = this.m_emitter.generateTmpRegister();
            this.checkArgumentsCollectionConstructor(sinfo, oftype, etype, cargs, rtreg);

            margs.push(rtreg);
            mtypes.push(ValueType.createUniform(ResolvedType.createSingle(oftype)));
        }

        //take all the pcodes and pass the "captured" variables in as arguments in alpha order
        let cinfo: [string, ResolvedType][] = [];
        if (pcodes.length !== 0) {
            let allcaptured = new Set<string>();
            pcodes.forEach((pc) => pc.captured.forEach((v, k) => allcaptured.add(k)));

            const cnames = [...allcaptured].sort();
            for (let i = 0; i < cnames.length; ++i) {
                const vinfo = env.lookupVar(cnames[i]);
                if(vinfo === null) {
                    //This is the first place we capture $$this_captured so we sould pass "this" as the arg for it
                    const tinfo = env.lookupVar("this") as VarInfo;
                    margs.push(new MIRRegisterArgument("this"));

                    cinfo.push([cnames[i], tinfo.flowType]);
                }
                else {
                    if(env.getLocalVarInfo(cnames[i]) !== undefined) {
                        margs.push(new MIRRegisterArgument(cnames[i]));
                    }
                    else {
                        margs.push(new MIRRegisterArgument(vinfo.isCaptured ? this.m_emitter.generateCapturedVarName(cnames[i]) : cnames[i]));
                    }

                    cinfo.push([cnames[i], vinfo.flowType]);
                }
            }
        }

        return { args: margs, types: mtypes, refs: refs, pcodes: pcodes, cinfo: cinfo };
    }

    private generateExpandedReturnSig(sinfo: SourceInfo, declaredType: ResolvedType, params: {name: string, refKind: "ref" | "out" | "out?" | undefined, ptype: ResolvedType}[]): MIRType {
        const rtype = this.m_emitter.registerResolvedTypeReference(declaredType);
        const rr = params.filter((fp) => fp.refKind !== undefined).map((fp) => fp.ptype);
        const refinfo = rr.map((fpt) => this.m_emitter.registerResolvedTypeReference(fpt));

        if (refinfo.length === 0) {
            return rtype;
        }
        else {
            
            if (rtype.options.length !== 1 || !(rtype.options[0] instanceof ResolvedEphemeralListType)) {
                const etl = ResolvedType.createSingle(ResolvedEphemeralListType.create([declaredType, ...rr]));

                return this.m_emitter.registerResolvedTypeReference(etl);
            }
            else {
                const elr = declaredType.options[0] as ResolvedEphemeralListType;
                const etl = ResolvedType.createSingle(ResolvedEphemeralListType.create([...elr.types, ...rr]));

                return this.m_emitter.registerResolvedTypeReference(etl);
            }
        }
    }

    private generateRefInfoForCallEmit(fsig: ResolvedFunctionType, refs: ["ref" | "out" | "out?", MIRRegisterArgument, ResolvedType][]): { declresult: MIRType, runtimeresult: MIRType, elrcount: number, refargs: [MIRRegisterArgument, MIRType][] } {
        const rtype = this.m_emitter.registerResolvedTypeReference(fsig.resultType);
        const refinfo = refs.map((rn) => {
            const ptk = this.m_emitter.registerResolvedTypeReference(rn[2]);
            return [rn[1], ptk] as [MIRRegisterArgument, MIRType];
        });

        if (refinfo.length === 0) {
            return { declresult: rtype, runtimeresult: rtype, elrcount: -1, refargs: refinfo };
        }
        else {
            const rr = refs.map((rn) => rn[2]);
            if (fsig.resultType.options.length !== 1 || !(fsig.resultType.options[0] instanceof ResolvedEphemeralListType)) {
                const etl = ResolvedType.createSingle(ResolvedEphemeralListType.create([fsig.resultType, ...rr]));

                return { declresult: rtype, runtimeresult: this.m_emitter.registerResolvedTypeReference(etl), elrcount: -1, refargs: refinfo };
            }
            else {
                const elr = fsig.resultType.options[0] as ResolvedEphemeralListType;
                const etl = ResolvedType.createSingle(ResolvedEphemeralListType.create([...elr.types, ...rr]));

                return { declresult: rtype, runtimeresult: this.m_emitter.registerResolvedTypeReference(etl), elrcount: elr.types.length, refargs: refinfo };
            }
        }
    }

    private generateRefInfoForReturnEmit(returntype: ResolvedType, refparams: [string, ResolvedType][]): { declresult: MIRType, runtimeresult: MIRType, elrcount: number, refargs: [string, MIRType][] } {
        if (!this.m_emitter.getEmitEnabled()) {
            return { declresult: this.m_emitter.registerResolvedTypeReference(this.m_emitter.assembly.getSpecialNoneType()), runtimeresult: this.m_emitter.registerResolvedTypeReference(this.m_emitter.assembly.getSpecialNoneType()), elrcount: -1, refargs: [] };
        }

        const rtype = this.m_emitter.registerResolvedTypeReference(returntype as ResolvedType);
        const refinfo = refparams.map((rn) => {
            const ptk = this.m_emitter.registerResolvedTypeReference(rn[1]);
            return [rn[0], ptk] as [string, MIRType];
        });

        if (refinfo.length === 0) {
            return { declresult: rtype, runtimeresult: rtype, elrcount: -1, refargs: [] };
        }
        else {
            const rr = refparams.map((rn) => rn[1]);
            if (rtype.options.length !== 1 || !(rtype.options[0] instanceof ResolvedEphemeralListType)) {
                const etl = ResolvedType.createSingle(ResolvedEphemeralListType.create([returntype as ResolvedType, ...rr]));

                return { declresult: rtype, runtimeresult: this.m_emitter.registerResolvedTypeReference(etl), elrcount: -1, refargs: refinfo };
            }
            else {
                const elr = (returntype as ResolvedType).options[0] as ResolvedEphemeralListType;
                const etl = ResolvedType.createSingle(ResolvedEphemeralListType.create([...elr.types, ...rr]));

                return { declresult: rtype, runtimeresult: this.m_emitter.registerResolvedTypeReference(etl), elrcount: elr.types.length, refargs: refinfo };
            }
        }
    }

    private updateEnvForOutParams(env: TypeEnvironment, refs: ["ref" | "out" | "out?", MIRRegisterArgument, ResolvedType][]): TypeEnvironment[] {
        if(refs.some((rr) => rr[0] === "out?")) {
            const flows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, [env]);
            let tenvs = flows.tenvs;
            let fenvs = flows.fenvs;
            for(let i = 0; i < refs.length; ++i) {
                tenvs = tenvs.map((eev) => eev.setRefVar(refs[i][1].nameID));

                if(refs[i][0] !== "out?") {
                    fenvs = fenvs.map((eev) => eev.setRefVar(refs[i][1].nameID));
                }
            }

            return [...tenvs, ...fenvs];
        }
        else {
            for(let i = 0; i < refs.length; ++i) {
                env.setRefVar(refs[i][1].nameID);
            }    
            return [env];
        }
    }

    private checkLiteralNoneExpression(env: TypeEnvironment, exp: LiteralNoneExpression, trgt: MIRRegisterArgument): TypeEnvironment {
        this.m_emitter.emitLoadConstNone(exp.sinfo, trgt);

        return env.setUniformResultExpression(this.m_assembly.getSpecialNoneType());
    }

    private checkLiteralBoolExpression(env: TypeEnvironment, exp: LiteralBoolExpression, trgt: MIRRegisterArgument): TypeEnvironment {
        this.m_emitter.emitLoadConstBool(exp.sinfo, exp.value, trgt);

        return env.setUniformResultExpression(this.m_assembly.getSpecialBoolType(), exp.value ? FlowTypeTruthValue.True : FlowTypeTruthValue.False);
    }

    private checkLiteralNumberinoExpression(env: TypeEnvironment, exp: LiteralNumberinoExpression, trgt: MIRRegisterArgument, infertype: ResolvedType | undefined): TypeEnvironment {
        //
        //TODO: we probably want to special case +, *, ==, etc so that they also provide an infer type here so we are a bit friendlier
        //      can do this by checking if left/right are a numberino and getting the type for the other side first
        //

        this.raiseErrorIf(exp.sinfo, infertype === undefined, "Did not have a valid type to infer number into");
        const iitype = infertype as ResolvedType;

        //
        //TODO: should do int/nat/FP bounds checks more generally here
        //

        if(iitype.isSameType(this.m_assembly.getSpecialIntType()) || iitype.isSameType(this.m_assembly.getSpecialBigIntType())) {
            //TODO: should also check bounds

            const ispec = iitype.isSameType(this.m_assembly.getSpecialIntType()) ? "i" : "I";
            this.m_emitter.emitLoadConstIntegralValue(exp.sinfo, this.m_emitter.registerResolvedTypeReference(iitype), exp.value + ispec, trgt);
            return env.setUniformResultExpression(iitype);
        }
        else if(iitype.isSameType(this.m_assembly.getSpecialNatType()) || iitype.isSameType(this.m_assembly.getSpecialBigNatType())) {
            this.raiseErrorIf(exp.sinfo, exp.value.startsWith("-"), "Cannot have negative BigNat literal");

            const ispec = iitype.isSameType(this.m_assembly.getSpecialNatType()) ? "n" : "N";
            this.m_emitter.emitLoadConstIntegralValue(exp.sinfo, this.m_emitter.registerResolvedTypeReference(iitype), exp.value + ispec, trgt);
            return env.setUniformResultExpression(iitype);
        }
        else if(iitype.isSameType(this.m_assembly.getSpecialFloatType()) || iitype.isSameType(this.m_assembly.getSpecialDecimalType())) {
            const fspec = iitype.isSameType(this.m_assembly.getSpecialFloatType()) ? "f" : "d";

            this.m_emitter.emitLoadConstFloatPoint(exp.sinfo, this.m_emitter.registerResolvedTypeReference(iitype), exp.value + fspec, trgt);
            return env.setUniformResultExpression(iitype);
        }
        else if(iitype.isSameType(this.m_assembly.getSpecialRationalType())) {
            this.m_emitter.emitLoadConstRational(exp.sinfo, exp.value + "R", trgt);
            return env.setUniformResultExpression(this.m_assembly.getSpecialRationalType());
        }
        else {
            this.raiseErrorIf(exp.sinfo, !iitype.isUniqueCallTargetType() || !iitype.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.TypeDeclNumeric), "Not a valid numeric decl type");

            const tt = (iitype.getUniqueCallTargetType().object.memberFields.find((mf) => mf.name === "value") as MemberFieldDecl).declaredType;
            const rtt = this.m_assembly.normalizeTypeOnly(tt, new Map<string, ResolvedType>());

            let vspec = "?";
            if(rtt.isSameType(this.m_assembly.getSpecialIntType()) || rtt.isSameType(this.m_assembly.getSpecialBigIntType())) {
                vspec = rtt.isSameType(this.m_assembly.getSpecialIntType()) ? "i" : "I";
            }
            else if(rtt.isSameType(this.m_assembly.getSpecialNatType()) || rtt.isSameType(this.m_assembly.getSpecialBigNatType())) {
                vspec = rtt.isSameType(this.m_assembly.getSpecialNatType()) ? "n" : "N";
            }
            else if(rtt.isSameType(this.m_assembly.getSpecialFloatType()) || rtt.isSameType(this.m_assembly.getSpecialDecimalType())) {
                vspec = rtt.isSameType(this.m_assembly.getSpecialFloatType()) ? "f" : "d";
            }
            else {
                vspec = "R";
            }

            return this.checkTypedTypedNumericConstructor_helper(exp.sinfo, env, exp.value + vspec, iitype, rtt, trgt);
        }
    }

    private checkLiteralIntegralExpression(env: TypeEnvironment, exp: LiteralIntegralExpression, trgt: MIRRegisterArgument): TypeEnvironment {
        const itype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.itype, env.terms);
        
        //
        //TODO: should do int/nat/FP bounds checks more generally here
        //
        if(itype.isSameType(this.m_assembly.getSpecialNatType()) || itype.isSameType(this.m_assembly.getSpecialBigNatType())) {
            this.raiseErrorIf(exp.sinfo, exp.value.startsWith("-"), "Cannot have negative Nat/BigNat literal");
        }

        this.m_emitter.emitLoadConstIntegralValue(exp.sinfo, this.m_emitter.registerResolvedTypeReference(itype), exp.value, trgt);

        return env.setUniformResultExpression(itype);
    }

    private checkLiteralRationalExpression(env: TypeEnvironment, exp: LiteralRationalExpression, trgt: MIRRegisterArgument): TypeEnvironment {
        this.m_emitter.emitLoadConstRational(exp.sinfo, exp.value, trgt);

        return env.setUniformResultExpression(this.m_assembly.getSpecialRationalType());
    }

    private checkLiteralFloatExpression(env: TypeEnvironment, exp: LiteralFloatPointExpression, trgt: MIRRegisterArgument): TypeEnvironment {
        const fptype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.fptype, env.terms);
        this.m_emitter.emitLoadConstFloatPoint(exp.sinfo, this.m_emitter.registerResolvedTypeReference(fptype), exp.value, trgt);

        return env.setUniformResultExpression(fptype);
    }

    private checkLiteralStringExpression(env: TypeEnvironment, exp: LiteralStringExpression, trgt: MIRRegisterArgument): TypeEnvironment {
       this.m_emitter.emitLoadConstString(exp.sinfo, exp.value, trgt);

        return env.setUniformResultExpression(this.m_assembly.getSpecialStringType());
    }

    private checkLiteralRegexExpression(env: TypeEnvironment, exp: LiteralRegexExpression, trgt: MIRRegisterArgument): TypeEnvironment {
        this.m_emitter.emitLoadLiteralRegex(exp.sinfo, exp.value, trgt);

        return env.setUniformResultExpression(this.m_assembly.getSpecialRegexType());
    }

    private checkLiteralParameterValueExpression(env: TypeEnvironment, exp: LiteralParamerterValueExpression, trgt: MIRRegisterArgument, infertype: ResolvedType | undefined): TypeEnvironment {
        const vv = (env.terms.get(exp.ltype.name) as ResolvedType).options[0] as ResolvedLiteralAtomType;
        return this.checkExpression(env, vv.vexp, trgt, infertype);
    }

    private checkStringOfCommon(sinfo: SourceInfo, env: TypeEnvironment, ttype: TypeSignature): { oftype: [OOPTypeDecl, Map<string, ResolvedType>], ofresolved: ResolvedType, stringtype: ResolvedType } {
        const oftype = this.resolveAndEnsureTypeOnly(sinfo, ttype, env.terms);
        this.raiseErrorIf(sinfo, !oftype.isUniqueCallTargetType() || !oftype.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.ValidatorTypeDecl), "Validator type must be a unique type");
        
        const aoftype = ResolvedType.tryGetOOTypeInfo(oftype);
        const oodecl = (aoftype as ResolvedEntityAtomType).object;
        const oobinds = (aoftype as ResolvedEntityAtomType).binds;

        //ensure full string<T> type is registered
        const terms = [new TemplateTypeSignature("T")];
        const binds = new Map<string, ResolvedType>().set("T", oftype);
        const stype = this.resolveAndEnsureTypeOnly(sinfo, new NominalTypeSignature("NSCore", ["StringOf"], terms), binds);

        return { oftype: [oodecl, oobinds], ofresolved: oftype, stringtype: stype };
    }

    private checkDataStringCommon(sinfo: SourceInfo, env: TypeEnvironment, ttype: TypeSignature): { oftype: [OOPTypeDecl, Map<string, ResolvedType>], ofresolved: ResolvedType, stringtype: ResolvedType, parsetype: ResolvedType } {
        const oftype = this.resolveAndEnsureTypeOnly(sinfo, ttype, env.terms);
        this.raiseErrorIf(sinfo, oftype.options.length !== 1, "Cannot have union of parsable types");
        this.raiseErrorIf(sinfo, oftype.options[0] instanceof ResolvedConceptAtomType && (oftype.options[0] as ResolvedConceptAtomType).conceptTypes.length !== 1, "Cannot have & of concepts");
        
        const aoftype = oftype.options[0];
        const oodecl = (aoftype instanceof ResolvedEntityAtomType) ? aoftype.object : (aoftype as ResolvedConceptAtomType).conceptTypes[0].concept;
        const oobinds = (aoftype instanceof ResolvedEntityAtomType) ? aoftype.binds : (aoftype as ResolvedConceptAtomType).conceptTypes[0].binds;

        const fdecltry = oodecl.staticFunctions.find((sf) => sf.name === "tryParse");
        this.raiseErrorIf(sinfo, fdecltry === undefined, `Constant value not defined for type '${oftype.idStr}'`);

        //ensure full DataString<T> type is registered
        const terms = [new TemplateTypeSignature("T")];
        const binds = new Map<string, ResolvedType>().set("T", oftype);
        const stype = this.resolveAndEnsureTypeOnly(sinfo, new NominalTypeSignature("NSCore", ["DataString"], terms), binds);

        const frbinds = this.m_assembly.resolveBindsForCallComplete([], [], binds, new Map<string, ResolvedType>(), new Map<string, ResolvedType>()) as Map<string, ResolvedType>;
        const ptype = this.resolveAndEnsureTypeOnly(sinfo, (fdecltry as StaticFunctionDecl).invoke.resultType, frbinds);

        return { oftype: [oodecl, oobinds], ofresolved: oftype, stringtype: stype, parsetype: ptype };
    }

    private checkCreateTypedString(env: TypeEnvironment, exp: LiteralTypedStringExpression, trgt: MIRRegisterArgument): TypeEnvironment {
        const oftype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.stype, env.terms);
        this.raiseErrorIf(exp.sinfo, !oftype.isUniqueCallTargetType(), "Type must be a unique type");
        
        if(oftype.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.ValidatorTypeDecl)) {
            const aoftype = this.checkStringOfCommon(exp.sinfo, env, exp.stype);
    
            const sdecl = aoftype.oftype[0].staticFunctions.find((sf) => sf.name === "accepts");
            assert(sdecl !== undefined);

            const vv = this.m_assembly.tryGetValidatorForFullyResolvedName(oftype.idStr);
            this.raiseErrorIf(exp.sinfo, vv === undefined, `Bad Validator type for StringOf ${oftype.idStr}`);
            
            const argstr = unescapeLiteralString(exp.value.substring(1, exp.value.length - 1));
            const mtchre = (vv as BSQRegex).compileToJS();
            const mtch = new RegExp(mtchre, "u").exec(argstr);
            this.raiseErrorIf(exp.sinfo, mtch === null || mtch[0].length !== argstr.length, "Literal string failed Validator regex");

            const stype = this.m_emitter.registerResolvedTypeReference(aoftype.stringtype);

            this.m_emitter.emitLoadLiteralStringOf(exp.sinfo, exp.value, stype.trkey, trgt);
            return env.setUniformResultExpression(aoftype.stringtype);
        }
        else {
            const aoftype = this.checkDataStringCommon(exp.sinfo, env, exp.stype);
            const sdecl = aoftype.oftype[0].staticFunctions.find((sf) => sf.name === "tryParse");
            this.raiseErrorIf(exp.sinfo, sdecl === undefined, "Missing static function 'tryParse'");

            const stype = this.m_emitter.registerResolvedTypeReference(aoftype.stringtype);

            const presult = this.m_emitter.registerResolvedTypeReference(aoftype.parsetype);

            const sbinds = this.m_assembly.resolveBindsForCallComplete([], [], (aoftype.stringtype.options[0] as ResolvedEntityAtomType).binds, new Map<string, ResolvedType>(), new Map<string, ResolvedType>()) as Map<string, ResolvedType>;
            const ctype = this.m_emitter.registerResolvedTypeReference(this.resolveOOTypeFromDecls(aoftype.oftype[0], aoftype.oftype[1]));
            const skey = this.m_emitter.registerStaticCall([ctype, aoftype.oftype[0], aoftype.oftype[1]], sdecl as StaticFunctionDecl, "tryParse", sbinds, [], []);

            const tmps = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitInvokeFixedFunction(exp.sinfo, skey, [new MIRConstantString(exp.value)], undefined, presult, tmps);

            const tmpokt = this.m_emitter.generateTmpRegister();
            const oktype = this.m_emitter.registerResolvedTypeReference(this.getResultSubtypes(aoftype.parsetype)[0]);
            this.m_emitter.emitCheckNoError(exp.sinfo, tmps, presult, oktype, tmpokt);
            this.m_emitter.emitAssertCheck(exp.sinfo, "String not parsable as given type", tmpokt);
            
            this.m_emitter.emitLoadConstDataString(exp.sinfo, exp.value, stype.trkey, trgt);
            return env.setUniformResultExpression(aoftype.stringtype);
        }
    }

    private checkDataStringConstructor(env: TypeEnvironment, exp: LiteralTypedStringConstructorExpression, trgt: MIRRegisterArgument): TypeEnvironment {
        const aoftype = this.checkDataStringCommon(exp.sinfo, env, exp.stype);

        const sdecl = aoftype.oftype[0].staticFunctions.find((sf) => sf.name === "parse");
        this.raiseErrorIf(exp.sinfo, sdecl === undefined, "Missing static function 'parse'");

        this.raiseErrorIf(exp.sinfo, this.isConstructorTypeOfValue(this.getResultBinds(aoftype.parsetype).T) !== exp.isvalue, "Mismatch in storage layout decl and call");
        const presult = this.m_emitter.registerResolvedTypeReference(aoftype.parsetype);

        const sbinds = this.m_assembly.resolveBindsForCallComplete([], [], (aoftype.stringtype.options[0] as ResolvedEntityAtomType).binds, new Map<string, ResolvedType>(), new Map<string, ResolvedType>()) as Map<string, ResolvedType>;
        const ctype = this.m_emitter.registerResolvedTypeReference(this.resolveOOTypeFromDecls(aoftype.oftype[0], aoftype.oftype[1]));
        const skey = this.m_emitter.registerStaticCall([ctype, aoftype.oftype[0], aoftype.oftype[1]], sdecl as StaticFunctionDecl, "tryParse", sbinds, [], []);

        const tmps = this.m_emitter.generateTmpRegister();
        this.m_emitter.emitInvokeFixedFunction(exp.sinfo, skey, [new MIRConstantString(exp.value)], undefined, presult, tmps);

        const tmpokt = this.m_emitter.generateTmpRegister();
        const oktype = this.m_emitter.registerResolvedTypeReference(this.getResultSubtypes(aoftype.parsetype)[0]);
        const okvfield = MIRKeyGenerator.generateFieldKey(this.getResultSubtypes(aoftype.parsetype)[0], "value");
        this.m_emitter.emitCheckNoError(exp.sinfo, tmps, presult, oktype, tmpokt);
        this.m_emitter.emitAssertCheck(exp.sinfo, "String not parsable as given type", tmpokt);

        this.m_emitter.emitExtractResultOkValue(exp.sinfo, tmps, presult, oktype, okvfield, this.m_emitter.registerResolvedTypeReference(this.getResultBinds(aoftype.parsetype).T), trgt);
        return env.setUniformResultExpression(this.getResultBinds(aoftype.parsetype).T);
    }

    private checkTypedTypedNumericConstructor_helper(sinfo: SourceInfo, env: TypeEnvironment, value: string, tntt: ResolvedType, ntype: ResolvedType, trgt: MIRRegisterArgument): TypeEnvironment {
        const oftype = (tntt.options[0] as ResolvedEntityAtomType).object;
        const ofbinds = (tntt.options[0] as ResolvedEntityAtomType).binds;

        const consf = oftype.staticFunctions.find((sf) => sf.name === "create");
        this.raiseErrorIf(sinfo, consf === undefined, "Missing static function 'create'");

        let nval: MIRArgument = new MIRConstantNone();
        if(ntype.isSameType(this.m_assembly.getSpecialIntType())) {
            //TODO: should also check bounds

            nval = new MIRConstantInt(value);
        }
        else if(ntype.isSameType(this.m_assembly.getSpecialNatType())) {
            this.raiseErrorIf(sinfo, value.startsWith("-"), "Cannot have negative Nat literal");
            //TODO: should also check bounds

            nval = new MIRConstantNat(value);
        }
        else if(ntype.isSameType(this.m_assembly.getSpecialBigIntType())) {
            nval = new MIRConstantBigInt(value);
        }
        else if(ntype.isSameType(this.m_assembly.getSpecialBigNatType())) {
            this.raiseErrorIf(sinfo, value.startsWith("-"), "Cannot have negative BigNat literal");

            nval = new MIRConstantBigNat(value);
        }
        else if(ntype.isSameType(this.m_assembly.getSpecialRationalType())) {
            nval = new MIRConstantRational(value);
        }
        else if(ntype.isSameType(this.m_assembly.getSpecialFloatType())) {
            nval = new MIRConstantFloat(value);
        }
        else {
            nval = new MIRConstantDecimal(value);
        }

        if(oftype.invariants.length !== 0) {
            const fkey = MIRKeyGenerator.generateFunctionKey(`${oftype.ns}::${oftype.name}`, "@@invariant", ofbinds, []);
        
            const tmps = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitInvokeFixedFunction(sinfo, fkey, [nval], undefined, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), tmps);
            this.m_emitter.emitAssertCheck(sinfo, "Number does not satisfy requirements for type", tmps);    
        }
        
        this.m_emitter.emitLoadTypedNumeric(sinfo, nval, this.m_emitter.registerResolvedTypeReference(tntt).trkey, trgt);
        return env.setUniformResultExpression(tntt);
    }

    private checkTypedTypedNumericConstructor(env: TypeEnvironment, exp: LiteralTypedNumericConstructorExpression, trgt: MIRRegisterArgument): TypeEnvironment {
        const tntt = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.vtype, env.terms);
        const ntype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.ntype, new Map<string, ResolvedType>());

        return this.checkTypedTypedNumericConstructor_helper(exp.sinfo, env, exp.value, tntt, ntype, trgt);
    }

    private checkAccessNamespaceConstant(env: TypeEnvironment, exp: AccessNamespaceConstantExpression, trgt: MIRRegisterArgument): TypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !this.m_assembly.hasNamespace(exp.ns), `Namespace '${exp.ns}' is not defined`);
        const nsdecl = this.m_assembly.getNamespace(exp.ns);

        this.raiseErrorIf(exp.sinfo, !nsdecl.consts.has(exp.name), `Constant named '${exp.name}' is not defined`);
        const cdecl = nsdecl.consts.get(exp.name) as NamespaceConstDecl;

        this.raiseErrorIf(exp.sinfo, cdecl.value.captured.size !== 0, "Expression uses unbound variables");
        const cexp = this.m_assembly.compileTimeReduceConstantExpression(cdecl.value.exp, env.terms, this.resolveAndEnsureTypeOnly(exp.sinfo, cdecl.declaredType, new Map<string, ResolvedType>()));
        const rtype = this.resolveAndEnsureTypeOnly(exp.sinfo, cdecl.declaredType, new Map<string, ResolvedType>());

        if (cexp !== undefined) {
            const ccreg = this.m_emitter.generateTmpRegister();
            const vtype = this.checkExpression(env, cexp, ccreg, undefined).getExpressionResult().valtype;
            this.m_emitter.emitRegisterStore(exp.sinfo, this.emitInlineConvertIfNeeded(exp.sinfo, ccreg, vtype, rtype), trgt, this.m_emitter.registerResolvedTypeReference(rtype), undefined);
        }
        else {
            const gkey = this.m_emitter.registerPendingGlobalProcessing(cdecl, rtype);
            this.m_emitter.emitRegisterStore(exp.sinfo, new MIRGlobalVariable(gkey), trgt, this.m_emitter.registerResolvedTypeReference(rtype), undefined);
        }

        return env.setUniformResultExpression(rtype);
    }

    private checkAccessStaticField(env: TypeEnvironment, exp: AccessStaticFieldExpression, trgt: MIRRegisterArgument): TypeEnvironment {
        const oftype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.stype, env.terms);

        const cdecltry = this.m_assembly.tryGetConstMemberUniqueDeclFromType(oftype, exp.name);
        this.raiseErrorIf(exp.sinfo, cdecltry === undefined, `Constant value not defined (or not uniquely defined) for type '${oftype.idStr}'`);

        const cdecl = cdecltry as OOMemberLookupInfo<StaticMemberDecl>;
        
        this.raiseErrorIf(exp.sinfo, (cdecl.decl.value as ConstantExpressionValue).captured.size !== 0, "Expression uses unbound variables");
        const cexp = this.m_assembly.compileTimeReduceConstantExpression((cdecl.decl.value as ConstantExpressionValue).exp, env.terms, this.resolveAndEnsureTypeOnly(exp.sinfo, cdecl.decl.declaredType, cdecl.binds));
        const rtype = this.resolveAndEnsureTypeOnly(exp.sinfo, cdecl.decl.declaredType, cdecl.binds);
        
        if (cexp !== undefined) {
            const ccreg = this.m_emitter.generateTmpRegister();
            const vtype = this.checkExpression(env, cexp, ccreg, undefined).getExpressionResult().valtype;
            this.m_emitter.emitRegisterStore(exp.sinfo, this.emitInlineConvertIfNeeded(exp.sinfo, ccreg, vtype, rtype), trgt, this.m_emitter.registerResolvedTypeReference(rtype), undefined);
        }
        else {
            const rctype = this.resolveOOTypeFromDecls(cdecl.contiainingType, cdecl.binds);
            const skey = this.m_emitter.registerPendingConstProcessing([this.m_emitter.registerResolvedTypeReference(rctype), cdecl.contiainingType, cdecl.binds], cdecl.decl, cdecl.binds, rtype);
            this.m_emitter.emitRegisterStore(exp.sinfo, new MIRGlobalVariable(skey), trgt, this.m_emitter.registerResolvedTypeReference(rtype), undefined);
        }
        
        return env.setUniformResultExpression(rtype);
    }

    private checkAccessVariable(env: TypeEnvironment, exp: AccessVariableExpression, trgt: MIRRegisterArgument): TypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !env.isVarNameDefined(exp.name), `Variable name '${exp.name}' is not defined`);

        const vinfo = env.lookupVar(exp.name) as VarInfo;
        this.raiseErrorIf(exp.sinfo, !vinfo.mustDefined, "Var may not have been assigned a value");
        if(vinfo.isCaptured) {
            this.m_emitter.emitRegisterStore(exp.sinfo, new MIRRegisterArgument(this.m_emitter.generateCapturedVarName(exp.name)), trgt, this.m_emitter.registerResolvedTypeReference(vinfo.declaredType), undefined);    
        }
        else {
            this.m_emitter.emitRegisterStore(exp.sinfo, new MIRRegisterArgument(exp.name), trgt, this.m_emitter.registerResolvedTypeReference(vinfo.declaredType), undefined);    
        }

        return env.setVarResultExpression(vinfo.declaredType, vinfo.flowType, exp.name);
    }

    private checkConstructorPrimary(env: TypeEnvironment, exp: ConstructorPrimaryExpression, trgt: MIRRegisterArgument): TypeEnvironment {
        const ctype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.ctype, env.terms);
        const objtype = ResolvedType.tryGetOOTypeInfo(ctype);
        this.raiseErrorIf(exp.sinfo, objtype === undefined || !(objtype instanceof ResolvedEntityAtomType), "Invalid constructor type");
        this.raiseErrorIf(exp.sinfo, this.isConstructorTypeOfValue(ctype) !== exp.isvalue, "Mismatch in storage layout decl and call");

        const oodecl = (objtype as ResolvedEntityAtomType).object;
        const oobinds = (objtype as ResolvedEntityAtomType).binds;
        this.checkTemplateTypes(exp.sinfo, oodecl.terms, oobinds);

        const oftype = ResolvedEntityAtomType.create(oodecl, oobinds);
        if (oodecl.isTypeAListEntity() || oodecl.isTypeAStackEntity() || oodecl.isTypeAQueueEntity()) {
            const ctype = oobinds.get("T") as ResolvedType;
            const eargs = this.checkArgumentsEvaluationCollection(env, exp.args, ctype);
            const atype = this.checkArgumentsCollectionConstructor(exp.sinfo, oftype, ctype, eargs, trgt);

            return env.setUniformResultExpression(atype);
        }
        else if (oodecl.isTypeASetEntity()) {
            const ctype = oobinds.get("T") as ResolvedType;
            const eargs = this.checkArgumentsEvaluationCollection(env, exp.args, ctype);
            const atype = this.checkArgumentsCollectionConstructor(exp.sinfo, oftype, ctype, eargs, trgt);

            return env.setUniformResultExpression(atype);
        }
        else if (oodecl.isTypeAMapEntity()) {
            const entrytuple = new TupleTypeSignature(true, [[new TemplateTypeSignature("K"), false], [new TemplateTypeSignature("K"), false]]);
            const entrybinds = new Map<string, ResolvedType>().set("K", oobinds.get("K") as ResolvedType).set("V", oobinds.get("V") as ResolvedType);
            const entryobj = this.resolveAndEnsureTypeOnly(exp.sinfo, entrytuple, entrybinds);

            const eargs = this.checkArgumentsEvaluationCollection(env, exp.args, entryobj);
            const atype = this.checkArgumentsCollectionConstructor(exp.sinfo, oftype, entryobj, eargs, trgt);

            return env.setUniformResultExpression(atype);
        }
        else {
            const eargs = this.checkArgumentsEvaluationEntity(exp.sinfo, env, oftype, exp.args);
            const atype = this.checkArgumentsEntityConstructor(exp.sinfo, oftype, eargs, trgt);

            return env.setUniformResultExpression(atype);
        }
    }

    private checkConstructorPrimaryWithFactory(env: TypeEnvironment, exp: ConstructorPrimaryWithFactoryExpression, trgt: MIRRegisterArgument): TypeEnvironment {
        const ctype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.ctype, env.terms);
        const objtype = ResolvedType.tryGetOOTypeInfo(ctype);
        this.raiseErrorIf(exp.sinfo, objtype === undefined || !(objtype instanceof ResolvedEntityAtomType), "Invalid constructor type");
        this.raiseErrorIf(exp.sinfo, this.isConstructorTypeOfValue(ctype) === exp.isvalue, "Mismatch in storage layout decl and call");

        const oodecl = (objtype as ResolvedEntityAtomType).object;
        const oobinds = (objtype as ResolvedEntityAtomType).binds;
        this.raiseErrorIf(exp.sinfo, !(oodecl instanceof EntityTypeDecl), "Can only construct concrete entities");
        this.checkTemplateTypes(exp.sinfo, oodecl.terms, oobinds);

        const fdecl = oodecl.staticFunctions.find((sf) => sf.name === exp.factoryName);
        this.raiseErrorIf(exp.sinfo, fdecl === undefined || !OOPTypeDecl.attributeSetContains("factory", fdecl.invoke.attributes), `Function is not a factory function for type '${ctype.idStr}'`);

        const [fsig, callbinds, eargs] = this.inferAndCheckArguments(exp.sinfo, env, exp.args, (fdecl as StaticFunctionDecl).invoke, exp.terms.targs, oobinds, env.terms, undefined, false);
        const rargs = this.checkArgumentsSignature(exp.sinfo, env, exp.factoryName, fsig, eargs);

        this.checkRecursion(exp.sinfo, fsig, rargs.pcodes, exp.rec);

        const etreg = this.m_emitter.generateTmpRegister();
        const ootype = this.m_emitter.registerResolvedTypeReference(this.resolveOOTypeFromDecls(oodecl, oobinds));
        const skey = this.m_emitter.registerStaticCall([ootype, oodecl, oobinds], fdecl as StaticFunctionDecl, exp.factoryName, callbinds, rargs.pcodes, rargs.cinfo);

        const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
        this.m_emitter.emitInvokeFixedFunction(exp.sinfo, skey, rargs.args, rargs.fflag, refinfo, etreg);

        const oftype = ResolvedEntityAtomType.create(oodecl, oobinds);
        const returntype = (fsig as ResolvedFunctionType).resultType;
        const atype = this.checkArgumentsEntityConstructor(exp.sinfo, oftype, [{ name: undefined, argtype: ValueType.createUniform(returntype), expando: true, ref: undefined, pcode: undefined, treg: etreg }], trgt);

        return env.setUniformResultExpression(atype);
    }

    private checkTupleConstructor(env: TypeEnvironment, exp: ConstructorTupleExpression, trgt: MIRRegisterArgument, infertype: ResolvedType | undefined): TypeEnvironment {
        let itype: ResolvedTupleAtomType | undefined = undefined;
        if(infertype !== undefined) {
            itype = infertype.tryGetInferrableTupleConstructorType(exp.isvalue);
        }

        const eargs = this.checkArgumentsEvaluationTuple(env, exp.args, itype);
        const rtype = this.checkArgumentsTupleConstructor(exp.sinfo, exp.isvalue, eargs, trgt);

        return env.setUniformResultExpression(rtype);
    }

    private checkRecordConstructor(env: TypeEnvironment, exp: ConstructorRecordExpression, trgt: MIRRegisterArgument, infertype: ResolvedType | undefined): TypeEnvironment {
        let itype: ResolvedRecordAtomType | undefined = undefined;
        if(infertype !== undefined) {
            itype = infertype.tryGetInferrableRecordConstructorType(exp.isvalue);
        }

        const eargs = this.checkArgumentsEvaluationRecord(env, exp.args, itype);
        const rtype = this.checkArgumentsRecordConstructor(exp.sinfo, exp.isvalue, eargs, trgt);
        return env.setUniformResultExpression(rtype);
    }

    private checkConstructorEphemeralValueList(env: TypeEnvironment, exp: ConstructorEphemeralValueList, trgt: MIRRegisterArgument, infertype: ResolvedType | undefined): TypeEnvironment {
        let itype: ResolvedEphemeralListType | undefined = undefined;
        if(infertype !== undefined) {
            itype = infertype.tryGetInferrableValueListConstructorType();
        }

        const eargs = this.checkArgumentsEvaluationValueList(env, exp.args, itype);
        const rtype = this.checkArgumentsValueListConstructor(exp.sinfo, eargs, trgt);
        return env.setUniformResultExpression(rtype);
    }

    private checkSpecialConstructorExpression(env: TypeEnvironment, exp: SpecialConstructorExpression, trgt: MIRRegisterArgument, infertype: ResolvedType | undefined): TypeEnvironment {
        this.raiseErrorIf(exp.sinfo, infertype !== undefined && (infertype.options.length !== 1 || !(infertype as ResolvedType).idStr.startsWith("NSCore::Result<")), "ok/err shorthand constructors only valid with NSCore::Result typed expressions");

        const { T, E } = infertype !== undefined && infertype.options.length === 1 ? this.getResultBinds(infertype) : { T: undefined, E: undefined };
        const treg = this.m_emitter.generateTmpRegister();
        if (exp.rop === "ok") {
            const okenv = this.checkExpression(env, exp.arg, treg, T);
            const oktdcl = this.m_assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Result::Ok") as EntityTypeDecl;
            const okbinds = new Map<string, ResolvedType>().set("T", T || okenv.getExpressionResult().valtype.flowtype).set("E", E || this.m_assembly.getSpecialAnyConceptType());
            const okconstype = ResolvedType.createSingle(ResolvedEntityAtomType.create(oktdcl, okbinds));
            const mirokconstype = this.m_emitter.registerResolvedTypeReference(okconstype);

            const okconsfunc = oktdcl.staticFunctions.find((sf) => sf.name === "create") as StaticFunctionDecl;
            const ootype = this.m_emitter.registerResolvedTypeReference(this.resolveOOTypeFromDecls(oktdcl, okbinds));
            const okconskey = this.m_emitter.registerStaticCall([ootype, oktdcl, okbinds], okconsfunc, "create", new Map<string, ResolvedType>(), [], []);

            const ctarg = this.emitInlineConvertIfNeeded(exp.sinfo, treg, okenv.getExpressionResult().valtype, okbinds.get("T") as ResolvedType);
            this.m_emitter.emitInvokeFixedFunction(exp.sinfo, okconskey, [ctarg], undefined, mirokconstype, trgt);
    
            return env.setUniformResultExpression(okconstype);
        }
        else {
            this.raiseErrorIf(exp.sinfo, infertype === undefined, "Can't infer success type for Result<T, E>::Err");

            const errenv = this.checkExpression(env, exp.arg, treg, E);
            const errtdcl = this.m_assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Result::Err") as EntityTypeDecl;
            const errbinds = new Map<string, ResolvedType>().set("T", T as ResolvedType).set("E", E || errenv.getExpressionResult().valtype.flowtype);
            const errconstype = ResolvedType.createSingle(ResolvedEntityAtomType.create(errtdcl, errbinds));
            const mirerrconstype = this.m_emitter.registerResolvedTypeReference(errconstype);

            const errconsfunc = errtdcl.staticFunctions.find((sf) => sf.name === "create") as StaticFunctionDecl;
            const ootype = this.m_emitter.registerResolvedTypeReference(this.resolveOOTypeFromDecls(errtdcl, errbinds));
            const errconskey = this.m_emitter.registerStaticCall([ootype, errtdcl, errbinds], errconsfunc, "create", new Map<string, ResolvedType>(), [], []);

            const ctarg = this.emitInlineConvertIfNeeded(exp.sinfo, treg, errenv.getExpressionResult().valtype, errbinds.get("E") as ResolvedType);
            this.m_emitter.emitInvokeFixedFunction(exp.sinfo, errconskey, [ctarg], undefined, mirerrconstype, trgt);
    
            return env.setUniformResultExpression(errconstype);
        }
    }

    private checkNamespaceOperatorInvoke(sinfo: SourceInfo, env: TypeEnvironment, opdecl: NamespaceOperatorDecl, args: MIRArgument[], argtypes: ValueType[], refs: ["ref" | "out" | "out?", MIRRegisterArgument, ResolvedType][], pcodes: PCode[], cinfo: [string, ResolvedType][], recursive: RecursiveAnnotation, trgt: MIRRegisterArgument, refok: boolean): TypeEnvironment[] {
        const fsig = this.m_assembly.normalizeTypeFunction(opdecl.invoke.generateSig(), new Map<string, ResolvedType>()) as ResolvedFunctionType;
        this.checkRecursion(sinfo, fsig, pcodes, recursive);

        //if it is a static operator or it has a unique dynamic resolution based on the types
        if (!opdecl.isDynamic || !OOPTypeDecl.attributeSetContains("abstract", opdecl.invoke.attributes)) {
            let cargs: MIRArgument[] = [];
            let sigkeys: string[] = [];
            for (let i = 0; i < fsig.params.length; ++i) {
                if(fsig.params[i] instanceof ResolvedFunctionType) {
                    continue;
                }

                const argidx = cargs.length;
                if(fsig.params[i].refKind !== undefined) {
                    this.raiseErrorIf(sinfo, !refok, "ref argument not supported in this call position");
                    this.raiseErrorIf(sinfo, !argtypes[argidx].layout.isSameType(fsig.params[i].type as ResolvedType));
                }
                cargs.push(this.emitInlineConvertIfNeeded(sinfo, args[argidx], argtypes[argidx], fsig.params[i].type as ResolvedType));

                if(opdecl.invoke.params[i].litexp === undefined) {
                    sigkeys.push(this.m_emitter.registerResolvedTypeReference(fsig.params[i].type as ResolvedType).trkey);
                }
                else {
                    const lev = (opdecl.invoke.params[i].litexp as LiteralExpressionValue);
                    const cexp = this.m_assembly.reduceLiteralValueToCanonicalForm(lev.exp, env.terms, fsig.params[i].type as ResolvedType);
                    this.raiseErrorIf(sinfo, cexp === undefined, "Invalid literal argument");
                    
                    const [clexp, cltype, cltag] = cexp as [Expression, ResolvedType, string, boolean | number | undefined];
                    sigkeys.push(cltag)
                    
                    const lcreg = this.m_emitter.generateTmpRegister();    
                    this.checkExpression(env, clexp, lcreg, undefined);

                    //Should have same error if we fail to find suitable dynamic dispatch -- this is just a nice optimization
                    const ichkreg = this.m_emitter.generateTmpRegister();
                    const mirlhstype = this.m_emitter.registerResolvedTypeReference(fsig.params[i].type as ResolvedType);
                    const mirrhstype = this.m_emitter.registerResolvedTypeReference(cltype);
                    this.m_emitter.emitBinKeyEq(sinfo, mirlhstype, mirlhstype, cargs[argidx], mirrhstype, mirrhstype, lcreg, ichkreg);
                    this.m_emitter.emitAssertCheck(sinfo, "Failed to match literal tag on dynamic operator invoke", ichkreg);
                }
            }

            const opkey = this.m_emitter.registerNamespaceOperatorCall(opdecl.ns, opdecl.name, opdecl, sigkeys, pcodes, cinfo);
            const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, refs);
            this.m_emitter.emitInvokeFixedFunction(sinfo, opkey, cargs, undefined, refinfo, trgt);
        }
        else {
            let cargs: {arglayouttype: MIRType, argflowtype: MIRType, arg: MIRArgument}[] = [];
            for (let i = 0; i < fsig.params.length; ++i) {
                if(fsig.params[i] instanceof ResolvedFunctionType) {
                    continue;
                }

                const argidx = cargs.length;
                if(opdecl.invoke.params[i].refKind !== undefined) {
                    this.raiseErrorIf(sinfo, !argtypes[argidx].layout.isSameType(opdecl.invoke.params[i].type as ResolvedType));
                }
                cargs.push({ arglayouttype: this.m_emitter.registerResolvedTypeReference(fsig.params[argidx].type as ResolvedType), argflowtype: this.m_emitter.registerResolvedTypeReference(argtypes[argidx].flowtype), arg: this.emitInlineConvertIfNeeded(sinfo, args[argidx], argtypes[argidx], fsig.params[argidx].type as ResolvedType) });
            }

            const opkey = this.m_emitter.registerVirtualNamespaceOperatorCall(opdecl.ns, opdecl.name, pcodes, cinfo);
            const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, refs);
            this.m_emitter.emitInvokeVirtualOperator(sinfo, opkey, cargs, refinfo, trgt);
        }

        return this.updateEnvForOutParams(env.setUniformResultExpression(fsig.resultType), refs);
    }

    private checkStaticOperatorInvoke(sinfo: SourceInfo, env: TypeEnvironment, oodecl: OOPTypeDecl, oobinds: Map<string, ResolvedType>, opdecl: StaticOperatorDecl, args: MIRArgument[], argtypes: ValueType[], refs: ["ref" | "out" | "out?", MIRRegisterArgument, ResolvedType][], pcodes: PCode[], cinfo: [string, ResolvedType][], recursive: RecursiveAnnotation, trgt: MIRRegisterArgument, refok: boolean): TypeEnvironment[] {
        const ootype = this.resolveOOTypeFromDecls(oodecl, oobinds)
        const mirootype = this.m_emitter.registerResolvedTypeReference(ootype);
        const fsig = this.m_assembly.normalizeTypeFunction(opdecl.invoke.generateSig(), oobinds) as ResolvedFunctionType;
        this.checkRecursion(sinfo, fsig, pcodes, recursive);

        //if it is a static operator or it has a unique dynamic resolution based on the types
        if (!opdecl.isDynamic || !OOPTypeDecl.attributeSetContains("abstract", opdecl.invoke.attributes)) {
            let cargs: MIRArgument[] = [];
            let sigkeys: string[] = [];
            for (let i = 0; i < fsig.params.length; ++i) {
                if(fsig.params[i] instanceof ResolvedFunctionType) {
                    continue;
                }

                const argidx = cargs.length;
                if(fsig.params[i].refKind !== undefined) {
                    this.raiseErrorIf(sinfo, !refok, "ref argument not supported in this call position");
                    this.raiseErrorIf(sinfo, !argtypes[argidx].layout.isSameType(fsig.params[i].type as ResolvedType));
                }
                cargs.push(this.emitInlineConvertIfNeeded(sinfo, args[argidx], argtypes[argidx], fsig.params[i].type as ResolvedType));

                if(opdecl.invoke.params[i].litexp === undefined) {
                    sigkeys.push(this.m_emitter.registerResolvedTypeReference(fsig.params[i].type as ResolvedType).trkey);
                }
                else {
                    const lev = (opdecl.invoke.params[i].litexp as LiteralExpressionValue);
                    const cexp = this.m_assembly.reduceLiteralValueToCanonicalForm(lev.exp, env.terms, fsig.params[i].type as ResolvedType);
                    this.raiseErrorIf(sinfo, cexp === undefined, "Invalid literal argument");
                    
                    const [clexp, cltype, cltag] = cexp as [Expression, ResolvedType, string, boolean | number | undefined];
                    sigkeys.push(cltag)
                    
                    const lcreg = this.m_emitter.generateTmpRegister();    
                    this.checkExpression(env, clexp, lcreg, undefined);

                    //Should have same error if we fail to find suitable dynamic dispatch -- this is just a nice optimization
                    const ichkreg = this.m_emitter.generateTmpRegister();
                    const mirlhstype = this.m_emitter.registerResolvedTypeReference(fsig.params[i].type as ResolvedType);
                    const mirrhstype = this.m_emitter.registerResolvedTypeReference(cltype);
                    this.m_emitter.emitBinKeyEq(sinfo, mirlhstype, mirlhstype, cargs[argidx], mirrhstype, mirrhstype, lcreg, ichkreg);
                    this.m_emitter.emitAssertCheck(sinfo, "Failed to match literal tag on dynamic operator invoke", ichkreg);
                }
            }

            const opkey = this.m_emitter.registerStaticOperatorCall([mirootype, oodecl, oobinds], opdecl.name, opdecl, sigkeys, oobinds, pcodes, cinfo);
            const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, refs);
            this.m_emitter.emitInvokeFixedFunction(sinfo, opkey, cargs, "[IGNORE]", refinfo, trgt);
        }
        else {
            let cargs: {arglayouttype: MIRType, argflowtype: MIRType, arg: MIRArgument}[] = [];
            for (let i = 0; i < fsig.params.length; ++i) {
                if(fsig.params[i] instanceof ResolvedFunctionType) {
                    continue;
                }

                const argidx = cargs.length;
                if(opdecl.invoke.params[i].refKind !== undefined) {
                    this.raiseErrorIf(sinfo, !argtypes[argidx].layout.isSameType(opdecl.invoke.params[i].type as ResolvedType));
                }
                cargs.push({ arglayouttype: this.m_emitter.registerResolvedTypeReference(fsig.params[argidx].type as ResolvedType), argflowtype: this.m_emitter.registerResolvedTypeReference(argtypes[argidx].flowtype), arg: this.emitInlineConvertIfNeeded(sinfo, args[argidx], argtypes[argidx], fsig.params[argidx].type as ResolvedType) });
            }

            const opkey = this.m_emitter.registerVirtualStaticOperatorCall([mirootype, oodecl, oobinds], opdecl.name, oobinds, pcodes, cinfo);
            const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, refs);
            this.m_emitter.emitInvokeVirtualOperator(sinfo, opkey, cargs,  refinfo, trgt);
        }

        return this.updateEnvForOutParams(env.setUniformResultExpression(fsig.resultType), refs);
    }

    private checkCallNamespaceFunctionOrOperatorExpression(env: TypeEnvironment, exp: CallNamespaceFunctionOrOperatorExpression, trgt: MIRRegisterArgument, refok: boolean): TypeEnvironment[] {
        this.raiseErrorIf(exp.sinfo, !this.m_assembly.hasNamespace(exp.ns), `Namespace '${exp.ns}' is not defined`);
        const nsdecl = this.m_assembly.getNamespace(exp.ns);

        if (nsdecl.operators.has(exp.name)) {
            const opsintro = (nsdecl.operators.get(exp.name) as NamespaceOperatorDecl[]).find((nso) => nso.doesKindTagMatch(exp.opkind) && OOPTypeDecl.attributeSetContains("abstract", nso.invoke.attributes));
            const opdecls = (nsdecl.operators.get(exp.name) as NamespaceOperatorDecl[]).filter((nso) => nso.doesKindTagMatch(exp.opkind) && !OOPTypeDecl.attributeSetContains("abstract", nso.invoke.attributes));
            this.raiseErrorIf(exp.sinfo, opdecls.length === 0, "Operator must have at least one decl");

            const pnames = (opsintro as NamespaceOperatorDecl).invoke.params.map((p) => p.name);
            const hasrest = (opsintro as NamespaceOperatorDecl).invoke.optRestType !== undefined;

            //No terms to be bound on operator call

            const eargs = this.checkArgumentsEvaluationWOperator(exp.sinfo, env, env.terms, exp.args, refok);
            const rargs = this.checkArgumentsWOperator(exp.sinfo, env, pnames, hasrest, eargs);

            const isigs = opdecls.map((opd) => this.m_assembly.normalizeTypeFunction(opd.invoke.generateSig(), new Map<string, ResolvedType>()) as ResolvedFunctionType);
            const opidx = this.m_assembly.tryGetUniqueStaticOperatorResolve(rargs.types.map((vt) => vt.flowtype), isigs);

            this.raiseErrorIf(exp.sinfo, opidx === -1 || (opsintro !== undefined && opsintro.isDynamic), "Cannot resolve operator");
            const opdecl = opidx !== -1 ? opdecls[opidx] : opsintro as NamespaceOperatorDecl;
            
            return this.checkNamespaceOperatorInvoke(exp.sinfo, env, opdecl, rargs.args, rargs.types, rargs.refs, rargs.pcodes, rargs.cinfo, exp.rec, trgt, refok);
        } 
        else {
            this.raiseErrorIf(exp.sinfo, !nsdecl.functions.has(exp.name), `Function named '${exp.name}' is not defined`);
            const fdecl = nsdecl.functions.get(exp.name) as NamespaceFunctionDecl;

            const [fsig, callbinds, eargs] = this.inferAndCheckArguments(exp.sinfo, env, exp.args, fdecl.invoke, exp.terms.targs, new Map<string, ResolvedType>(), env.terms, undefined, refok);
            this.checkTemplateTypes(exp.sinfo, fdecl.invoke.terms, callbinds, fdecl.invoke.termRestrictions);

            const rargs = this.checkArgumentsSignature(exp.sinfo, env, exp.name, fsig, eargs);
            this.checkRecursion(exp.sinfo, fsig, rargs.pcodes, exp.rec);

            const ckey = this.m_emitter.registerFunctionCall(exp.ns, exp.name, fdecl, callbinds, rargs.pcodes, rargs.cinfo);
            const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
            this.m_emitter.emitInvokeFixedFunction(exp.sinfo, ckey, rargs.args, rargs.fflag, refinfo, trgt);
    
            return this.updateEnvForOutParams(env.setUniformResultExpression(fsig.resultType), rargs.refs);
        }
    }

    private checkCallStaticFunctionOrOperatorExpression(env: TypeEnvironment, exp: CallStaticFunctionOrOperatorExpression, trgt: MIRRegisterArgument, refok: boolean): TypeEnvironment[] {
        const fromtype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.ttype, env.terms);
        const fdecltry = this.m_assembly.tryGetFunctionUniqueDeclFromType(fromtype, exp.name);
        const opdecltry = this.m_assembly.tryGetOperatorUniqueDeclFromType(fromtype, exp.name);

        this.raiseErrorIf(exp.sinfo, (fdecltry === undefined && opdecltry === undefined), `Static function/operator not defined for type '${fromtype.idStr}'`);
        this.raiseErrorIf(exp.sinfo, (fdecltry !== undefined && opdecltry !== undefined), `Static function/operator multiply defined for type '${fromtype.idStr}'`);

        if(fdecltry !== undefined && fdecltry.contiainingType.ns === "NSCore" && fdecltry.contiainingType.name === "KeyType" && (exp.name === "less" || exp.name === "equal")) {
            const ktype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.terms.targs[0], env.terms);
            this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(ktype, this.m_assembly.getSpecialKeyTypeConceptType()) || !ktype.isGroundedType(), "Invalid argument");

            const lhsexp = exp.args.argList[0].value;
            const lhsreg = this.m_emitter.generateTmpRegister();
            const tlhs = this.checkExpression(env, lhsexp, lhsreg, undefined).getExpressionResult().valtype;

            this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(tlhs.flowtype, ktype), "Invalid argument");
            this.raiseErrorIf(exp.sinfo, !tlhs.flowtype.isGroundedType(), "Invalid argument");

            const rhsexp = exp.args.argList[1].value;
            const rhsreg = this.m_emitter.generateTmpRegister();
            const trhs = this.checkExpression(env, rhsexp, rhsreg, undefined).getExpressionResult().valtype;

            this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(trhs.flowtype, ktype), "Invalid argument");
            this.raiseErrorIf(exp.sinfo, !trhs.flowtype.isGroundedType(), "Invalid argument");

            if (exp.name === "equal") {
                this.m_emitter.emitBinKeyEq(exp.sinfo, this.m_emitter.registerResolvedTypeReference(tlhs.layout), this.m_emitter.registerResolvedTypeReference(tlhs.flowtype), lhsreg, this.m_emitter.registerResolvedTypeReference(trhs.layout), this.m_emitter.registerResolvedTypeReference(trhs.flowtype), rhsreg, trgt);
            }
            else {
                this.m_emitter.emitBinKeyLess(exp.sinfo, this.m_emitter.registerResolvedTypeReference(tlhs.layout), this.m_emitter.registerResolvedTypeReference(tlhs.flowtype), lhsreg, this.m_emitter.registerResolvedTypeReference(trhs.layout), this.m_emitter.registerResolvedTypeReference(trhs.flowtype), rhsreg, trgt);
            }

            return [env.setUniformResultExpression(this.m_assembly.getSpecialBoolType())];
        }
        else if(fdecltry !== undefined && fdecltry.contiainingType.ns === "NSCore" && fromtype.idStr === "Tuple" && exp.name === "append") {
            let eargs: [ResolvedType, ResolvedType, MIRRegisterArgument][] = [];
            let ttypes: ResolvedTupleAtomTypeEntry[] = [];
            let isvalue: boolean[] = [];

            for (let i = 0; i < exp.args.argList.length; ++i) {
                const arg = exp.args.argList[i];
                this.raiseErrorIf(arg.value.sinfo, arg.ref !== undefined, "Cannot use ref params in this call position");
                this.raiseErrorIf(arg.value.sinfo, this.isPCodeTypedExpression(arg.value, env), "Cannot use function in this call position");

                this.raiseErrorIf(arg.value.sinfo, !(arg instanceof PositionalArgument), "Only positional arguments allowed in Tuple::append");
                this.raiseErrorIf(arg.value.sinfo, (arg as PositionalArgument).isSpread, "Expando parameters are not allowed in Tuple::append");

                const treg = this.m_emitter.generateTmpRegister();
                const earg = this.checkExpression(env, arg.value, treg, undefined).getExpressionResult().valtype;

                this.raiseErrorIf(exp.sinfo, earg.flowtype.isUniqueTupleTargetType(), "Can only join arguments of (known) Tuple types");
                eargs.push([earg.layout, earg.flowtype, treg]);
                ttypes = [...ttypes, ...earg.flowtype.getUniqueTupleTargetType().types.map((tt) => new ResolvedTupleAtomTypeEntry(tt.type, false))];
                isvalue.push(earg.flowtype.getUniqueTupleTargetType().isvalue);
            }

            const vcons = isvalue.every((vv) => vv);
            this.raiseErrorIf(exp.sinfo, isvalue.some((vv) => vv !== vcons), "Mix of value and reference tuple types is not allowed");

            const rtupletype = ResolvedType.createSingle(ResolvedTupleAtomType.create(vcons, ttypes));
            const argstypes = eargs.map((arg) => {
                return { layout: this.m_emitter.registerResolvedTypeReference(arg[0]), flow: this.m_emitter.registerResolvedTypeReference(arg[1]) };
            });
            this.m_emitter.emitStructuredAppendTuple(exp.sinfo, this.m_emitter.registerResolvedTypeReference(rtupletype), eargs.map((ee) => ee[2]), argstypes, trgt);

            return [env.setUniformResultExpression(rtupletype)];
        }
        else if(fdecltry !== undefined && fdecltry.contiainingType.ns === "NSCore" && fromtype.idStr === "Record" && exp.name === "join") {
            let eargs: [ResolvedType, ResolvedType, MIRRegisterArgument][] = [];
            let ttypes: ResolvedRecordAtomTypeEntry[] = [];
            let isvalue: boolean[] = [];
            let names = new Set<string>();

            for (let i = 0; i < exp.args.argList.length; ++i) {
                const arg = exp.args.argList[i];
                this.raiseErrorIf(arg.value.sinfo, arg.ref !== undefined, "Cannot use ref params in this call position");
                this.raiseErrorIf(arg.value.sinfo, this.isPCodeTypedExpression(arg.value, env), "Cannot use function in this call position");

                this.raiseErrorIf(arg.value.sinfo, !(arg instanceof PositionalArgument), "Only positional arguments allowed in Record::join");
                this.raiseErrorIf(arg.value.sinfo, (arg as PositionalArgument).isSpread, "Expando parameters are not allowed in Record::join");

                const treg = this.m_emitter.generateTmpRegister();
                const earg = this.checkExpression(env, arg.value, treg, undefined).getExpressionResult().valtype;

                this.raiseErrorIf(exp.sinfo, earg.flowtype.isUniqueRecordTargetType(), "Can only join arguments of (known) Record types");
                eargs.push([earg.layout, earg.flowtype, treg]);
                
                const allnamegroups = earg.flowtype.options.map((opt) => (opt as ResolvedRecordAtomType).entries.map((entry) => entry.name));
                const allnames = [...new Set<string>(([] as string[]).concat(...allnamegroups))].sort();

                const allvals = earg.flowtype.options.every((opt) => (opt as ResolvedRecordAtomType).isvalue);
                const allrefs = earg.flowtype.options.every((opt) => !(opt as ResolvedRecordAtomType).isvalue);

                this.raiseErrorIf(exp.sinfo, allnames.some((pname) => names.has(pname)), "Cannot have (possibly) duplicate properties in join");
                this.raiseErrorIf(exp.sinfo, !allvals && !allrefs, "Cannot have mix of value and reference records");

                const ecc = allnames.map((pname) => {
                    names.add(pname);

                    const isopt = earg.flowtype.options.some((opt) => {
                        const entry = (opt as ResolvedRecordAtomType).entries.find((ee) => ee.name === pname);
                        return entry === undefined || entry.isOptional;
                    });

                    const rtypes = earg.flowtype.options
                        .filter((opt) => (opt as ResolvedRecordAtomType).entries.find((ee) => ee.name === pname) !== undefined)
                        .map((opt) => ((opt as ResolvedRecordAtomType).entries.find((ee) => ee.name === pname) as ResolvedRecordAtomTypeEntry).type);

                    return new ResolvedRecordAtomTypeEntry(pname, this.m_assembly.typeUpperBound(rtypes), isopt);
                });

                ttypes.push(...ecc);
                isvalue.push(allvals);
            }

            const vcons = isvalue.every((vv) => vv);
            this.raiseErrorIf(exp.sinfo, isvalue.some((vv) => vv !== vcons), "Mix of value and reference record types is not allowed");

            const rrecordtype = ResolvedType.createSingle(ResolvedRecordAtomType.create(vcons, ttypes));
            const argstypes = eargs.map((arg) => {
                return { layout: this.m_emitter.registerResolvedTypeReference(arg[0]), flow: this.m_emitter.registerResolvedTypeReference(arg[1]) };
            });
            this.m_emitter.emitStructuredJoinRecord(exp.sinfo, this.m_emitter.registerResolvedTypeReference(rrecordtype), eargs.map((arg) => arg[2]), argstypes, trgt);

            return [env.setUniformResultExpression(rrecordtype)];
        }
        else {
            if (opdecltry !== undefined) {
                const oodecl = (opdecltry as OOMemberLookupInfo<StaticOperatorDecl[]>).contiainingType;
                const oobinds = (opdecltry as OOMemberLookupInfo<StaticOperatorDecl[]>).binds;

                const opsintro = (opdecltry as OOMemberLookupInfo<StaticOperatorDecl[]>).decl.find((nso) => nso.doesKindTagMatch(exp.opkind) && OOPTypeDecl.attributeSetContains("abstract", nso.invoke.attributes));
                const opdecls = (opdecltry as OOMemberLookupInfo<StaticOperatorDecl[]>).decl.filter((nso) => nso.doesKindTagMatch(exp.opkind) && !OOPTypeDecl.attributeSetContains("abstract", nso.invoke.attributes));
                this.raiseErrorIf(exp.sinfo, opdecls.length === 0, "Operator must have at least one decl");

                const pnames = (opsintro as StaticOperatorDecl).invoke.params.map((p) => p.name);
                const hasrest = (opsintro as StaticOperatorDecl).invoke.optRestType !== undefined;

                //No terms to be bound on operator call

                const eargs = this.checkArgumentsEvaluationWOperator(exp.sinfo, env, env.terms, exp.args, refok);
                const rargs = this.checkArgumentsWOperator(exp.sinfo, env, pnames, hasrest, eargs);

                const isigs = opdecls.map((opd) => this.m_assembly.normalizeTypeFunction(opd.invoke.generateSig(), new Map<string, ResolvedType>()) as ResolvedFunctionType);
                const opidx = this.m_assembly.tryGetUniqueStaticOperatorResolve(rargs.types.map((vt) => vt.flowtype), isigs);

                this.raiseErrorIf(exp.sinfo, opidx !== -1 || (opsintro !== undefined && opsintro.isDynamic), "Cannot resolve operator");
                const opdecl = opidx !== -1 ? opdecls[opidx] : opsintro as StaticOperatorDecl;
            
                return this.checkStaticOperatorInvoke(exp.sinfo, env, oodecl, oobinds, opdecl, rargs.args, rargs.types, rargs.refs, rargs.pcodes, rargs.cinfo, exp.rec, trgt, refok); 
            }
            else {
                const fdecl = fdecltry as OOMemberLookupInfo<StaticFunctionDecl>;

                const [fsig, callbinds, eargs] = this.inferAndCheckArguments(exp.sinfo, env, exp.args, fdecl.decl.invoke, exp.terms.targs, fdecl.binds, env.terms, undefined, refok);
                this.checkTemplateTypes(exp.sinfo, fdecl.decl.invoke.terms, callbinds, fdecl.decl.invoke.termRestrictions);

                const rargs = this.checkArgumentsSignature(exp.sinfo, env, exp.name, fsig, eargs);
                this.checkRecursion(exp.sinfo, fsig, rargs.pcodes, exp.rec);

                const ootype = this.m_emitter.registerResolvedTypeReference(this.resolveOOTypeFromDecls(fdecl.contiainingType, fdecl.binds));
                const ckey = this.m_emitter.registerStaticCall([ootype, fdecl.contiainingType, fdecl.binds], fdecl.decl, exp.name, callbinds, rargs.pcodes, rargs.cinfo);
                const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
                this.m_emitter.emitInvokeFixedFunction(exp.sinfo, ckey, rargs.args, rargs.fflag, refinfo, trgt);

                return this.updateEnvForOutParams(env.setUniformResultExpression(fsig.resultType), rargs.refs);
            }
        }
    }

    private checkPCodeDirectInvokeExpression(env: TypeEnvironment, exp: PCodeDirectInvokeExpression, trgt: MIRRegisterArgument, refok: boolean): TypeEnvironment[] {
        const pcode = exp.pc;
        const captured = exp.captured;
        refok = refok && exp.isrefok;

        const callargs = [...(exp.args.map((arg) => new PositionalArgument(undefined, false, arg)))];
        const eargs = this.checkArgumentsEvaluationWSig(exp.sinfo, env, pcode.ftype, new Map<string, ResolvedType>(), new Arguments(callargs), undefined, refok);

        const margs = this.checkArgumentsSignature(exp.sinfo, env, "pcode", pcode.ftype, eargs);
        const cargsext = captured.map((carg) => {
            const rreg = this.m_emitter.generateTmpRegister();
            this.checkAccessVariable(env, new AccessVariableExpression(exp.sinfo, carg), rreg);

            return rreg;
        });

        const refinfo = this.generateRefInfoForCallEmit((pcode as PCode).ftype, margs.refs);
        this.m_emitter.emitInvokeFixedFunction(exp.sinfo, MIRKeyGenerator.generatePCodeKey((pcode as PCode).code), [...margs.args, ...cargsext], undefined, refinfo, trgt);   

        return this.updateEnvForOutParams(env.setUniformResultExpression(pcode.ftype.resultType), margs.refs);
    }

    private checkPCodeInvokeExpression(env: TypeEnvironment, exp: PCodeInvokeExpression, trgt: MIRRegisterArgument, refok: boolean): TypeEnvironment[] {
        const pco = env.lookupPCode(exp.pcode);
        this.raiseErrorIf(exp.sinfo, pco === undefined, "Code name not defined");
        const pcode = (pco as { pcode: PCode, captured: string[] }).pcode;
        const captured = (pco as { pcode: PCode, captured: string[] }).captured;

        const callargs = [...exp.args.argList];
        const eargs = this.checkArgumentsEvaluationWSig(exp.sinfo, env, pcode.ftype, new Map<string, ResolvedType>(), new Arguments(callargs), undefined, refok);

        const margs = this.checkArgumentsSignature(exp.sinfo, env, "pcode", pcode.ftype, eargs);
        const cargsext = captured.map((carg) => {
            const rreg = this.m_emitter.generateTmpRegister();
            this.checkAccessVariable(env, new AccessVariableExpression(exp.sinfo, carg), rreg);

            return rreg;
        });

        this.checkRecursion(exp.sinfo, pcode.ftype, margs.pcodes, exp.rec);

        const refinfo = this.generateRefInfoForCallEmit((pcode as PCode).ftype, margs.refs);
        this.m_emitter.emitInvokeFixedFunction(exp.sinfo, MIRKeyGenerator.generatePCodeKey((pcode as PCode).code), [...margs.args, ...cargsext], undefined, refinfo, trgt);   

        return this.updateEnvForOutParams(env.setUniformResultExpression(pcode.ftype.resultType), margs.refs);
    }

    private checkOfTypeConvertExpression(env: TypeEnvironment, exp: OfTypeConvertExpression, trgt: MIRRegisterArgument, refok: boolean): TypeEnvironment {
        const treg = this.m_emitter.generateTmpRegister();
        const oftype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.oftype, env.terms);
        const fenv = this.checkExpression(env, exp.arg, treg, oftype, { refok: refok, orok: false });

        const tsplits = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, oftype, [env]);
        assert(tsplits.tenvs.length <= 1);

        if (tsplits.tenvs.length === 0) {
            this.m_emitter.emitAbort(exp.sinfo, "Never of required type");
            return env.setAbort();
        }
        else {
            if (tsplits.fenvs.length !== 0) {
                const creg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitTypeOf(exp.sinfo, creg, this.m_emitter.registerResolvedTypeReference(oftype), treg, this.m_emitter.registerResolvedTypeReference(fenv.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(fenv.getExpressionResult().valtype.flowtype), undefined);
                this.m_emitter.emitAssertCheck(exp.sinfo, "Failed type conversion", creg);
            }

            this.m_emitter.emitRegisterStore(exp.sinfo, treg, this.emitInlineConvertIfNeeded(exp.sinfo, trgt, fenv.getExpressionResult().valtype, oftype), this.m_emitter.registerResolvedTypeReference(oftype), undefined);
            return tsplits.tenvs[0];
        }
    }

    private checkAccessFromIndex(env: TypeEnvironment, op: PostfixAccessFromIndex, arg: MIRRegisterArgument, trgt: MIRRegisterArgument): TypeEnvironment {
        const texp = env.getExpressionResult().valtype;

        this.raiseErrorIf(op.sinfo, !texp.flowtype.isTupleTargetType(), "Base of index expression must be of Tuple type");
        this.raiseErrorIf(op.sinfo, op.index < 0, "Index cannot be negative");
        this.raiseErrorIf(op.sinfo, this.getInfoForHasIndex(op.sinfo, texp.flowtype, op.index) !== "yes", "Index may not be defined for tuple");

        const idxtype = this.getInfoForLoadFromSafeIndex(op.sinfo, texp.flowtype, op.index);
        this.m_emitter.emitLoadTupleIndex(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.index, !texp.flowtype.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(idxtype), trgt);

        return env.setUniformResultExpression(idxtype);
    }

    private checkProjectFromIndecies(env: TypeEnvironment, op: PostfixProjectFromIndecies, arg: MIRRegisterArgument, trgt: MIRRegisterArgument, infertype: ResolvedType | undefined): TypeEnvironment {
        const texp = env.getExpressionResult().valtype;

        this.raiseErrorIf(op.sinfo, !texp.flowtype.isTupleTargetType(), "Base of index expression must be of Tuple type");
        this.raiseErrorIf(op.sinfo, op.indecies.some((idx) => idx.index < 0), "Index cannot be negative");
        this.raiseErrorIf(op.sinfo, op.indecies.some((idx) => this.getInfoForHasIndex(op.sinfo, texp.flowtype, idx.index) !== "yes"), "Index may not be defined for all tuples");

        //
        //TODO: I don't think I check the consistency of the tuple type, the infer type, and the reqtype bits...
        //      Should also look at other project (and related ops).
        //

        let itype: ResolvedType[] | undefined = undefined;
        if (infertype !== undefined) {
            if (op.isEphemeralListResult) {
                const eitype = infertype.tryGetInferrableValueListConstructorType();
                itype = eitype !== undefined ? eitype.types : undefined;
            }
            else {
                const eitype = infertype.tryGetInferrableTupleConstructorType(op.isValue);
                itype = eitype !== undefined ? eitype.types.map((entry) => entry.type) : undefined;
            }

            this.raiseErrorIf(op.sinfo, itype !== undefined && itype.length !== op.indecies.length, "Mismatch between number of indecies loaded and number expected by inferred type");
        }

        let etypes: ResolvedType[] = [];
        for (let i = 0; i < op.indecies.length; ++i) {
            const reqtype = op.indecies[i].reqtype !== undefined ? this.resolveAndEnsureTypeOnly(op.sinfo, op.indecies[i].reqtype as TypeSignature, env.terms) : undefined;
            let inferidx: ResolvedType | undefined = undefined
            if (reqtype !== undefined || itype !== undefined) {
                inferidx = reqtype !== undefined ? reqtype : (itype as ResolvedType[])[i];
            }

            const ttype = this.getInfoForLoadFromSafeIndex(op.sinfo, texp.flowtype, op.indecies[i].index);
            etypes.push(inferidx || ttype);
        }

        const rephemeralatom = ResolvedEphemeralListType.create(etypes);
        const rephemeral = ResolvedType.createSingle(rephemeralatom);

        const rindecies = op.indecies.map((idv) => idv.index);

        const prjtemp = this.m_emitter.generateTmpRegister();
        this.m_emitter.emitTupleProjectToEphemeral(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), rindecies, !texp.flowtype.isUniqueTupleTargetType(), rephemeralatom, trgt);
       
        if (op.isEphemeralListResult) {
            this.m_emitter.emitRegisterStore(op.sinfo, prjtemp, trgt, this.m_emitter.registerResolvedTypeReference(rephemeral), undefined);
            return env.setUniformResultExpression(rephemeral);
        }
        else {
            const tupleatom = ResolvedTupleAtomType.create(op.isValue, etypes.map((tt) => new ResolvedTupleAtomTypeEntry(tt, false)));
            const rtuple = ResolvedType.createSingle(tupleatom);

            const tupkey = this.m_emitter.registerResolvedTypeReference(rtuple);
            this.m_emitter.emitConstructorTupleFromEphemeralList(op.sinfo, tupkey, prjtemp, this.m_emitter.registerResolvedTypeReference(rephemeral), trgt);
    
            return env.setUniformResultExpression(rtuple);
        }
    }

    private checkAccessFromName(env: TypeEnvironment, op: PostfixAccessFromName, arg: MIRRegisterArgument, trgt: MIRRegisterArgument): TypeEnvironment {
        const texp = env.getExpressionResult().valtype;

        if (texp.flowtype.isRecordTargetType()) {
            this.raiseErrorIf(op.sinfo, !texp.flowtype.isRecordTargetType(), "Base of property access expression must be of Record type");
            this.raiseErrorIf(op.sinfo, this.getInfoForHasProperty(op.sinfo, texp.flowtype, op.name) !== "yes", "Property may not be defined for record");

            const rtype = this.getInfoForLoadFromSafeProperty(op.sinfo, texp.flowtype, op.name);
            this.m_emitter.emitLoadProperty(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.name, !texp.flowtype.isUniqueRecordTargetType(), this.m_emitter.registerResolvedTypeReference(rtype), trgt);

            return env.setUniformResultExpression(rtype);
        }
        else {
            const tryfinfo = this.m_assembly.tryGetFieldUniqueDeclFromType(texp.flowtype, op.name);
            this.raiseErrorIf(op.sinfo, tryfinfo === undefined, "Field name is not defined (or is multiply) defined");

            const finfo = tryfinfo as OOMemberLookupInfo<MemberFieldDecl>;
            const ftype = this.resolveAndEnsureTypeOnly(op.sinfo, finfo.decl.declaredType, finfo.binds);
            
            const fkey = MIRKeyGenerator.generateFieldKey(this.resolveOOTypeFromDecls(finfo.contiainingType, finfo.binds), op.name);
            this.m_emitter.emitLoadField(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), fkey, !texp.flowtype.isUniqueCallTargetType(), this.m_emitter.registerResolvedTypeReference(ftype), trgt);
            
            return env.setUniformResultExpression(ftype);
        }
    }

    private checkProjectFromNames(env: TypeEnvironment, op: PostfixProjectFromNames, arg: MIRRegisterArgument, trgt: MIRRegisterArgument, infertype: ResolvedType | undefined): TypeEnvironment {
        const texp = env.getExpressionResult().valtype;

        let itype: ResolvedType[] | undefined = undefined;
        if (infertype !== undefined) {
            if (op.isEphemeralListResult) {
                const eitype = infertype.tryGetInferrableValueListConstructorType();
                itype = eitype !== undefined ? eitype.types : undefined;
            }
            else {
                const eitype = infertype.tryGetInferrableRecordConstructorType(op.isValue);
                this.raiseErrorIf(op.sinfo, eitype !== undefined && op.names.some((ln) => this.getInfoForHasProperty(op.sinfo, ResolvedType.createSingle(eitype), ln.name) !== "yes"), "Property may not be defined for all records");

                itype = eitype !== undefined ? op.names.map((nn) => (eitype.entries.find((entry) => entry.name === nn.name) as ResolvedRecordAtomTypeEntry).type) : undefined;
            }
        }
        this.raiseErrorIf(op.sinfo, itype !== undefined && itype.length !== op.names.length, "Mismatch between number of properties loaded and number expected by inferred type");

        if (texp.flowtype.isRecordTargetType()) {
            this.raiseErrorIf(op.sinfo, op.names.some((ln) => this.getInfoForHasProperty(op.sinfo, texp.flowtype, ln.name) !== "yes"), "Property may not be defined for all records");

            let etypes: [string, ResolvedType][] = [];
            for (let i = 0; i < op.names.length; ++i) {
                const reqtype = op.names[i].reqtype !== undefined ? this.resolveAndEnsureTypeOnly(op.sinfo, op.names[i].reqtype as TypeSignature, env.terms) : undefined;
                let inferidx: ResolvedType | undefined = undefined
                if (reqtype !== undefined || itype !== undefined) {
                    inferidx = reqtype !== undefined ? reqtype : (itype as ResolvedType[])[i];
                }

                const ttype = this.getInfoForLoadFromSafeProperty(op.sinfo, texp.flowtype, op.names[i].name);
                etypes.push([op.names[i].name, inferidx || ttype]);
            }

            const rephemeralatom = ResolvedEphemeralListType.create(etypes.map((ee) => ee[1]));
            const rephemeral = ResolvedType.createSingle(rephemeralatom);

            const pindecies = op.names.map((ndv) => ndv.name);

            const prjtemp = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitRecordProjectToEphemeral(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), pindecies, !texp.flowtype.isUniqueRecordTargetType(), rephemeralatom, trgt);

            if (op.isEphemeralListResult) {
                this.m_emitter.emitRegisterStore(op.sinfo, prjtemp, trgt, this.m_emitter.registerResolvedTypeReference(rephemeral), undefined);
                return env.setUniformResultExpression(rephemeral);
            }
            else {
                const recordatom = ResolvedRecordAtomType.create(op.isValue, etypes.map((tt) => new ResolvedRecordAtomTypeEntry(tt[0], tt[1], false)));
                const rrecord = ResolvedType.createSingle(recordatom);

                const reckey = this.m_emitter.registerResolvedTypeReference(rrecord);
                this.m_emitter.emitConstructorRecordFromEphemeralList(op.sinfo, reckey, prjtemp, this.m_emitter.registerResolvedTypeReference(rephemeral), pindecies, trgt);

                return env.setUniformResultExpression(rrecord);
            }

        }
        else {
            const rfields = op.names.map((idv) => {
                const ff = this.m_assembly.tryGetFieldUniqueDeclFromType(texp.flowtype, idv.name);
                this.raiseErrorIf(op.sinfo, ff === undefined, `Could not resolve field name "${idv}"`);

                return ff as OOMemberLookupInfo<MemberFieldDecl>;
            });

            const rephemeralatom = ResolvedEphemeralListType.create(rfields.map((ee) => this.resolveAndEnsureTypeOnly(op.sinfo, ee.decl.declaredType, ee.binds)));
            const rephemeral = ResolvedType.createSingle(rephemeralatom);

            const pindecies = rfields.map((ndv) => MIRKeyGenerator.generateFieldKey(this.resolveOOTypeFromDecls(ndv.contiainingType, ndv.binds), ndv.decl.name));

            const prjtemp = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitEntityProjectToEphemeral(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), pindecies, !texp.flowtype.isUniqueCallTargetType(), rephemeralatom, trgt);

            if (op.isEphemeralListResult) {
                this.m_emitter.emitRegisterStore(op.sinfo, prjtemp, trgt, this.m_emitter.registerResolvedTypeReference(rephemeral), undefined);
                return env.setUniformResultExpression(rephemeral);
            }
            else {
                const recordatom = ResolvedRecordAtomType.create(op.isValue, rfields.map((tt) => new ResolvedRecordAtomTypeEntry(tt.decl.name, this.resolveOOTypeFromDecls(tt.contiainingType, tt.binds), false)));
                const rrecord = ResolvedType.createSingle(recordatom);

                const reckey = this.m_emitter.registerResolvedTypeReference(rrecord);
                this.m_emitter.emitConstructorRecordFromEphemeralList(op.sinfo, reckey, prjtemp, this.m_emitter.registerResolvedTypeReference(rephemeral), rfields.map((tt) => tt.decl.name), trgt);

                return env.setUniformResultExpression(rrecord);
            }
        }
    }

    private checkModifyWithIndecies(env: TypeEnvironment, op: PostfixModifyWithIndecies, arg: MIRRegisterArgument, trgt: MIRRegisterArgument): TypeEnvironment {
        const texp = env.getExpressionResult().valtype;

        this.raiseErrorIf(op.sinfo, !texp.flowtype.isTupleTargetType());

        const maxupdl = texp.flowtype.getTupleTargetTypeIndexRange().req;
        const updates = op.updates.map<[number, ResolvedType, MIRArgument]>((update) => {
            this.raiseErrorIf(op.sinfo, update.index >= maxupdl, "Updates can only be applied to known indecies (i.e. cannot change the types of tuples)");

            const etreg = this.m_emitter.generateTmpRegister();
            const itype = this.getInfoForLoadFromSafeIndex(op.sinfo, texp.flowtype, update.index);

            let eev = this.checkDeclareSingleVariable(op.sinfo, env, `$${update.index}_#${op.sinfo.pos}`, true, itype, {etype: ValueType.createUniform(itype), etreg: etreg});
            if (op.isBinder) {
                eev = this.checkDeclareSingleVariable(op.sinfo, eev, `$this_#${op.sinfo.pos}`, true, texp.layout, {etype: texp, etreg: arg});
            }

            const utype = this.checkExpression(eev, update.value, etreg, itype).getExpressionResult().valtype;

            this.m_emitter.localLifetimeEnd(op.sinfo, `$${update.index}_#${op.sinfo.pos}`);
            if (op.isBinder) {
                this.m_emitter.localLifetimeEnd(op.sinfo, `$this_#${op.sinfo.pos}`);
            }

            return [update.index, itype, this.emitInlineConvertIfNeeded(op.sinfo, etreg, utype, itype)];
        });

        this.m_emitter.emitTupleUpdate(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), updates, !texp.flowtype.isUniqueTupleTargetType(), trgt);
        
        return env.setUniformResultExpression(texp.flowtype);
    }

    private checkModifyWithNames(env: TypeEnvironment, op: PostfixModifyWithNames, arg: MIRRegisterArgument, trgt: MIRRegisterArgument): TypeEnvironment {
        const texp = env.getExpressionResult().valtype;

        if (texp.flowtype.isRecordTargetType()) {
            const maxupdn = texp.flowtype.getRecordTargetTypePropertySets().req;
            const updates = op.updates.map<[string, ResolvedType, MIRArgument]>((update) => {
                this.raiseErrorIf(op.sinfo, !maxupdn.has(update.name), "Updates can only be applied to known properties (i.e. cannot change the types of records)");

                const etreg = this.m_emitter.generateTmpRegister();
                const itype = this.getInfoForLoadFromSafeProperty(op.sinfo, texp.flowtype, update.name);

                let eev = this.checkDeclareSingleVariable(op.sinfo, env, `$${update.name}_#${op.sinfo.pos}`, true, itype, { etype: ValueType.createUniform(itype), etreg: etreg });
                if (op.isBinder) {
                    eev = this.checkDeclareSingleVariable(op.sinfo, eev, `$this_#${op.sinfo.pos}`, true, texp.layout, { etype: texp, etreg: arg });
                }

                const utype = this.checkExpression(eev, update.value, etreg, itype).getExpressionResult().valtype;

                this.m_emitter.localLifetimeEnd(op.sinfo, `$${update.name}_#${op.sinfo.pos}`);
                if (op.isBinder) {
                    this.m_emitter.localLifetimeEnd(op.sinfo, `$this_#${op.sinfo.pos}`);
                }

                return [update.name, itype, this.emitInlineConvertIfNeeded(op.sinfo, etreg, utype, itype)];
            });

            this.m_emitter.emitRecordUpdate(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), updates, !texp.flowtype.isUniqueRecordTargetType(), trgt);

            return env.setUniformResultExpression(texp.flowtype);
        }
        else {
            const updates = op.updates.map<[OOMemberLookupInfo<MemberFieldDecl>, ResolvedType, MIRArgument]>((update) => {
                const etreg = this.m_emitter.generateTmpRegister();

                const tryfinfo = this.m_assembly.tryGetFieldUniqueDeclFromType(texp.flowtype, update.name);
                this.raiseErrorIf(op.sinfo, tryfinfo === undefined, "Field name is not defined (or is multiply) defined");

                const finfo = tryfinfo as OOMemberLookupInfo<MemberFieldDecl>;
                const ftype = this.resolveAndEnsureTypeOnly(op.sinfo, finfo.decl.declaredType, finfo.binds);

                let eev = this.checkDeclareSingleVariable(op.sinfo, env,`$${update.name}_#${op.sinfo.pos}`, true, ftype, {etype: ValueType.createUniform(ftype), etreg: etreg});
                if (op.isBinder) {
                    eev = this.checkDeclareSingleVariable(op.sinfo, eev,`$${update.name}_#${op.sinfo.pos}`, true, texp.layout, {etype: texp, etreg: arg});
                }

                const utype = this.checkExpression(eev, update.value, etreg, ftype).getExpressionResult().valtype;

                this.m_emitter.localLifetimeEnd(op.sinfo, `$${update.name}_#${op.sinfo.pos}`);
                if (op.isBinder) {
                    this.m_emitter.localLifetimeEnd(op.sinfo, `$this_#${op.sinfo.pos}`);
                }

                return [finfo, ftype, this.emitInlineConvertIfNeeded(op.sinfo, etreg, utype, ftype)];
            });

            const updateinfo = updates.map((upd) => {
                const fkey = MIRKeyGenerator.generateFieldKey(this.resolveOOTypeFromDecls(upd[0].contiainingType, upd[0].binds), upd[0].decl.name);
                return [fkey, upd[1], upd[2]] as [MIRFieldKey, ResolvedType, MIRArgument];
            });

            //
            //TODO: This is a tiny bit messy as the update calls the constructor which can call default initializers and invariant check code
            //      This is potentially recursive but it won't show up now -- do we want to add recursive annotations here or is there a better idea??
            //      Maybe require all default params and invariant checks be non-recursive? -- offhand I favor this option since I don't think you want these to be expensive (overly complex) anyway -- same with other default values (but not pre/post conds).
            //
            this.m_emitter.emitEntityUpdate(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), updateinfo, !texp.flowtype.isUniqueRecordTargetType(), trgt);

            return env.setUniformResultExpression(texp.flowtype);
        }
    }

    private checkPostfixIsMulti(env: TypeEnvironment, op: PostfixIs, arg: MIRRegisterArgument, trgt: MIRRegisterArgument): TypeEnvironment[] {
        const texp = env.getExpressionResult().valtype;
        const oftype = this.resolveAndEnsureTypeOnly(op.sinfo, op.istype, env.terms);

        this.m_emitter.emitTypeOf(op.sinfo, trgt, this.m_emitter.registerResolvedTypeReference(oftype), arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), undefined);
        
        const renvs = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, oftype, [env]);
        return [
            ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))), 
            ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
        ];
    }

    private checkPostfixIsMono(env: TypeEnvironment, op: PostfixIs, arg: MIRRegisterArgument, trgt: MIRRegisterArgument): TypeEnvironment {
        return TypeEnvironment.join(this.m_assembly, ...this.checkPostfixIsMulti(env, op, arg, trgt));
    }

    private checkPostfixAs(env: TypeEnvironment, op: PostfixAs, arg: MIRRegisterArgument, trgt: MIRRegisterArgument): TypeEnvironment {
        const texp = env.getExpressionResult().valtype;
        const astype = this.resolveAndEnsureTypeOnly(op.sinfo, op.astype, env.terms);

        const tsplits = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, astype, [env]);
        assert(tsplits.tenvs.length <= 1);

        if (tsplits.tenvs.length === 0) {
            this.m_emitter.emitAbort(op.sinfo, "Never of required type");
            return env.setAbort();
        }
        else {
            if (tsplits.fenvs.length !== 0) {
                const creg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitTypeOf(op.sinfo, creg, this.m_emitter.registerResolvedTypeReference(astype), arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), undefined);
                this.m_emitter.emitAssertCheck(op.sinfo, "Failed type conversion", creg);
            }

            this.m_emitter.emitRegisterStore(op.sinfo, this.emitInlineConvertIfNeeded(op.sinfo, arg, texp, astype), trgt, this.m_emitter.registerResolvedTypeReference(astype), undefined);
            return tsplits.tenvs[0];
        }
    }

    private checkPostfixHasIndexMulti(env: TypeEnvironment, op: PostfixHasIndex, arg: MIRRegisterArgument, trgt: MIRRegisterArgument): TypeEnvironment[] {
        const texp = env.getExpressionResult().valtype;
        this.raiseErrorIf(op.sinfo, !texp.flowtype.isTupleTargetType(), "Can only check for indecies on tuple types");

        const hpi = this.getInfoForHasIndex(op.sinfo, texp.flowtype, op.idx);
        if(hpi === "no") {
            this.m_emitter.emitLoadConstBool(op.sinfo, false, trgt);
            return [env.setUniformResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)];
        }
        else if(hpi === "yes") {
            this.m_emitter.emitLoadConstBool(op.sinfo, true, trgt);
            return [env.setUniformResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)];
        }
        else {
            assert(!texp.flowtype.isUniqueTupleTargetType(), "If this is unique then we should have been in one of the cases above");

            this.m_emitter.emitTupleHasIndex(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.idx, trgt);
            
            const renvs = TypeEnvironment.convertToHasIndexNotHasIndexFlowsOnResult(this.m_assembly, op.idx, [env]);
            return [
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
    }

    private checkPostfixHasIndexMono(env: TypeEnvironment, op: PostfixHasIndex, arg: MIRRegisterArgument, trgt: MIRRegisterArgument): TypeEnvironment {
        return TypeEnvironment.join(this.m_assembly, ...this.checkPostfixHasIndexMulti(env, op, arg, trgt));
    }

    private checkPostfixGetIndexOrNone(env: TypeEnvironment, op: PostfixGetIndexOrNone, arg: MIRRegisterArgument, trgt: MIRRegisterArgument): TypeEnvironment {
        const texp = env.getExpressionResult().valtype;
        this.raiseErrorIf(op.sinfo, !texp.flowtype.isTupleTargetType(), "Can only load indecies from tuple types");

        const hpi = this.getInfoForHasIndex(op.sinfo, texp.flowtype, op.idx);
        if(hpi === "no") {
            this.m_emitter.emitLoadConstNone(op.sinfo, trgt);
            return env.setUniformResultExpression(this.m_assembly.getSpecialNoneType());
        }
        else if(hpi === "yes") {
            const linfo = this.getInfoForLoadFromSafeIndex(op.sinfo, texp.flowtype, op.idx);

            this.m_emitter.emitLoadTupleIndex(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.idx, !texp.flowtype.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), trgt);
            return env.setUniformResultExpression(linfo);
        }
        else {
            const ttype = this.getInfoForLoadFromSafeIndexOnly(op.sinfo, texp.flowtype, op.idx);
            const linfo = this.m_assembly.typeUpperBound([this.m_assembly.getSpecialNoneType(), ttype]);

            this.m_emitter.emitRegisterStore(op.sinfo, this.emitInlineConvertIfNeeded(op.sinfo, new MIRConstantNone(), ValueType.createUniform(this.m_assembly.getSpecialNoneType()), linfo), trgt, this.m_emitter.registerResolvedTypeReference(linfo), undefined);

            const loadreg = this.m_emitter.generateTmpRegister();
            const hasreg = this.m_emitter.generateTmpRegister();
            const guard = new MIRArgGuard(hasreg);
            this.m_emitter.emitLoadTupleIndexSetGuard(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.idx, !texp.flowtype.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(ttype), loadreg, guard);
            if(ttype.isSameType(linfo)) {
                this.m_emitter.emitRegisterStore(op.sinfo, loadreg, trgt, this.m_emitter.registerResolvedTypeReference(linfo), new MIRStatmentGuard(guard, "defaultonfalse", trgt));
            }
            else {
                this.m_emitter.emitConvert(op.sinfo, this.m_emitter.registerResolvedTypeReference(ttype), this.m_emitter.registerResolvedTypeReference(ttype), this.m_emitter.registerResolvedTypeReference(linfo), loadreg, trgt, new MIRStatmentGuard(guard, "defaultonfalse", trgt));
            }

            return env.setUniformResultExpression(linfo);
        }
    }

    private checkPostfixGetIndexTryMulti(env: TypeEnvironment, op: PostfixGetIndexTry, arg: MIRRegisterArgument, trgt: MIRRegisterArgument): TypeEnvironment[] {
        const texp = env.getExpressionResult().valtype;
        this.raiseErrorIf(op.sinfo, !texp.flowtype.isTupleTargetType(), "Can only load indecies from tuple types");

        const hpi = this.getInfoForHasIndex(op.sinfo, texp.flowtype, op.idx);
        if (hpi === "no") {
            this.m_emitter.emitLoadConstBool(op.sinfo, false, trgt);
            return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)];
        }
        else if (hpi === "yes") {
            const linfo = this.getInfoForLoadFromSafeIndex(op.sinfo, texp.flowtype, op.idx);

            const lreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitLoadTupleIndex(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.idx, !texp.flowtype.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), lreg);
            const aenv = this.checkAssignSingleVariable(op.sinfo, env, op.vname, ValueType.createUniform(linfo), lreg);

            this.m_emitter.emitLoadConstBool(op.sinfo, true, trgt);
            return [aenv.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)];
        }
        else {
            const linfo = this.getInfoForLoadFromSafeIndex(op.sinfo, texp.flowtype, op.idx);

            this.m_emitter.emitLoadTupleIndexSetGuard(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.idx, !texp.flowtype.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), new MIRRegisterArgument(op.vname), new MIRArgGuard(trgt));
            return [
                env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False),
                env.setVar(op.vname, linfo).setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)
            ];
        }
    }

    private checkPostfixGetIndexTryMono(env: TypeEnvironment, op: PostfixGetIndexTry, arg: MIRRegisterArgument, trgt: MIRRegisterArgument): TypeEnvironment {
        return TypeEnvironment.join(this.m_assembly, ...this.checkPostfixGetIndexTryMulti(env, op, arg, trgt));
    }

    private checkPostfixHasPropertyMulti(env: TypeEnvironment, op: PostfixHasProperty, arg: MIRRegisterArgument, trgt: MIRRegisterArgument): TypeEnvironment[] {
        const texp = env.getExpressionResult().valtype;
        this.raiseErrorIf(op.sinfo, !texp.flowtype.isRecordTargetType(), "Can only check for properties on record types");

        const hpi = this.getInfoForHasProperty(op.sinfo, texp.flowtype, op.pname);
        if(hpi === "no") {
            this.m_emitter.emitLoadConstBool(op.sinfo, false, trgt);
            return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)];
        }
        else if(hpi === "yes") {
            this.m_emitter.emitLoadConstBool(op.sinfo, true, trgt);
            return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)];
        }
        else {
            assert(!texp.flowtype.isUniqueRecordTargetType(), "If this is unique then we should have been in one of the cases above");

            this.m_emitter.emitRecordHasProperty(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.pname, trgt);

            const renvs = TypeEnvironment.convertToHasIndexNotHasPropertyFlowsOnResult(this.m_assembly, op.pname, [env]);
            return [
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
    }

    private checkPostfixHasPropertyMono(env: TypeEnvironment, op: PostfixHasProperty, arg: MIRRegisterArgument, trgt: MIRRegisterArgument): TypeEnvironment {
        return TypeEnvironment.join(this.m_assembly, ...this.checkPostfixHasPropertyMulti(env, op, arg, trgt));
    }

    private checkPostfixGetPropertyOrNone(env: TypeEnvironment, op: PostfixGetPropertyOrNone, arg: MIRRegisterArgument, trgt: MIRRegisterArgument): TypeEnvironment {
        const texp = env.getExpressionResult().valtype;
        this.raiseErrorIf(op.sinfo, !texp.flowtype.isRecordTargetType(), "Can only load properties from record types");

        const hpi = this.getInfoForHasProperty(op.sinfo, texp.flowtype, op.pname);
        if(hpi === "no") {
            this.m_emitter.emitLoadConstNone(op.sinfo, trgt);
            return env.setUniformResultExpression(this.m_assembly.getSpecialNoneType());
        }
        else if(hpi === "yes") {
            const linfo = this.getInfoForLoadFromSafeProperty(op.sinfo, texp.flowtype, op.pname);

            this.m_emitter.emitLoadProperty(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.pname, !texp.flowtype.isUniqueRecordTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), trgt);
            return env.setUniformResultExpression(linfo);
        }
        else {
            const rtype = this.getInfoForLoadFromSafePropertyOnly(op.sinfo, texp.flowtype, op.pname);
            const linfo = this.m_assembly.typeUpperBound([this.m_assembly.getSpecialNoneType(), rtype]);

            this.m_emitter.emitRegisterStore(op.sinfo, this.emitInlineConvertIfNeeded(op.sinfo, new MIRConstantNone(), ValueType.createUniform(this.m_assembly.getSpecialNoneType()), linfo), trgt, this.m_emitter.registerResolvedTypeReference(linfo), undefined);

            const loadreg = this.m_emitter.generateTmpRegister();
            const hasreg = this.m_emitter.generateTmpRegister();
            const guard = new MIRArgGuard(hasreg);
            this.m_emitter.emitLoadRecordPropertySetGuard(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.pname, !texp.flowtype.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(rtype), loadreg, guard);
            if(rtype.isSameType(linfo)) {
                this.m_emitter.emitRegisterStore(op.sinfo, loadreg, trgt, this.m_emitter.registerResolvedTypeReference(linfo), new MIRStatmentGuard(guard, "defaultonfalse", trgt));
            }
            else {
                this.m_emitter.emitConvert(op.sinfo, this.m_emitter.registerResolvedTypeReference(rtype), this.m_emitter.registerResolvedTypeReference(rtype), this.m_emitter.registerResolvedTypeReference(linfo), loadreg, trgt, new MIRStatmentGuard(guard, "defaultonfalse", trgt));
            }

            return env.setUniformResultExpression(linfo);
        }
    }

    private checkPostfixGetPropertyTryMulti(env: TypeEnvironment, op: PostfixGetPropertyTry, arg: MIRRegisterArgument, trgt: MIRRegisterArgument): TypeEnvironment[] {
        const texp = env.getExpressionResult().valtype;
        this.raiseErrorIf(op.sinfo, !texp.flowtype.isRecordTargetType(), "Can only load properties from record types");

        const hpi = this.getInfoForHasProperty(op.sinfo, texp.flowtype, op.pname);
        if(hpi === "no") {
            this.m_emitter.emitLoadConstBool(op.sinfo, false, trgt);
            return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)];
        }
        else if(hpi === "yes") {
            const linfo = this.getInfoForLoadFromSafeProperty(op.sinfo, texp.flowtype, op.pname);

            const lreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitLoadProperty(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.pname, !texp.flowtype.isUniqueRecordTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), lreg);
            const aenv = this.checkAssignSingleVariable(op.sinfo, env, op.vname, ValueType.createUniform(linfo), lreg);

            this.m_emitter.emitLoadConstBool(op.sinfo, true, trgt);
            return [aenv.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)];
        }
        else {
            const linfo = this.getInfoForLoadFromSafePropertyOnly(op.sinfo, texp.flowtype, op.pname);
            
            this.m_emitter.emitLoadRecordPropertySetGuard(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.pname, !texp.flowtype.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), new MIRRegisterArgument(op.vname), new MIRArgGuard(trgt));
            return [
                env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False),
                env.setVar(op.vname, linfo).setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)
            ];
        }
    }

    private checkPostfixGetPropertyTryMono(env: TypeEnvironment, op: PostfixGetPropertyTry, arg: MIRRegisterArgument, trgt: MIRRegisterArgument): TypeEnvironment {
        return TypeEnvironment.join(this.m_assembly, ...this.checkPostfixGetPropertyTryMulti(env, op, arg, trgt));
    }

    //A hack for out overload resolution logic
    private getLambdaArgCount_Hack(env: TypeEnvironment, args: Arguments): number {
        //TODO: get rid of this later

        for(let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i].value;
            if(arg instanceof AccessVariableExpression && env.pcodes.has(arg.name)) {
                return (env.pcodes.get(arg.name) as {pcode: PCode, captured: string[]}).pcode.code.params.length;
            }
            else if(arg instanceof ConstructorPCodeExpression) {
                return arg.invoke.params.length;
            }
            else if(arg instanceof CombinatorPCodeExpression) {
                if(arg.cexp instanceof PrefixNotOp) {
                    const parg = arg.cexp.exp;
                    if(parg instanceof AccessVariableExpression) {
                        return (env.pcodes.get(parg.name) as {pcode: PCode, captured: string[]}).pcode.code.params.length;
                    }
                    else {
                        return (parg as ConstructorPCodeExpression).invoke.params.length;
                    }
                }
                else {
                    assert(false);
                    return -1;
                }
            }
            else {
                ;
            }
        }

        return -1;
    }

    private checkInvokeMulti(env: TypeEnvironment, op: PostfixInvoke, arg: MIRRegisterArgument, trgt: MIRRegisterArgument, refok: boolean): TypeEnvironment[] {
        const texp = env.getExpressionResult().valtype;

        const resolvefrom = op.specificResolve !== undefined ? this.resolveAndEnsureTypeOnly(op.sinfo, op.specificResolve, env.terms) : texp.flowtype;
        const knownimpl_multi = this.m_assembly.tryGetMethodUniqueConcreteDeclFromType(resolvefrom, op.name);
        const vinfo_multi = this.m_assembly.tryGetMethodUniqueRootDeclFromType(texp.flowtype, op.name);

        if(knownimpl_multi !== undefined && knownimpl_multi.decl.length > 1) {
            //
            //TODO: Big hack workaround for static overloading -- need to implement in general but we really need it for some container functions with functor options
            //

            let eev = env;
            if (op.isBinder) {
                eev = this.checkDeclareSingleVariable(op.sinfo, env, `$this_#${op.sinfo.pos}`, true, texp.layout, { etype: texp, etreg: arg });
            }

            const hackpc = this.getLambdaArgCount_Hack(env, op.args);
            const knownimpl_find = knownimpl_multi.decl.find((ki) => {
                const lp = ki.invoke.params.find((pp) => pp.type instanceof FunctionTypeSignature);
                return lp !== undefined && (lp.type as FunctionTypeSignature).params.length === hackpc;
            });
            assert(knownimpl_find !== undefined);

            const knownimpl = new OOMemberLookupInfo<MemberMethodDecl>(knownimpl_multi.contiainingType, knownimpl_find as MemberMethodDecl, knownimpl_multi.binds);
            const selfvar = [texp, knownimpl.decl.refRcvr ? env.getExpressionResult().expvar : undefined, arg] as [ValueType, string | undefined, MIRRegisterArgument];
            const [fsig, callbinds, eargs] = this.inferAndCheckArguments(op.sinfo, eev, op.args, knownimpl.decl.invoke, op.terms.targs, knownimpl.binds, env.terms, selfvar, refok);
            this.checkTemplateTypes(op.sinfo, knownimpl.decl.invoke.terms, callbinds, knownimpl.decl.invoke.termRestrictions);

            const rargs = this.checkArgumentsSignature(op.sinfo, eev, op.name, fsig, eargs);
            this.checkRecursion(op.sinfo, fsig, rargs.pcodes, op.rec);

            const ootype = this.m_emitter.registerResolvedTypeReference(this.resolveOOTypeFromDecls(knownimpl.contiainingType, knownimpl.binds));
            const ckey = this.m_emitter.registerMethodCall([ootype, knownimpl.contiainingType, knownimpl.binds], knownimpl.decl, op.name, callbinds, rargs.pcodes, rargs.cinfo);
            const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
            this.m_emitter.emitInvokeFixedFunction(op.sinfo, ckey, rargs.args, rargs.fflag, refinfo, trgt);

            if (op.isBinder) {
                this.m_emitter.localLifetimeEnd(op.sinfo, `$this_#${op.sinfo.pos}`)
            }

            return this.updateEnvForOutParams(env.setUniformResultExpression(fsig.resultType), rargs.refs);
        }
        else {
            if (knownimpl_multi !== undefined) {
                const knownimpl = new OOMemberLookupInfo<MemberMethodDecl>(knownimpl_multi.contiainingType, knownimpl_multi.decl[0], knownimpl_multi.binds);

                let eev = env;
                if (op.isBinder) {
                    eev = this.checkDeclareSingleVariable(op.sinfo, env, `$this_#${op.sinfo.pos}`, true, texp.layout, { etype: texp, etreg: arg });
                }

                const selfvar = [texp, knownimpl.decl.refRcvr ? env.getExpressionResult().expvar : undefined, arg] as [ValueType, string | undefined, MIRRegisterArgument];
                const [fsig, callbinds, eargs] = this.inferAndCheckArguments(op.sinfo, eev, op.args, knownimpl.decl.invoke, op.terms.targs, knownimpl.binds, env.terms, selfvar, refok);
                this.checkTemplateTypes(op.sinfo, knownimpl.decl.invoke.terms, callbinds, knownimpl.decl.invoke.termRestrictions);

                const rargs = this.checkArgumentsSignature(op.sinfo, eev, op.name, fsig, eargs);
                this.checkRecursion(op.sinfo, fsig, rargs.pcodes, op.rec);

                const ootype = this.m_emitter.registerResolvedTypeReference(this.resolveOOTypeFromDecls(knownimpl.contiainingType, knownimpl.binds));
                const ckey = this.m_emitter.registerMethodCall([ootype, knownimpl.contiainingType, knownimpl.binds], knownimpl.decl, op.name, callbinds, rargs.pcodes, rargs.cinfo);
                const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
                this.m_emitter.emitInvokeFixedFunction(op.sinfo, ckey, rargs.args, rargs.fflag, refinfo, trgt);

                if (op.isBinder) {
                    this.m_emitter.localLifetimeEnd(op.sinfo, `$this_#${op.sinfo.pos}`)
                }

                return this.updateEnvForOutParams(env.setUniformResultExpression(fsig.resultType), rargs.refs);
            }
            else {
                this.raiseErrorIf(op.sinfo, vinfo_multi === undefined, `Missing (or multiple possible) declarations of "${op.name}" method`);

                let eev = env;
                if (op.isBinder) {
                    eev = this.checkDeclareSingleVariable(op.sinfo, env, `$this_#${op.sinfo.pos}`, true, texp.layout, { etype: texp, etreg: arg });
                }

                const vinfo = vinfo_multi as OOMemberLookupInfo<MemberMethodDecl[]>;
                const minfo = new OOMemberLookupInfo<MemberMethodDecl>(vinfo.contiainingType, vinfo.decl[0], vinfo.binds);

                const selfvar = [texp, minfo.decl.refRcvr ? env.getExpressionResult().expvar : undefined, arg] as [ValueType, string | undefined, MIRRegisterArgument];
                const [fsig, callbinds, eargs] = this.inferAndCheckArguments(op.sinfo, eev, op.args, minfo.decl.invoke, op.terms.targs, minfo.binds, env.terms, selfvar, refok);
                this.checkTemplateTypes(op.sinfo, minfo.decl.invoke.terms, callbinds, minfo.decl.invoke.termRestrictions);

                const rargs = this.checkArgumentsSignature(op.sinfo, eev, op.name, fsig, eargs);
                this.checkRecursion(op.sinfo, fsig, rargs.pcodes, op.rec);

                const ootype = this.resolveOOTypeFromDecls(minfo.contiainingType, minfo.binds);
                const ckey = this.m_emitter.registerVirtualMethodCall(ootype, op.name, callbinds, rargs.pcodes, rargs.cinfo);
                const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
                this.m_emitter.emitInvokeVirtualFunction(op.sinfo, ckey, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), rargs.args, rargs.fflag, refinfo, trgt);

                if (op.isBinder) {
                    this.m_emitter.localLifetimeEnd(op.sinfo, `$this_#${op.sinfo.pos}`)
                }

                return this.updateEnvForOutParams(env.setUniformResultExpression(fsig.resultType), rargs.refs);
            }
        }
    }

    private checkInvokeMono(env: TypeEnvironment, op: PostfixInvoke, arg: MIRRegisterArgument, trgt: MIRRegisterArgument, refok: boolean): TypeEnvironment {
        return TypeEnvironment.join(this.m_assembly, ...this.checkInvokeMulti(env, op, arg, trgt, refok));
    }

    private checkElvisAction(sinfo: SourceInfo, env: TypeEnvironment, elvisEnabled: boolean, customCheck: Expression | undefined, etrgt: MIRRegisterArgument, bailblck: string): [TypeEnvironment[], TypeEnvironment[]] {
        if(!elvisEnabled) {
            return [[env], []];
        }

        if (customCheck === undefined) {
            const paths = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [env]);

            if (paths.tenvs.length === 0 && paths.fenvs.length !== 0) {
                //always some just keep going on current block emit
            }
            if (paths.tenvs.length === 0 && paths.fenvs.length !== 0) {
                //always none
                this.m_emitter.emitDirectJump(sinfo, bailblck);
            }
            else {
                const nextblk = this.m_emitter.createNewBlock("Lelvis");
                this.m_emitter.emitNoneJump(sinfo, etrgt, this.m_emitter.registerResolvedTypeReference(env.getExpressionResult().valtype.layout), bailblck, nextblk);
                this.m_emitter.setActiveBlock(nextblk);
            }

            return [paths.fenvs, paths.tenvs];
        }
        else {
            const eresinfo = env.getExpressionResult();
            const eev = this.checkDeclareSingleVariable(sinfo, env.pushLocalScope(),`$chkval_#${sinfo.pos}`, true, eresinfo.valtype.layout, {etype: eresinfo.valtype, etreg: etrgt});

            const ctrgt = this.m_emitter.generateTmpRegister();
            const cenv = this.checkExpressionMultiFlow(eev, customCheck, ctrgt, this.m_assembly.getSpecialBoolType()).map((tev) => tev.popLocalScope());
            this.m_emitter.localLifetimeEnd(sinfo, `$chkval_#${sinfo.pos}`);

            const paths = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, cenv);
            if (paths.tenvs.length === 0 && paths.fenvs.length !== 0) {
                //always some just keep going on current block emit
            }
            if (paths.tenvs.length === 0 && paths.fenvs.length !== 0) {
                //always none
                this.m_emitter.emitDirectJump(sinfo, bailblck);
            }
            else {
                const nextblk = this.m_emitter.createNewBlock("Lelvis");
                this.m_emitter.emitBoolJump(sinfo, etrgt, bailblck, nextblk);
                this.m_emitter.setActiveBlock(nextblk);
            }

            return [
                paths.fenvs.map((ee) => ee.setResultExpression(eresinfo.valtype.layout, eresinfo.valtype.flowtype, eresinfo.truthval, eresinfo.expvar)), 
                paths.tenvs.map((ee) => ee.setResultExpression(eresinfo.valtype.layout, eresinfo.valtype.flowtype, eresinfo.truthval, eresinfo.expvar))
            ];
        }
    }

    private checkPostfixExpression(env: TypeEnvironment, exp: PostfixOp, trgt: MIRRegisterArgument, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const hasNoneCheck = exp.ops.some((op) => op.isElvis);
        const noneblck = hasNoneCheck ? this.m_emitter.createNewBlock("Lelvis_none") : "INVALID";

        //we don't want to do ref assigns if there are mutilple flows throught this
        refok = refok && exp.ops.every((op) => !op.isElvis);

        let etgrt = this.m_emitter.generateTmpRegister();
        let eenv = this.checkExpression(env, exp.rootExp, etgrt, undefined, {refok: refok, orok: false});

        let scflows: TypeEnvironment[] = [];
        let cenv = eenv;
        let lenv: TypeEnvironment[] = [];
        for (let i = 0; i < exp.ops.length; ++i) {
            const [fflow, scflow] = this.checkElvisAction(exp.sinfo, cenv, exp.ops[i].isElvis, exp.ops[i].customCheck, etgrt, noneblck);
            scflows = [...scflows, ...scflow];

            const lastop = (i + 1 === exp.ops.length);
            const itype = lastop ? infertype : undefined;

            if (fflow.length === 0) {
                lenv = [];
                break;
            }
            const nflow = TypeEnvironment.join(this.m_assembly, ...fflow);

            const ntgrt = this.m_emitter.generateTmpRegister();
            switch (exp.ops[i].op) {
                case PostfixOpTag.PostfixAccessFromIndex:
                    cenv = this.checkAccessFromIndex(nflow, exp.ops[i] as PostfixAccessFromIndex, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixProjectFromIndecies:
                    cenv = this.checkProjectFromIndecies(nflow, exp.ops[i] as PostfixProjectFromIndecies, etgrt, ntgrt, itype);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixAccessFromName:
                    cenv = this.checkAccessFromName(nflow, exp.ops[i] as PostfixAccessFromName, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixProjectFromNames:
                    cenv = this.checkProjectFromNames(nflow, exp.ops[i] as PostfixProjectFromNames, etgrt, ntgrt, itype);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixModifyWithIndecies:
                    cenv = this.checkModifyWithIndecies(nflow, exp.ops[i] as PostfixModifyWithIndecies, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixModifyWithNames:
                    cenv = this.checkModifyWithNames(nflow, exp.ops[i] as PostfixModifyWithNames, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixIs:
                    if (!lastop) {
                        cenv = this.checkPostfixIsMono(nflow, exp.ops[i] as PostfixIs, etgrt, ntgrt);
                    }
                    else {
                        lenv = this.checkPostfixIsMulti(nflow, exp.ops[i] as PostfixIs, etgrt, ntgrt);
                    }
                    break;
                case PostfixOpTag.PostfixAs:
                    cenv = this.checkPostfixAs(nflow, exp.ops[i] as PostfixAs, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixHasIndex:
                    if (!lastop) {
                        cenv = this.checkPostfixHasIndexMono(nflow, exp.ops[i] as PostfixHasIndex, etgrt, ntgrt);
                    }
                    else {
                        lenv = this.checkPostfixHasIndexMulti(nflow, exp.ops[i] as PostfixHasIndex, etgrt, ntgrt);
                    }
                    break;
                case PostfixOpTag.PostfixHasProperty:
                    if (!lastop) {
                        cenv = this.checkPostfixHasPropertyMono(nflow, exp.ops[i] as PostfixHasProperty, etgrt, ntgrt);
                    }
                    else {
                        lenv = this.checkPostfixHasPropertyMulti(nflow, exp.ops[i] as PostfixHasProperty, etgrt, ntgrt);
                    }
                    break;
                case PostfixOpTag.PostfixGetIndexOrNone:
                    cenv = this.checkPostfixGetIndexOrNone(nflow, exp.ops[i] as PostfixGetIndexOrNone, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixGetIndexTry:
                    if (!lastop) {
                        cenv = this.checkPostfixGetIndexTryMono(nflow, exp.ops[i] as PostfixGetIndexTry, etgrt, ntgrt);
                    }
                    else {
                        lenv = this.checkPostfixGetIndexTryMulti(nflow, exp.ops[i] as PostfixGetIndexTry, etgrt, ntgrt);
                    }
                    break;
                case PostfixOpTag.PostfixGetPropertyOrNone:
                    cenv = this.checkPostfixGetPropertyOrNone(nflow, exp.ops[i] as PostfixGetPropertyOrNone, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixHasProperty:
                    if (!lastop) {
                        cenv = this.checkPostfixGetPropertyTryMono(nflow, exp.ops[i] as PostfixGetPropertyTry, etgrt, ntgrt);
                    }
                    else {
                        lenv = this.checkPostfixGetPropertyTryMulti(nflow, exp.ops[i] as PostfixGetPropertyTry, etgrt, ntgrt);
                    }
                    break;
                default:
                    this.raiseErrorIf(exp.sinfo, exp.ops[i].op !== PostfixOpTag.PostfixInvoke, "Unknown postfix op");
                    if (!lastop) {
                        cenv = this.checkInvokeMono(nflow, exp.ops[i] as PostfixInvoke, etgrt, ntgrt, refok);
                    }
                    else {
                        lenv = this.checkInvokeMulti(nflow, exp.ops[i] as PostfixInvoke, etgrt, ntgrt, refok);
                    }
                    break;
            }

            etgrt = ntgrt;
        }

        const oktype = ValueType.join(this.m_assembly, ...lenv.map((ee) => ee.getExpressionResult().valtype));
        const fulltype = this.m_assembly.typeUpperBound([oktype.flowtype, ...(hasNoneCheck && scflows.length !== 0 ? [this.m_assembly.getSpecialNoneType()] : [])]);
        if (lenv.length === 0 && scflows.length === 0) {
            return [];
        }
        else {
            if (lenv.length !== 0) {
                this.m_emitter.emitRegisterStore(exp.sinfo, this.emitInlineConvertIfNeeded(exp.sinfo, etgrt, oktype, fulltype), trgt, this.m_emitter.registerResolvedTypeReference(fulltype), undefined);
            }

            if (hasNoneCheck && scflows.length !== 0) {
                const doneblck = this.m_emitter.createNewBlock("Lelvis_done");

                this.m_emitter.emitDirectJump(exp.sinfo, doneblck);

                this.m_emitter.setActiveBlock(noneblck);
                this.m_emitter.emitRegisterStore(exp.sinfo, this.emitInlineConvertIfNeeded(exp.sinfo, new MIRConstantNone(), ValueType.createUniform(this.m_assembly.getSpecialNoneType()), fulltype), trgt, this.m_emitter.registerResolvedTypeReference(fulltype), undefined);
                this.m_emitter.emitDirectJump(exp.sinfo, doneblck);

                this.m_emitter.setActiveBlock(doneblck);
            }

            return [...lenv, ...scflows].map((ee) => ee.updateResultExpression(fulltype, ee.getExpressionResult().valtype.flowtype));
        }
    }

    private checkPrefixNotOpAsCombinator(env: TypeEnvironment, exp: PrefixNotOp, cbinds: Map<string, ResolvedType>, expectedFunction: ResolvedFunctionType | undefined): PCode {
        let subpc: PCode | undefined = undefined;
        
        if(exp.exp instanceof AccessVariableExpression) {
            subpc = (env.pcodes.get(exp.exp.name) as { pcode: PCode, captured: string[] }).pcode;
        }
        else if(exp.exp instanceof PrefixNotOp) {
            subpc = this.checkPrefixNotOpAsCombinator(env, exp.exp, cbinds, expectedFunction);
        }
        else if(exp.exp instanceof BinLogicExpression) {
            subpc = this.checkBinLogicAsCombinator(env, exp.exp, cbinds, expectedFunction);
        }
        else {
            this.raiseErrorIf(exp.sinfo, !(exp.exp instanceof ConstructorPCodeExpression), "Expected Lambda Predicate Constructor");
            const cexp = exp.exp as ConstructorPCodeExpression;

            const ltypetry = cexp.isAuto ? expectedFunction : this.m_assembly.normalizeTypeFunction(cexp.invoke.generateSig(), cbinds);
            this.raiseErrorIf(cexp.sinfo, ltypetry === undefined, "Invalid lambda type");

            this.raiseErrorIf(cexp.sinfo, cexp.invoke.params.length !== (ltypetry as ResolvedFunctionType).params.length, "Mismatch in expected parameter count and provided function parameter count");
            this.raiseErrorIf(cexp.sinfo, expectedFunction !== undefined && !this.m_assembly.functionSubtypeOf(ltypetry as ResolvedFunctionType, expectedFunction), "Mismatch in expected and provided function signature");

            let capturedMap: Map<string, ResolvedType> = new Map<string, ResolvedType>();

            let captures: string[] = [];
            cexp.invoke.captureSet.forEach((v) => captures.push(v));
            captures.sort();

            captures.forEach((v) => {
                if (v === "%this_captured" && env.lookupVar(v) === null) {
                    const vinfo = env.lookupVar("this") as VarInfo;

                    capturedMap.set(v, vinfo.flowType);
                }
                else {
                    const vinfo = env.lookupVar(v) as VarInfo;
                    this.raiseErrorIf(exp.sinfo, vinfo.declaredType instanceof ResolvedFunctionType, "Cannot capture function typed argument");

                    capturedMap.set(v, vinfo.flowType);
                }
            });

            this.m_emitter.registerPCode(cexp.invoke, ltypetry as ResolvedFunctionType, cbinds, [...capturedMap].sort((a, b) => a[0].localeCompare(b[0])));

            subpc = { code: cexp.invoke, scope: env.scope, captured: capturedMap, ftype: ltypetry as ResolvedFunctionType };
        }

        let args = subpc.code.params.map((pp) => new AccessVariableExpression(exp.sinfo, pp.name));
        if(subpc.code.optRestName !== undefined) {
            args.push(new AccessVariableExpression(exp.sinfo, subpc.code.optRestName));
        }

        const nbody = new PrefixNotOp(exp.sinfo, new PCodeDirectInvokeExpression(exp.sinfo, subpc, [...subpc.captured].sort((a, b) => a[0].localeCompare(b[0])).map((cc) => cc[0]), args, true))
        const bodyid = `${this.m_file}::${exp.sinfo.pos}`;
        const body = new BodyImplementation(bodyid, this.m_file, nbody);
        const ninvoke = new InvokeDecl(exp.sinfo, this.m_file, [], subpc.code.recursive, [], undefined, subpc.code.params, subpc.code.optRestName, subpc.code.optRestType, this.m_assembly.getSpecialBoolType(), [], [], false, true, subpc.code.captureSet, body, [], []);
        
        this.m_emitter.registerPCode(ninvoke, subpc.ftype, cbinds, [...subpc.captured].sort((a, b) => a[0].localeCompare(b[0])));

        return { code: ninvoke, scope: env.scope + `(${exp.sinfo.pos})`, captured: subpc.captured, ftype: subpc.ftype };
    }

    private checkPrefixNotOp(env: TypeEnvironment, exp: PrefixNotOp, trgt: MIRRegisterArgument, refok: boolean): TypeEnvironment[] {
        const etreg = this.m_emitter.generateTmpRegister();
        const estates = this.checkExpressionMultiFlow(env, exp.exp, etreg, this.m_assembly.getSpecialBoolType(), {refok: refok, orok: false});

        this.m_emitter.emitPrefixNotOp(exp.sinfo, etreg, trgt);

        const bstates = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, estates);
        const ntstates = bstates.fenvs.map((state) => state.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False));
        const nfstates = bstates.tenvs.map((state) => state.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True));

        return [...ntstates, ...nfstates];
    }

    private checkKeyEq(env: TypeEnvironment, exp: BinKeyExpression, trgt: MIRRegisterArgument): TypeEnvironment[] {
        const lhsreg = this.m_emitter.generateTmpRegister();
        const lhs = this.checkExpression(env, exp.lhs, lhsreg, undefined);
        let olhs = lhs.getExpressionResult().valtype;

        this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(olhs.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()), "Type must be KeyType");
        this.raiseErrorIf(exp.sinfo, !olhs.flowtype.isGroundedType(), "Type must be grounded");

        const rhsreg = this.m_emitter.generateTmpRegister();
        const rhs = this.checkExpression(env, exp.rhs, rhsreg, undefined);
        let orhs = rhs.getExpressionResult().valtype;

        this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(orhs.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()), "Type must be KeyType");
        this.raiseErrorIf(exp.sinfo, !orhs.flowtype.isGroundedType(), "Type must be grounded");

        const action = this.checkValueEq(exp.lhs, lhs.getExpressionResult().valtype.flowtype, exp.rhs, rhs.getExpressionResult().valtype.flowtype);
        this.raiseErrorIf(exp.sinfo, action === "err", "Compared types are not equivalent (or not unique modulo none)");

        if(action === "truealways" || action === "falsealways") {
            this.m_emitter.emitLoadConstBool(exp.sinfo, action === "truealways" ? true : false, trgt);
            return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), action === "truealways" ? FlowTypeTruthValue.True : FlowTypeTruthValue.False)];
        }
        else if (action === "lhsnone" || action === "rhsnone") {
            if(action === "lhsnone") {
                this.m_emitter.emitTypeOf(exp.sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()), rhsreg, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().valtype.flowtype), undefined);
            }
            else if (exp.rhs instanceof LiteralNoneExpression) {
                this.m_emitter.emitTypeOf(exp.sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()), lhsreg, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.flowtype), undefined);
            }

            const eevs = (action === "lhsnone") ? rhs : lhs;
            const renvs = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [eevs]);
            return [
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
        else if(action === "lhssomekey" || action === "rhssomekey") {
            if (exp.op === "===") {
                this.m_emitter.emitBinKeyEq(exp.sinfo, this.m_emitter.registerResolvedTypeReference(olhs.layout), this.m_emitter.registerResolvedTypeReference(olhs.flowtype), lhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), this.m_emitter.registerResolvedTypeReference(orhs.flowtype), rhsreg, trgt);
            }
            else {
                const treg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitBinKeyEq(exp.sinfo, this.m_emitter.registerResolvedTypeReference(olhs.layout), this.m_emitter.registerResolvedTypeReference(olhs.flowtype), lhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), this.m_emitter.registerResolvedTypeReference(orhs.flowtype), rhsreg, treg);
                this.m_emitter.emitPrefixNotOp(exp.sinfo, treg, trgt);
            }

            const eevs = (action === "lhssomekey") ? rhs : lhs;
            const renvs = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [eevs]);
            return [
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False))),
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.Unknown)))
            ];
        }
        else {
            if (exp.op === "===") {
                this.m_emitter.emitBinKeyEq(exp.sinfo, this.m_emitter.registerResolvedTypeReference(olhs.layout), this.m_emitter.registerResolvedTypeReference(olhs.flowtype), lhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), this.m_emitter.registerResolvedTypeReference(orhs.flowtype), rhsreg, trgt);
            }
            else {
                const treg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitBinKeyEq(exp.sinfo, this.m_emitter.registerResolvedTypeReference(olhs.layout), this.m_emitter.registerResolvedTypeReference(olhs.flowtype), lhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), this.m_emitter.registerResolvedTypeReference(orhs.flowtype), rhsreg, treg);
                this.m_emitter.emitPrefixNotOp(exp.sinfo, treg, trgt);
            }

            return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.Unknown)];
        }
    }

    private checkBinLogicAsCombinator(env: TypeEnvironment, exp: BinLogicExpression, cbinds: Map<string, ResolvedType>, expectedFunction: ResolvedFunctionType | undefined): PCode {
        //
        //TODO: this is more complicated but similar to the not case above -- implement when needed
        //

        assert(false);
        return (undefined as any) as PCode;
    }

    private checkBinLogic(env: TypeEnvironment, exp: BinLogicExpression, trgt: MIRRegisterArgument, refok: boolean): TypeEnvironment[] {
        if (exp.op === "|" || exp.op === "&") {
            const lhsreg = this.m_emitter.generateTmpRegister();
            const lhs = this.checkExpressionMultiFlow(env, exp.lhs, lhsreg, undefined, { refok: refok, orok: false });

            this.raiseErrorIf(exp.sinfo, lhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");
            const blhsreg = this.emitInlineConvertToFlow(exp.sinfo, lhsreg, ValueType.join(this.m_assembly, ...lhs.map((eev) => eev.getExpressionResult().valtype)));

            const rhsreg = this.m_emitter.generateTmpRegister();
            const rhs = this.checkExpressionMultiFlow(env, exp.rhs, rhsreg, undefined, { refok: refok, orok: false });

            this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");
            const brhsreg = this.emitInlineConvertToFlow(exp.sinfo, rhsreg, ValueType.join(this.m_assembly, ...rhs.map((eev) => eev.getExpressionResult().valtype)));

            if (exp.op === "|") {
                if (lhs.every((ee) => ee.getExpressionResult().truthval === FlowTypeTruthValue.False) || rhs.every((ee) => ee.getExpressionResult().truthval === FlowTypeTruthValue.False)) {
                    this.m_emitter.emitLoadConstBool(exp.sinfo, false, trgt);
                    return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)];
                }
                else {
                    this.m_emitter.emitSomeTrue(exp.sinfo, [blhsreg, brhsreg], trgt);

                    //
                    //TODO: this is imprecise but we need to check both sides in the full type env and then do a "intersect" of the 
                    //      infered type info (not a join)
                    return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.Unknown)];
                }
            }
            else {
                if (lhs.every((ee) => ee.getExpressionResult().truthval === FlowTypeTruthValue.True) || rhs.every((ee) => ee.getExpressionResult().truthval === FlowTypeTruthValue.True)) {
                    this.m_emitter.emitLoadConstBool(exp.sinfo, true, trgt);
                    return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)];
                }
                else {
                    this.m_emitter.emitAllTrue(exp.sinfo, [blhsreg, brhsreg], trgt);

                    //
                    //TODO: this is imprecise but we need to check both sides in the full type env and then do a "intersect" of the 
                    //      infered type info (not a join)
                    return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.Unknown)];
                }
            }
        }
        else {
            const lhsreg = this.m_emitter.generateTmpRegister();
            const lhs = this.checkExpressionMultiFlow(env, exp.lhs, lhsreg, undefined, { refok: refok, orok: false });

            this.raiseErrorIf(exp.sinfo, lhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");
            const blhsreg = this.emitInlineConvertToFlow(exp.sinfo, lhsreg, ValueType.join(this.m_assembly, ...lhs.map((eev) => eev.getExpressionResult().valtype)));

            if (exp.op === "||") {
                if (lhs.every((ee) => ee.getExpressionResult().truthval === FlowTypeTruthValue.True)) {
                    this.m_emitter.emitLoadConstBool(exp.sinfo, true, trgt);
                    return lhs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True));
                }
                else {
                    const doneblck = this.m_emitter.createNewBlock("Llogic_or_done");
                    const restblck = this.m_emitter.createNewBlock("Llogic_or_rest");

                    const fflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, lhs);

                    this.m_emitter.emitRegisterStore(exp.sinfo, blhsreg, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), undefined);
                    this.m_emitter.emitBoolJump(exp.sinfo, blhsreg, doneblck, restblck);
                    this.m_emitter.setActiveBlock(restblck);

                    const rhsreg = this.m_emitter.generateTmpRegister();
                    const rhs = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...fflows.fenvs), exp.rhs, rhsreg, undefined, { refok: refok, orok: false });

                    this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");
                    this.m_emitter.emitRegisterStore(exp.sinfo, this.emitInlineConvertToFlow(exp.sinfo, rhsreg, ValueType.join(this.m_assembly, ...rhs.map((eev) => eev.getExpressionResult().valtype))), trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), undefined);

                    this.m_emitter.emitDirectJump(exp.sinfo, doneblck);
                    this.m_emitter.setActiveBlock(doneblck);

                    const oflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, rhs);
                    return [...fflows.tenvs, ...oflows.tenvs, ...oflows.fenvs].map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), eev.getExpressionResult().truthval));
                }
            }
            else if (exp.op === "&&") {
                if (lhs.every((ee) => ee.getExpressionResult().truthval === FlowTypeTruthValue.False)) {
                    this.m_emitter.emitLoadConstBool(exp.sinfo, false, trgt);
                    return lhs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False));
                }
                else {
                    const doneblck = this.m_emitter.createNewBlock("Llogic_and_done");
                    const restblck = this.m_emitter.createNewBlock("Llogic_and_rest");

                    const fflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, lhs);

                    this.m_emitter.emitRegisterStore(exp.sinfo, blhsreg, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), undefined);
                    this.m_emitter.emitBoolJump(exp.sinfo, blhsreg, restblck, doneblck);
                    this.m_emitter.setActiveBlock(restblck);

                    const rhsreg = this.m_emitter.generateTmpRegister();
                    const rhs = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...fflows.tenvs), exp.rhs, rhsreg, undefined, { refok: refok, orok: false });

                    this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");
                    this.m_emitter.emitRegisterStore(exp.sinfo, this.emitInlineConvertToFlow(exp.sinfo, rhsreg, ValueType.join(this.m_assembly, ...rhs.map((eev) => eev.getExpressionResult().valtype))), trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), undefined);

                    this.m_emitter.emitDirectJump(exp.sinfo, doneblck);
                    this.m_emitter.setActiveBlock(doneblck);
                    const oflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, rhs);
                    return [...fflows.fenvs, ...oflows.tenvs, ...oflows.fenvs].map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), eev.getExpressionResult().truthval));
                }
            }
            else {
                if (lhs.every((ee) => ee.getExpressionResult().truthval === FlowTypeTruthValue.False)) {
                    this.m_emitter.emitLoadConstBool(exp.sinfo, false, trgt);
                    return lhs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True));
                }
                else {
                    const doneblck = this.m_emitter.createNewBlock("Llogic_imply_done");
                    const restblck = this.m_emitter.createNewBlock("Llogic_imply_rest");

                    const fflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, lhs);

                    this.m_emitter.emitPrefixNotOp(exp.sinfo, blhsreg, trgt);
                    this.m_emitter.emitBoolJump(exp.sinfo, blhsreg, restblck, doneblck);
                    this.m_emitter.setActiveBlock(restblck);

                    const rhsreg = this.m_emitter.generateTmpRegister();
                    const rhs = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...fflows.tenvs), exp.rhs, rhsreg, undefined, { refok: refok, orok: false });

                    this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");
                    this.m_emitter.emitRegisterStore(exp.sinfo, this.emitInlineConvertToFlow(exp.sinfo, rhsreg, ValueType.join(this.m_assembly, ...rhs.map((eev) => eev.getExpressionResult().valtype))), trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), undefined);

                    this.m_emitter.emitDirectJump(exp.sinfo, doneblck);
                    this.m_emitter.setActiveBlock(doneblck);

                    const oflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, rhs);
                    return [...fflows.fenvs, ...oflows.tenvs, ...oflows.fenvs].map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), eev.getExpressionResult().truthval));
                }
            }
        }
    }

    private checkMapEntryConstructorExpression(env: TypeEnvironment, exp: MapEntryConstructorExpression, trgt: MIRRegisterArgument, infertype: ResolvedType | undefined): TypeEnvironment {
        const itype = infertype !== undefined ? infertype.tryGetInferrableTupleConstructorType(true) : undefined;
        const metype = (itype !== undefined && itype.types.length === 2 && itype.types.every((ee) => !ee.isOptional)) ? itype : undefined;

        const kreg = this.m_emitter.generateTmpRegister();
        const kinfer = metype !== undefined ? metype.types[0].type : undefined;
        const ktype = this.checkExpression(env, exp.kexp, kreg, kinfer).getExpressionResult().valtype;

        this.raiseErrorIf(exp.kexp.sinfo, !this.m_assembly.subtypeOf(ktype.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()) || !ktype.flowtype.isGroundedType(), "Key must be a grounded KeyType value");

        const vreg = this.m_emitter.generateTmpRegister();
        const vinfer = metype !== undefined ? metype.types[1].type : undefined;
        const vtype = this.checkExpression(env, exp.vexp, vreg, vinfer).getExpressionResult().valtype;

        const mtype = ResolvedType.createSingle(ResolvedTupleAtomType.create(true, [new ResolvedTupleAtomTypeEntry(ktype.flowtype, false), new ResolvedTupleAtomTypeEntry(vtype.flowtype, false)]));

        const targs = [ this.emitInlineConvertToFlow(exp.sinfo, kreg, ktype), this.emitInlineConvertToFlow(exp.sinfo, vreg, vtype)];
        this.m_emitter.emitConstructorTuple(exp.sinfo, this.m_emitter.registerResolvedTypeReference(mtype), targs, trgt);

        return env.setUniformResultExpression(mtype);
    }

    private checkNonecheck(env: TypeEnvironment, exp: NonecheckExpression, trgt: MIRRegisterArgument, infertype: ResolvedType | undefined): TypeEnvironment {
        const lhsreg = this.m_emitter.generateTmpRegister();
        const lhs = this.checkExpression(env, exp.lhs, lhsreg, undefined);

        if (exp.customCheck === undefined) {
            const fflows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [lhs]);
            if (fflows.fenvs.length === 0) {
                this.m_emitter.emitLoadConstNone(exp.sinfo, trgt);
                return TypeEnvironment.join(this.m_assembly, ...fflows.tenvs);
            }
            else {
                const noneblck = this.m_emitter.createNewBlock("Lnonecheck_none");
                const doneblck = this.m_emitter.createNewBlock("Lnonecheck_done");
                const restblck = this.m_emitter.createNewBlock("Lnonecheck_rest");

                this.m_emitter.emitNoneJump(exp.sinfo, lhsreg, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.layout), noneblck, restblck);

                this.m_emitter.setActiveBlock(restblck);
                const rhsreg = this.m_emitter.generateTmpRegister();
                const rhs = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...fflows.fenvs), exp.rhs, rhsreg, infertype);

                const fulltype = this.m_assembly.typeUpperBound([...fflows.tenvs, rhs].map((eev) => eev.getExpressionResult().valtype.flowtype));

                this.m_emitter.emitRegisterStore(exp.sinfo, this.emitInlineConvertIfNeeded(exp.sinfo, rhsreg, rhs.getExpressionResult().valtype, fulltype), trgt, this.m_emitter.registerResolvedTypeReference(fulltype), undefined);
                this.m_emitter.emitDirectJump(exp.sinfo, doneblck);

                this.m_emitter.setActiveBlock(noneblck);
                const convreg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitLoadConstNone(exp.sinfo, convreg);
                this.m_emitter.emitRegisterStore(exp.sinfo, this.emitInlineConvertIfNeeded(exp.sinfo, convreg, ValueType.createUniform(this.m_assembly.getSpecialNoneType()), fulltype), trgt, this.m_emitter.registerResolvedTypeReference(fulltype), undefined);
                this.m_emitter.emitDirectJump(exp.sinfo, doneblck);

                this.m_emitter.setActiveBlock(doneblck);

                return TypeEnvironment.join(this.m_assembly, ...[...fflows.tenvs, rhs].map((eev) => eev.updateResultExpression(fulltype, eev.getExpressionResult().valtype.flowtype)));
            }
        }
        else {
            //
            //TODO: Implement this path
            //
            this.raiseError(exp.sinfo, "checkNonecheck with custom op is not implemented!!!");
            return env;
        }
    }

    private checkCoalesce(env: TypeEnvironment, exp: CoalesceExpression, trgt: MIRRegisterArgument, infertype: ResolvedType | undefined): TypeEnvironment {
        const lhsreg = this.m_emitter.generateTmpRegister();
        const lhs = this.checkExpression(env, exp.lhs, lhsreg, infertype);

        if (exp.customCheck === undefined) {
            const fflows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [lhs]);

            if (fflows.tenvs.length === 0) {
                return this.checkExpression(TypeEnvironment.join(this.m_assembly, ...fflows.fenvs), exp.rhs, trgt, infertype);
            }
            else {
                const someblck = this.m_emitter.createNewBlock("Lcoalesce_some");
                const doneblck = this.m_emitter.createNewBlock("Lcoalesce_done");
                const restblck = this.m_emitter.createNewBlock("Lcoalesce_rest");

                this.m_emitter.emitNoneJump(exp.sinfo, lhsreg, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.layout), restblck, someblck);

                this.m_emitter.setActiveBlock(restblck);
                const rhsreg = this.m_emitter.generateTmpRegister();
                const rhs = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...fflows.tenvs), exp.rhs, rhsreg, infertype);

                const fulltype = this.m_assembly.typeUpperBound([...fflows.fenvs, rhs].map((eev) => eev.getExpressionResult().valtype.flowtype));

                this.m_emitter.emitRegisterStore(exp.sinfo, this.emitInlineConvertIfNeeded(exp.sinfo, rhsreg, rhs.getExpressionResult().valtype, fulltype), trgt, this.m_emitter.registerResolvedTypeReference(fulltype), undefined);
                this.m_emitter.emitDirectJump(exp.sinfo, doneblck);

                this.m_emitter.setActiveBlock(someblck);
                const convarg = this.emitInlineConvertIfNeeded(exp.sinfo, lhsreg, ValueType.join(this.m_assembly, ...fflows.fenvs.map((eev) => eev.getExpressionResult().valtype)), fulltype);
                this.m_emitter.emitRegisterStore(exp.sinfo, convarg, trgt, this.m_emitter.registerResolvedTypeReference(fulltype), undefined);
                this.m_emitter.emitDirectJump(exp.sinfo, doneblck);

                this.m_emitter.setActiveBlock(doneblck);

                return TypeEnvironment.join(this.m_assembly, ...[...fflows.fenvs, rhs].map((eev) => eev.updateResultExpression(fulltype, eev.getExpressionResult().valtype.flowtype)));
            }
        }
        else {
            //
            //TODO: Implement this path
            //
            this.raiseError(exp.sinfo, "checkCoalesce with custom op is not implemented!!!");
            return env;
        }
    }

    private checkSelect(env: TypeEnvironment, exp: SelectExpression, trgt: MIRRegisterArgument, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment {
        const testreg = this.m_emitter.generateTmpRegister();
        const test = this.checkExpressionMultiFlow(env, exp.test, testreg, undefined, { refok: refok, orok: false });

        this.raiseErrorIf(exp.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");
        const btestreg = this.emitInlineConvertToFlow(exp.sinfo, testreg, ValueType.createUniform(this.m_assembly.getSpecialBoolType()));

        const fflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, test);

        if(fflows.tenvs.length === 0) {
            return this.checkExpression(TypeEnvironment.join(this.m_assembly, ...fflows.fenvs), exp.option2, trgt, infertype);
        }
        else if (fflows.fenvs.length === 0) {
            return this.checkExpression(TypeEnvironment.join(this.m_assembly, ...fflows.tenvs), exp.option1, trgt, infertype);
        }
        else {
            const doneblck = this.m_emitter.createNewBlock("Lselect_done");
            const trueblck = this.m_emitter.createNewBlock("Lselect_true");
            const falseblck = this.m_emitter.createNewBlock("Lselect_false");

            this.m_emitter.emitBoolJump(exp.sinfo, btestreg, trueblck, falseblck);

            this.m_emitter.setActiveBlock(trueblck);
            const truereg = this.m_emitter.generateTmpRegister();
            const truestate = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...fflows.tenvs), exp.option1, truereg, infertype);
            //note jump isn't set yet

            this.m_emitter.setActiveBlock(falseblck);
            const falsereg = this.m_emitter.generateTmpRegister();
            const falsestate = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...fflows.fenvs), exp.option2, falsereg, infertype);
            //note jump isn't set yet

            const fulltype = this.m_assembly.typeUpperBound([truestate.getExpressionResult().valtype.flowtype, falsestate.getExpressionResult().valtype.flowtype]);

            //set the assigns and jumps
            this.m_emitter.setActiveBlock(trueblck);
            this.m_emitter.emitRegisterStore(exp.sinfo, this.emitInlineConvertIfNeeded(exp.sinfo, truereg, truestate.getExpressionResult().valtype, fulltype), trgt, this.m_emitter.registerResolvedTypeReference(fulltype), undefined);
            this.m_emitter.emitDirectJump(exp.sinfo, doneblck);

            this.m_emitter.setActiveBlock(falseblck);
            this.m_emitter.emitRegisterStore(exp.sinfo, this.emitInlineConvertIfNeeded(exp.sinfo, falsereg, falsestate.getExpressionResult().valtype, fulltype), trgt, this.m_emitter.registerResolvedTypeReference(fulltype), undefined);
            this.m_emitter.emitDirectJump(exp.sinfo, doneblck);

            this.m_emitter.setActiveBlock(doneblck);

            return TypeEnvironment.join(this.m_assembly, ...[truestate, falsestate].map((eev) => eev.updateResultExpression(fulltype, eev.getExpressionResult().valtype.flowtype)));
        }
    }

    private checkOrExpression(env: TypeEnvironment, exp: ExpOrExpression, trgt: MIRRegisterArgument, infertype: ResolvedType | undefined, extraok: { refok: boolean, orok: boolean }): TypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !extraok.orok, "Or expression is not valid in this position");

        const scblck = this.m_emitter.createNewBlock("Lorcheck_return");
        const regularblck = this.m_emitter.createNewBlock("Lorcheck_regular");

        let normalexps: TypeEnvironment[] = [];
        let terminalexps: TypeEnvironment[] = [];

        if((exp.cond !== "none" && exp.cond !== "err") || exp.result !== undefined) {
            //
            //TODO: these cases need to be implemented!!!
            //
            this.raiseError(exp.sinfo, "NOT IMPLEMENTED!!!");

            return env;
        }
        else {
            let eeinfer: ResolvedType | undefined = undefined;
            if (exp.cond === "none") {
                eeinfer = infertype !== undefined ? this.m_assembly.typeUpperBound([infertype, this.m_assembly.getSpecialNoneType()]) : undefined;
            }
            else {
                let iitype = exp.action === "return" ? env.inferResult : env.inferYield[env.inferYield.length - 1];
                eeinfer = iitype !== undefined && iitype.isResultGeneralType() ? iitype : undefined;
            }

            const eereg = this.m_emitter.generateTmpRegister();
            const evalue = this.checkExpression(env, exp.exp, eereg, eeinfer, {refok: extraok.refok, orok: false});

            //do test for return or normal result
            if (exp.cond === "none") {
                const flows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [evalue]);
                normalexps = flows.fenvs
                terminalexps = flows.tenvs;

                if (normalexps.length === 0 || terminalexps.length === 0) {
                    this.m_emitter.emitDirectJump(exp.sinfo, normalexps.length !== 0 ? regularblck : scblck);
                }
                else {
                    this.m_emitter.emitNoneJump(exp.sinfo, eereg, this.m_emitter.registerResolvedTypeReference(evalue.getExpressionResult().valtype.layout), scblck, regularblck);
                }
            }
            else {
                const etype = evalue.getExpressionResult().valtype.flowtype;
                this.raiseErrorIf(exp.sinfo, etype.options.length !== 1 || etype.options[0] instanceof ResolvedConceptAtomType || (etype.options[0] as ResolvedConceptAtomType).conceptTypes.length !== 1 || !etype.idStr.startsWith("NSCore::Result<"), "Expected a Result<T, E> type");

                const oktype = this.getResultSubtypes(etype)[0];
                const flows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, oktype, [evalue]);
                normalexps = flows.tenvs
                terminalexps = flows.fenvs;

                if (normalexps.length === 0 || terminalexps.length === 0) {
                    this.m_emitter.emitDirectJump(exp.sinfo, normalexps.length !== 0 ? regularblck : scblck);
                }
                else {
                    const treg = this.m_emitter.generateTmpRegister();
                    const oktype = this.m_emitter.registerResolvedTypeReference(this.getResultSubtypes(etype)[0]);
                    this.m_emitter.emitCheckNoError(exp.sinfo, eereg, this.m_emitter.registerResolvedTypeReference(etype), oktype, treg);

                    this.m_emitter.emitBoolJump(exp.sinfo, treg, scblck, regularblck);
                }
            }

            //load early return block and process
            let terminalenvironments: TypeEnvironment[] = [];
            if (terminalexps.length !== 0) {
                const terminaltype = ValueType.join(this.m_assembly, ...terminalexps.map((eev) => eev.getExpressionResult().valtype));

                this.m_emitter.setActiveBlock(scblck);
                if (exp.action === "return") {
                    this.raiseErrorIf(exp.sinfo, env.isInYieldBlock(), "Cannot use return statment inside an expression block");

                    this.m_emitter.getActiveReturnSet().push([this.m_emitter.getActiveBlockName(), eereg, terminaltype]);
                    terminalenvironments = [env.setReturn(this.m_assembly, terminaltype.flowtype)];
                }
                else {
                    this.raiseErrorIf(exp.sinfo, !env.isInYieldBlock(), "Cannot use yield statment unless inside and expression block");

                    this.m_emitter.getActiveYieldSet().push([this.m_emitter.getActiveBlockName(), eereg, terminaltype]);
                    terminalenvironments = [env.setYield(this.m_assembly, terminaltype.flowtype)];
                }
            }

            //load normal block and process
            let normalenvironments: TypeEnvironment[] = [];
            this.m_emitter.setActiveBlock(regularblck);
            if (normalexps.length !== 0) {
                if (exp.cond === "none") {
                    const ntype = this.m_assembly.typeUpperBound(normalenvironments.map((eev) => eev.getExpressionResult().valtype.flowtype));
                    this.m_emitter.emitRegisterStore(exp.sinfo, this.emitInlineConvertIfNeeded(exp.sinfo, eereg, evalue.getExpressionResult().valtype, ntype), trgt, this.m_emitter.registerResolvedTypeReference(ntype), undefined);

                    normalenvironments = normalexps.map((eev) => eev.setUniformResultExpression(ntype));
                }
                else {
                    const rtype = evalue.getExpressionResult().valtype.flowtype;
                    const oktype = this.m_emitter.registerResolvedTypeReference(this.getResultSubtypes(rtype)[0]);
                    const okvfield = MIRKeyGenerator.generateFieldKey(this.getResultSubtypes(rtype)[0], "value");
                    const vtype = this.getResultBinds(rtype).T
                    this.m_emitter.emitExtractResultOkValue(exp.sinfo, this.emitInlineConvertToFlow(exp.sinfo, eereg, evalue.getExpressionResult().valtype), this.m_emitter.registerResolvedTypeReference(rtype), oktype, okvfield, this.m_emitter.registerResolvedTypeReference(vtype), trgt);

                    normalenvironments = normalexps.map((eev) => eev.setUniformResultExpression(vtype));
                }
            }

            return TypeEnvironment.join(this.m_assembly, ...normalenvironments, ...terminalenvironments);
        }
    }

    private checkBlockExpression(env: TypeEnvironment, exp: BlockStatementExpression, infertype: ResolvedType | undefined, trgt: MIRRegisterArgument): TypeEnvironment {
        try {
            this.m_emitter.processEnterYield();
            let cenv = env.freezeVars(infertype).pushLocalScope();

            for (let i = 0; i < exp.ops.length; ++i) {
                if (!cenv.hasNormalFlow()) {
                    break;
                }

                cenv = this.checkStatement(cenv, exp.ops[i]);
            }

            const yblck = this.m_emitter.createNewBlock("Lyield");
            if (cenv.hasNormalFlow()) {
                this.m_emitter.setActiveBlock(yblck);

                const deadvars = cenv.getCurrentFrameNames();
                for (let i = 0; i < deadvars.length; ++i) {
                    this.m_emitter.localLifetimeEnd(exp.sinfo, deadvars[i]);
                }
            }

            this.raiseErrorIf(exp.sinfo, cenv.hasNormalFlow(), "Not all flow paths yield a value!");
            this.raiseErrorIf(exp.sinfo, cenv.yieldResult === undefined, "No valid flow through expresssion block");

            const ytype = cenv.yieldResult as ResolvedType;
            const yeildcleanup = this.m_emitter.getActiveYieldSet();
            if (cenv.hasNormalFlow()) {
                for (let i = 0; i < yeildcleanup.length; ++i) {
                    const yci = yeildcleanup[i];
                    this.m_emitter.setActiveBlock(yci[0]);

                    const convreg = this.emitInlineConvertIfNeeded(exp.sinfo, yci[1], yci[2], ytype);
                    this.m_emitter.emitRegisterStore(exp.sinfo, convreg, trgt, this.m_emitter.registerResolvedTypeReference(ytype), undefined);

                    this.m_emitter.emitDirectJump(exp.sinfo, yblck);
                }
            }

            return env.setUniformResultExpression(ytype);
        }
        finally {
            this.m_emitter.processExitYield();
        }
    }

    private checkIfExpression(env: TypeEnvironment, exp: IfExpression, trgt: MIRRegisterArgument, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment {
        const doneblck = this.m_emitter.createNewBlock("Lifexp_done");

        let cenv = env;
        let hasfalseflow = true;
        let results: TypeEnvironment[] = [];
        let rblocks: [string, MIRRegisterArgument, ValueType][] = [];

        for (let i = 0; i < exp.flow.conds.length && hasfalseflow; ++i) {
            const testreg = this.m_emitter.generateTmpRegister();
            const test = this.checkExpressionMultiFlow(cenv, exp.flow.conds[i].cond, testreg, infertype, i === 0 ? { refok: refok, orok: false } : undefined);
            this.raiseErrorIf(exp.sinfo, !test.every((eev) => this.m_assembly.subtypeOf(eev.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "If test expression must return a Bool");

            const cflow = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, test);
            
            if (cflow.tenvs.length === 0) {
                //can just keep generating tests in striaght line
                cenv = TypeEnvironment.join(this.m_assembly, ...cflow.fenvs);
            }
            else if (cflow.fenvs.length === 0) {
                //go though true block (without jump) and then skip else
                const trueblck = this.m_emitter.createNewBlock(`Lifexp_${i}true`);
                this.m_emitter.emitDirectJump(exp.sinfo, trueblck);
                this.m_emitter.setActiveBlock(trueblck);

                const ttreg = this.m_emitter.generateTmpRegister();
                const truestate = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...cflow.tenvs), exp.flow.conds[i].action, ttreg, infertype);
                
                results.push(truestate);
                rblocks.push([this.m_emitter.getActiveBlockName(), ttreg, truestate.getExpressionResult().valtype]);
                hasfalseflow = false;
            }
            else {
                const trueblck = this.m_emitter.createNewBlock(`Lifexp_${i}true`);
                const falseblck = this.m_emitter.createNewBlock(`Lifexp_${i}false`);
                
                this.m_emitter.emitBoolJump(exp.sinfo, testreg, trueblck, falseblck);
                this.m_emitter.setActiveBlock(trueblck);
                
                const ttreg = this.m_emitter.generateTmpRegister();
                const truestate = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...cflow.tenvs), exp.flow.conds[i].action, ttreg, infertype);
                
                this.m_emitter.setActiveBlock(falseblck);
                
                results.push(truestate);
                rblocks.push([this.m_emitter.getActiveBlockName(), ttreg, truestate.getExpressionResult().valtype]);
                cenv = TypeEnvironment.join(this.m_assembly, ...cflow.fenvs);
            }
        }

        if(hasfalseflow) {
            const ttreg = this.m_emitter.generateTmpRegister();
            const aenv = this.checkExpression(cenv, exp.flow.elseAction as Expression, ttreg, infertype);

            results.push(aenv);
            rblocks.push([this.m_emitter.getActiveBlockName(), ttreg, aenv.getExpressionResult().valtype]);
        }

        this.raiseErrorIf(exp.sinfo, results.some((eev) => eev.hasNormalFlow()), "No feasible path in this conditional expression");

        const fulltype = this.m_assembly.typeUpperBound(results.map((eev) => eev.getExpressionResult().valtype.flowtype));
        for (let i = 0; i < rblocks.length; ++i) {
            const rcb = rblocks[i];
            this.m_emitter.setActiveBlock(rcb[0]);

            const convreg = this.emitInlineConvertIfNeeded(exp.sinfo, rcb[1], rcb[2], fulltype);
            this.m_emitter.emitRegisterStore(exp.sinfo, convreg, trgt, this.m_emitter.registerResolvedTypeReference(fulltype), undefined);

            this.m_emitter.emitDirectJump(exp.sinfo, doneblck);
        }

        this.m_emitter.setActiveBlock(doneblck);
        
        return TypeEnvironment.join(this.m_assembly, ...results.map((eev) => eev.updateResultExpression(fulltype, eev.getExpressionResult().valtype.flowtype)));
    }

    private checkMatchExpression(env: TypeEnvironment, exp: MatchExpression, trgt: MIRRegisterArgument, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment {
        const vreg = this.m_emitter.generateTmpRegister();
        const venv = this.checkExpression(env, exp.sval, vreg, undefined, { refok: refok, orok: false });
        const cvname = venv.getExpressionResult().expvar;

        const doneblck = this.m_emitter.createNewBlock("Lswitchexp_done");
        const matchvar = `$match_#${exp.sinfo.pos}`;
        let cenv = this.checkDeclareSingleVariable(exp.sinfo, venv.popLocalScope(), matchvar, true, venv.getExpressionResult().valtype.flowtype, {etype: ValueType.createUniform(venv.getExpressionResult().valtype.flowtype), etreg: vreg});

        let hasfalseflow = true;
        let results: TypeEnvironment[] = [];
        let rblocks: [string, MIRRegisterArgument, ValueType, string[]][] = [];
        for (let i = 0; i < exp.flow.length && !hasfalseflow; ++i) {
            const nextlabel = this.m_emitter.createNewBlock(`Lswitchexp_${i}next`);
            const actionlabel = this.m_emitter.createNewBlock(`Lswitchexp_${i}action`);

            const test = this.checkMatchGuard(exp.sinfo, true, i, cenv, matchvar, cvname, exp.flow[i].check, nextlabel, actionlabel);

            if(test.tenv === undefined) {
                this.m_emitter.setActiveBlock(actionlabel);
                this.m_emitter.emitDeadBlock(exp.sinfo);

                this.m_emitter.setActiveBlock(nextlabel);
                cenv = test.fenv as TypeEnvironment;
            }
            else if(test.fenv === undefined) {
                //go though action block and skip rest of generation
                this.m_emitter.setActiveBlock(actionlabel);

                const ttreg = this.m_emitter.generateTmpRegister();
                const truestate = this.checkExpression(test.tenv, exp.flow[i].action, ttreg, infertype);

                results.push(truestate);
                rblocks.push([this.m_emitter.getActiveBlockName(), ttreg, truestate.getExpressionResult().valtype, test.newlive]);

                this.m_emitter.setActiveBlock(nextlabel);
                this.m_emitter.emitDeadBlock(exp.sinfo);

                hasfalseflow = false;
            }
            else {
                this.m_emitter.setActiveBlock(actionlabel);

                const ttreg = this.m_emitter.generateTmpRegister();
                const truestate = this.checkExpression(test.tenv, exp.flow[i].action, ttreg, infertype);

                results.push(truestate);
                rblocks.push([this.m_emitter.getActiveBlockName(), ttreg, truestate.getExpressionResult().valtype, test.newlive]);

                this.m_emitter.setActiveBlock(nextlabel);
                cenv = test.fenv as TypeEnvironment;
            }
        }

        if (hasfalseflow) {
            this.m_emitter.emitAbort(exp.sinfo, "exhaustive");
        }
        this.raiseErrorIf(exp.sinfo, results.some((eev) => eev.hasNormalFlow()), "No feasible path in this conditional expression");

        const etype = this.m_assembly.typeUpperBound(results.map((eev) => eev.getExpressionResult().valtype.flowtype));
        for (let i = 0; i < rblocks.length; ++i) {
            const rcb = rblocks[i];
            this.m_emitter.setActiveBlock(rcb[0]);

            const convreg = this.emitInlineConvertIfNeeded(exp.sinfo, rcb[1], rcb[2], etype);
            this.m_emitter.emitRegisterStore(exp.sinfo, convreg, trgt, this.m_emitter.registerResolvedTypeReference(etype), undefined);

            this.m_emitter.localLifetimeEnd(exp.sinfo, matchvar);
            for (let i = 0; i < rcb[3].length; ++i) {
                this.m_emitter.localLifetimeEnd(exp.sinfo, rcb[3][i]);
            }

            this.m_emitter.emitDirectJump(exp.sinfo, doneblck);
        }

        this.m_emitter.setActiveBlock(doneblck);
        
        return TypeEnvironment.join(this.m_assembly, ...results.map((eev) => eev.popLocalScope().setUniformResultExpression(etype)));
    }

    private checkExpression(env: TypeEnvironment, exp: Expression, trgt: MIRRegisterArgument, infertype: ResolvedType | undefined, extraok?: { refok: boolean, orok: boolean }): TypeEnvironment {
        switch (exp.tag) {
            case ExpressionTag.LiteralNoneExpression:
                return this.checkLiteralNoneExpression(env, exp as LiteralNoneExpression, trgt);
            case ExpressionTag.LiteralBoolExpression:
                return this.checkLiteralBoolExpression(env, exp as LiteralBoolExpression, trgt);
            case ExpressionTag.LiteralNumberinoExpression:
                return this.checkLiteralNumberinoExpression(env, exp as LiteralNumberinoExpression, trgt, infertype);
            case ExpressionTag.LiteralIntegralExpression:
                return this.checkLiteralIntegralExpression(env, exp as LiteralIntegralExpression, trgt);
            case ExpressionTag.LiteralFloatPointExpression:
                return this.checkLiteralFloatExpression(env, exp as LiteralFloatPointExpression, trgt);
            case ExpressionTag.LiteralRationalExpression:
                return this.checkLiteralRationalExpression(env, exp as LiteralRationalExpression, trgt);
            case ExpressionTag.LiteralStringExpression:
                return this.checkLiteralStringExpression(env, exp as LiteralStringExpression, trgt);
            case ExpressionTag.LiteralRegexExpression:
                return this.checkLiteralRegexExpression(env, exp as LiteralRegexExpression, trgt);
            case ExpressionTag.LiteralParamerterValueExpression:
                return this.checkLiteralParameterValueExpression(env, exp as LiteralParamerterValueExpression, trgt, infertype);
            case ExpressionTag.LiteralTypedStringExpression:
                return this.checkCreateTypedString(env, exp as LiteralTypedStringExpression, trgt);
            case ExpressionTag.LiteralTypedNumericConstructorExpression:
                return this.checkTypedTypedNumericConstructor(env, exp as LiteralTypedNumericConstructorExpression, trgt);
            case ExpressionTag.LiteralTypedStringConstructorExpression:
                return this.checkDataStringConstructor(env, exp as LiteralTypedStringConstructorExpression, trgt);
            case ExpressionTag.AccessNamespaceConstantExpression:
                return this.checkAccessNamespaceConstant(env, exp as AccessNamespaceConstantExpression, trgt);
            case ExpressionTag.AccessStaticFieldExpression:
                return this.checkAccessStaticField(env, exp as AccessStaticFieldExpression, trgt);
            case ExpressionTag.AccessVariableExpression:
                return this.checkAccessVariable(env, exp as AccessVariableExpression, trgt);
            case ExpressionTag.ConstructorPrimaryExpression:
                return this.checkConstructorPrimary(env, exp as ConstructorPrimaryExpression, trgt);
            case ExpressionTag.ConstructorPrimaryWithFactoryExpression:
                return this.checkConstructorPrimaryWithFactory(env, exp as ConstructorPrimaryWithFactoryExpression, trgt);
            case ExpressionTag.ConstructorTupleExpression:
                return this.checkTupleConstructor(env, exp as ConstructorTupleExpression, trgt, infertype);
            case ExpressionTag.ConstructorRecordExpression:
                return this.checkRecordConstructor(env, exp as ConstructorRecordExpression, trgt, infertype);
            case ExpressionTag.ConstructorEphemeralValueList:
                return this.checkConstructorEphemeralValueList(env, exp as ConstructorEphemeralValueList, trgt, infertype);
            case ExpressionTag.SpecialConstructorExpression:
                return this.checkSpecialConstructorExpression(env, exp as SpecialConstructorExpression, trgt, infertype);
            case ExpressionTag.OfTypeConvertExpression:
                return this.checkOfTypeConvertExpression(env, exp as OfTypeConvertExpression, trgt, (extraok && extraok.refok) || false);
            case ExpressionTag.MapEntryConstructorExpression:
                return this.checkMapEntryConstructorExpression(env, exp as MapEntryConstructorExpression, trgt, infertype);
            case ExpressionTag.NonecheckExpression:
                return this.checkNonecheck(env, exp as NonecheckExpression, trgt, infertype);
            case ExpressionTag.CoalesceExpression:
                return this.checkCoalesce(env, exp as CoalesceExpression, trgt, infertype);
            case ExpressionTag.SelectExpression:
                return this.checkSelect(env, exp as SelectExpression, trgt, (extraok && extraok.refok) || false, infertype);
            case ExpressionTag.ExpOrExpression:
                return this.checkOrExpression(env, exp as ExpOrExpression, trgt, infertype, extraok || { refok: false, orok: false });
            case ExpressionTag.BlockStatementExpression:
                return this.checkBlockExpression(env, exp as BlockStatementExpression, infertype, trgt);
            case ExpressionTag.IfExpression:
                return this.checkIfExpression(env, exp as IfExpression, trgt, (extraok && extraok.refok) || false, infertype);
            case ExpressionTag.MatchExpression:
                return this.checkMatchExpression(env, exp as MatchExpression, trgt, (extraok && extraok.refok) || false, infertype);
            default: {
                let res: TypeEnvironment[] = [];

                if (exp.tag === ExpressionTag.PCodeDirectInvokeExpression) {
                    res = this.checkPCodeDirectInvokeExpression(env, exp as PCodeDirectInvokeExpression, trgt, (extraok && extraok.refok) || false);
                }
                else if (exp.tag === ExpressionTag.PCodeInvokeExpression) {
                    res = this.checkPCodeInvokeExpression(env, exp as PCodeInvokeExpression, trgt, (extraok && extraok.refok) || false);
                }
                else if (exp.tag === ExpressionTag.CallNamespaceFunctionOrOperatorExpression) {
                    res = this.checkCallNamespaceFunctionOrOperatorExpression(env, exp as CallNamespaceFunctionOrOperatorExpression, trgt, (extraok && extraok.refok) || false);
                }
                else if (exp.tag === ExpressionTag.CallStaticFunctionOrOperatorExpression) {
                    res = this.checkCallStaticFunctionOrOperatorExpression(env, exp as CallStaticFunctionOrOperatorExpression, trgt, (extraok && extraok.refok) || false);
                }
                else if (exp.tag === ExpressionTag.PostfixOpExpression) {
                    res = this.checkPostfixExpression(env, exp as PostfixOp, trgt, (extraok && extraok.refok) || false, infertype);
                }
                else if (exp.tag === ExpressionTag.PrefixNotOpExpression) {
                    res = this.checkPrefixNotOp(env, exp as PrefixNotOp, trgt, (extraok && extraok.refok) || false);
                }
                else if (exp.tag === ExpressionTag.BinKeyExpression) {
                    res = this.checkKeyEq(env, exp as BinKeyExpression, trgt);
                }
                else {
                    assert(exp.tag === ExpressionTag.BinLogicExpression);
                    res = this.checkBinLogic(env, exp as BinLogicExpression, trgt, (extraok && extraok.refok) || false);
                }

                return TypeEnvironment.join(this.m_assembly, ...res);
            }
        }
    }

    private checkExpressionMultiFlow(env: TypeEnvironment, exp: Expression, trgt: MIRRegisterArgument, infertype: ResolvedType | undefined, extraok?: { refok: boolean, orok: boolean }): TypeEnvironment[] {
        if (exp.tag === ExpressionTag.PCodeInvokeExpression) {
            return this.checkPCodeInvokeExpression(env, exp as PCodeInvokeExpression, trgt, (extraok && extraok.refok) || false);
        }
        else if (exp.tag === ExpressionTag.CallNamespaceFunctionOrOperatorExpression) {
            return this.checkCallNamespaceFunctionOrOperatorExpression(env, exp as CallNamespaceFunctionOrOperatorExpression, trgt, (extraok && extraok.refok) || false);
        }
        else if (exp.tag === ExpressionTag.CallStaticFunctionOrOperatorExpression) {
            return this.checkCallStaticFunctionOrOperatorExpression(env, exp as CallStaticFunctionOrOperatorExpression, trgt, (extraok && extraok.refok) || false);
        }
        else if (exp.tag === ExpressionTag.PostfixOpExpression) {
            return this.checkPostfixExpression(env, exp as PostfixOp, trgt, (extraok && extraok.refok) || false, infertype);
        }
        else if (exp.tag === ExpressionTag.PrefixNotOpExpression) {
            return this.checkPrefixNotOp(env, exp as PrefixNotOp, trgt, (extraok && extraok.refok) || false);
        }
        else if (exp.tag === ExpressionTag.BinKeyExpression) {
            return this.checkKeyEq(env, exp as BinKeyExpression, trgt);
        }
        else if (exp.tag  === ExpressionTag.BinLogicExpression) {
            return this.checkBinLogic(env, exp as BinLogicExpression, trgt, (extraok && extraok.refok) || false);
        }
        else {
            return [this.checkExpression(env, exp, trgt, infertype, extraok)];
        }
    }

    private checkDeclareSingleVariable(sinfo: SourceInfo, env: TypeEnvironment, vname: string, isConst: boolean, decltype: TypeSignature, venv: { etype: ValueType, etreg: MIRRegisterArgument } | undefined): TypeEnvironment {
        this.raiseErrorIf(sinfo, env.isVarNameDefined(vname), "Cannot shadow previous definition");

        this.raiseErrorIf(sinfo, venv === undefined && isConst, "Must define const var at declaration site");
        this.raiseErrorIf(sinfo, venv === undefined && decltype instanceof AutoTypeSignature, "Must define auto typed var at declaration site");

        const vtype = (decltype instanceof AutoTypeSignature) ? (venv as { etype: ValueType, etreg: MIRRegisterArgument }).etype : ValueType.createUniform(this.resolveAndEnsureTypeOnly(sinfo, decltype, env.terms));
        this.raiseErrorIf(sinfo, venv !== undefined && !this.m_assembly.subtypeOf(venv.etype.flowtype, vtype.layout), "Expression is not of declared type");

        const mirvtype = this.m_emitter.registerResolvedTypeReference(vtype.layout);
        this.m_emitter.localLifetimeStart(sinfo, vname, mirvtype);

        if (venv !== undefined) {
            const convreg = this.emitInlineConvertIfNeeded(sinfo, venv.etreg, venv.etype, vtype.layout);
            this.m_emitter.emitRegisterStore(sinfo, convreg, new MIRRegisterArgument(vname), mirvtype, undefined);
        }

        return env.addVar(vname, isConst, vtype.layout, venv !== undefined, venv !== undefined ? venv.etype.flowtype : vtype.flowtype);
    }

    private checkVariableDeclarationStatement(env: TypeEnvironment, stmt: VariableDeclarationStatement): TypeEnvironment {
        const infertype = stmt.vtype instanceof AutoTypeSignature ? undefined : this.resolveAndEnsureTypeOnly(stmt.sinfo, stmt.vtype, env.terms);

        const etreg = this.m_emitter.generateTmpRegister();
        const venv = stmt.exp !== undefined ? this.checkExpression(env, stmt.exp, etreg, infertype, { refok: true, orok: true }) : undefined;

        if(venv !== undefined) {
            this.raiseErrorIf(stmt.sinfo, venv.getExpressionResult().valtype.flowtype.options.some((opt) => opt instanceof ResolvedEphemeralListType), "Cannot store Ephemeral value lists in variables");
        }

        const vv = venv !== undefined ? { etype: venv.getExpressionResult().valtype, etreg: etreg } : undefined;
        return this.checkDeclareSingleVariable(stmt.sinfo, venv || env, stmt.name, stmt.isConst, stmt.vtype, vv);
    }

    private checkVariablePackDeclarationStatement(env: TypeEnvironment, stmt: VariablePackDeclarationStatement): TypeEnvironment {
        let cenv = env;
        if (stmt.exp === undefined) {
            for (let i = 0; i < stmt.vars.length; ++i) {
                cenv = this.checkDeclareSingleVariable(stmt.sinfo, env, stmt.vars[i].name, stmt.isConst, stmt.vars[i].vtype, undefined);
            }
        }
        else {
            if (stmt.exp.length === 1) {
                let infertypes = stmt.vars.map((vds) => vds.vtype instanceof AutoTypeSignature ? undefined : this.resolveAndEnsureTypeOnly(stmt.sinfo, vds.vtype, env.terms));
                let infertype = infertypes.includes(undefined) ? undefined : ResolvedType.createSingle(ResolvedEphemeralListType.create(infertypes as ResolvedType[]));

                const etreg = this.m_emitter.generateTmpRegister();
                cenv = this.checkExpression(env, stmt.exp[0], etreg, infertype, { refok: true, orok: true });
                const eetype = cenv.getExpressionResult().valtype.flowtype;

                this.raiseErrorIf(stmt.sinfo, eetype.options.length !== 1 || !(eetype.options[0] instanceof ResolvedEphemeralListType), "Expected Ephemeral List for multi assign");

                const elt = eetype.options[0] as ResolvedEphemeralListType;
                this.raiseErrorIf(stmt.sinfo, stmt.vars.length !== elt.types.length, "Missing initializers for variables");

                //check if all the assignments are conversion free -- if so we can do a multi-load
                const convertfree = stmt.vars.every((v, i) => {
                    const decltype = this.resolveAndEnsureTypeOnly(stmt.sinfo, v.vtype, cenv.terms);
                    const exptype = elt.types[i];

                    return decltype.isSameType(exptype);
                });

                if(convertfree) {
                    this.raiseErrorIf(stmt.sinfo, stmt.vars.some((vv) => env.isVarNameDefined(vv.name), "Cannot shadow previous definition"));

                    let trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRType }[] = [];
                    for (let i = 0; i < stmt.vars.length; ++i) {
                        const decltype = this.resolveAndEnsureTypeOnly(stmt.sinfo, stmt.vars[i].vtype, env.terms);
                        const mirvtype = this.m_emitter.registerResolvedTypeReference(decltype);
                        this.m_emitter.localLifetimeStart(stmt.sinfo, stmt.vars[i].name, mirvtype);

                        trgts.push({ pos: i, into: new MIRRegisterArgument(stmt.vars[i].name), oftype: mirvtype });
                    }

                    this.m_emitter.emitMultiLoadFromEpehmeralList(stmt.sinfo, etreg, this.m_emitter.registerResolvedTypeReference(eetype), trgts);

                    cenv = cenv.multiVarUpdate(stmt.vars.map((vv) => [stmt.isConst, vv.name, this.resolveAndEnsureTypeOnly(stmt.sinfo, vv.vtype, env.terms), [], this.resolveAndEnsureTypeOnly(stmt.sinfo, vv.vtype, env.terms)]), []);
                }
                else {
                    for (let i = 0; i < stmt.vars.length; ++i) {
                        const tlreg = this.m_emitter.generateTmpRegister();
                        this.m_emitter.emitLoadFromEpehmeralList(stmt.sinfo, etreg, this.m_emitter.registerResolvedTypeReference(elt.types[i]), i, this.m_emitter.registerResolvedTypeReference(eetype), tlreg);

                        cenv = this.checkDeclareSingleVariable(stmt.sinfo, cenv, stmt.vars[i].name, stmt.isConst, stmt.vars[i].vtype, { etype: ValueType.createUniform(elt.types[i]), etreg: tlreg });
                    }
                }
            }
            else {
                this.raiseErrorIf(stmt.sinfo, stmt.vars.length !== stmt.exp.length, "Missing initializers for variables");

                for (let i = 0; i < stmt.vars.length; ++i) {
                    const infertype = stmt.vars[i].vtype instanceof AutoTypeSignature ? undefined : this.resolveAndEnsureTypeOnly(stmt.sinfo, stmt.vars[i].vtype, env.terms);

                    const etreg = this.m_emitter.generateTmpRegister();
                    const venv = this.checkExpression(env, stmt.exp[i], etreg, infertype);

                    cenv = this.checkDeclareSingleVariable(stmt.sinfo, venv, stmt.vars[i].name, stmt.isConst, stmt.vars[i].vtype, { etype: venv.getExpressionResult().valtype, etreg: etreg });
                }
            }
        }

        return cenv;
    }

    private checkAssignSingleVariable(sinfo: SourceInfo, env: TypeEnvironment, vname: string, etype: ValueType, etreg: MIRRegisterArgument): TypeEnvironment {
        const vinfo = env.lookupVar(vname);
        this.raiseErrorIf(sinfo, vinfo === null, "Variable was not previously defined");
        this.raiseErrorIf(sinfo, (vinfo as VarInfo).isConst, "Variable defined as const");

        this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(etype.flowtype, (vinfo as VarInfo).declaredType), "Assign value is not subtype of declared variable type");

        const convreg = this.emitInlineConvertIfNeeded(sinfo, etreg, etype, (vinfo as VarInfo).declaredType) as MIRRegisterArgument;
        this.m_emitter.emitRegisterStore(sinfo, convreg, new MIRRegisterArgument(vname), this.m_emitter.registerResolvedTypeReference((vinfo as VarInfo).declaredType), undefined);

        return env.setVar(vname, etype.flowtype);
    }

    private checkVariableAssignmentStatement(env: TypeEnvironment, stmt: VariableAssignmentStatement): TypeEnvironment {
        const vinfo = env.lookupVar(stmt.name);
        this.raiseErrorIf(stmt.sinfo, vinfo === undefined, "Variable was not previously defined");

        const infertype = (vinfo as VarInfo).declaredType;
        const etreg = this.m_emitter.generateTmpRegister();
        const venv = this.checkExpression(env, stmt.exp, etreg, infertype, { refok: true, orok: true });
       
        if(venv !== undefined) {
            this.raiseErrorIf(stmt.sinfo, venv.getExpressionResult().valtype.flowtype.options.some((opt) => opt instanceof ResolvedEphemeralListType), "Cannot store Ephemeral value lists in variables");
        }

        return this.checkAssignSingleVariable(stmt.sinfo, venv, stmt.name, venv.getExpressionResult().valtype, etreg);
    }

    private checkVariablePackAssignmentStatement(env: TypeEnvironment, stmt: VariablePackAssignmentStatement): TypeEnvironment {
        let cenv = env;

        if (stmt.exp.length === 1) {
            let infertypes = stmt.names.map((vn) => env.lookupVar(vn));
            this.raiseErrorIf(stmt.sinfo, infertypes.includes(null), "Variable was not previously defined");
            let infertype = ResolvedType.createSingle(ResolvedEphemeralListType.create(infertypes.map((vi) => (vi as VarInfo).declaredType)));

            const etreg = this.m_emitter.generateTmpRegister();
            cenv = this.checkExpression(env, stmt.exp[0], etreg, infertype, { refok: true, orok: true });
            const eetype = cenv.getExpressionResult().valtype.flowtype;

            this.raiseErrorIf(stmt.sinfo, eetype.options.length !== 1 || !(eetype.options[0] instanceof ResolvedEphemeralListType), "Expected Ephemeral List for multi assign");

            const elt = eetype.options[0] as ResolvedEphemeralListType;
            this.raiseErrorIf(stmt.sinfo, stmt.names.length !== elt.types.length, "Missing initializers for variables");

            //check if all the assignments are conversion free -- if so we can do a multi-load
            const convertfree = stmt.names.every((v, i) => {
                const decltype = (env.lookupVar(v) as VarInfo).declaredType;
                const exptype = elt.types[i];

                return decltype.isSameType(exptype);
            });

            if (convertfree) {
                this.raiseErrorIf(stmt.sinfo, stmt.names.some((vv) => !env.isVarNameDefined(vv), "Variable was not previously defined"));
                this.raiseErrorIf(stmt.sinfo, stmt.names.some((vv) => (env.lookupVar(vv) as VarInfo).isConst, "Variable is const"));

                let trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRType }[] = [];
                for (let i = 0; i < stmt.names.length; ++i) {
                    const decltype = (env.lookupVar(stmt.names[i]) as VarInfo).declaredType;
                    const mirvtype = this.m_emitter.registerResolvedTypeReference(decltype);

                    const vstore = new MIRRegisterArgument(stmt.names[i]);
                    trgts.push({ pos: i, into: vstore, oftype: mirvtype });
                }

                this.m_emitter.emitMultiLoadFromEpehmeralList(stmt.sinfo, etreg, this.m_emitter.registerResolvedTypeReference(eetype), trgts);

                cenv = cenv.multiVarUpdate([], stmt.names.map((vv) => [vv, [], (env.lookupVar(vv) as VarInfo).declaredType]));
            }
            else {
                for (let i = 0; i < stmt.names.length; ++i) {
                    const tlreg = this.m_emitter.generateTmpRegister();
                    this.m_emitter.emitLoadFromEpehmeralList(stmt.sinfo, etreg, this.m_emitter.registerResolvedTypeReference(elt.types[i]), i, this.m_emitter.registerResolvedTypeReference(eetype), tlreg);

                    cenv = this.checkAssignSingleVariable(stmt.sinfo, cenv, stmt.names[i], ValueType.createUniform(elt.types[i]), etreg);
                }
            }
        }
        else {
            this.raiseErrorIf(stmt.sinfo, stmt.names.length !== stmt.exp.length, "Missing initializers for variables");

            for (let i = 0; i < stmt.names.length; ++i) {
                const vinfo = env.lookupVar(stmt.names[i]);
                this.raiseErrorIf(stmt.sinfo, vinfo === null, "Variable was not previously defined");

                const infertype = (vinfo as VarInfo).declaredType;

                const etreg = this.m_emitter.generateTmpRegister();
                const venv = this.checkExpression(env, stmt.exp[i], etreg, infertype);

                cenv = this.checkAssignSingleVariable(stmt.sinfo, cenv, stmt.names[i], venv.getExpressionResult().valtype, etreg);
            }
        }

        return cenv;
    }

    private checkSimpleStructuredAssignment(sinfo: SourceInfo, env: TypeEnvironment, etype: ResolvedType,
        assign: StructuredAssignment, isoptional: boolean, cpath: StructuredAssignmentPathStep | undefined,
        allDeclared: [string, ResolvedType, StructuredAssignmentPathStep | undefined, ResolvedType][],
        allAssigned: [string, StructuredAssignmentPathStep | undefined, ResolvedType][],
        allChecks: [StructuredAssignmentPathStep | undefined, StructuredAssignmentCheck][]): boolean 
    {
        if(isoptional && !(assign instanceof IgnoreTermStructuredAssignment && assign.isOptional)) {
            return false;
        }

        if (assign instanceof IgnoreTermStructuredAssignment) {
            const itype = this.resolveAndEnsureTypeOnly(sinfo, assign.termType, env.terms);

            const optt = this.m_assembly.splitTypes(etype, itype);
            if (optt.tp.isEmptyType()) {
                return false;
            }
            if (!optt.fp.isEmptyType()) {
                allChecks.push([cpath, createOfTypeCheck(etype, itype, isoptional)]);
            }

            return true;
        }
        else if (assign instanceof ConstValueStructuredAssignment) {
            allChecks.push([cpath, createTerminalEqCheck(etype, assign.constValue)]);

            return true;
        }
        else if (assign instanceof VariableDeclarationStructuredAssignment) {
            this.raiseErrorIf(sinfo, allDeclared.find((decl) => decl[0] === assign.vname) !== undefined || allAssigned.find((asgn) => asgn[0] === assign.vname) !== undefined, "Duplicate variables used in structured assign");

            const vtype = (assign.vtype instanceof AutoTypeSignature) ? etype : this.resolveAndEnsureTypeOnly(sinfo, assign.vtype, env.terms);
            allDeclared.push([assign.vname, vtype, cpath, etype]);

            const optt = this.m_assembly.splitTypes(etype, vtype);
            if (optt.tp.isEmptyType()) {
                return false;
            }
            if (!optt.fp.isEmptyType()) {
                allChecks.push([cpath, createOfTypeCheck(etype, vtype, false)]);
            }

            return true;
        }
        else if (assign instanceof VariableAssignmentStructuredAssignment) {
            this.raiseErrorIf(sinfo, allDeclared.find((decl) => decl[0] === assign.vname) !== undefined || allAssigned.find((asgn) => asgn[0] === assign.vname) !== undefined, "Duplicate variables used in structured assign");

            const vinfo = env.lookupVar(assign.vname);
            this.raiseErrorIf(sinfo, vinfo === undefined, "Variable was not previously defined");
            this.raiseErrorIf(sinfo, (vinfo as VarInfo).isConst, "Variable defined as const");

            allAssigned.push([assign.vname, cpath, etype]);

            const optt = this.m_assembly.splitTypes(etype, (vinfo as VarInfo).declaredType);
            if (optt.tp.isEmptyType()) {
                return false;
            }
            if (!optt.fp.isEmptyType()) {
                allChecks.push([cpath, createOfTypeCheck(etype, (vinfo as VarInfo).declaredType, false)]);
            }

            return true;
        }
        else {
            assert(false);
            return false;
        }
    }

    private checkStructuredMatch(sinfo: SourceInfo, env: TypeEnvironment, etype: ResolvedType,
        assign: StructuredAssignment,
        allDeclared: [string, ResolvedType, StructuredAssignmentPathStep | undefined, ResolvedType][],
        allAssigned: [string, StructuredAssignmentPathStep | undefined, ResolvedType][],
        allChecks: [StructuredAssignmentPathStep | undefined, StructuredAssignmentCheck][]): boolean {
        if (assign instanceof ValueListStructuredAssignment) {
            if (etype.options.length !== 1 || !(etype.options[0] instanceof ResolvedEphemeralListType)) {
                return false;
            }

            const eltype = etype.options[0] as ResolvedEphemeralListType;
            if (eltype.types.length !== assign.assigns.length) {
                return false;
            }

            let chksok = true;
            for (let i = 0; i < assign.assigns.length; ++i) {
                const step = createEphemeralStructuredAssignmentPathStep(etype, eltype.types[i], i);
                const ok = this.checkSimpleStructuredAssignment(sinfo, env, eltype.types[i], assign.assigns[i], false, step, allDeclared, allAssigned, allChecks);

                chksok = chksok && ok;
            }

            return chksok;
        }
        else if (assign instanceof NominalStructuredAssignment) {
            const ntype = this.resolveAndEnsureTypeOnly(sinfo, assign.atype, env.terms);
            if (ntype.options.length === 1 && ntype.options[0] instanceof ResolvedEntityAtomType) {
                const isstruct = OOPTypeDecl.attributeSetContains("struct", (ntype.options[0] as ResolvedEntityAtomType).object.attributes);
                this.raiseErrorIf(sinfo, isstruct !== assign.isvalue, "Mismatch in value type of Entity and match");
            }
            else {
                this.raiseErrorIf(sinfo, ntype.options.length !== 1 || !(ntype.options[0] instanceof ResolvedConceptAtomType));
                const anystructcpt = (ntype.options[0] as ResolvedConceptAtomType).conceptTypes.some((cpt) => OOPTypeDecl.attributeSetContains("struct", cpt.concept.attributes));
                this.raiseErrorIf(sinfo, anystructcpt !== assign.isvalue, "Mismatch in value type of Concept and match");
            }

            const optt = this.m_assembly.splitTypes(etype, ntype);
            if (optt.tp.isEmptyType()) {
                return false;
            }
            if (!optt.fp.isEmptyType()) {
                allChecks.push([undefined, createOfTypeCheck(etype, ntype, false)]);
            }

            const fieldkeys = assign.assigns.map((asn) => {
                const tryfinfo = this.m_assembly.tryGetFieldUniqueDeclFromType(ntype, asn[0]);
                this.raiseErrorIf(sinfo, tryfinfo === undefined, "Field name is not defined (or is multiply) defined");

                const finfo = tryfinfo as OOMemberLookupInfo<MemberFieldDecl>;
                const ffdecl = finfo.decl;
                const ftype = this.resolveAndEnsureTypeOnly(sinfo, ffdecl.declaredType, finfo.binds);
                return { key: MIRKeyGenerator.generateFieldKey(ftype, asn[0]), ftype: ftype };
            });

            const ptype = ntype.options[0];
            let fields = new Set<string>();
            if (ptype instanceof ResolvedEntityAtomType) {
                const fmap = this.m_assembly.getAllOOFieldsLayout(ptype.object, ptype.binds);
                fmap.forEach((v, k) => fields.add(k));
            }
            else {
                (ptype as ResolvedConceptAtomType).conceptTypes.forEach((concept) => {
                    const fmap = this.m_assembly.getAllOOFieldsLayout(concept.concept, concept.binds);
                    fmap.forEach((v, k) => fields.add(k));
                });
            }
            this.raiseErrorIf(sinfo, fields.size !== assign.assigns.length, "Mismatch in field counts and assignment");

            let chkok = true;
            for (let i = 0; i < assign.assigns.length; ++i) {
                const ttype = fieldkeys[i].ftype;
                const step = createNominalStructuredAssignmentPathStep(etype, ttype, fieldkeys[i].key);
                const ok = this.checkSimpleStructuredAssignment(sinfo, env, ttype, assign.assigns[i][1], false, step, allDeclared, allAssigned, allChecks);

                chkok = chkok && ok;
            }

            return chkok;
        }
        else if (assign instanceof TupleStructuredAssignment) {
            let seenopt = false;
            let maxreq = 0;
            for (let i = 0; i < assign.assigns.length; ++i) {
                const asgn = assign.assigns[i];
                if(asgn instanceof IgnoreTermStructuredAssignment && asgn.isOptional) {
                    seenopt = true;
                }
                else {
                    this.raiseErrorIf(sinfo, seenopt, "Cannot have required assign after an optional assign");
                    maxreq = i;
                }
            }
            const ttype = this.m_assembly.restrictTupleBaseOnMatch(etype, assign.isvalue, maxreq, assign.assigns.length);
            
            let chkok = true;
            for (let i = 0; i < assign.assigns.length; ++i) {
                const asgn = assign.assigns[i];
                const tuphasidx = this.getInfoForHasIndex(sinfo, ttype, i);
                assert(tuphasidx !== "no", "Should not happen by construction");

                let ok = true;
                if (tuphasidx === "maybe") {
                    const idxtype = this.getInfoForLoadFromSafeIndexOnly(sinfo, ttype, i);
                    const step = createTupleStructuredAssignmentPathStep(ttype, idxtype, i);

                    ok = this.checkSimpleStructuredAssignment(sinfo, env, idxtype, asgn, true, step, allDeclared, allAssigned, allChecks);
                }
                else {
                    const idxtype = this.getInfoForLoadFromSafeIndex(sinfo, ttype, i);
                    const step = createTupleStructuredAssignmentPathStep(ttype, idxtype, i);

                    ok = this.checkSimpleStructuredAssignment(sinfo, env, idxtype, asgn, false, step, allDeclared, allAssigned, allChecks);
                }

                chkok = chkok && ok;
            }

            if (!etype.isSameType(ttype)) {
                allChecks.push([undefined, createOfTypeCheck(etype, ttype, false)]);
            }

            return chkok;
        }
        else if (assign instanceof RecordStructuredAssignment) {
            let optNames = new Set<string>();
            let reqNames = new Set<string>();
            for (let i = 0; i < assign.assigns.length; ++i) {
                const asgn = assign.assigns[i];
                if(asgn[1] instanceof IgnoreTermStructuredAssignment && asgn[1].isOptional) {
                    optNames.add(asgn[0]);
                }
                else {
                    reqNames.add(asgn[0]);
                }
            }
            const ttype = this.m_assembly.restrictRecordBaseOnMatch(etype, assign.isvalue, reqNames, optNames);

            let chkok = true;
            for (let i = 0; i < assign.assigns.length; ++i) {
                const asgn = assign.assigns[i];
                const rechasprop = this.getInfoForHasProperty(sinfo, ttype, asgn[0]);
                assert(rechasprop !== "no", "Should be impossible by construction");

                let ok = true;
                if (rechasprop === "maybe") {
                    const ptype = this.getInfoForLoadFromSafePropertyOnly(sinfo, ttype, asgn[0]);
                    const step = createRecordStructuredAssignmentPathStep(ttype, ptype, asgn[0]);

                    ok = this.checkSimpleStructuredAssignment(sinfo, env, ptype, assign.assigns[i], true, step, allDeclared, allAssigned, allChecks);
                }
                else {
                    const ptype = this.getInfoForLoadFromSafeProperty(sinfo, ttype, asgn[0]);
                    const step = createRecordStructuredAssignmentPathStep(ttype, ptype, asgn[0]);

                    ok = this.checkSimpleStructuredAssignment(sinfo, env, ptype, assign.assigns[i], false, step, allDeclared, allAssigned, allChecks);
                }

                chkok = chkok && ok;
            }

            if (!etype.isSameType(ttype)) {
                allChecks.push([undefined, createOfTypeCheck(etype, ttype, false)]);
            }

            return chkok;
        }
        else {
            return this.checkSimpleStructuredAssignment(sinfo, env, etype, assign, false, undefined, allDeclared, allAssigned, allChecks);
        }
    }

    private generateRootReg(sinfo: SourceInfo, path: StructuredAssignmentPathStep | undefined, ereg: MIRRegisterArgument, etype: ResolvedType): [MIRRegisterArgument, ResolvedType] {
        if (path === undefined) {
                return [ereg, etype];
        }
        else {
            const nreg = this.m_emitter.generateTmpRegister();
            const fromtype = this.m_emitter.registerResolvedTypeReference(path.fromtype);
            const loadtype = this.m_emitter.registerResolvedTypeReference(path.t);

            if (path.step === "tuple") {
                this.m_emitter.emitLoadTupleIndex(sinfo, ereg, fromtype, fromtype, path.ival, path.fromtype.isUniqueTupleTargetType(), loadtype, nreg);
            }
            else if (path.step === "record") {
                this.m_emitter.emitLoadProperty(sinfo, ereg, fromtype, fromtype, path.nval, path.fromtype.isUniqueRecordTargetType(), loadtype, nreg);
            }
            else if (path.step === "nominal") {
                this.m_emitter.emitLoadField(sinfo, ereg, fromtype, fromtype, path.nval, path.fromtype.isUniqueCallTargetType(), loadtype, nreg);
            }
            else {
                this.m_emitter.emitLoadFromEpehmeralList(sinfo, ereg, fromtype, path.ival, loadtype, nreg);
            }

            return [nreg, path.t];
        }
    }

    private generateRootRegOptional(sinfo: SourceInfo, path: StructuredAssignmentPathStep, ereg: MIRRegisterArgument): [MIRRegisterArgument, MIRRegisterArgument, ResolvedType] {
            const nreg = this.m_emitter.generateTmpRegister();
            const greg = this.m_emitter.generateTmpRegister();
            const fromtype = this.m_emitter.registerResolvedTypeReference(path.fromtype);
            const loadtype = this.m_emitter.registerResolvedTypeReference(path.t);

            if (path.step === "tuple") {
                this.m_emitter.emitLoadTupleIndexSetGuard(sinfo, ereg, fromtype, fromtype, path.ival, path.fromtype.isUniqueTupleTargetType(), loadtype, nreg, new MIRArgGuard(greg));
            }
            else {
                this.m_emitter.emitLoadRecordPropertySetGuard(sinfo, ereg, fromtype, fromtype, path.nval, path.fromtype.isUniqueRecordTargetType(), loadtype, nreg, new MIRArgGuard(greg));
            }

            return [nreg, greg, path.t];
    }

    private generateMatchTestOps(env: TypeEnvironment, sinfo: SourceInfo, ereg: MIRRegisterArgument, etype: ValueType, matchvname: string, cvname: string | undefined, allChecks: [StructuredAssignmentPathStep, StructuredAssignmentCheck][], reqassigns: StructuredAssignmentPathStep[], assignregs: MIRRegisterArgument[], mreg: MIRRegisterArgument, matchfail: string): { okenvs: TypeEnvironment[], failenvs: TypeEnvironment[] } {
        //apply the root type of operation if there is one
        const roottc = allChecks.find((vv) => vv[0] === undefined && vv[1].action === "typechk");
        let oketype = etype;
        let okereg = ereg;
        let okenvs = [env];
        let failenvs = [env];
        if(roottc !== undefined) {
            const roottest = this.m_emitter.generateTmpRegister();
            const nblock = this.m_emitter.createNewBlock("postroottest");

            this.m_emitter.emitTypeOf(sinfo, roottest, this.m_emitter.registerResolvedTypeReference(roottc[1].oftype as ResolvedType), ereg, this.m_emitter.registerResolvedTypeReference(etype.layout), this.m_emitter.registerResolvedTypeReference(etype.flowtype), undefined);
            this.m_emitter.emitBoolJump(sinfo, roottest, nblock, matchfail);
            this.m_emitter.setActiveBlock(nblock);

            const splits = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, roottc[1].oftype as ResolvedType, [env]);
            okenvs = splits.tenvs;
            failenvs = splits.fenvs;

            if (okenvs.length !== 0) {
                oketype = ValueType.createUniform(roottc[1].oftype as ResolvedType);
                okereg = this.emitInlineConvertIfNeeded(sinfo, ereg, etype, oketype.flowtype);
            }

            okenvs = okenvs.map((eev) => eev.inferVarsOfType(eev.getExpressionResult().valtype.flowtype, matchvname, cvname).setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True));
            failenvs = failenvs.map((eev) => eev.inferVarsOfType(eev.getExpressionResult().valtype.flowtype, matchvname, cvname).setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False));
        }

        if (okenvs.length === 0) {
            return { okenvs: [], failenvs: failenvs };
        }
        else {
            //apply every (conditional) type check and equality check
            const elemtc = allChecks.filter((vv) => vv[0] !== undefined);
            let results: MIRRegisterArgument[] = [];
            for (let i = 0; i < elemtc.length; ++i) {
                const tcc = elemtc[i];
                if (tcc[1].isoptional) {
                    const [treg, greg, ttype] = this.generateRootRegOptional(sinfo, tcc[0], okereg);

                    const ncr = this.m_emitter.generateTmpRegister();
                    results.push(ncr);
                    this.m_emitter.emitTypeOf(sinfo, ncr, this.m_emitter.registerResolvedTypeReference(tcc[1].oftype as ResolvedType), treg, this.m_emitter.registerResolvedTypeReference(ttype), this.m_emitter.registerResolvedTypeReference(ttype), new MIRStatmentGuard(new MIRArgGuard(greg), "defaultonfalse", new MIRConstantFalse()));
                }
                else {
                    const [treg, ttype] = this.generateRootReg(sinfo, tcc[0], okereg, oketype.flowtype);

                    const assignpos = reqassigns.findIndex((pth) => pth.ival === tcc[0].ival && pth.nval === tcc[0].nval);
                    if (assignpos !== -1) {
                        assignregs[assignpos] = treg;
                    }

                    const ncr = this.m_emitter.generateTmpRegister();
                    results.push(ncr);

                    if (tcc[1].action === "typechk") {
                        this.m_emitter.emitTypeOf(sinfo, ncr, this.m_emitter.registerResolvedTypeReference(tcc[1].oftype as ResolvedType), treg, this.m_emitter.registerResolvedTypeReference(ttype), this.m_emitter.registerResolvedTypeReference(ttype), undefined);
                    }
                    else {
                        let chkreg = this.m_emitter.generateTmpRegister();
                        let chktype = ValueType.createUniform(this.m_assembly.getSpecialNoneType());

                        const cev = (tcc[1].eqvalue as ConstantExpressionValue);
                        const cexp = this.m_assembly.compileTimeReduceConstantExpression(cev.exp, env.terms, undefined);
                        if (cexp !== undefined) {
                            chktype = this.checkExpression(env, cexp, chkreg, undefined).getExpressionResult().valtype;
                        }
                        else {
                            this.raiseErrorIf(sinfo, cev.captured.size !== 0, "Invalid use of local variables in constant expression");
                            chktype = this.doConstantExpressionTypeInferNoEmit(env, this.m_file, cev.exp, new Map<string, VarInfo>());

                            const gkey = this.m_emitter.registerConstExpr(this.m_file, cev, env.terms, chktype.flowtype);
                            this.m_emitter.emitRegisterStore(cev.exp.sinfo, new MIRGlobalVariable(gkey), chkreg, this.m_emitter.registerResolvedTypeReference(chktype.flowtype), undefined);
                        }

                        this.raiseErrorIf(sinfo, !chktype.flowtype.isGroundedType() || !this.m_assembly.subtypeOf(chktype.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()), "Invalid constant");
                        this.raiseErrorIf(sinfo, !ttype.isGroundedType() || !this.m_assembly.subtypeOf(ttype, this.m_assembly.getSpecialKeyTypeConceptType()), "Invalid type for constant comparision");

                        this.m_emitter.emitBinKeyEq(sinfo, this.m_emitter.registerResolvedTypeReference(chktype.layout), this.m_emitter.registerResolvedTypeReference(chktype.flowtype), chkreg, this.m_emitter.registerResolvedTypeReference(ttype), this.m_emitter.registerResolvedTypeReference(ttype), treg, ncr);
                    }
                }
            }

            this.m_emitter.emitAllTrue(sinfo, results, mreg);
            return { okenvs: okenvs, failenvs: failenvs };
        }
    }

    private checkStructuredVariableAssignmentStatement(env: TypeEnvironment, stmt: StructuredVariableAssignmentStatement): TypeEnvironment {
        const expreg = this.m_emitter.generateTmpRegister();
        const eenv = this.checkExpression(env, stmt.exp, expreg, undefined, { refok: true, orok: true });

        let allDeclared: [string, ResolvedType, StructuredAssignmentPathStep, ResolvedType][] = [];
        let allAssigned: [string, StructuredAssignmentPathStep, ResolvedType][] = [];
        let allChecks: [StructuredAssignmentPathStep, StructuredAssignmentCheck][] = [];
        const ok = this.checkStructuredMatch(stmt.sinfo, eenv, eenv.getExpressionResult().valtype.flowtype, stmt.assign, allDeclared, allAssigned, allChecks);

        this.raiseErrorIf(stmt.sinfo, !ok || allChecks.length !== 0, "Structured assignment may fail");

        let fenv = eenv;
        for (let i = 0; i < allDeclared.length; ++i) {
            const declv = allDeclared[i];
            const etreg = this.generateRootReg(stmt.sinfo, declv[2], expreg, eenv.getExpressionResult().valtype.flowtype)[0];
            fenv = this.checkDeclareSingleVariable(stmt.sinfo, fenv, declv[0], stmt.isConst, declv[1], { etype: ValueType.createUniform(declv[3]), etreg: etreg as MIRRegisterArgument });
        }

        for (let i = 0; i < allAssigned.length; ++i) {
            const assignv = allAssigned[i];

            const etreg = this.generateRootReg(stmt.sinfo, assignv[1], expreg, eenv.getExpressionResult().valtype.flowtype)[0];
            fenv = this.checkAssignSingleVariable(stmt.sinfo, fenv, assignv[0], ValueType.createUniform(assignv[2]), etreg as MIRRegisterArgument);
        }

        return fenv;
    }

    private checkIfElseStatement(env: TypeEnvironment, stmt: IfElseStatement): TypeEnvironment {
        this.raiseErrorIf(stmt.sinfo, stmt.flow.conds.length > 1 && stmt.flow.elseAction === undefined, "Must terminate elseifs with an else clause");

        const doneblck = this.m_emitter.createNewBlock("Lifstmt_done");

        let cenv = env;
        let hasfalseflow = true;
        let results: TypeEnvironment[] = [];
        for (let i = 0; i < stmt.flow.conds.length && hasfalseflow; ++i) {
            const testreg = this.m_emitter.generateTmpRegister();
            const test = this.checkExpressionMultiFlow(cenv, stmt.flow.conds[i].cond, testreg, undefined, i === 0 ? { refok: true, orok: false } : undefined);
            this.raiseErrorIf(stmt.sinfo, !test.every((eev) => this.m_assembly.subtypeOf(eev.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "If test expression must return a Bool");

            const cflow = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, test);
            
            if (cflow.tenvs.length === 0) {
                //can just keep generating tests in striaght line
                cenv = TypeEnvironment.join(this.m_assembly, ...cflow.fenvs);
            }
            else if (cflow.fenvs.length === 0) {
                //go though true block (without jump) and then skip else
                const trueblck = this.m_emitter.createNewBlock(`Lifstmt_${i}true`);
                this.m_emitter.emitDirectJump(stmt.sinfo, trueblck);
                this.m_emitter.setActiveBlock(trueblck);

                const truestate = this.checkStatement(TypeEnvironment.join(this.m_assembly, ...cflow.tenvs), stmt.flow.conds[i].action);
                if(truestate.hasNormalFlow()) {
                    this.m_emitter.emitDirectJump(stmt.sinfo, doneblck);
                }

                results.push(truestate);
                hasfalseflow = false;
            }
            else {
                const trueblck = this.m_emitter.createNewBlock(`Lifstmt_${i}true`);
                const falseblck = this.m_emitter.createNewBlock(`Lifstmt_${i}false`);
                
                this.m_emitter.emitBoolJump(stmt.sinfo, testreg, trueblck, falseblck);
                this.m_emitter.setActiveBlock(trueblck);
                
                const truestate = this.checkStatement(TypeEnvironment.join(this.m_assembly, ...cflow.tenvs), stmt.flow.conds[i].action);
                if (truestate.hasNormalFlow()) {
                    this.m_emitter.emitDirectJump(stmt.sinfo, doneblck);
                }
                
                this.m_emitter.setActiveBlock(falseblck);
                
                results.push(truestate);
                cenv = TypeEnvironment.join(this.m_assembly, ...cflow.fenvs);
            }
        }

        if (stmt.flow.elseAction === undefined || !hasfalseflow) {
            results.push(cenv);

            if(cenv.hasNormalFlow()) {
                this.m_emitter.emitDirectJump(stmt.sinfo, doneblck);
            }
        }
        else {
            const aenv = this.checkStatement(cenv, stmt.flow.elseAction);
            results.push(aenv);

            if (aenv.hasNormalFlow()) {
                this.m_emitter.emitDirectJump(stmt.sinfo, doneblck);
            }
        }

        this.m_emitter.setActiveBlock(doneblck);
        return TypeEnvironment.join(this.m_assembly, ...results);
    }

    private checkMatchGuard(sinfo: SourceInfo, isconst: boolean, midx: number, env: TypeEnvironment, matchvname: string, cvname: string | undefined, guard: MatchGuard, nextlabel: string, actionlabel: string): { newlive: string[], tenv: TypeEnvironment | undefined, fenv: TypeEnvironment | undefined } {
        let opts: { tenv: TypeEnvironment | undefined, fenv: TypeEnvironment | undefined } = { tenv: undefined, fenv: undefined };
        let mreg = this.m_emitter.generateTmpRegister();

        const vspecial = new MIRRegisterArgument(matchvname);
        const vspecialinfo = env.getLocalVarInfo(matchvname) as VarInfo;
        env = env.setResultExpression(vspecialinfo.declaredType, vspecialinfo.flowType, undefined, undefined);

        let lifetimes: string[] = [];
        if (guard instanceof WildcardMatchGuard) {
            this.m_emitter.emitLoadConstBool(sinfo, true, mreg);
            opts = { tenv: env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True), fenv: undefined };
        }
        else if (guard instanceof TypeMatchGuard) {
            const tmatch = this.resolveAndEnsureTypeOnly(sinfo, guard.oftype, env.terms);
            this.m_emitter.emitTypeOf(sinfo, mreg, this.m_emitter.registerResolvedTypeReference(tmatch), vspecial, this.m_emitter.registerResolvedTypeReference(vspecialinfo.declaredType), this.m_emitter.registerResolvedTypeReference(vspecialinfo.flowType), undefined);
            
            const fflows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, tmatch, [env]);
            const okenvs = fflows.tenvs.map((eev) => eev.inferVarsOfType(eev.getExpressionResult().valtype.flowtype, matchvname, cvname).setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True));
            const failenvs = fflows.fenvs.map((eev) => eev.inferVarsOfType(eev.getExpressionResult().valtype.flowtype, matchvname, cvname).setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False));

            if(okenvs.length === 0) {
                opts = {
                    tenv: undefined,
                    fenv: TypeEnvironment.join(this.m_assembly, ...failenvs)
                }
            }
            else if(failenvs.length === 0) {
                opts = {
                    tenv: TypeEnvironment.join(this.m_assembly, ...okenvs),
                    fenv: undefined
                };
            }
            
            opts = {
                tenv: TypeEnvironment.join(this.m_assembly, ...okenvs),
                fenv: TypeEnvironment.join(this.m_assembly, ...failenvs)
            };
        }
        else {
            const sguard = guard as StructureMatchGuard;

            let allDeclared: [string, ResolvedType, StructuredAssignmentPathStep, ResolvedType][] = [];
            let allAssigned: [string, StructuredAssignmentPathStep, ResolvedType][] = [];
            let allChecks: [StructuredAssignmentPathStep, StructuredAssignmentCheck][] = [];

            const eetype = ValueType.createUniform(vspecialinfo.flowType);
            const eereg = this.emitInlineConvertToFlow(sinfo, vspecial, new ValueType(vspecialinfo.declaredType, vspecialinfo.flowType));
            const ok = this.checkStructuredMatch(sinfo, env, eetype.flowtype, sguard.match, allDeclared, allAssigned, allChecks);
            if(!ok) {
                opts = {
                    tenv: undefined,
                    fenv: env
                }
            }
            else {
                let reqassigns: StructuredAssignmentPathStep[] = [...allDeclared.map((dv) => dv[2]), ...allAssigned.map((av) => av[1])];
                let assignregs: MIRRegisterArgument[] = [];

                const filllabel = this.m_emitter.createNewBlock(`match${midx}_scfill`);
                const ottinfo = this.generateMatchTestOps(env, sinfo, eereg, eetype, matchvname, cvname, allChecks, reqassigns, assignregs, mreg, nextlabel);
                opts = {
                    tenv: TypeEnvironment.join(this.m_assembly, ...ottinfo.okenvs),
                    fenv: ottinfo.failenvs.length !== 0 ? TypeEnvironment.join(this.m_assembly, ...ottinfo.failenvs) : undefined
                };

                this.m_emitter.emitBoolJump(sinfo, mreg, filllabel, nextlabel);

                lifetimes = allDeclared.map((dv) => dv[0]);
                this.m_emitter.setActiveBlock(filllabel);
                for (let i = 0; i < allDeclared.length; ++i) {
                    const declv = allDeclared[i];

                    const regidv = reqassigns.findIndex((pth) => pth.ival === declv[2].ival && pth.nval === declv[2].nval);
                    const vvreg = (regidv !== -1 ? assignregs[regidv] : this.generateRootReg(sinfo, declv[2], eereg, eetype.flowtype)[0]) as MIRRegisterArgument;
                    opts.tenv = this.checkDeclareSingleVariable(sinfo, opts.tenv as TypeEnvironment, declv[0], isconst, declv[1], {etype: ValueType.createUniform(declv[3]), etreg: vvreg });
                }

                for (let i = 0; i < allAssigned.length; ++i) {
                    const assignv = allAssigned[i];

                    const regidv = reqassigns.findIndex((pth) => pth.ival === assignv[1].ival && pth.nval === assignv[1].nval);
                    const vvreg = (regidv !== -1 ? assignregs[regidv] : this.generateRootReg(sinfo, assignv[1], eereg, eetype.flowtype)[0]) as MIRRegisterArgument;
                    opts.tenv = this.checkAssignSingleVariable(sinfo, opts.tenv as TypeEnvironment, assignv[0], ValueType.createUniform(assignv[2]), vvreg);
                }
            }
        }

        if (guard.optionalWhen === undefined) {
            if(lifetimes.length === 0) {
                this.m_emitter.emitBoolJump(sinfo, mreg, actionlabel, nextlabel);
            }
            else {
                const endlifeblock = this.m_emitter.createNewBlock(`match${midx}_endlife`);
                this.m_emitter.emitBoolJump(sinfo, mreg, actionlabel, endlifeblock);

                this.m_emitter.setActiveBlock(endlifeblock);
                for(let i = 0; i < lifetimes.length; ++i) {
                    this.m_emitter.localLifetimeEnd(sinfo, lifetimes[i]);
                }

                this.m_emitter.emitDirectJump(sinfo, nextlabel);
            }

            return { 
                newlive: lifetimes, 
                tenv: (opts.tenv !== undefined ? opts.tenv.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True) : undefined),
                fenv: (opts.fenv !== undefined ? opts.fenv.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False) : undefined)
            };
        }
        else {
            const whenblck = this.m_emitter.createNewBlock(`match${midx}_when`);
            this.m_emitter.emitBoolJump(sinfo, mreg, whenblck, nextlabel);

            this.m_emitter.setActiveBlock(whenblck);

            let wreg = this.m_emitter.generateTmpRegister();
            const wopts = this.checkExpressionMultiFlow(opts.tenv as TypeEnvironment, guard.optionalWhen, wreg, undefined);

            this.raiseErrorIf(sinfo, wopts.some((opt) => !opt.getExpressionResult().valtype.flowtype.isSameType(this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");
            const bwreg = this.emitInlineConvertToFlow(sinfo, wreg, ValueType.join(this.m_assembly, ...wopts.map((eev) => eev.getExpressionResult().valtype)));

            if (lifetimes.length === 0) {
                this.m_emitter.emitBoolJump(sinfo, bwreg, actionlabel, nextlabel);
            }
            else {
                const endlifeblock = this.m_emitter.createNewBlock(`match${midx}_whenendlife`);
                this.m_emitter.emitBoolJump(sinfo, bwreg, actionlabel, endlifeblock);

                this.m_emitter.setActiveBlock(endlifeblock);
                for (let i = 0; i < lifetimes.length; ++i) {
                    this.m_emitter.localLifetimeEnd(sinfo, lifetimes[i]);
                }

                this.m_emitter.emitDirectJump(sinfo, nextlabel);
            }

            const wflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, wopts);
            return { 
                newlive: lifetimes, 
                tenv: TypeEnvironment.join(this.m_assembly, ...wflows.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))), 
                fenv: TypeEnvironment.join(this.m_assembly, ...([...(opts.fenv !== undefined ? [opts.fenv as TypeEnvironment] : []), ...wflows.fenvs].map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False))))
            };
        }
    }

    private checkMatchStatement(env: TypeEnvironment, stmt: MatchStatement): TypeEnvironment {
        const vreg = this.m_emitter.generateTmpRegister();
        const venv = this.checkExpression(env, stmt.sval, vreg, undefined, { refok: true, orok: false });
        const cvname = venv.getExpressionResult().expvar;

        const doneblck = this.m_emitter.createNewBlock("Lswitchstmt_done");
        const matchvar = `$match_#${stmt.sinfo.pos}`;
        let cenv = this.checkDeclareSingleVariable(stmt.sinfo, venv.popLocalScope(), matchvar, true, venv.getExpressionResult().valtype.flowtype, {etype: ValueType.createUniform(venv.getExpressionResult().valtype.flowtype), etreg: vreg});

        let hasfalseflow = true;
        let results: TypeEnvironment[] = [];
        let rblocks: [string, string[]][] = [];
        for (let i = 0; i < stmt.flow.length && !hasfalseflow; ++i) {
            const nextlabel = this.m_emitter.createNewBlock(`Lswitchstmt_${i}next`);
            const actionlabel = this.m_emitter.createNewBlock(`Lswitchstmt_${i}action`);

            const test = this.checkMatchGuard(stmt.sinfo, true, i, cenv, matchvar, cvname, stmt.flow[i].check, nextlabel, actionlabel);

            if(test.tenv === undefined) {
                this.m_emitter.setActiveBlock(actionlabel);
                this.m_emitter.emitDeadBlock(stmt.sinfo);

                this.m_emitter.setActiveBlock(nextlabel);
                cenv = test.fenv as TypeEnvironment;
            }
            else if(test.fenv === undefined) {
                //go though action block and skip rest of generation
                this.m_emitter.setActiveBlock(actionlabel);

                const truestate = this.checkStatement(test.tenv, stmt.flow[i].action);

                results.push(truestate);
                if(truestate.hasNormalFlow()) {
                    rblocks.push([actionlabel, test.newlive]);
                }

                this.m_emitter.setActiveBlock(nextlabel);
                this.m_emitter.emitDeadBlock(stmt.sinfo);

                hasfalseflow = false;
            }
            else {
                this.m_emitter.setActiveBlock(actionlabel);

                const truestate = this.checkStatement(test.tenv, stmt.flow[i].action);

                results.push(truestate);
                if(truestate.hasNormalFlow()) {
                    rblocks.push([actionlabel, test.newlive]);
                }

                this.m_emitter.setActiveBlock(nextlabel);
                cenv = test.fenv as TypeEnvironment;
            }
        }

        if (hasfalseflow) {
            this.m_emitter.emitAbort(stmt.sinfo, "exhaustive");
        }

        for (let i = 0; i < rblocks.length; ++i) {
            const rcb = rblocks[i];
            this.m_emitter.setActiveBlock(rcb[0]);

            this.m_emitter.localLifetimeEnd(stmt.sinfo, matchvar);
            for (let i = 0; i < rcb[1].length; ++i) {
                this.m_emitter.localLifetimeEnd(stmt.sinfo, rcb[1][i]);
            }

            this.m_emitter.emitDirectJump(stmt.sinfo, doneblck);
        }

        this.m_emitter.setActiveBlock(doneblck);
        if(results.length === 0) {
            this.m_emitter.emitAbort(stmt.sinfo, "Terminal Flows");
            return env.setAbort();
        }

        return TypeEnvironment.join(this.m_assembly, ...results.map((eev) => eev.popLocalScope()));
    }

    private checkNakedCallStatement(env: TypeEnvironment, stmt: NakedCallStatement): TypeEnvironment {
        const rdiscard = this.m_emitter.generateTmpRegister();

        if(stmt.call instanceof CallNamespaceFunctionOrOperatorExpression) {
            const cenv = this.checkCallNamespaceFunctionOrOperatorExpression(env, stmt.call as CallNamespaceFunctionOrOperatorExpression, rdiscard, true);
            return TypeEnvironment.join(this.m_assembly, ...cenv);
        }
        else { 
            const cenv = this.checkCallStaticFunctionOrOperatorExpression(env, stmt.call as CallStaticFunctionOrOperatorExpression, rdiscard, true);
            return TypeEnvironment.join(this.m_assembly, ...cenv);
        }
    }

    private checkReturnStatement(env: TypeEnvironment, stmt: ReturnStatement): TypeEnvironment {
        this.raiseErrorIf(stmt.sinfo, env.isInYieldBlock(), "Cannot use return statment inside an expression block");

        if (stmt.values.length === 1) {
            const etreg = this.m_emitter.generateTmpRegister();
            const venv = this.checkExpression(env, stmt.values[0], etreg, env.inferResult, { refok: true, orok: false });

            const etype = env.inferResult || venv.getExpressionResult().valtype.flowtype;
            this.m_emitter.emitReturnAssign(stmt.sinfo, this.emitInlineConvertIfNeeded(stmt.sinfo, etreg, venv.getExpressionResult().valtype, etype), this.m_emitter.registerResolvedTypeReference(etype));
            this.m_emitter.emitDirectJump(stmt.sinfo, "returnassign");

            return env.setReturn(this.m_assembly, etype);
        }
        else {
            let regs: MIRRegisterArgument[] = [];
            let rtypes: ResolvedType[] = [];
            const itype = env.inferResult !== undefined ? env.inferResult.tryGetInferrableValueListConstructorType() : undefined;
            for (let i = 0; i < stmt.values.length; ++i) {
                const einfer = itype !== undefined ? itype.types[i] : undefined;

                const etreg = this.m_emitter.generateTmpRegister();
                const venv = this.checkExpression(env, stmt.values[i], etreg, einfer);

                const rrtype = einfer || venv.getExpressionResult().valtype.flowtype;
                regs.push(this.emitInlineConvertIfNeeded(stmt.sinfo, etreg, venv.getExpressionResult().valtype, rrtype));
                rtypes.push(rrtype);
            }

            const etype = ResolvedType.createSingle(ResolvedEphemeralListType.create(rtypes));

            const elreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitConstructorValueList(stmt.sinfo, this.m_emitter.registerResolvedTypeReference(etype), regs, elreg);
                
            this.m_emitter.emitReturnAssign(stmt.sinfo, elreg, this.m_emitter.registerResolvedTypeReference(etype));
            this.m_emitter.emitDirectJump(stmt.sinfo, "returnassign");

            return env.setReturn(this.m_assembly, etype);
        }
    }

    private checkYieldStatement(env: TypeEnvironment, stmt: YieldStatement): TypeEnvironment {
        this.raiseErrorIf(stmt.sinfo, !env.isInYieldBlock(), "Cannot use yield statment outside expression blocks");

        const yinfo = this.m_emitter.getActiveYieldSet();
        const yinfer = env.inferYield[env.inferYield.length - 1];

        if (stmt.values.length === 1) {
            const ytrgt = this.m_emitter.generateTmpRegister();
            const venv = this.checkExpression(env, stmt.values[0], ytrgt, yinfer, { refok: true, orok: false });

            const ctype = yinfer || venv.getExpressionResult().valtype.flowtype;
            const yvv = venv.getExpressionResult().valtype.inferFlow(ctype);

            yinfo.push([this.m_emitter.getActiveBlockName(), ytrgt, yvv]);
            return env.setYield(this.m_assembly, ctype);
        }
        else {
            let regs: MIRRegisterArgument[] = [];
            let rtypes: ResolvedType[] = [];
            const itype = yinfer !== undefined ? yinfer.tryGetInferrableValueListConstructorType() : undefined;
            for (let i = 0; i < stmt.values.length; ++i) {
                const einfer = itype !== undefined ? itype.types[i] : undefined;

                const etreg = this.m_emitter.generateTmpRegister();
                const venv = this.checkExpression(env, stmt.values[i], etreg, einfer);

                const rrtype = einfer || venv.getExpressionResult().valtype.flowtype;
                regs.push(this.emitInlineConvertIfNeeded(stmt.sinfo, etreg, venv.getExpressionResult().valtype, rrtype));
                rtypes.push(rrtype);
            }

            const etype = ResolvedType.createSingle(ResolvedEphemeralListType.create(rtypes));

            const elreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitConstructorValueList(stmt.sinfo, this.m_emitter.registerResolvedTypeReference(etype), regs, elreg);

            yinfo.push([this.m_emitter.getActiveBlockName(), elreg, ValueType.createUniform(etype)]);
            return env.setYield(this.m_assembly, etype);
        }
    }

    private checkAbortStatement(env: TypeEnvironment, stmt: AbortStatement): TypeEnvironment {
        this.m_emitter.emitAbort(stmt.sinfo, "abort");

        return env.setAbort();
    }

    private checkAssertStatement(env: TypeEnvironment, stmt: AssertStatement): TypeEnvironment {
        const testreg = this.m_emitter.generateTmpRegister();
        const test = this.checkExpressionMultiFlow(env, stmt.cond, testreg, undefined);

        this.raiseErrorIf(stmt.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");

        const flow = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, test);
        if(flow.fenvs.length === 0) {
            return TypeEnvironment.join(this.m_assembly, ...flow.tenvs);
        }
        else if(flow.tenvs.length === 0) {
            this.m_emitter.emitAbort(stmt.sinfo, "always false assert");
            return env.setAbort();
        }
        else {
            if (isBuildLevelEnabled(stmt.level, this.m_buildLevel)) {
                this.m_emitter.emitAssertCheck(stmt.sinfo, "assert fail", testreg);
            }

            return TypeEnvironment.join(this.m_assembly, ...flow.tenvs);
        }
    }

    private checkCheckStatement(env: TypeEnvironment, stmt: CheckStatement): TypeEnvironment {
        const testreg = this.m_emitter.generateTmpRegister();
        const test = this.checkExpressionMultiFlow(env, stmt.cond, testreg, undefined);

        this.raiseErrorIf(stmt.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");

        const flow = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, test);
        if(flow.fenvs.length === 0) {
            return TypeEnvironment.join(this.m_assembly, ...flow.tenvs);
        }
        else if(flow.tenvs.length === 0) {
            this.m_emitter.emitAbort(stmt.sinfo, "always false check");
            return env.setAbort();
        }
        else {
            this.m_emitter.emitAssertCheck(stmt.sinfo, "check fail", testreg);

            return TypeEnvironment.join(this.m_assembly, ...flow.tenvs);
        }
    }

    private checkDebugStatement(env: TypeEnvironment, stmt: DebugStatement): TypeEnvironment {
        if (stmt.value === undefined) {
            if (this.m_buildLevel === "debug") {
                this.m_emitter.emitDebugBreak(stmt.sinfo);
            }
        }
        else {
            const vreg = this.m_emitter.generateTmpRegister();
            const venv = this.checkExpression(env, stmt.value, vreg, undefined);

            if (this.m_buildLevel !== "release") {
                this.m_emitter.emitDebugPrint(stmt.sinfo, this.emitInlineConvertIfNeeded(stmt.sinfo, vreg, venv.getExpressionResult().valtype, this.m_emitter.assembly.getSpecialAnyConceptType()));
            }
        }

        return env;
    }

    private checkValidateStatement(env: TypeEnvironment, stmt: ValidateStatement): TypeEnvironment {
        const testreg = this.m_emitter.generateTmpRegister();
        const test = this.checkExpressionMultiFlow(env, stmt.cond, testreg, undefined);


        this.raiseErrorIf(stmt.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");

        const flow = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, test);
        this.raiseErrorIf(stmt.sinfo, env.inferResult !== undefined, "Cannot do type inference if using validate in the body");
        
        if(flow.fenvs.length === 0) {
            return TypeEnvironment.join(this.m_assembly, ...flow.tenvs);
        }
        else {
            const rrtype = env.inferResult as ResolvedType;
            this.raiseErrorIf(stmt.sinfo, !rrtype.isResultConceptType(), "Return type must be Result<T, E> when using validate");

            const doneblck = this.m_emitter.createNewBlock("Lcheck_done");
            const failblck = this.m_emitter.createNewBlock("Lcheck_fail");
            
            this.m_emitter.emitBoolJump(stmt.sinfo, testreg, doneblck, failblck);
            this.m_emitter.setActiveBlock(failblck);

            const errreg = this.m_emitter.generateTmpRegister();
            const errflow = TypeEnvironment.join(this.m_assembly, ...flow.fenvs.map((te) => te.setReturn(this.m_assembly, rrtype)));
           
            let errenv = errflow;
            if (stmt.err instanceof LiteralNoneExpression) {
                const conserrbinds = this.getResultBinds(rrtype);
                this.raiseErrorIf(stmt.sinfo, !this.m_assembly.subtypeOf(conserrbinds.E, this.m_assembly.getSpecialNoneType()));

                const errtdcl = this.m_assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Result::Err") as EntityTypeDecl;
                const errbinds = new Map<string, ResolvedType>().set("T", conserrbinds.T as ResolvedType).set("E", conserrbinds.E);
                const errconstype = ResolvedType.createSingle(ResolvedEntityAtomType.create(errtdcl, errbinds));
                const mirerrconstype = this.m_emitter.registerResolvedTypeReference(errconstype);

                const errconsfunc = errtdcl.staticFunctions.find((sf) => sf.name === "create") as StaticFunctionDecl;
                const errconskey = this.m_emitter.registerStaticCall([mirerrconstype, errtdcl, errbinds], errconsfunc, "create", new Map<string, ResolvedType>(), [], []);

                const terrreg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitInvokeFixedFunction(stmt.sinfo, errconskey, [new MIRConstantNone()], undefined, mirerrconstype, terrreg);
                this.m_emitter.emitRegisterStore(stmt.sinfo, this.emitInlineConvertIfNeeded(stmt.sinfo, terrreg, ValueType.createUniform(errconstype), rrtype), errreg, this.m_emitter.registerResolvedTypeReference(rrtype), undefined);

                errenv = errflow.setReturn(this.m_assembly, rrtype);
            }
            else {
                const terrreg = this.m_emitter.generateTmpRegister();
                errenv = this.checkExpression(errflow, stmt.err, terrreg, rrtype);
                const errres = errenv.getExpressionResult().valtype;
                this.raiseErrorIf(stmt.sinfo, !this.m_assembly.subtypeOf(errres.flowtype, rrtype), "Error result must evaluate to Result<T, E>");

                this.m_emitter.emitRegisterStore(stmt.sinfo, this.emitInlineConvertToFlow(stmt.sinfo, terrreg, errres), errreg, this.m_emitter.registerResolvedTypeReference(errres.flowtype), undefined);
            }

            this.m_emitter.emitReturnAssign(stmt.sinfo, errreg, this.m_emitter.registerResolvedTypeReference(rrtype));
            this.m_emitter.emitDirectJump(stmt.sinfo, "returnassign");

            this.m_emitter.setActiveBlock(doneblck);

            return TypeEnvironment.join(this.m_assembly, ...flow.tenvs, errenv);
        }
    }

    private checkStatement(env: TypeEnvironment, stmt: Statement): TypeEnvironment {
        this.raiseErrorIf(stmt.sinfo, !env.hasNormalFlow(), "Unreachable statements");

        switch (stmt.tag) {
            case StatementTag.EmptyStatement:
                return env;
            case StatementTag.VariableDeclarationStatement:
                return this.checkVariableDeclarationStatement(env, stmt as VariableDeclarationStatement).clearExpressionResult();
            case StatementTag.VariablePackDeclarationStatement:
                return this.checkVariablePackDeclarationStatement(env, stmt as VariablePackDeclarationStatement).clearExpressionResult();
            case StatementTag.VariableAssignmentStatement:
                return this.checkVariableAssignmentStatement(env, stmt as VariableAssignmentStatement).clearExpressionResult();
            case StatementTag.VariablePackAssignmentStatement:
                return this.checkVariablePackAssignmentStatement(env, stmt as VariablePackAssignmentStatement).clearExpressionResult();
            case StatementTag.StructuredVariableAssignmentStatement:
                return this.checkStructuredVariableAssignmentStatement(env, stmt as StructuredVariableAssignmentStatement).clearExpressionResult();
            case StatementTag.IfElseStatement:
                return this.checkIfElseStatement(env, stmt as IfElseStatement).clearExpressionResult();
            case StatementTag.MatchStatement:
                return this.checkMatchStatement(env, stmt as MatchStatement).clearExpressionResult();
            case StatementTag.NakedCallStatement:
                return this.checkNakedCallStatement(env, stmt as NakedCallStatement).clearExpressionResult();
            case StatementTag.ReturnStatement:
                return this.checkReturnStatement(env, stmt as ReturnStatement).clearExpressionResult();
            case StatementTag.YieldStatement:
                return this.checkYieldStatement(env, stmt as YieldStatement).clearExpressionResult();
            case StatementTag.AbortStatement:
                return this.checkAbortStatement(env, stmt as AbortStatement).clearExpressionResult();
            case StatementTag.AssertStatement:
                return this.checkAssertStatement(env, stmt as AssertStatement).clearExpressionResult();
            case StatementTag.CheckStatement:
                return this.checkCheckStatement(env, stmt as CheckStatement).clearExpressionResult();
            case StatementTag.DebugStatement:
                return this.checkDebugStatement(env, stmt as DebugStatement).clearExpressionResult();
            case StatementTag.ValidateStatement:
                return this.checkValidateStatement(env, stmt as ValidateStatement).clearExpressionResult();
            default:
                this.raiseErrorIf(stmt.sinfo, stmt.tag !== StatementTag.BlockStatement, "Unknown statement");
                return this.checkBlock(env, stmt as BlockStatement).clearExpressionResult();
        }
    }

    private checkBlock(env: TypeEnvironment, stmt: BlockStatement): TypeEnvironment {
        let cenv = env.pushLocalScope();

        for (let i = 0; i < stmt.statements.length; ++i) {
            if (!cenv.hasNormalFlow()) {
                break;
            }

            cenv = this.checkStatement(cenv, stmt.statements[i]);
        }

        if (cenv.hasNormalFlow()) {
            const deadvars = cenv.getCurrentFrameNames();
            for (let i = 0; i < deadvars.length; ++i) {
                this.m_emitter.localLifetimeEnd(stmt.sinfo, deadvars[i]);
            }
        }

        return cenv.popLocalScope();
    }

    private emitPrelogForRefParamsAndPostCond(sinfo: SourceInfo, env: TypeEnvironment, refparams: string[]): string[] {
        let rpnames: string[] = [];

        for(let i = 0; i < refparams.length; ++i) {
            rpnames.push(`$${refparams[i]}`);
            const rpt = (env.lookupVar(refparams[0]) as VarInfo).declaredType;
            this.m_emitter.emitRegisterStore(sinfo, new MIRRegisterArgument(refparams[i]), new MIRRegisterArgument(`$${refparams[i]}`), this.m_emitter.registerResolvedTypeReference(rpt), undefined);
        }

        return rpnames;
    }

    private emitPrologForReturn(sinfo: SourceInfo, rrinfo: { declresult: MIRType, runtimeresult: MIRType, elrcount: number, refargs: [string, MIRType][] }, wpost: boolean) {
        if(wpost) {
            this.m_emitter.emitRegisterStore(sinfo, new MIRRegisterArgument("$__ir_ret__"), new MIRRegisterArgument("$return"), rrinfo.declresult, undefined);
        }

        if(rrinfo.refargs.length === 0) {
            this.m_emitter.emitRegisterStore(sinfo, new MIRRegisterArgument("$__ir_ret__"), new MIRRegisterArgument("$$return"), rrinfo.declresult, undefined);
        }
        else {
            const rreg = this.m_emitter.generateTmpRegister();

            if(rrinfo.elrcount === -1) {
                let args = [new MIRRegisterArgument("$__ir_ret__"), ...rrinfo.refargs.map((rv) => new MIRRegisterArgument(rv[0]))];
                this.m_emitter.emitConstructorValueList(sinfo, rrinfo.runtimeresult, args, rreg);
            }
            else {
                let args: MIRArgument[] = [new MIRRegisterArgument("$__ir_ret__")];
                for(let i = 0; i < rrinfo.refargs.length; ++i) {
                    args.push(new MIRRegisterArgument(rrinfo.refargs[i][0]));
                }

                this.m_emitter.emitMIRPackExtend(sinfo, new MIRRegisterArgument("$__ir_ret__"), rrinfo.declresult, args, rrinfo.runtimeresult, rreg);
            }

            this.m_emitter.emitRegisterStore(sinfo, rreg, new MIRRegisterArgument("$$return"), rrinfo.runtimeresult, undefined);
        }
    }

    private checkBodyExpression(srcFile: string, env: TypeEnvironment, body: Expression, outparaminfo: { pname: string, ptype: ResolvedType }[]): MIRBody | undefined {
        this.m_emitter.initializeBodyEmitter();

        for (let i = 0; i < outparaminfo.length; ++i) {
            const opi = outparaminfo[i];
            this.m_emitter.emitLoadUninitVariableValue(body.sinfo, this.m_emitter.registerResolvedTypeReference(opi.ptype), new MIRRegisterArgument(opi.pname));
        }

        const etreg = this.m_emitter.generateTmpRegister();
        const evalue = this.checkExpression(env, body, etreg, undefined);

        this.m_emitter.emitReturnAssign(body.sinfo, this.emitInlineConvertIfNeeded(body.sinfo, etreg, evalue.getExpressionResult().valtype, env.inferResult || evalue.getExpressionResult().valtype.flowtype), this.m_emitter.registerResolvedTypeReference(evalue.getExpressionResult().valtype.flowtype));
        this.m_emitter.emitDirectJump(body.sinfo, "returnassign");

        this.m_emitter.setActiveBlock("returnassign");

        const rrinfo = this.generateRefInfoForReturnEmit(evalue.getExpressionResult().valtype.flowtype, []);
        this.emitPrologForReturn(body.sinfo, rrinfo, false);
        this.m_emitter.emitDirectJump(body.sinfo, "exit");

        return this.m_emitter.getBody(srcFile, body.sinfo);
    }

    private checkBodyStatement(srcFile: string, env: TypeEnvironment, body: BlockStatement, optparaminfo: { pname: string, ptype: ResolvedType, maskidx: number, initaction: InitializerEvaluationAction }[], outparaminfo: { pname: string, defonentry: boolean, ptype: ResolvedType }[], preject: [{ ikey: string, sinfo: SourceInfo, srcFile: string }[], string[]] | undefined, postject: [{ ikey: string, sinfo: SourceInfo, srcFile: string }[], string[]] | undefined | undefined): MIRBody | undefined {
        this.m_emitter.initializeBodyEmitter();

        for (let i = 0; i < outparaminfo.length; ++i) {
            const opi = outparaminfo[i];
            if(!opi.defonentry) {
                this.m_emitter.emitLoadUninitVariableValue(body.sinfo, this.m_emitter.registerResolvedTypeReference(opi.ptype), new MIRRegisterArgument(opi.pname));
            }
        }

        let opidone: Set<string> = new Set<string>(["this"]);
        for (let i = 0; i < optparaminfo.length; ++i) {
            const opidx = optparaminfo.findIndex((opp) => !opidone.has(opp.pname) && opp.initaction.deps.every((dep) => opidone.has(dep)));
            const opi = optparaminfo[opidx];

            const iv = opi.initaction;
            const oftype = opi.ptype;
            const storevar = new MIRRegisterArgument(opi.pname);
            const guard = new MIRMaskGuard("#maskparam#", opidx, optparaminfo.length);
            if(iv instanceof InitializerEvaluationLiteralExpression) {
                const ttmp = this.m_emitter.generateTmpRegister();
                const oftt = this.checkExpression(env, iv.constexp, ttmp, oftype).getExpressionResult().valtype;

                this.m_emitter.emitRegisterStore(body.sinfo, storevar, storevar, this.m_emitter.registerResolvedTypeReference(oftype), new MIRStatmentGuard(guard, "defaultonfalse", this.emitInlineConvertIfNeeded(iv.constexp.sinfo, ttmp, oftt, oftype)));
            }
            else if (iv instanceof InitializerEvaluationConstantLoad) {
                this.m_emitter.emitRegisterStore(body.sinfo, storevar, storevar, this.m_emitter.registerResolvedTypeReference(oftype), new MIRStatmentGuard(guard, "defaultonfalse", new MIRGlobalVariable(iv.gkey)));
            }
            else {
                const civ = iv as InitializerEvaluationCallAction;
                this.m_emitter.emitInvokeFixedFunctionWithGuard(body.sinfo, civ.ikey, civ.args, undefined, this.m_emitter.registerResolvedTypeReference(oftype), storevar, new MIRStatmentGuard(guard, "defaultontrue", storevar));
            }

            opidone.add(opi.pname);
        }

        if (preject !== undefined) {
            const preargs = preject[1].map((pn) => new MIRRegisterArgument(pn));
            for (let i = 0; i < preject[0].length; ++i) {
                const prechk = preject[0][i];

                const prereg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitInvokeFixedFunction(body.sinfo, prechk.ikey, preargs, undefined, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), prereg);
                this.m_emitter.emitAssertCheck(body.sinfo, "Fail pre-condition", prereg);
            }
        }

        let postrnames: string[] = [];
        if (postject !== undefined) {
            postrnames = this.emitPrelogForRefParamsAndPostCond(body.sinfo, env, outparaminfo.filter((op) => op.defonentry).map((op) => op.pname));
        }

        const renv = this.checkBlock(env, body);
        this.raiseErrorIf(body.sinfo, renv.hasNormalFlow(), "Not all flow paths return a value!");

        this.m_emitter.setActiveBlock("returnassign");

        const rrinfo = this.generateRefInfoForReturnEmit(renv.inferResult as ResolvedType, outparaminfo.map((op) => [op.pname, op.ptype]));
        this.emitPrologForReturn(body.sinfo, rrinfo, postject !== undefined);

        if (postject !== undefined) {
            const postargs = [...postject[1].map((pn) => new MIRRegisterArgument(pn)), ...postrnames.map((prn) => new MIRRegisterArgument(prn))];

            for (let i = 0; i < postject[0].length; ++i) {
                const postchk = postject[0][i];

                const postreg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitInvokeFixedFunction(body.sinfo, postchk.ikey, postargs, undefined, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), postreg);
                this.m_emitter.emitAssertCheck(body.sinfo, "Fail post-condition", postreg);
            }
        }

        this.m_emitter.emitDirectJump(body.sinfo, "exit");

        return this.m_emitter.getBody(srcFile, body.sinfo);
    }

    private abortIfTooManyErrors() {
        if (this.m_errors.length > 20) {
            throw new Error("More than 20 errors ... halting type checker");
        }
    }

    private getCapturedTypeInfoForFields(sinfo: SourceInfo, captured: Set<string>, allfieldstypes: Map<string, ResolvedType>): Map<string, ResolvedType> {
        let cci = new Map<string, ResolvedType>();
        captured.forEach((cp) => {
            this.raiseErrorIf(sinfo, !allfieldstypes.get(cp.slice(1)), `Unbound variable reference in field initializer "${cp}"`);

            cci.set(cp, allfieldstypes.get(cp.slice(1)) as ResolvedType);
        });

        return cci;
    }

    private processExpressionForFieldInitializer(containingType: OOPTypeDecl, decl: MemberFieldDecl, binds: Map<string, ResolvedType>, allfieldstypes: Map<string, ResolvedType>): InitializerEvaluationAction {
        const ddecltype = this.resolveAndEnsureTypeOnly(decl.sourceLocation, decl.declaredType, binds);
        const enclosingType = MIRKeyGenerator.generateTypeKey(this.resolveOOTypeFromDecls(containingType, binds));
        const ikey = MIRKeyGenerator.generateMethodKey(`$initfield_func_${decl.name}`, this.m_emitter.registerResolvedTypeReference(this.resolveOOTypeFromDecls(containingType, binds)).trkey, binds, []);
        const iname = `$initfield::${enclosingType}::${decl.name}`;

        try {
            const cexp = decl.value as ConstantExpressionValue;
            if (cexp.captured.size === 0) {
                const lexp = this.m_assembly.compileTimeReduceConstantExpression(cexp.exp, binds, ddecltype);
                if(lexp !== undefined) {
                    return new InitializerEvaluationLiteralExpression(lexp);
                }
                else {
                    const gkey = "$global_" + ikey;
                    if (!this.m_emitter.masm.constantDecls.has(gkey)) {
                        const idecl = this.processInvokeInfo_ExpressionIsolated(decl.srcFile, cexp.exp, iname, ikey, decl.sourceLocation, ["static_initializer", "private"], ddecltype, binds);
                        this.m_emitter.masm.invokeDecls.set(ikey, idecl as MIRInvokeBodyDecl);

                        const dtype = this.m_emitter.registerResolvedTypeReference(ddecltype);
                        const mirglobal = new MIRConstantDecl(enclosingType, [], iname, ikey, decl.sourceLocation, decl.srcFile, dtype.trkey, gkey);

                        this.m_emitter.masm.constantDecls.set(gkey, mirglobal);
                    }

                    return new InitializerEvaluationConstantLoad(gkey);
                }
            }
            else {
                if (!this.m_emitter.masm.invokeDecls.has(ikey)) {
                    const capturedtypes = this.getCapturedTypeInfoForFields(decl.sourceLocation, cexp.captured, allfieldstypes);
                    const fparams = [...cexp.captured].sort().map((cp) => {
                        return { name: cp, refKind: undefined, ptype: capturedtypes.get(cp) as ResolvedType };
                    });

                    const idecl = this.processInvokeInfo_ExpressionLimitedArgs(decl.srcFile, cexp.exp, iname, ikey, decl.sourceLocation, ["dynamic_initializer", "private", ...decl.attributes], fparams, ddecltype, binds);
                    this.m_emitter.masm.invokeDecls.set(ikey, idecl as MIRInvokeBodyDecl);
                }

                return new InitializerEvaluationCallAction(ikey, [...cexp.captured].sort().map((cp) => new MIRRegisterArgument(cp)));
            }
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();

            return new InitializerEvaluationCallAction(ikey, []);
        }
    }

    private processExpressionForOptParamDefault(srcFile: string, fkey: MIRInvokeKey, pname: string, ptype: ResolvedType, cexp: ConstantExpressionValue, binds: Map<string, ResolvedType>, enclosingDecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, invoke: InvokeDecl): InitializerEvaluationAction {
        const ikey = MIRKeyGenerator.generateFunctionKey(fkey, `$initparam_${pname}`, new Map<string, ResolvedType>(), []); //binds and pcodes already handled in fkey so no need to repeat
        const iname = `$initparam::${fkey}::${pname}`;
        try {
            if (cexp.captured.size === 0) {
                const lexp = this.m_assembly.compileTimeReduceConstantExpression(cexp.exp, binds, ptype);
                if (lexp !== undefined) {
                    return new InitializerEvaluationLiteralExpression(lexp);
                }
                else {
                    const gkey = "$global_" + ikey;
                    const idecl = this.processInvokeInfo_ExpressionIsolated(srcFile, cexp.exp, iname, ikey, cexp.exp.sinfo, ["static_initializer", "private"], ptype, binds);
                    this.m_emitter.masm.invokeDecls.set(ikey, idecl as MIRInvokeBodyDecl);

                    const dtype = this.m_emitter.registerResolvedTypeReference(ptype);
                    const mirglobal = new MIRConstantDecl(undefined, [], iname, ikey, cexp.exp.sinfo, srcFile, dtype.trkey, gkey);

                    this.m_emitter.masm.constantDecls.set(gkey, mirglobal);

                    return new InitializerEvaluationConstantLoad(gkey);
                }
            }
            else {
                const ppnames = [...cexp.captured].sort();
                const fparams = ppnames.map((cp) => {
                    let cptype: ResolvedType | undefined = undefined;
                    if (cp === "%this_captured") {
                        if (enclosingDecl !== undefined) {
                            cptype = this.resolveOOTypeFromDecls(enclosingDecl[1], enclosingDecl[2]);
                        }
                    }
                    else {
                        const cparam = invoke.params.find((ip) => ip.name === cp);
                        if (cparam !== undefined) {
                            cptype = this.resolveAndEnsureTypeOnly(cexp.exp.sinfo, cparam.type as TypeSignature, binds);
                        }
                    }

                    this.raiseErrorIf(cexp.exp.sinfo, cptype === undefined, "Unbound variable in initializer expression");
                    return { name: cp, refKind: undefined, ptype: cptype as ResolvedType };
                });

                const idecl = this.processInvokeInfo_ExpressionGeneral(srcFile, cexp.exp, iname, ikey, cexp.exp.sinfo, ["dynamic_initializer", "private"], fparams, ptype, binds, new Map<string, { pcode: PCode, captured: string[] }>(), []);
                this.m_emitter.masm.invokeDecls.set(ikey, idecl as MIRInvokeBodyDecl);

                return new InitializerEvaluationCallAction(ikey, [...cexp.captured].sort().map((cp) => new MIRRegisterArgument(cp !== "%this_captured" ? cp : "this")));
            }
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();

            return new InitializerEvaluationCallAction(ikey, []);
        }
    }

    private processGenerateSpecialInvariantDirectFunction(conskey: MIRInvokeKey, exps: [ConstantExpressionValue, OOPTypeDecl, Map<string, ResolvedType>][], allfieldstypes: Map<string, ResolvedType>): { ikey: string, sinfo: SourceInfo, srcFile: string, args: string[] }[] {
        try {
            const clauses = exps.map((cev, i) => {
                const iname = `$invariant::${conskey}::${i}`;
                const ikey = `$invariant_${i}_${conskey}`;

                const capturedtypes = this.getCapturedTypeInfoForFields(cev[0].exp.sinfo, cev[0].captured, allfieldstypes);
                const fparams = [...cev[0].captured].sort().map((cp) => {
                    return { name: cp, refKind: undefined, ptype: capturedtypes.get(cp) as ResolvedType };
                });

                const idecl = this.processInvokeInfo_ExpressionLimitedArgs(cev[1].srcFile, cev[0].exp, iname, ikey, cev[1].sourceLocation, ["invariant_clause", "private"], fparams, this.m_assembly.getSpecialBoolType(), cev[2]);
                this.m_emitter.masm.invokeDecls.set(ikey, idecl as MIRInvokeBodyDecl);

                return { ikey: ikey, sinfo: cev[0].exp.sinfo, srcFile: cev[1].srcFile, args: [...cev[0].captured].sort() };
            });

            return clauses;
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();

            return [];
        }
    }

    private generateConstructor(env: TypeEnvironment, conskey: MIRInvokeKey, tdecl: EntityTypeDecl, binds: Map<string, ResolvedType>) {
        const constype = this.resolveOOTypeFromDecls(tdecl, binds);

        const allfields = this.m_assembly.getAllOOFieldsLayout(tdecl, binds);
        const allfieldstypes = new Map<string, ResolvedType>();
        allfields.forEach((v, k) => allfieldstypes.set(k, this.resolveAndEnsureTypeOnly(tdecl.sourceLocation, v[1].declaredType, v[2])));

        const invs = ([] as [ConstantExpressionValue, OOPTypeDecl, Map<string, ResolvedType>][]).concat(...
            this.m_assembly.getAllInvariantProvidingTypes(tdecl, binds).map((ipt) => 
            ipt[1].invariants
            .filter((inv) => isBuildLevelEnabled(inv.level, this.m_buildLevel))
            .map((inv) => [inv.exp, ipt[1], ipt[2]] as [ConstantExpressionValue, OOPTypeDecl, Map<string, ResolvedType>]))
        );
        const clauses = this.processGenerateSpecialInvariantDirectFunction(conskey, invs, allfieldstypes);

        const optfields = [...allfields].filter((ff) => ff[1][1].value !== undefined).map((af) => af[1]);
        const fieldparams = this.m_assembly.getAllOOFieldsConstructors(tdecl, binds);

        const optinits = optfields.map((opf) => {
            return this.processExpressionForFieldInitializer(opf[0], opf[1], opf[2], allfieldstypes);
        });

        this.m_emitter.initializeBodyEmitter();

        let opidone: Set<string> = new Set<string>();
        for(let i = 0; i < optfields.length; ++i) {
            const opidx = optfields.findIndex((vv, idx) => !opidone.has(`$${vv[1].name}`) && optinits[idx].deps.every((dep) => opidone.has(dep)));
            const ofi = optfields[opidx];
            const iv = optinits[opidx];

            const oftype = this.resolveAndEnsureTypeOnly(ofi[1].sourceLocation, ofi[1].declaredType, ofi[2]);
            const storevar = new MIRRegisterArgument(`$${ofi[1].name}`);
            const guard = new MIRMaskGuard("#maskparam#", opidx, optfields.length);
            if(iv instanceof InitializerEvaluationLiteralExpression) {
                const ttmp = this.m_emitter.generateTmpRegister();
                const oftt = this.checkExpression(env, iv.constexp, ttmp, oftype).getExpressionResult().valtype;

                this.m_emitter.emitRegisterStore(ofi[1].sourceLocation, storevar, storevar, this.m_emitter.registerResolvedTypeReference(oftype), new MIRStatmentGuard(guard, "defaultonfalse", this.emitInlineConvertIfNeeded(ofi[1].sourceLocation, ttmp, oftt, oftype)));
            }
            else if (iv instanceof InitializerEvaluationConstantLoad) {
                this.m_emitter.emitRegisterStore(ofi[1].sourceLocation, storevar, storevar, this.m_emitter.registerResolvedTypeReference(oftype), new MIRStatmentGuard(guard, "defaultonfalse", new MIRGlobalVariable(iv.gkey)));
            }
            else {
                const civ = iv as InitializerEvaluationCallAction;
                this.m_emitter.emitInvokeFixedFunctionWithGuard(ofi[1].sourceLocation, civ.ikey, civ.args, undefined, this.m_emitter.registerResolvedTypeReference(oftype), storevar, new MIRStatmentGuard(guard, "defaultontrue", storevar));
            }

            opidone.add(`$${ofi[1].name}`);
        }

        for (let i = 0; i < clauses.length; ++i) {
            const ttarg = this.m_emitter.generateTmpRegister();
            const chkargs = clauses[i].args.map((cv) => new MIRRegisterArgument(cv));
            this.m_emitter.emitInvokeFixedFunction(clauses[i].sinfo, clauses[i].ikey, chkargs, undefined, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), ttarg);
            this.m_emitter.emitAssertCheck(clauses[i].sinfo, `Failed invariant on line ${clauses[i].srcFile}::${clauses[i].sinfo.line}`, ttarg);
        }

        let consargs: MIRArgument[] = [];
        allfields.forEach((v) => {
            consargs.push(new MIRRegisterArgument(`$${v[1].name}`));
        });

        this.m_emitter.emitReturnAssignOfCons(tdecl.sourceLocation, this.m_emitter.registerResolvedTypeReference(constype), consargs);
        this.m_emitter.emitDirectJump(tdecl.sourceLocation, "returnassign");

        this.m_emitter.setActiveBlock("returnassign");

        const rrinfo = this.generateRefInfoForReturnEmit(constype, []);
        this.emitPrologForReturn(tdecl.sourceLocation, rrinfo, false);
        this.m_emitter.emitDirectJump(tdecl.sourceLocation, "exit");

        let params: MIRFunctionParameter[] = [];
        [...fieldparams.req, ...fieldparams.opt].forEach((fpi) => {
            const ftype =  this.m_emitter.registerResolvedTypeReference(this.resolveAndEnsureTypeOnly(fpi[1][1].sourceLocation, fpi[1][1].declaredType, fpi[1][2]));
            params.push(new MIRFunctionParameter(`$${fpi[0]}`, ftype.trkey));
        });

        const consbody = this.m_emitter.getBody(tdecl.srcFile, tdecl.sourceLocation);
        if (consbody !== undefined) {
            const consinv = new MIRInvokeBodyDecl(this.m_emitter.registerResolvedTypeReference(constype).trkey, "@@constructor", `${constype.idStr}@@constructor`, conskey, ["constructor", "private"], false, tdecl.sourceLocation, tdecl.srcFile, params, optfields.length, this.m_emitter.registerResolvedTypeReference(constype).trkey, undefined, undefined, consbody);
            this.m_emitter.masm.invokeDecls.set(conskey, consinv);
        }
    }

    private processGenerateSpecialPreFunction_FailFast(fkey: MIRInvokeKey, invkparams: {name: string, refKind: "ref" | "out" | "out?" | undefined, ptype: ResolvedType}[], pcodes: Map<string, { pcode: PCode, captured: string[] }>, pargs: [string, ResolvedType][], exps: PreConditionDecl[], binds: Map<string, ResolvedType>, srcFile: string): { ikey: string, sinfo: SourceInfo, srcFile: string }[] {
        try {
            const clauses = exps
            .filter((cev) => isBuildLevelEnabled(cev.level, this.m_buildLevel))
            .map((cev, i) => {
                const iname = `$precond::${fkey}::${i}`;
                const ikey = `$precond_${i}_${fkey}`;

                const idecl = this.processInvokeInfo_ExpressionGeneral(srcFile, cev.exp, iname, ikey, cev.sinfo, ["precondition", "private"], invkparams, this.m_assembly.getSpecialBoolType(), binds, pcodes, pargs);
                this.m_emitter.masm.invokeDecls.set(ikey, idecl as MIRInvokeBodyDecl);

                return { ikey: ikey, sinfo: cev.sinfo, srcFile: srcFile };
            });

            return clauses;
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();

            return [];
        }
    }

    private processGenerateSpecialPreFunction_ResultT(sinfo: SourceInfo, exps: PreConditionDecl[], body: BodyImplementation): BodyImplementation {
        const ops = exps.map((pc) => {
            return new CondBranchEntry<BlockStatement>(new PrefixNotOp(pc.sinfo, pc.exp), new BlockStatement((pc.err as Expression).sinfo, [new ReturnStatement((pc.err as Expression).sinfo, [pc.err as Expression])]));
        });
        const ite = new IfElseStatement(sinfo, new IfElse<BlockStatement>(ops, body.body as BlockStatement));

        return new BodyImplementation(body.id, body.file, new BlockStatement(sinfo, [ite]));
    }

    private processGenerateSpecialPostFunction(fkey: MIRInvokeKey, invkparams: {name: string, refKind: "ref" | "out" | "out?" | undefined, ptype: ResolvedType}[], pcodes: Map<string, { pcode: PCode, captured: string[] }>, pargs: [string, ResolvedType][], exps: PostConditionDecl[], binds: Map<string, ResolvedType>, srcFile: string): { ikey: string, sinfo: SourceInfo, srcFile: string }[] {
        try {
            const clauses = exps
            .filter((cev) => isBuildLevelEnabled(cev.level, this.m_buildLevel))
            .map((cev, i) => {
                const iname = `$postcond::${fkey}::${i}`;
                const ikey = `$postcond_${i}_ + ${fkey}`;

                const idecl = this.processInvokeInfo_ExpressionGeneral(srcFile, cev.exp, iname, ikey, cev.sinfo, ["postcondition", "private"], invkparams, this.m_assembly.getSpecialBoolType(), binds, pcodes, pargs);
                this.m_emitter.masm.invokeDecls.set(ikey, idecl as MIRInvokeBodyDecl);

                return { ikey: ikey, sinfo: cev.sinfo, srcFile: srcFile };
            });

            return clauses;
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();

            return [];
        }
    }

    processOOType(tkey: MIRResolvedTypeKey, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>) {
        try {
            this.m_file = tdecl.srcFile;

            let terms = new Map<string, MIRType>();
            tdecl.terms.forEach((term) => terms.set(term.name, this.m_emitter.registerResolvedTypeReference(binds.get(term.name) as ResolvedType)));

            const provides = this.m_assembly.resolveProvides(tdecl, binds).map((provide) => {
                const ptype = this.resolveAndEnsureTypeOnly(new SourceInfo(0, 0, 0, 0), provide, binds);
                return this.m_emitter.registerResolvedTypeReference(ptype).trkey;
            });

            let conskey: MIRInvokeKey | undefined = undefined;
            let consfuncfields: MIRFieldKey[] = [];
            if (!OOPTypeDecl.attributeSetContains("__internal", tdecl.attributes)) {
                conskey = MIRKeyGenerator.generateFunctionKey(tkey, "@@constructor", new Map<string, ResolvedType>(), []);
                const consenvargs = new Map<string, VarInfo>();
                const ccfields = this.m_assembly.getAllOOFieldsConstructors(tdecl, binds);
                [...ccfields.req, ...ccfields.opt].forEach((ff) => {
                    const fdi = ff[1];
                    const ftype = this.resolveAndEnsureTypeOnly(fdi[1].sourceLocation, fdi[1].declaredType, fdi[2]);
                    consenvargs.set(`$${fdi[1].name}`, new VarInfo(ftype, fdi[1].value === undefined, false, true, ftype));
                });
                consfuncfields = [...ccfields.req, ...ccfields.opt].map((ccf) => MIRKeyGenerator.generateFieldKey(this.resolveOOTypeFromDecls(ccf[1][0], ccf[1][2]), ccf[1][1].name));

                if (tdecl instanceof EntityTypeDecl) {
                    const consenv = TypeEnvironment.createInitialEnvForCall(conskey, binds, new Map<string, { pcode: PCode, captured: string[] }>(), consenvargs, undefined);
                    this.generateConstructor(consenv, conskey, tdecl, binds);
                }
            }

            //
            //TODO: we need to check inheritance and provides rules here -- diamonds, virtual/abstract/override use, etc.
            //

            const ooname = `${tdecl.ns}::${tdecl.name}`;
            if (tdecl instanceof EntityTypeDecl) {
                const fields: MIRFieldDecl[] = [];
                const finfos = [...this.m_assembly.getAllOOFieldsLayout(tdecl, binds)];
                finfos.forEach((ff) => {
                    const fi = ff[1];
                    const f = fi[1];

                    const fkey = MIRKeyGenerator.generateFieldKey(this.resolveOOTypeFromDecls(fi[0], fi[2]), f.name);
                    if (!this.m_emitter.masm.fieldDecls.has(fkey)) {
                        const dtypeResolved = this.resolveAndEnsureTypeOnly(f.sourceLocation, f.declaredType, binds);
                        const dtype = this.m_emitter.registerResolvedTypeReference(dtypeResolved);

                        const fname = `${fi[0].ns}::${fi[0].name}.${f.name}`;
                        const mfield = new MIRFieldDecl(tkey, f.attributes, fname, f.sourceLocation, f.srcFile, fkey, f.name, dtype.trkey);
                        this.m_emitter.masm.fieldDecls.set(fkey, mfield);
                    }

                    fields.push(this.m_emitter.masm.fieldDecls.get(fkey) as MIRFieldDecl);
                });

                let specialTemplateInfo: { tname: string, tkind: MIRResolvedTypeKey }[] | undefined = undefined;
                if (tdecl.specialDecls.has(SpecialTypeCategory.StringOfDecl) || tdecl.specialDecls.has(SpecialTypeCategory.DataStringDecl)) {
                    specialTemplateInfo = [{ tname: "T", tkind: this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType).trkey }];
                }
                else if (tdecl.specialDecls.has(SpecialTypeCategory.BufferDecl) || tdecl.specialDecls.has(SpecialTypeCategory.DataBufferDecl)) {
                    specialTemplateInfo = [{ tname: "T", tkind: this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType).trkey }];
                }
                else if (tdecl.specialDecls.has(SpecialTypeCategory.EnumTypeDecl)) {
                    const etype = (tdecl.staticFunctions.find((vv) => vv.name === "s_create") as StaticFunctionDecl).invoke.params[0].type;
                    const retype = this.resolveAndEnsureTypeOnly(tdecl.sourceLocation, etype, binds);
                    specialTemplateInfo = [{ tname: "T", tkind: this.m_emitter.registerResolvedTypeReference(retype).trkey }];
                }
                else if (tdecl.specialDecls.has(SpecialTypeCategory.VectorTypeDecl) || tdecl.specialDecls.has(SpecialTypeCategory.ListTypeDecl)) {
                    specialTemplateInfo = [{ tname: "T", tkind: this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType).trkey }];
                }
                else if (tdecl.specialDecls.has(SpecialTypeCategory.QueueTypeDecl) || tdecl.specialDecls.has(SpecialTypeCategory.StackTypeDecl)) {
                    specialTemplateInfo = [{ tname: "T", tkind: this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType).trkey }];
                }
                else if (tdecl.specialDecls.has(SpecialTypeCategory.SetTypeDecl)) {
                    specialTemplateInfo = [{ tname: "T", tkind: this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType).trkey }];
                }
                else if (tdecl.specialDecls.has(SpecialTypeCategory.MapTypeDecl)) {
                    specialTemplateInfo = [
                        { tname: "K", tkind: this.m_emitter.registerResolvedTypeReference(binds.get("V") as ResolvedType).trkey },
                        { tname: "V", tkind: this.m_emitter.registerResolvedTypeReference(binds.get("V") as ResolvedType).trkey }
                    ];
                }
                else if (tdecl.specialDecls.has(SpecialTypeCategory.ResultOkDecl) || tdecl.specialDecls.has(SpecialTypeCategory.ResultErrDecl)) {
                    specialTemplateInfo = [
                        { tname: "T", tkind: this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType).trkey },
                        { tname: "E", tkind: this.m_emitter.registerResolvedTypeReference(binds.get("E") as ResolvedType).trkey }
                    ];
                }
                else {
                    ;
                }

                const mirentity = new MIREntityTypeDecl(ooname, tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, conskey, consfuncfields, fields, [...tdecl.specialDecls].map((ee) => (ee as string) as MIRSpecialTypeCategory), specialTemplateInfo);
                this.m_emitter.masm.entityDecls.set(tkey, mirentity);
            }
            else {
                const mirconcept = new MIRConceptTypeDecl(ooname, tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides);
                this.m_emitter.masm.conceptDecls.set(tkey, mirconcept);
            }
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();
        }
    }

    //e.g. expressions in match-case which must be constantly evaluatable
    private processInvokeInfo_ExpressionIsolated(srcFile: string, exp: Expression, iname: string, ikey: MIRInvokeKey, sinfo: SourceInfo, attributes: string[], declaredResult: ResolvedType, binds: Map<string, ResolvedType>): MIRInvokeDecl {
        const resultType = this.generateExpandedReturnSig(sinfo, declaredResult, []);

        const env = TypeEnvironment.createInitialEnvForCall(ikey, binds, new Map<string, { pcode: PCode, captured: string[] }>(), new Map<string, VarInfo>(), declaredResult);
        
        const mirbody = this.checkBodyExpression(srcFile, env, exp, []);
        return new MIRInvokeBodyDecl(undefined, "[SPECIAL]", iname, ikey, attributes, false, sinfo, this.m_file, [], 0, resultType.trkey, undefined, undefined, mirbody as MIRBody);
    }

    //e.g. expressions as default arguments or field values which can only have other specific refs (but not pcodes or random other values)
    private processInvokeInfo_ExpressionLimitedArgs(srcFile: string, exp: Expression, iname: string, ikey: MIRInvokeKey, sinfo: SourceInfo, attributes: string[], invkparams: {name: string, refKind: "ref" | "out" | "out?" | undefined, ptype: ResolvedType}[], declaredResult: ResolvedType, binds: Map<string, ResolvedType>): MIRInvokeDecl {
        let cargs = new Map<string, VarInfo>();
        let params: MIRFunctionParameter[] = [];

        invkparams.forEach((p) => {
            assert(p.refKind === undefined);
            const mtype = this.m_emitter.registerResolvedTypeReference(p.ptype);

            cargs.set(p.name, new VarInfo(p.ptype, true, false, true, p.ptype));
            params.push(new MIRFunctionParameter(p.name, mtype.trkey));
        });

        const resultType = this.generateExpandedReturnSig(sinfo, declaredResult, invkparams);
        const env = TypeEnvironment.createInitialEnvForCall(ikey, binds, new Map<string, { pcode: PCode, captured: string[] }>(), cargs, declaredResult);
        
        const mirbody = this.checkBodyExpression(srcFile, env, exp, []);
        return new MIRInvokeBodyDecl(undefined, "[SPECIAL]", iname, ikey, attributes, false, sinfo, this.m_file, params, 0, resultType.trkey, undefined, undefined, mirbody as MIRBody);
    }

    //e.g. things like pre and post conditions
    private processInvokeInfo_ExpressionGeneral(srcFile: string, exp: Expression, iname: string, ikey: MIRInvokeKey, sinfo: SourceInfo, attributes: string[], invkparams: {name: string, refKind: "ref" | "out" | "out?" | undefined, ptype: ResolvedType}[], declaredResult: ResolvedType, binds: Map<string, ResolvedType>, pcodes: Map<string, { pcode: PCode, captured: string[] }>, pargs: [string, ResolvedType][]): MIRInvokeDecl {
        let cargs = new Map<string, VarInfo>();
        let params: MIRFunctionParameter[] = [];

        invkparams.forEach((p) => {
            assert(p.refKind === undefined);
            const mtype = this.m_emitter.registerResolvedTypeReference(p.ptype);

            cargs.set(p.name, new VarInfo(p.ptype, true, false, true, p.ptype));
            params.push(new MIRFunctionParameter(p.name, mtype.trkey));
        });

        for (let i = 0; i < pargs.length; ++i) {
            cargs.set(pargs[i][0], new VarInfo(pargs[i][1], true, true, true, pargs[i][1]));

            const ctype = this.m_emitter.registerResolvedTypeReference(pargs[i][1]);
            params.push(new MIRFunctionParameter(this.m_emitter.generateCapturedVarName(pargs[i][0]), ctype.trkey));
        }

        const resultType = this.generateExpandedReturnSig(sinfo, declaredResult, invkparams);
        const env = TypeEnvironment.createInitialEnvForCall(ikey, binds, pcodes, cargs, declaredResult);
        
        const mirbody = this.checkBodyExpression(srcFile, env, exp, []);
        return new MIRInvokeBodyDecl(undefined, "[SPECIAL]", iname, ikey, attributes, false, sinfo, this.m_file, params, 0, resultType.trkey, undefined, undefined, mirbody as MIRBody);
    }

    private processInvokeInfo(fname: string, enclosingDecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, kind: "namespace" | "static" | "member" | "operator", iname: string, ikey: MIRInvokeKey, invoke: InvokeDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], pargs: [string, ResolvedType][]): MIRInvokeDecl {
        this.checkInvokeDecl(invoke.sourceLocation, invoke, binds, pcodes);

        let terms = new Map<string, MIRType>();
        invoke.terms.forEach((term) => terms.set(term.name, this.m_emitter.registerResolvedTypeReference(binds.get(term.name) as ResolvedType)));

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && pcodes.some((pc) => pc.code.recursive === "yes"));
        
        let cargs = new Map<string, VarInfo>();
        let fargs = new Map<string, { pcode: PCode, captured: string[] }>();
        let refnames: string[] = [];
        let outparaminfo: {pname: string, defonentry: boolean, ptype: ResolvedType}[] = [];
        let entrycallparams: {name: string, refKind: "ref" | "out" | "out?" | undefined, ptype: ResolvedType}[] = [];
        let params: MIRFunctionParameter[] = [];

        invoke.params.forEach((p) => {
            const pdecltype = this.m_assembly.normalizeTypeGeneral(p.type, binds);
            if (pdecltype instanceof ResolvedFunctionType) {
                const pcarg = { pcode: pcodes[fargs.size], captured: [...pcodes[fargs.size].captured].map((cc) => cc[0]).sort() };
                fargs.set(p.name, pcarg);
            }
            else {
                if (p.refKind !== undefined) {
                    refnames.push(p.name);

                    if (p.refKind === "out" || p.refKind === "out?") {
                        outparaminfo.push({ pname: p.name, defonentry: false, ptype: pdecltype });
                    }
                    else {
                        outparaminfo.push({ pname: p.name, defonentry: true, ptype: pdecltype });
                    }
                }

                if (p.refKind === undefined || p.refKind === "ref") {
                    const mtype = this.m_emitter.registerResolvedTypeReference(pdecltype);

                    cargs.set(p.name, new VarInfo(pdecltype, p.refKind === undefined, false, true, pdecltype));
                    entrycallparams.push({name: p.name, refKind: p.refKind, ptype: pdecltype});
                    params.push(new MIRFunctionParameter(p.name, mtype.trkey));
                }
            }
        });

        if (invoke.optRestType !== undefined) {
            const rtype = this.resolveAndEnsureTypeOnly(invoke.sourceLocation, invoke.optRestType, binds);
            cargs.set(invoke.optRestName as string, new VarInfo(rtype, true, false, true, rtype));

            const resttype = this.m_emitter.registerResolvedTypeReference(rtype);

            entrycallparams.push({name: invoke.optRestName as string, refKind: undefined, ptype: rtype});
            params.push(new MIRFunctionParameter(invoke.optRestName as string, resttype.trkey));
        }

        let prepostcapturednames: string[] = [];
        for (let i = 0; i < pargs.length; ++i) {
            cargs.set(pargs[i][0], new VarInfo(pargs[i][1], true, true, true, pargs[i][1]));

            const ctype = this.m_emitter.registerResolvedTypeReference(pargs[i][1]);
            params.push(new MIRFunctionParameter(this.m_emitter.generateCapturedVarName(pargs[i][0]), ctype.trkey));

            prepostcapturednames.push(this.m_emitter.generateCapturedVarName(pargs[i][0]));
        }

        let optparaminfo: {pname: string, ptype: ResolvedType, maskidx: number, initaction: InitializerEvaluationAction}[] = [];
        invoke.params.forEach((p) => {
            const pdecltype = this.m_assembly.normalizeTypeGeneral(p.type, binds);
            if (pdecltype instanceof ResolvedType && p.isOptional) {
                if (p.defaultexp === undefined) {
                    const ii = new InitializerEvaluationLiteralExpression(new LiteralNoneExpression(invoke.sourceLocation));
                    optparaminfo.push({pname: p.name, ptype: pdecltype, maskidx: optparaminfo.length, initaction: ii});
                }
                else {
                    const ii = this.processExpressionForOptParamDefault(invoke.srcFile, ikey, p.name, pdecltype, p.defaultexp, binds, enclosingDecl, invoke);
                    optparaminfo.push({pname: p.name, ptype: pdecltype, maskidx: optparaminfo.length, initaction: ii});
                }
            }
        });

        const declaredResult = this.resolveAndEnsureTypeOnly(invoke.sourceLocation, invoke.resultType, binds);
        const resultType = this.generateExpandedReturnSig(invoke.sourceLocation, declaredResult, entrycallparams);

        let rprs: { name: string, refKind: "ref" | "out" | "out?" | undefined, ptype: ResolvedType }[] = [];
        rprs.push({ name: "$return", refKind: undefined, ptype: declaredResult });

        let rreforig: { name: string, refKind: "ref" | "out" | "out?" | undefined, ptype: ResolvedType }[] = [];
        invoke.params
        .filter((p) => p.refKind === "ref")
        .map((p) => {
                const pdecltype = this.m_assembly.normalizeTypeOnly(p.type, binds);
                rreforig.push({name: `$${p.name}`, refKind: undefined, ptype: pdecltype});
        });
        
        let preject: [{ ikey: string, sinfo: SourceInfo, srcFile: string }[], string[]] | undefined = undefined;
        let postject: [{ ikey: string, sinfo: SourceInfo, srcFile: string }[], string[]] | undefined = undefined;
        let realbody = invoke.body;
        if (kind === "namespace") {
            if (invoke.preconditions.length !== 0) {
                this.raiseErrorIf(invoke.sourceLocation, invoke.preconditions.some((pre) => pre.isvalidate) && !invoke.preconditions.some((pre) => pre.isvalidate), "Cannot mix terminal and validate preconditions");

                if (invoke.preconditions.every((pre) => pre.isvalidate)) {
                    realbody = this.processGenerateSpecialPreFunction_ResultT(invoke.sourceLocation, invoke.preconditions, invoke.body as BodyImplementation);
                }
                else {
                    const preclauses = this.processGenerateSpecialPreFunction_FailFast(ikey, entrycallparams, fargs, pargs, invoke.preconditions, binds, invoke.srcFile);
                    preject = [preclauses, [...entrycallparams.map((pp) => pp.name), ...prepostcapturednames]];
                }
            }

            if (invoke.postconditions.length !== 0) {
                const postcluases = this.processGenerateSpecialPostFunction(ikey, [...entrycallparams, ...rprs, ...rreforig], fargs, pargs, invoke.postconditions, binds, invoke.srcFile);
                postject = [postcluases, [...[...entrycallparams, ...rprs, ...rreforig].map((pp) => pp.name), ...prepostcapturednames]];
            }
        }
        else {
            const ootype = (enclosingDecl as [MIRType, OOPTypeDecl, Map<string, ResolvedType>])[1];
            const oobinds = (enclosingDecl as [MIRType, OOPTypeDecl, Map<string, ResolvedType>])[2];
            const absconds = this.m_assembly.getAbstractPrePostConds(fname as string, ootype, oobinds, binds);

            if ((absconds !== undefined && absconds.pre[0].length !== 0) || invoke.preconditions.length !== 0) {
                this.raiseErrorIf(invoke.sourceLocation, invoke.preconditions.some((pre) => pre.isvalidate) || (absconds !== undefined && absconds.pre[0].some((pre) => pre.isvalidate)), "Cannot use validate preconditions on non-entrypoint functions");

                const abspreclauses = absconds !== undefined ? this.processGenerateSpecialPreFunction_FailFast(ikey, entrycallparams, fargs, pargs, absconds.pre[0], absconds.pre[1], invoke.srcFile) : [];
                const preclauses = this.processGenerateSpecialPreFunction_FailFast(ikey, entrycallparams, fargs, pargs, invoke.preconditions, binds, invoke.srcFile);
                preject = [[...abspreclauses, ...preclauses], [...entrycallparams.map((pp) => pp.name), ...prepostcapturednames]];
            }

            if ((absconds !== undefined && absconds.post[0].length !== 0) || invoke.postconditions.length !== 0) {
                const abspostclauses = absconds !== undefined ? this.processGenerateSpecialPostFunction(ikey, [...entrycallparams, ...rprs, ...rreforig], fargs, pargs, absconds.post[0], absconds.post[1], invoke.srcFile) : [];
                const postcluases = this.processGenerateSpecialPostFunction(ikey, [...entrycallparams, ...rprs, ...rreforig], fargs, pargs, invoke.postconditions, binds, invoke.srcFile);
                postject = [[...abspostclauses, ...postcluases], [...[...entrycallparams, ...rprs, ...rreforig].map((pp) => pp.name), ...prepostcapturednames]];
            }
        }

        const encdecl = enclosingDecl !== undefined ? enclosingDecl[0].trkey : undefined;
        if (typeof ((invoke.body as BodyImplementation).body) === "string") {
            if ((invoke.body as BodyImplementation).body !== "default" || OOPTypeDecl.attributeSetContains("__primitive", invoke.attributes)) {
                let mpc = new Map<string, MIRPCode>();
                fargs.forEach((v, k) => mpc.set(k, { code: MIRKeyGenerator.generatePCodeKey(v.pcode.code), cargs: [...v.captured].map((cname) => this.m_emitter.generateCapturedVarName(cname)) }));

                let mbinds = new Map<string, MIRResolvedTypeKey>();
                binds.forEach((v, k) => mbinds.set(k, this.m_emitter.registerResolvedTypeReference(v).trkey));

                const scalarslots = invoke.optscalarslots.map((sslot) => {
                    const rtype = this.resolveAndEnsureTypeOnly(invoke.sourceLocation, sslot.vtype, binds);
                    return { vname: sslot.vname, vtype: this.m_emitter.registerResolvedTypeReference(rtype).trkey };
                });
                const mixedslots = invoke.optmixedslots.map((mslot) => {
                    const rtype = this.resolveAndEnsureTypeOnly(invoke.sourceLocation, mslot.vtype, binds);
                    return { vname: mslot.vname, vtype: this.m_emitter.registerResolvedTypeReference(rtype).trkey };
                });

                return new MIRInvokePrimitiveDecl(encdecl, fname, iname, ikey, invoke.attributes, recursive, invoke.sourceLocation, invoke.srcFile, mbinds, params, resultType.trkey, (invoke.body as BodyImplementation).body as string, mpc, scalarslots, mixedslots);
            }
            else {
                //
                //TODO: should do some checking that this is a valid thing to default implement
                //

                const env = TypeEnvironment.createInitialEnvForCall(ikey, binds, fargs, cargs, declaredResult);

                const vops = invoke.params.map((p) => {
                    const bvar = new AccessVariableExpression(invoke.sourceLocation, p.name);
                    const faccess = new PostfixAccessFromName(invoke.sourceLocation, false, undefined, "v");
                    return new PositionalArgument(undefined, false, new PostfixOp(invoke.sourceLocation, bvar, [faccess]));
                });
                const opexp = new CallNamespaceFunctionOrOperatorExpression(invoke.sourceLocation, "NSCore", fname, new TemplateArguments([]), "no", new Arguments(vops), OOPTypeDecl.attributeSetContains("prefix", invoke.attributes) ? "prefix" : "infix");
                const consexp = new CallStaticFunctionOrOperatorExpression(invoke.sourceLocation, invoke.resultType, "create", new TemplateArguments([]), "no", new Arguments([new PositionalArgument(undefined, false, opexp)]), "std");

                const mirbody = this.checkBodyExpression(invoke.srcFile, env, consexp, []) as MIRBody;
                return new MIRInvokeBodyDecl(encdecl, fname, iname, ikey, invoke.attributes, recursive, invoke.sourceLocation, invoke.srcFile, params, 0, resultType.trkey, undefined, undefined, mirbody);
            }
        }
        else {
            const env = TypeEnvironment.createInitialEnvForCall(ikey, binds, fargs, cargs, declaredResult);

            const mirbody = this.checkBodyStatement(invoke.srcFile, env, (realbody as BodyImplementation).body as BlockStatement, optparaminfo, outparaminfo, preject, postject);
            return new MIRInvokeBodyDecl(encdecl, fname, iname, ikey, invoke.attributes, recursive, invoke.sourceLocation, invoke.srcFile, params, optparaminfo.length, resultType.trkey, preject !== undefined ? preject[0].map((pc) => pc.ikey) : undefined, postject !== undefined ? postject[0].map((pc) => pc.ikey) : undefined, mirbody as MIRBody);
        }
    }

    private processPCodeInfo(iname: string, ikey: MIRInvokeKey, sinfo: SourceInfo, pci: InvokeDecl, binds: Map<string, ResolvedType>, fsig: ResolvedFunctionType, pargs: [string, ResolvedType][]): MIRInvokeDecl {
        this.checkPCodeDecl(sinfo, fsig, pci.recursive);

        let cargs = new Map<string, VarInfo>();
        let refnames: string[] = [];
        let outparaminfo: {pname: string, defonentry: boolean, ptype: ResolvedType}[] = [];
        let entrycallparams: {name: string, refKind: "ref" | "out" | "out?" | undefined, ptype: ResolvedType}[] = [];
        let params: MIRFunctionParameter[] = [];

        pci.params.forEach((p, i) => {
            const pdecltype = fsig.params[i].type as ResolvedType;
            if (p.refKind !== undefined) {
                refnames.push(p.name);

                if (p.refKind === "out" || p.refKind === "out?") {
                    outparaminfo.push({ pname: p.name, defonentry: false, ptype: pdecltype });
                }
                else {
                    outparaminfo.push({ pname: p.name, defonentry: true, ptype: pdecltype });
                }
            }

            if (p.refKind === undefined || p.refKind === "ref") {
                const mtype = this.m_emitter.registerResolvedTypeReference(pdecltype);

                cargs.set(p.name, new VarInfo(pdecltype, p.refKind === undefined, false, true, pdecltype));

                entrycallparams.push({ name: p.name, refKind: p.refKind, ptype: pdecltype });
                params.push(new MIRFunctionParameter(p.name, mtype.trkey));
            }
        });

        if (pci.optRestType !== undefined) {
            const rtype = fsig.optRestParamType as ResolvedType;
            cargs.set(pci.optRestName as string, new VarInfo(rtype, true, false, true, rtype));

            const resttype = this.m_emitter.registerResolvedTypeReference(rtype);
            entrycallparams.push({name: pci.optRestName as string, refKind: undefined, ptype: rtype});
            params.push(new MIRFunctionParameter(pci.optRestName as string, resttype.trkey));
        }

        for (let i = 0; i < pargs.length; ++i) {
            cargs.set(pargs[i][0], new VarInfo(pargs[i][1], true, true, true, pargs[i][1]));

            const ctype = this.m_emitter.registerResolvedTypeReference(pargs[i][1]);
            params.push(new MIRFunctionParameter(this.m_emitter.generateCapturedVarName(pargs[i][0]), ctype.trkey));
        }

        let resolvedResult = fsig.resultType;
        const resultType = this.generateExpandedReturnSig(sinfo, resolvedResult, entrycallparams);

        const realbody = ((pci.body as BodyImplementation).body instanceof Expression) 
            ? new BlockStatement(sinfo, [new ReturnStatement(sinfo, [(pci.body as BodyImplementation).body as Expression])])
            : ((pci.body as BodyImplementation).body as BlockStatement);


        const env = TypeEnvironment.createInitialEnvForCall(ikey, binds, new Map<string, { pcode: PCode, captured: string[] }>(), cargs, fsig.resultType);

        const mirbody = this.checkBodyStatement(pci.srcFile, env, realbody, [], outparaminfo, undefined, undefined);
        return new MIRInvokeBodyDecl(undefined, "[PCODE]", iname, ikey, pci.attributes, pci.recursive === "yes", sinfo, pci.srcFile, params, 0, resultType.trkey, undefined, undefined, mirbody as MIRBody);
    }

    processConstExpr(ikey: MIRInvokeKey, srcFile: string, name: string, containingType: [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, cexp: ConstantExpressionValue, attribs: string[], binds: Map<string, ResolvedType>, ddecltype: ResolvedType) {
        try {
            const gkey = "$global_" + ikey;
            const idecl = this.processInvokeInfo_ExpressionIsolated(srcFile, cexp.exp, name, ikey, cexp.exp.sinfo, attribs, ddecltype, binds);
            this.m_emitter.masm.invokeDecls.set(ikey, idecl as MIRInvokeBodyDecl);

            const dtype = this.m_emitter.registerResolvedTypeReference(ddecltype);
            const mirconst = new MIRConstantDecl(containingType !== undefined ? containingType[0].trkey : undefined, attribs, name, ikey, cexp.exp.sinfo, srcFile, dtype.trkey, gkey);

            this.m_emitter.masm.constantDecls.set(gkey, mirconst);
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();
        }
    }

    processFunctionDecl(fkey: MIRInvokeKey, shortname: string, name: string, enclosingdecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, invoke: InvokeDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
        try {
            this.m_file = invoke.srcFile;
            const invinfo = this.processInvokeInfo(shortname, enclosingdecl, enclosingdecl === undefined ? "namespace" : "static", name, fkey, invoke, binds, pcodes, cargs);

            if (invinfo instanceof MIRInvokePrimitiveDecl) {
                this.m_emitter.masm.primitiveInvokeDecls.set(fkey, invinfo);
            }
            else {
                this.m_emitter.masm.invokeDecls.set(fkey, invinfo as MIRInvokeBodyDecl);
            }
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();
        }
    }

    processLambdaFunction(lkey: MIRInvokeKey, invoke: InvokeDecl, sigt: ResolvedFunctionType, binds: Map<string, ResolvedType>, cargs: [string, ResolvedType][]) {
        try {
            this.m_file = invoke.srcFile;
            const iname = `fn::${invoke.sourceLocation.line}##${invoke.sourceLocation.pos}`;
            const invinfo = this.processPCodeInfo(iname, lkey, invoke.sourceLocation, invoke, binds, sigt, cargs);

            this.m_emitter.masm.invokeDecls.set(lkey, invinfo as MIRInvokeBodyDecl);
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();
        }
    }

    processMethodFunction(vkey: MIRVirtualMethodKey, mkey: MIRInvokeKey, shortname: string, name: string, enclosingDecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], mdecl: MemberMethodDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
        if (this.m_emitter.masm.invokeDecls.has(mkey)) {
            return;
        }

        try {
            this.m_file = mdecl.srcFile;
            const invinfo = this.processInvokeInfo(shortname, enclosingDecl, "member", name, mkey, mdecl.invoke, binds, pcodes, cargs);

            this.m_emitter.masm.invokeDecls.set(mkey, invinfo as MIRInvokeBodyDecl);

            if(mdecl.invoke.attributes.includes("override") || mdecl.invoke.attributes.includes("virtual")) {
                const tkey = MIRKeyGenerator.generateTypeKey(this.resolveOOTypeFromDecls(enclosingDecl[1], enclosingDecl[2]));
                (this.m_emitter.masm.entityDecls.get(tkey) as MIREntityTypeDecl).vcallMap.set(vkey, mkey);
            }
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();
        }
    }

    processVirtualOperator(vkey: MIRVirtualMethodKey, mkey: MIRInvokeKey, shortname: string, name: string, enclosingDecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, invoke: InvokeDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
        try {
            this.m_file = invoke.srcFile;
            const invinfo = this.processInvokeInfo(shortname, enclosingDecl, "operator", name, mkey, invoke, binds, pcodes, cargs);

            if (invinfo instanceof MIRInvokePrimitiveDecl) {
                this.m_emitter.masm.primitiveInvokeDecls.set(mkey, invinfo);
            }
            else {
                this.m_emitter.masm.invokeDecls.set(mkey, invinfo as MIRInvokeBodyDecl);
            }

            if(!this.m_emitter.masm.virtualOperatorDecls.has(vkey)) {
                this.m_emitter.masm.virtualOperatorDecls.set(vkey, []);
            }
            (this.m_emitter.masm.virtualOperatorDecls.get(vkey) as MIRInvokeKey[]).push(mkey);
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();
        }
    }

    processRegexInfo() {
        this.m_assembly.getAllLiteralRegexs().forEach((lre) => {
            this.m_emitter.masm.literalRegexs.push(lre);
        })

        this.m_assembly.getAllValidators().forEach((vre) => {
            const vkey = MIRKeyGenerator.generateTypeKey(ResolvedType.createSingle(vre[0]));
            this.m_emitter.masm.validatorRegexs.set(vkey, vre[1]);
        });
    }
}

export { TypeError, TypeChecker };
