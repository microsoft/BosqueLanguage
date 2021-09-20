//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ResolvedType, ResolvedTupleAtomType, ResolvedEntityAtomType, ResolvedRecordAtomType, ResolvedConceptAtomType, ResolvedFunctionType, ResolvedEphemeralListType, ResolvedConceptAtomTypeEntry } from "../ast/resolved_type";
import { Assembly, NamespaceConstDecl, OOPTypeDecl, StaticMemberDecl, EntityTypeDecl, StaticFunctionDecl, InvokeDecl, MemberFieldDecl, NamespaceFunctionDecl, TemplateTermDecl, OOMemberLookupInfo, MemberMethodDecl, BuildLevel, isBuildLevelEnabled, PreConditionDecl, PostConditionDecl, TypeConditionRestriction, ConceptTypeDecl, NamespaceOperatorDecl, StaticOperatorDecl } from "../ast/assembly";
import { TypeEnvironment, VarInfo, FlowTypeTruthValue, ValueType } from "./type_environment";
import { TypeSignature, TemplateTypeSignature, NominalTypeSignature, AutoTypeSignature, FunctionParameter, TupleTypeSignature, FunctionTypeSignature } from "../ast/type_signature";
import { Expression, ExpressionTag, LiteralTypedStringExpression, LiteralTypedStringConstructorExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, NamedArgument, ConstructorPrimaryExpression, ConstructorPrimaryWithFactoryExpression, ConstructorTupleExpression, ConstructorRecordExpression, Arguments, PositionalArgument, CallNamespaceFunctionOrOperatorExpression, CallStaticFunctionOrOperatorExpression, PostfixOp, PostfixOpTag, PostfixAccessFromIndex, PostfixProjectFromIndecies, PostfixAccessFromName, PostfixProjectFromNames, PostfixInvoke, PostfixModifyWithIndecies, PostfixModifyWithNames, PrefixNotOp, LiteralNoneExpression, BinLogicExpression, SelectExpression, VariableDeclarationStatement, VariableAssignmentStatement, IfElseStatement, Statement, StatementTag, BlockStatement, ReturnStatement, LiteralBoolExpression, LiteralStringExpression, BodyImplementation, AssertStatement, CheckStatement, DebugStatement, StructuredVariableAssignmentStatement, StructuredAssignment, RecordStructuredAssignment, VariableDeclarationStructuredAssignment, TupleStructuredAssignment, MatchStatement, MatchGuard, WildcardMatchGuard, TypeMatchGuard, StructureMatchGuard, AbortStatement, YieldStatement, IfExpression, MatchExpression, BlockStatementExpression, ConstructorPCodeExpression, PCodeInvokeExpression, ExpOrExpression, LiteralRegexExpression, ConstructorEphemeralValueList, VariablePackDeclarationStatement, VariablePackAssignmentStatement, NominalStructuredAssignment, ValueListStructuredAssignment, NakedCallStatement, ValidateStatement, IfElse, CondBranchEntry, MapEntryConstructorExpression, SpecialConstructorExpression, RecursiveAnnotation, PostfixIs, PostfixHasIndex, PostfixHasProperty, PostfixAs, LiteralIntegralExpression, LiteralRationalExpression, LiteralFloatPointExpression, LiteralExpressionValue, PostfixGetIndexOrNone, PostfixGetIndexTry, PostfixGetPropertyOrNone, PostfixGetPropertyTry, ConstantExpressionValue, LiteralNumberinoExpression, BinKeyExpression, TemplateArguments, LiteralNothingExpression, LiteralTypedPrimitiveConstructorExpression, IsTypeExpression, AsTypeExpression, PostfixGetPropertyOption, PostfixGetIndexOption, SwitchExpression, WildcardSwitchGuard, LiteralSwitchGuard, SwitchGuard, SwitchStatement } from "../ast/body";
import { PCode, MIREmitter, MIRKeyGenerator } from "../compiler/mir_emitter";
import { MIRArgument, MIRConstantNone, MIRVirtualMethodKey, MIRInvokeKey, MIRResolvedTypeKey, MIRFieldKey, MIRConstantString, MIRRegisterArgument, MIRConstantInt, MIRConstantNat, MIRConstantBigNat, MIRConstantBigInt, MIRConstantRational, MIRConstantDecimal, MIRConstantFloat, MIRGlobalKey, MIRGlobalVariable, MIRBody, MIRMaskGuard, MIRArgGuard, MIRStatmentGuard, MIRConstantFalse, MIRConstantNothing, MIRConstantArgument } from "../compiler/mir_ops";
import { SourceInfo, unescapeLiteralString } from "../ast/parser";
import { MIRConceptTypeDecl, MIRFieldDecl, MIRInvokeDecl, MIRFunctionParameter, MIRType, MIRConstantDecl, MIRPCode, MIRInvokePrimitiveDecl, MIRInvokeBodyDecl, MIRObjectEntityTypeDecl, MIRPrimitiveInternalEntityTypeDecl, MIRPrimitiveMapEntityTypeDecl, MIRPrimitiveListEntityTypeDecl, MIRConstructableInternalEntityTypeDecl, MIREnumEntityTypeDecl, MIRConstructableEntityTypeDecl } from "../compiler/mir_assembly";
import { BSQRegex, RegexAlternation, RegexCharRange, RegexComponent, RegexConstClass, RegexDotCharClass, RegexLiteral, RegexOptional, RegexPlusRepeat, RegexRangeRepeat, RegexSequence, RegexStarRepeat } from "../ast/bsqregex";

import * as assert from "assert";

const NAT_MAX = 18446744073709551615n;
const INT_MIN = -9223372036854775808n;
const INT_MAX = 9223372036854775807n;

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
    readonly shortgkey: string;

    constructor(gkey: MIRGlobalKey, shortgkey: string) {
        super([]);

        this.gkey = gkey;
        this.shortgkey = shortgkey;
    }
}

class InitializerEvaluationCallAction extends InitializerEvaluationAction {
    readonly ikey: MIRInvokeKey;
    readonly shortikey: string;
    readonly args: MIRArgument[];

    constructor(ikey: MIRInvokeKey, shortikey: string, args: MIRArgument[]) {
        super(args.map((arg) => arg.nameID));

        this.ikey = ikey;
        this.shortikey = shortikey;
        this.args = args;
    }
}

class TypeChecker {
    private readonly m_assembly: Assembly;

    private readonly m_buildLevel: BuildLevel;

    private m_file: string;
    private m_errors: [string, number, string][];

    private readonly m_emitter: MIREmitter;
    private readonly m_sortedSrcFiles: {fullname: string, shortname: string}[]; 

    constructor(assembly: Assembly, emitter: MIREmitter, buildlevel: BuildLevel, sortedSrcFiles: {fullname: string, shortname: string}[]) {
        this.m_assembly = assembly;

        this.m_buildLevel = buildlevel;

        this.m_file = "[No File]";
        this.m_errors = [];

        this.m_emitter = emitter;
        this.m_sortedSrcFiles = sortedSrcFiles;
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

    private generateBodyID(sinfo: SourceInfo, srcFile: string, etag?: string): string {
        //Keep consistent with version in parser!!!
        const sfpos = this.m_sortedSrcFiles.findIndex((entry) => entry.fullname === srcFile);

        return `${this.m_sortedSrcFiles[sfpos].shortname}#k${sfpos}${etag !== undefined ? ("_" + etag) : ""}::${sinfo.line}@${sinfo.pos}`;
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

    private getUniqueTypeBinds(ttype: ResolvedType): Map<string, ResolvedType> {
        assert(ttype.options.length === 1 && ((ttype.options[0] instanceof ResolvedConceptAtomType) || (ttype.options[0] instanceof ResolvedEntityAtomType)));

        if(ttype.options[0] instanceof ResolvedEntityAtomType) {
            return (ttype.options[0] as ResolvedEntityAtomType).binds;
        }
        else {
            return (ttype.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds;
        }
    }

    private getTBind(binds: Map<string, ResolvedType>): ResolvedType {
        return binds.get("T") as ResolvedType;
    }

    private getTEBinds(binds: Map<string, ResolvedType>): { T: ResolvedType, E: ResolvedType } {
        return { T: binds.get("T") as ResolvedType, E: binds.get("E") as ResolvedType };
    }

    private getKVBinds(binds: Map<string, ResolvedType>): { K: ResolvedType, V: ResolvedType } {
        return { K: binds.get("K") as ResolvedType, V: binds.get("V") as ResolvedType };
    }

    private emitInlineConvertIfNeeded<T extends MIRArgument>(sinfo: SourceInfo, src: T, srctype: ValueType, trgttype: ResolvedType): T | MIRRegisterArgument {
        if(srctype.layout.isSameType(trgttype)) {
            return src;
        }

        this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(srctype.flowtype, trgttype), `Cannot convert type ${srctype.flowtype.typeID} into ${trgttype.typeID}`);

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

        this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(srctype.flowtype, trgttype), `Cannot convert type ${srctype.flowtype.typeID} into ${trgttype.typeID}`);

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
            this.raiseErrorIf(sinfo, !boundsok, `Template instantiation does not satisfy specified bounds -- not subtype of ${termconstraint.typeID}`);

            if (terminfo.isunique) {
                this.raiseErrorIf(sinfo, !termtype.isUniqueType(), `Template type ${termtype.typeID} is not unique`);
            }

            if(terminfo.isgrounded) {
                this.raiseErrorIf(sinfo, !termtype.isGroundedType(), `Template type ${termtype.typeID} is not grounded`);
            }
        }

        if (optTypeRestrict !== undefined) {
            for (let i = 0; i < optTypeRestrict.constraints.length; ++i) {
                const consinfo = optTypeRestrict.constraints[i];
                const constype = this.resolveAndEnsureTypeOnly(sinfo, consinfo.t, binds)

                const constrainttype = this.resolveAndEnsureTypeOnly(sinfo, consinfo.tconstraint, binds);
                const boundsok = this.m_assembly.subtypeOf(constype, constrainttype);
                this.raiseErrorIf(sinfo, !boundsok, `Template instantiation does not satisfy specified restriction -- not subtype of ${constrainttype.typeID}`);
            }
        }
    }

    private isPCodeTypedExpression(e: Expression, env: TypeEnvironment): boolean {
        if(e instanceof ConstructorPCodeExpression) {
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

    private checkPCodeDecl(sinfo: SourceInfo, fsig: ResolvedFunctionType, rec: "yes" | "no" | "cond", capturedpcodes: PCode[]) {
        this.raiseErrorIf(sinfo, fsig.optRestParamType !== undefined && fsig.params.some((param) => param.isOptional), "Cannot have optional and rest parameters in an invocation signature");
        this.raiseErrorIf(sinfo, rec === "no" && fsig.recursive === "yes", "Recursive decl does not match use");
        this.raiseErrorIf(sinfo, fsig.recursive === "no" && capturedpcodes.some((pc) => pc.code.recursive === "yes"), "Recursive decl does not match use");

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

    private checkValueEq(lhsexp: Expression, lhs: ResolvedType, rhsexp: Expression, rhs: ResolvedType): "err" | "truealways" | "falsealways" | "lhsnone" | "rhsnone" | "lhsnothing" | "rhsnothing" | "lhssomekey" | "rhssomekey" | "stdkey" {
        if (lhsexp instanceof LiteralNoneExpression && rhsexp instanceof LiteralNoneExpression) {
            return "truealways";
        }

        if (lhsexp instanceof LiteralNothingExpression && rhsexp instanceof LiteralNothingExpression) {
            return "truealways";
        }

        if (lhsexp instanceof LiteralNoneExpression) {
            return rhs.options.some((opt) => opt.typeID === "NSCore::None") ? "lhsnone" : "falsealways";
        }

        if (rhsexp instanceof LiteralNoneExpression) {
            return lhs.options.some((opt) => opt.typeID === "NSCore::None") ? "rhsnone" : "falsealways";
        }

        if (lhsexp instanceof LiteralNothingExpression) {
            return rhs.options.some((opt) => opt.typeID === "NSCore::None") ? "lhsnothing" : "falsealways";
        }

        if (rhsexp instanceof LiteralNothingExpression) {
            return lhs.options.some((opt) => opt.typeID === "NSCore::None") ? "rhsnothing" : "falsealways";
        }

        //should be a subtype on one of the sides
        if (!this.m_assembly.subtypeOf(lhs, rhs) && !this.m_assembly.subtypeOf(rhs, lhs)) {
            return "err";
        }

        if (lhs.typeID === rhs.typeID) {
            return "stdkey";
        }
        else {
            return this.m_assembly.subtypeOf(lhs, rhs) ? "lhssomekey" : "rhssomekey";
        }
    }

    private getInfoForHasIndex(sinfo: SourceInfo, rtype: ResolvedType, idx: number): "yes" | "no" | "maybe" {
        this.raiseErrorIf(sinfo, rtype.options.some((atom) => !(atom instanceof ResolvedTupleAtomType)), "Can only load indecies from Tuples");

        const yhas = rtype.options.every((atom) => {
            const tatom = atom as ResolvedTupleAtomType;
            return (idx < tatom.types.length);
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
        return this.m_assembly.typeUpperBound(rtype.options.map((atom) => (atom as ResolvedTupleAtomType).types[idx]));
    }

    private getInfoForLoadFromSafeIndexOnly(sinfo: SourceInfo, rtype: ResolvedType, idx: number): ResolvedType {
        this.raiseErrorIf(sinfo, this.getInfoForHasIndex(sinfo, rtype, idx) === "no");
        return this.m_assembly.typeUpperBound(rtype.options
            .filter((atom) => (atom as ResolvedTupleAtomType).types.length > idx)
            .map((atom) => (atom as ResolvedTupleAtomType).types[idx])
        );
    }

    private getInfoForHasProperty(sinfo: SourceInfo, rtype: ResolvedType, pname: string): "yes" | "no" | "maybe" {
        this.raiseErrorIf(sinfo, rtype.options.some((atom) => !(atom instanceof ResolvedRecordAtomType)), "Can only load properties from Records");

        const yhas = rtype.options.every((atom) => {
            const tatom = atom as ResolvedRecordAtomType;
            const eidx = tatom.entries.findIndex((entry) => entry.pname === pname);
            return (eidx !== -1);
        });

        const yno = rtype.options.every((atom) => {
            const tatom = atom as ResolvedRecordAtomType;
            const eidx = tatom.entries.findIndex((entry) => entry.pname === pname);
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
        return this.m_assembly.typeUpperBound(rtype.options.map((atom) => ((atom as ResolvedRecordAtomType).entries.find((re) => re.pname === pname) as {pname: string, ptype: ResolvedType}).ptype));
    }

    private getInfoForLoadFromSafePropertyOnly(sinfo: SourceInfo, rtype: ResolvedType, pname: string): ResolvedType {
        this.raiseErrorIf(sinfo, this.getInfoForHasProperty(sinfo, rtype, pname) === "no");
        return this.m_assembly.typeUpperBound(rtype.options
            .filter((atom) => (atom as ResolvedRecordAtomType).entries.find((re) => re.pname === pname) !== undefined)
            .map((atom) => ((atom as ResolvedRecordAtomType).entries.find((re) => re.pname === pname) as {pname: string, ptype: ResolvedType}).ptype)
        );
    }

    private checkTypeOkForTupleExpando(sinfo: SourceInfo, rtype: ResolvedType): [number, number] {
        const tslist = rtype.options.map((opt) => {
            this.raiseErrorIf(sinfo, !(opt instanceof ResolvedTupleAtomType), "Can only expando into positional arguments with Tuple");
            return opt as ResolvedTupleAtomType;
        });

        const reqlen = tslist.reduce((acc, v) => Math.min(acc, v.types.length), Number.MAX_SAFE_INTEGER);
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
                allNames.add(re.pname);

                if (rslist.every((rtype) => rtype.entries.find((ee) => ee.pname === re.pname) !== undefined)) {
                    reqNames.add(re.pname);
                }
            });
        });

        return [reqNames, allNames];
    }

    private checkPCodeExpressionInfer(env: TypeEnvironment, exp: ConstructorPCodeExpression, cbinds: Map<string, ResolvedType>, expectedFunction: ResolvedFunctionType | undefined): ResolvedType {
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

        let capturedpcode = new Map<string, { pcode: PCode, captured: string[] }>();
        exp.invoke.captureSet.forEach((v) => {
            if (v === "%this_captured" && env.lookupVar(v) === null) {
                const vinfo = env.lookupVar("this") as VarInfo;
                cargs.set(v, vinfo);
            }
            else {
                if (env.pcodes.has(v)) {
                    capturedpcode.set(v, env.pcodes.get(v) as { pcode: PCode, captured: string[] });
                }
                else {
                    const vinfo = env.lookupVar(v) as VarInfo;
                    this.raiseErrorIf(exp.sinfo, vinfo.declaredType instanceof ResolvedFunctionType, "Cannot capture function typed argument");
                    cargs.set(v, vinfo);
                }
            }
        });

        //TODO: this may capture too many types that are not strictly needed -- maybe want to parse scope track captured types like we do for captured variables
        let bodybinds = new Map<string, ResolvedType>(cbinds);
        env.terms.forEach((ttype, ttname) => {
            if (!bodybinds.has(ttname)) {
                bodybinds.set(ttname, ttype);
            }
        });

        const pikey = MIRKeyGenerator.generatePCodeKey(exp.invoke.isPCodeFn, exp.invoke.bodyID);
        const pcenv = TypeEnvironment.createInitialEnvForCall(pikey, exp.invoke.bodyID, bodybinds, new Map<string, { pcode: PCode, captured: string[] }>(), cargs, undefined);

        if ((exp.invoke.body as BodyImplementation).body instanceof Expression) {
            const dummyreg = this.m_emitter.generateTmpRegister();
            const evalue = this.checkExpression(pcenv, (exp.invoke.body as BodyImplementation).body as Expression, dummyreg, undefined);
            return evalue.getExpressionResult().valtype.flowtype;
        }
        else {
            const renv = this.checkBlock(pcenv, (exp.invoke.body as BodyImplementation).body as BlockStatement);

            this.raiseErrorIf(exp.sinfo, renv.hasNormalFlow(), "Not all flow paths return a value!");
            return renv.returnResult as ResolvedType;
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
            
            if (arg.value instanceof ConstructorPCodeExpression) {
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

    private checkPCodeExpression(env: TypeEnvironment, exp: ConstructorPCodeExpression, cbinds: Map<string, ResolvedType>, expectedFunction: ResolvedFunctionType | undefined): PCode {
        this.raiseErrorIf(exp.sinfo, exp.isAuto && expectedFunction === undefined, "Could not infer auto function type");

        const ltypetry = exp.isAuto ? expectedFunction : this.m_assembly.normalizeTypeFunction(exp.invoke.generateSig(), cbinds);
        this.raiseErrorIf(exp.sinfo, ltypetry === undefined, "Invalid lambda type");

        this.raiseErrorIf(exp.sinfo, exp.invoke.params.length !== (ltypetry as ResolvedFunctionType).params.length, "Mismatch in expected parameter count and provided function parameter count");
        this.raiseErrorIf(exp.sinfo, expectedFunction !== undefined && !this.m_assembly.functionSubtypeOf(ltypetry as ResolvedFunctionType, expectedFunction), "Mismatch in expected and provided function signature");

        let capturedMap: Map<string, ResolvedType> = new Map<string, ResolvedType>();
        let capturedpcode = new Map<string, { pcode: PCode, captured: string[] }>();

        let captures: string[] = [];
        exp.invoke.captureSet.forEach((v) => captures.push(v));
        captures.sort();

        captures.forEach((v) => {
            if (v === "%this_captured" && env.lookupVar(v) === null) {
                const vinfo = env.lookupVar("this") as VarInfo;

                capturedMap.set(v, vinfo.flowType);
            }
            else {
                if (env.pcodes.has(v)) {
                    capturedpcode.set(v, env.pcodes.get(v) as { pcode: PCode, captured: string[] });
                }
                else {
                    const vinfo = env.lookupVar(v) as VarInfo;
                    this.raiseErrorIf(exp.sinfo, vinfo.declaredType instanceof ResolvedFunctionType, "Cannot capture function typed argument");

                    capturedMap.set(v, vinfo.flowType);
                }
            }
        });

        //TODO: this may capture too many types that are not strictly needed -- maybe want to parse scope track captured types like we do for captured variables
        let bodybinds = new Map<string, ResolvedType>(cbinds);
        env.terms.forEach((ttype, ttname) => {
            if (!bodybinds.has(ttname)) {
                bodybinds.set(ttname, ttype);
            }
        });

        const ikey = MIRKeyGenerator.generatePCodeKey(exp.invoke.isPCodeFn, exp.invoke.bodyID);
        this.m_emitter.registerPCode(ikey, ikey, exp.invoke, ltypetry as ResolvedFunctionType, bodybinds, [...capturedMap].sort((a, b) => a[0].localeCompare(b[0])), [...capturedpcode].sort((a, b) => a[0].localeCompare(b[0])));

        return { code: exp.invoke, ikey: ikey, captured: capturedMap, ftype: ltypetry as ResolvedFunctionType };
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
                if (narg.value instanceof ConstructorPCodeExpression) {
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
                if (parg.value instanceof ConstructorPCodeExpression) {
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

                if (arg.value instanceof ConstructorPCodeExpression) {
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

            if (arg.value instanceof ConstructorPCodeExpression) {
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

    private checkArgumentsTupleConstructor(sinfo: SourceInfo, args: [ResolvedType, MIRRegisterArgument][], trgt: MIRRegisterArgument): ResolvedType {
        const tupleatom = ResolvedTupleAtomType.create(args.map((targ) => targ[0]));
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
            if(itype !== undefined && itype.entries.findIndex((entry) => entry.pname === (arg as NamedArgument).name) !== -1) {
                etype = (itype.entries.find((entry) => entry.pname === (arg as NamedArgument).name) as {pname: string, ptype: ResolvedType}).ptype;
            }
            
            const earg = this.checkExpression(env, arg.value, treg, etype).getExpressionResult();
            const ttype = etype || earg.valtype.flowtype;
            this.raiseErrorIf(arg.value.sinfo, ttype.options.some((opt) => opt instanceof ResolvedEphemeralListType), "Cannot store ephemeral lists");
            this.raiseErrorIf(arg.value.sinfo, !this.m_assembly.subtypeOf(earg.valtype.flowtype, ttype), "Argument not of expected type");

            eargs.push([(arg as NamedArgument).name, ttype, this.emitInlineConvertIfNeeded(arg.value.sinfo, treg, earg.valtype, ttype)]);
        }

        return eargs;
    }

    private checkArgumentsRecordConstructor(sinfo: SourceInfo, args: [string, ResolvedType, MIRRegisterArgument][], trgt: MIRRegisterArgument): ResolvedType {
        let rargs: [string, ResolvedType][] = [];

        const seenNames = new Set<string>();
        for (let i = 0; i < args.length; ++i) {
            this.raiseErrorIf(sinfo, seenNames.has(args[i][0] as string), "Duplicate argument name in Record constructor");

            rargs.push([args[i][0] as string, args[i][1] as ResolvedType]);
        }

        const rentries = rargs.map((targ) => { return {pname: targ[0], ptype: targ[1]}; });
        const recordatom = ResolvedRecordAtomType.create(rentries);
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

        const tkey = this.m_emitter.registerResolvedTypeReference(resulttype).typeID;
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
        if(oftype.object.attributes.includes("__constructable")) {
            if(oftype.object.attributes.includes("__enum_type")) {
                this.raiseErrorIf(sinfo, args.argList.length !== 1 || !(args.argList[0] instanceof PositionalArgument), "Expected single argument");

                const treg = this.m_emitter.generateTmpRegister();
                const earg = this.checkExpression(env, (args.argList[0] as PositionalArgument).value, treg, this.m_assembly.getSpecialNatType()).getExpressionResult();

                return [{ name: "[constructable]", argtype: earg.valtype, ref: undefined, expando: false, pcode: undefined, treg: treg }];
            }
            else {
                const atype = (oftype.object.memberMethods.find((mm) => mm.name === "value") as MemberMethodDecl).invoke.resultType;
                const ratype = this.resolveAndEnsureTypeOnly(sinfo, atype, oftype.binds);

                this.raiseErrorIf(sinfo, args.argList.length !== 1 || !(args.argList[0] instanceof PositionalArgument), "Expected single argument");

                const treg = this.m_emitter.generateTmpRegister();
                const earg = this.checkExpression(env, (args.argList[0] as PositionalArgument).value, treg, ratype).getExpressionResult();

                return [{ name: "[constructable]", argtype: earg.valtype, ref: undefined, expando: false, pcode: undefined, treg: treg }];
            }
        }
        else {
            this.raiseErrorIf(sinfo, oftype.object.attributes.includes("__internal"), "Type is not constructable");

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
    }

    private checkArgumentsEntityConstructor(sinfo: SourceInfo, oftype: ResolvedEntityAtomType, args: ExpandedArgument[], trgt: MIRRegisterArgument): ResolvedType {
        if(oftype.object.attributes.includes("__constructable")) {
            if(oftype.object.attributes.includes("__enum_type")) {
                this.raiseErrorIf(sinfo, args.length !== 1, "Expected single argument");

                const mirfromtype = this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNatType());

                const constype = ResolvedType.createSingle(oftype);
                const rtype = this.m_emitter.registerResolvedTypeReference(constype);

                this.m_emitter.emitInject(sinfo, mirfromtype, rtype, args[0].treg as MIRRegisterArgument, trgt);
                return constype;
            }
            else {
                this.raiseErrorIf(sinfo, !oftype.object.attributes.includes("__typedprimitive"), "Can only construct typed primitives directly");
                this.raiseErrorIf(sinfo, args.length !== 1, "Expected single argument");

                const atype = (oftype.object.memberMethods.find((mm) => mm.name === "value") as MemberMethodDecl).invoke.resultType;
                const ratype = this.resolveAndEnsureTypeOnly(sinfo, atype, oftype.binds);
                const mirfromtype = this.m_emitter.registerResolvedTypeReference(ratype);

                const aarg = this.emitInlineConvertIfNeeded(sinfo, args[0].treg as MIRRegisterArgument, args[0].argtype as ValueType, ratype);

                const constype = ResolvedType.createSingle(oftype);
                const rtype = this.m_emitter.registerResolvedTypeReference(constype);

                if (oftype.object.invariants.length === 0) {
                    this.m_emitter.emitInject(sinfo, mirfromtype, rtype, aarg, trgt);
                }
                else {
                    const conskey = MIRKeyGenerator.generateFunctionKeyWType(constype, "@@constructor", new Map<string, ResolvedType>(), []);
                    this.m_emitter.emitInvokeFixedFunction(sinfo, conskey.keyid, [aarg], undefined, rtype, trgt);
                }
                return constype;
            }
        }
        else {
            this.raiseErrorIf(sinfo, oftype.object.attributes.includes("__internal"), "Type is not constructable");

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
                    this.raiseErrorIf(sinfo, fidx === -1, `Entity ${oftype.typeID} does not have field named "${arg.name}"`);
                    this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${arg.name}"`);

                    filledLocations[fidx] = { vtype: arg.argtype as ValueType, mustDef: true, fflagchk: false, trgt: arg.treg as MIRRegisterArgument };
                    if (flatfinfo[fidx][1].value !== undefined) {
                        this.m_emitter.emitSetGuardFlagConstant(sinfo, fflag as string, fidx - optfirst, true);
                    }
                }
                else if (arg.expando && (arg.argtype as ValueType).flowtype.isRecordTargetType()) {
                    const expandInfo = this.checkTypeOkForRecordExpando(sinfo, (arg.argtype as ValueType).flowtype);

                    expandInfo[1].forEach((pname) => {
                        const fidx = fields.indexOf(pname);
                        this.raiseErrorIf(sinfo, fidx === -1, `Entity ${oftype.typeID} does not have field named "${pname}"`);
                        this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${pname}"`);

                        this.raiseErrorIf(sinfo, flatfinfo[fidx][1].value !== undefined && !expandInfo[0].has(pname), `Constructor requires "${pname}" but it is provided as an optional argument`);

                        const etreg = this.m_emitter.generateTmpRegister();
                        const lvtype = this.getInfoForLoadFromSafeProperty(sinfo, (arg.argtype as ValueType).flowtype, pname);
                        const ptype = this.m_emitter.registerResolvedTypeReference(lvtype);

                        if (expandInfo[0].has(pname)) {
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
                    if (flatfinfo[ii][1].value !== undefined) {
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

                        if (ectr < expandInfo[0]) {
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

                if (filledLocations[i].fflagchk) {
                    cargs.push(this.emitCheckedInlineConvertIfNeeded(sinfo, filledLocations[i].trgt, filledLocations[i].vtype, fieldtype, new MIRStatmentGuard(new MIRMaskGuard(fflag as string, i - optfirst, optcount), "defaultonfalse", undefined)));
                }
                else {
                    cargs.push(this.emitInlineConvertIfNeeded(sinfo, filledLocations[i].trgt, filledLocations[i].vtype, fieldtype));
                }
            }

            const constype = ResolvedType.createSingle(oftype);
            const rtype = this.m_emitter.registerResolvedTypeReference(constype);

            const ikey = MIRKeyGenerator.generateFunctionKeyWType(constype, "@@constructor", new Map<string, ResolvedType>(), []);
            this.m_emitter.emitInvokeFixedFunction(sinfo, ikey.keyid, cargs, fflag, rtype, trgt);
            return constype;
        }
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
                this.raiseErrorIf(sinfo, !this.m_assembly.functionSubtypeOf(filledLocations[j].vtype as ResolvedFunctionType, paramtype as ResolvedFunctionType), `Parameter ${sig.params[j].name} expected function of type ${paramtype.typeID}`);

                pcodes.push(filledLocations[j].pcode as PCode);
            }
            else {
                this.raiseErrorIf(sinfo, filledLocations[j].pcode !== undefined, `Parameter ${sig.params[j].name} cannot take a function`);

                if (sig.params[j].refKind !== undefined) {
                    this.raiseErrorIf(sinfo, filledLocations[j].ref === undefined, `Parameter ${sig.params[j].name} expected reference parameter`);
                    this.raiseErrorIf(sinfo, !(filledLocations[j].vtype as ValueType).layout.isSameType(paramtype as ResolvedType), `Parameter ${sig.params[j].name} expected argument of type ${paramtype.typeID}`);

                    refs.push([...(filledLocations[j].ref as ["ref" | "out" | "out?", MIRRegisterArgument]), (filledLocations[j].vtype as ValueType).layout] as ["ref" | "out" | "out?", MIRRegisterArgument, ResolvedType]);
                }
                else {
                    this.raiseErrorIf(sinfo, filledLocations[j].ref !== undefined, `Parameter ${sig.params[j].name} reference parameter is not allowed in this position`);
                    this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf((filledLocations[j].vtype as ValueType).flowtype, paramtype as ResolvedType), `Parameter ${sig.params[j].name} expected argument of type ${paramtype.typeID}`);
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

        //take all the pcodes and pass the "captured" variables in as arguments in pcode/alpha order
        let cinfo: [string, ResolvedType][] = [];
        if (pcodes.length !== 0) {
            const scodes = [...pcodes].sort((a, b) => a.ikey.localeCompare(b.ikey));

            for(let j = 0; j < scodes.length; ++j) {
                const cnames = [...pcodes[j].captured].map((cn) => cn[0]).sort();
                for (let i = 0; i < cnames.length; ++i) {
                    const vinfo = env.lookupVar(cnames[i]);
                    if (vinfo === null) {
                        //This is the first place we capture $$this_captured so we sould pass "this" as the arg for it
                        const tinfo = env.lookupVar("this") as VarInfo;
                        margs.push(new MIRRegisterArgument("this"));

                        cinfo.push([cnames[i], tinfo.flowType]);
                    }
                    else {
                        if (env.getLocalVarInfo(cnames[i]) !== undefined) {
                            margs.push(new MIRRegisterArgument(cnames[i]));
                        }
                        else {
                            margs.push(new MIRRegisterArgument(vinfo.isCaptured ? this.m_emitter.generateCapturedVarName(cnames[i], scodes[j].code.bodyID) : cnames[i]));
                        }

                        cinfo.push([cnames[i], vinfo.flowType]);
                    }
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

        //take all the pcodes and pass the "captured" variables in as arguments in pcode/alpha order
        let cinfo: [string, ResolvedType][] = [];
        if (pcodes.length !== 0) {
            const scodes = [...pcodes].sort((a, b) => a.ikey.localeCompare(b.ikey));

            for(let j = 0; j < scodes.length; ++j) {
                const cnames = [...pcodes[j].captured].map((cn) => cn[0]).sort();
                for (let i = 0; i < cnames.length; ++i) {
                    const vinfo = env.lookupVar(cnames[i]);
                    if (vinfo === null) {
                        //This is the first place we capture $$this_captured so we sould pass "this" as the arg for it
                        const tinfo = env.lookupVar("this") as VarInfo;
                        margs.push(new MIRRegisterArgument("this"));

                        cinfo.push([cnames[i], tinfo.flowType]);
                    }
                    else {
                        if (env.getLocalVarInfo(cnames[i]) !== undefined) {
                            margs.push(new MIRRegisterArgument(cnames[i]));
                        }
                        else {
                            margs.push(new MIRRegisterArgument(vinfo.isCaptured ? this.m_emitter.generateCapturedVarName(cnames[i], scodes[j].code.bodyID) : cnames[i]));
                        }

                        cinfo.push([cnames[i], vinfo.flowType]);
                    }
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

    private checkLiteralNothingExpression(env: TypeEnvironment, exp: LiteralNothingExpression, trgt: MIRRegisterArgument): TypeEnvironment {
        this.m_emitter.emitLoadConstNothing(exp.sinfo, trgt);

        return env.setUniformResultExpression(this.m_assembly.getSpecialNothingType());
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

        if(iitype.isSameType(this.m_assembly.getSpecialIntType()) || iitype.isSameType(this.m_assembly.getSpecialBigIntType())) {
            const ispec = iitype.isSameType(this.m_assembly.getSpecialIntType()) ? "i" : "I";

            if(ispec === "i") {
                const biv = BigInt(exp.value);
                this.raiseErrorIf(exp.sinfo, biv < INT_MIN || INT_MAX < biv, "Constant Int out of valid range");
            }

            this.m_emitter.emitLoadConstIntegralValue(exp.sinfo, this.m_emitter.registerResolvedTypeReference(iitype), exp.value + ispec, trgt);
            return env.setUniformResultExpression(iitype);
        }
        else if(iitype.isSameType(this.m_assembly.getSpecialNatType()) || iitype.isSameType(this.m_assembly.getSpecialBigNatType())) {
            this.raiseErrorIf(exp.sinfo, exp.value.startsWith("-"), "Cannot have negative BigNat literal");

            const ispec = iitype.isSameType(this.m_assembly.getSpecialNatType()) ? "n" : "N";

            if(ispec === "n") {
                const biv = BigInt(exp.value);
                this.raiseErrorIf(exp.sinfo, NAT_MAX < biv, "Constant Nat out of valid range");
            }

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
            this.raiseErrorIf(exp.sinfo, !iitype.isUniqueCallTargetType() || !iitype.getUniqueCallTargetType().object.attributes.includes("__typedprimitive"), "Not a valid typed primitive decl type");

            const tt = (iitype.getUniqueCallTargetType().object.memberFields.find((mf) => mf.name === "value") as MemberFieldDecl).declaredType;
            const rtt = this.m_assembly.normalizeTypeOnly(tt, new Map<string, ResolvedType>());

            let vspec = "[MISSING CASE]";
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
        
        if(itype.isSameType(this.m_assembly.getSpecialNatType()) || itype.isSameType(this.m_assembly.getSpecialBigNatType())) {
            this.raiseErrorIf(exp.sinfo, exp.value.startsWith("-"), "Cannot have negative Nat/BigNat literal");
        }

        if(itype.isSameType(this.m_assembly.getSpecialIntType())) {
            const biv = BigInt(exp.value.slice(0, exp.value.length - 1));
            this.raiseErrorIf(exp.sinfo, biv < INT_MIN || INT_MAX < biv, "Constant Int out of valid range");
        }

        if(itype.isSameType(this.m_assembly.getSpecialNatType())) {
            const biv = BigInt(exp.value.slice(0, exp.value.length - 1));
            this.raiseErrorIf(exp.sinfo, NAT_MAX < biv, "Constant Nat out of valid range");
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

    private checkStringOfCommon(sinfo: SourceInfo, env: TypeEnvironment, ttype: TypeSignature): { oftype: [OOPTypeDecl, Map<string, ResolvedType>], ofresolved: ResolvedType, stringtype: ResolvedType } {
        const oftype = this.resolveAndEnsureTypeOnly(sinfo, ttype, env.terms);
        this.raiseErrorIf(sinfo, !oftype.isUniqueCallTargetType() || !oftype.getUniqueCallTargetType().object.attributes.includes("__validator_type"), "Validator type must be a unique type");
        
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
        this.raiseErrorIf(sinfo, (oftype.options[0] instanceof ResolvedEntityAtomType) || (oftype.options[0] instanceof ResolvedConceptAtomType && (oftype.options[0] as ResolvedConceptAtomType).conceptTypes.length !== 1), "Cannot have & of concepts");
        
        const aoftype = oftype.options[0];
        const oodecl = (aoftype instanceof ResolvedEntityAtomType) ? aoftype.object : (aoftype as ResolvedConceptAtomType).conceptTypes[0].concept;
        const oobinds = (aoftype instanceof ResolvedEntityAtomType) ? aoftype.binds : (aoftype as ResolvedConceptAtomType).conceptTypes[0].binds;

        const fdecltry = oodecl.staticFunctions.find((sf) => sf.name === "tryParse");
        this.raiseErrorIf(sinfo, fdecltry === undefined, `Constant value not defined for type '${oftype.typeID}'`);

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
        
        if(oftype.getUniqueCallTargetType().object.attributes.includes("__validator_type")) {
            const aoftype = this.checkStringOfCommon(exp.sinfo, env, exp.stype);
    
            const sdecl = aoftype.oftype[0].staticFunctions.find((sf) => sf.name === "accepts");
            assert(sdecl !== undefined);

            const vv = this.m_assembly.tryGetValidatorForFullyResolvedName(oftype.typeID);
            this.raiseErrorIf(exp.sinfo, vv === undefined, `Bad Validator type for StringOf ${oftype.typeID}`);
            
            const argstr = unescapeLiteralString(exp.value.substring(1, exp.value.length - 1));
            const mtchre = (vv as BSQRegex).compileToJS();
            //
            //TODO: we actually have NFA semantics for our regex -- JS matching is a subset so we need to replace this!!!
            //
            const mtch = new RegExp(mtchre, "u").exec(argstr);
            this.raiseErrorIf(exp.sinfo, mtch === null || mtch[0].length !== argstr.length, "Literal string failed Validator regex");

            const stype = this.m_emitter.registerResolvedTypeReference(aoftype.stringtype);

            this.m_emitter.emitLoadLiteralStringOf(exp.sinfo, exp.value, stype.typeID, trgt);
            return env.setUniformResultExpression(aoftype.stringtype);
        }
        else {
            const aoftype = this.checkDataStringCommon(exp.sinfo, env, exp.stype);
            const sdecl = aoftype.oftype[0].staticFunctions.find((sf) => sf.name === "accepts");
            this.raiseErrorIf(exp.sinfo, sdecl === undefined, "Missing static function 'accepts'");

            const stype = this.m_emitter.registerResolvedTypeReference(aoftype.stringtype);
            const presult = this.m_emitter.registerResolvedTypeReference(aoftype.parsetype);

            const sbinds = this.m_assembly.resolveBindsForCallComplete([], [], (aoftype.stringtype.options[0] as ResolvedEntityAtomType).binds, new Map<string, ResolvedType>(), new Map<string, ResolvedType>()) as Map<string, ResolvedType>;
            const ctype = this.m_emitter.registerResolvedTypeReference(this.resolveOOTypeFromDecls(aoftype.oftype[0], aoftype.oftype[1]));
            const skey = this.m_emitter.registerStaticCall(this.resolveOOTypeFromDecls(aoftype.oftype[0], aoftype.oftype[1]), [ctype, aoftype.oftype[0], aoftype.oftype[1]], sdecl as StaticFunctionDecl, "accepts", sbinds, [], []);

            const tmps = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitInvokeFixedFunction(exp.sinfo, skey, [new MIRConstantString(exp.value)], undefined, presult, tmps);
            this.m_emitter.emitAssertCheck(exp.sinfo, "String not parsable as given type", tmps);
            
            this.m_emitter.emitLoadConstDataString(exp.sinfo, exp.value, stype.typeID, trgt);
            return env.setUniformResultExpression(aoftype.stringtype);
        }
    }

    private checkDataStringConstructor(env: TypeEnvironment, exp: LiteralTypedStringConstructorExpression, trgt: MIRRegisterArgument): TypeEnvironment {
        const aoftype = this.checkDataStringCommon(exp.sinfo, env, exp.stype);

        const sdecl = aoftype.oftype[0].staticFunctions.find((sf) => sf.name === "parse");
        this.raiseErrorIf(exp.sinfo, sdecl === undefined, "Missing static function 'parse'");

        const presult = this.m_emitter.registerResolvedTypeReference(aoftype.parsetype);

        const sbinds = this.m_assembly.resolveBindsForCallComplete([], [], (aoftype.stringtype.options[0] as ResolvedEntityAtomType).binds, new Map<string, ResolvedType>(), new Map<string, ResolvedType>()) as Map<string, ResolvedType>;
        const ctype = this.m_emitter.registerResolvedTypeReference(this.resolveOOTypeFromDecls(aoftype.oftype[0], aoftype.oftype[1]));
        const skey = this.m_emitter.registerStaticCall(this.resolveOOTypeFromDecls(aoftype.oftype[0], aoftype.oftype[1]), [ctype, aoftype.oftype[0], aoftype.oftype[1]], sdecl as StaticFunctionDecl, "tryParse", sbinds, [], []);

        const tmps = this.m_emitter.generateTmpRegister();
        this.m_emitter.emitInvokeFixedFunction(exp.sinfo, skey, [new MIRConstantString(exp.value)], undefined, presult, tmps);

        const oktype = this.m_assembly.getOkType(aoftype.ofresolved, this.m_assembly.getSpecialStringType());
        const miroktype = this.m_emitter.registerResolvedTypeReference(oktype);
        
        const tmpokt = this.m_emitter.generateTmpRegister();
        this.m_emitter.emitCheckNoError(exp.sinfo, tmps, presult, miroktype, tmpokt);
        this.m_emitter.emitAssertCheck(exp.sinfo, "String not parsable as given type", tmpokt);

        const argok = this.emitInlineConvertIfNeeded(exp.sinfo, tmps, new ValueType(aoftype.parsetype, oktype), oktype);
        this.m_emitter.emitExtract(exp.sinfo, miroktype, ctype, argok, trgt);
        return env.setUniformResultExpression(aoftype.ofresolved);
    }

    private checkTypedTypedNumericConstructor_helper(sinfo: SourceInfo, env: TypeEnvironment, value: string, tntt: ResolvedType, ntype: ResolvedType, trgt: MIRRegisterArgument): TypeEnvironment {
        const oftype = (tntt.options[0] as ResolvedEntityAtomType).object;
        const ofbinds = (tntt.options[0] as ResolvedEntityAtomType).binds;

        this.raiseErrorIf(sinfo, !oftype.attributes.includes("__typedprimitive"), `Cannot construct typed primitive of ${tntt.typeID}`);
        this.raiseErrorIf(sinfo, !oftype.attributes.includes("__typedeclable"), `Cannot construct typed primitive using ${tntt.typeID}`);

        let nval: MIRConstantArgument = new MIRConstantNone();
        if(ntype.isSameType(this.m_assembly.getSpecialIntType())) {
            const biv = BigInt(value.slice(0, value.length - 1));
            this.raiseErrorIf(sinfo, biv < INT_MIN || INT_MAX < biv, "Constant Int out of valid range");

            nval = new MIRConstantInt(value);
        }
        else if(ntype.isSameType(this.m_assembly.getSpecialNatType())) {
            this.raiseErrorIf(sinfo, value.startsWith("-"), "Cannot have negative Nat literal");
            
            const biv = BigInt(value.slice(0, value.length - 1));
            this.raiseErrorIf(sinfo, NAT_MAX < biv, "Constant Nat out of valid range");

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
            const fkey = MIRKeyGenerator.generateFunctionKeyWType(tntt, "@@invariant", ofbinds, []);
        
            const tmps = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitInvokeFixedFunction(sinfo, fkey.keyid, [nval], undefined, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), tmps);
            this.m_emitter.emitAssertCheck(sinfo, "Value does not satisfy requirements for type", tmps);    
        }
        
        this.m_emitter.emitLoadTypedNumeric(sinfo, nval, this.m_emitter.registerResolvedTypeReference(tntt).typeID, trgt);
        return env.setUniformResultExpression(tntt);
    }

    private checkTypedTypedNumericConstructor(env: TypeEnvironment, exp: LiteralTypedPrimitiveConstructorExpression, trgt: MIRRegisterArgument): TypeEnvironment {
        const tntt = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.oftype, env.terms);
        const ntype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.vtype, new Map<string, ResolvedType>());

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
            this.m_emitter.emitRegisterStore(exp.sinfo, new MIRGlobalVariable(gkey.keyid, gkey.shortname), trgt, this.m_emitter.registerResolvedTypeReference(rtype), undefined);
        }

        return env.setUniformResultExpression(rtype);
    }

    private checkAccessStaticField(env: TypeEnvironment, exp: AccessStaticFieldExpression, trgt: MIRRegisterArgument): TypeEnvironment {
        const oftype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.stype, env.terms);

        const cdecltry = this.m_assembly.tryGetConstMemberUniqueDeclFromType(oftype, exp.name);
        this.raiseErrorIf(exp.sinfo, cdecltry === undefined, `Constant value not defined (or not uniquely defined) for type ${oftype.typeID}`);

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
            const skey = this.m_emitter.registerPendingConstProcessing(rctype, [this.m_emitter.registerResolvedTypeReference(rctype), cdecl.contiainingType, cdecl.binds], cdecl.decl, cdecl.binds, rtype);
            this.m_emitter.emitRegisterStore(exp.sinfo, new MIRGlobalVariable(skey.keyid, skey.shortname), trgt, this.m_emitter.registerResolvedTypeReference(rtype), undefined);
        }
        
        return env.setUniformResultExpression(rtype);
    }

    private checkAccessVariable(env: TypeEnvironment, exp: AccessVariableExpression, trgt: MIRRegisterArgument): TypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !env.isVarNameDefined(exp.name), `Variable name '${exp.name}' is not defined`);

        const vinfo = env.lookupVar(exp.name) as VarInfo;
        this.raiseErrorIf(exp.sinfo, !vinfo.mustDefined, "Var may not have been assigned a value");
        if(vinfo.isCaptured) {
            this.m_emitter.emitRegisterStore(exp.sinfo, new MIRRegisterArgument(this.m_emitter.generateCapturedVarName(exp.name, env.bodyid)), trgt, this.m_emitter.registerResolvedTypeReference(vinfo.declaredType), undefined);    
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

        const oodecl = (objtype as ResolvedEntityAtomType).object;
        const oobinds = (objtype as ResolvedEntityAtomType).binds;
        this.checkTemplateTypes(exp.sinfo, oodecl.terms, oobinds);

        const oftype = ResolvedEntityAtomType.create(oodecl, oobinds);
        if (oodecl.isListType() || oodecl.isStackType() || oodecl.isQueueType()) {
            const ctype = this.getTBind(oobinds);
            const eargs = this.checkArgumentsEvaluationCollection(env, exp.args, ctype);
            const atype = this.checkArgumentsCollectionConstructor(exp.sinfo, oftype, ctype, eargs, trgt);

            return env.setUniformResultExpression(atype);
        }
        else if (oodecl.isSetType()) {
            const ctype = this.getTBind(oobinds);
            this.raiseErrorIf(exp.sinfo, !ctype.isGroundedType() || !this.m_assembly.subtypeOf(ctype, this.m_assembly.getSpecialKeyTypeConceptType()), "Must be grounded key type for Set");

            const eargs = this.checkArgumentsEvaluationCollection(env, exp.args, ctype);
            const atype = this.checkArgumentsCollectionConstructor(exp.sinfo, oftype, ctype, eargs, trgt);

            return env.setUniformResultExpression(atype);
        }
        else if (oodecl.isMapType()) {
            const kvtypes = this.getKVBinds(oobinds);
            this.raiseErrorIf(exp.sinfo, !kvtypes.K.isGroundedType() || !this.m_assembly.subtypeOf(kvtypes.K, this.m_assembly.getSpecialKeyTypeConceptType()), "Must be grounded key type for Map key");

            const entryobj = this.resolveAndEnsureTypeOnly(exp.sinfo, new TupleTypeSignature([kvtypes.K, kvtypes.V]), new Map<string, ResolvedType>());
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

        const oodecl = (objtype as ResolvedEntityAtomType).object;
        const oobinds = (objtype as ResolvedEntityAtomType).binds;
        this.raiseErrorIf(exp.sinfo, !(oodecl instanceof EntityTypeDecl), "Can only construct concrete entities");
        this.checkTemplateTypes(exp.sinfo, oodecl.terms, oobinds);

        const fdecl = oodecl.staticFunctions.find((sf) => sf.name === exp.factoryName);
        this.raiseErrorIf(exp.sinfo, fdecl === undefined || !OOPTypeDecl.attributeSetContains("factory", fdecl.invoke.attributes), `Function is not a factory function for type ${ctype.typeID}`);

        const [fsig, callbinds, eargs] = this.inferAndCheckArguments(exp.sinfo, env, exp.args, (fdecl as StaticFunctionDecl).invoke, exp.terms.targs, oobinds, env.terms, undefined, false);
        const rargs = this.checkArgumentsSignature(exp.sinfo, env, exp.factoryName, fsig, eargs);

        this.checkRecursion(exp.sinfo, fsig, rargs.pcodes, exp.rec);

        const etreg = this.m_emitter.generateTmpRegister();
        const ootype = this.m_emitter.registerResolvedTypeReference(this.resolveOOTypeFromDecls(oodecl, oobinds));
        const skey = this.m_emitter.registerStaticCall(this.resolveOOTypeFromDecls(oodecl, oobinds), [ootype, oodecl, oobinds], fdecl as StaticFunctionDecl, exp.factoryName, callbinds, rargs.pcodes, rargs.cinfo);

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
            itype = infertype.tryGetInferrableTupleConstructorType();
        }

        const eargs = this.checkArgumentsEvaluationTuple(env, exp.args, itype);
        const rtype = this.checkArgumentsTupleConstructor(exp.sinfo, eargs, trgt);

        return env.setUniformResultExpression(rtype);
    }

    private checkRecordConstructor(env: TypeEnvironment, exp: ConstructorRecordExpression, trgt: MIRRegisterArgument, infertype: ResolvedType | undefined): TypeEnvironment {
        let itype: ResolvedRecordAtomType | undefined = undefined;
        if(infertype !== undefined) {
            itype = infertype.tryGetInferrableRecordConstructorType();
        }

        const eargs = this.checkArgumentsEvaluationRecord(env, exp.args, itype);
        const rtype = this.checkArgumentsRecordConstructor(exp.sinfo, eargs, trgt);
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
        if(exp.rop === "something") {
            this.raiseErrorIf(exp.sinfo, infertype !== undefined && (infertype.options.length !== 1 || !(infertype as ResolvedType).typeID.startsWith("NSCore::Option<")), "something shorthand constructors only valid with NSCore::Option typed expressions");

            const T = infertype !== undefined && infertype.options.length === 1 ? this.getTBind(this.getUniqueTypeBinds(infertype)) : undefined;
            const treg = this.m_emitter.generateTmpRegister();
            const senv = this.checkExpression(env, exp.arg, treg, T);
            const rrtype = T || senv.getExpressionResult().valtype.flowtype;
            const mirrrtype = this.m_emitter.registerResolvedTypeReference(rrtype);

            const opttype = this.m_assembly.getSomethingType(rrtype);
            const miropttype = this.m_emitter.registerResolvedTypeReference(opttype);

            const ctarg = this.emitInlineConvertIfNeeded(exp.sinfo, treg, senv.getExpressionResult().valtype, rrtype);
            this.m_emitter.emitInject(exp.sinfo, mirrrtype, miropttype, ctarg, trgt);

            return env.setUniformResultExpression(opttype);
           
        }
        else {
            this.raiseErrorIf(exp.sinfo, infertype !== undefined && (infertype.options.length !== 1 || !(infertype as ResolvedType).typeID.startsWith("NSCore::Result<")), "ok/err shorthand constructors only valid with NSCore::Result typed expressions");

            const {T, E} = infertype !== undefined && infertype.options.length === 1 ? this.getTEBinds(this.getUniqueTypeBinds(infertype)) : { T: undefined, E: undefined };
            const treg = this.m_emitter.generateTmpRegister();

            if (exp.rop === "ok") {
                const okenv = this.checkExpression(env, exp.arg, treg, T);
                
                const ttype = T || okenv.getExpressionResult().valtype.flowtype;
                const mirttype = this.m_emitter.registerResolvedTypeReference(ttype);
                const eetype = E || this.m_assembly.getSpecialNoneType();
                
                const okconstype = this.m_assembly.getOkType(ttype, eetype);
                const mirokconstype = this.m_emitter.registerResolvedTypeReference(okconstype);

                const ctarg = this.emitInlineConvertIfNeeded(exp.sinfo, treg, okenv.getExpressionResult().valtype, ttype);
                this.m_emitter.emitInject(exp.sinfo, mirttype, mirokconstype, ctarg, trgt);

                return env.setUniformResultExpression(okconstype);
            }
            else {
                this.raiseErrorIf(exp.sinfo, infertype !== undefined, "No default type known for T -- must explicitly construct or specify")
                const errenv = this.checkExpression(env, exp.arg, treg, E);
                
                const ttype = T as ResolvedType;
                const eetype = E || errenv.getExpressionResult().valtype.flowtype;
                const mireetype = this.m_emitter.registerResolvedTypeReference(eetype);

                const errconstype = this.m_assembly.getErrType(ttype, eetype);
                const mirerrconstype = this.m_emitter.registerResolvedTypeReference(errconstype);

                const ctarg = this.emitInlineConvertIfNeeded(exp.sinfo, treg, errenv.getExpressionResult().valtype, eetype);
                this.m_emitter.emitInject(exp.sinfo, mireetype, mirerrconstype, ctarg, trgt);

                return env.setUniformResultExpression(errconstype);
            }
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
                    sigkeys.push(this.m_emitter.registerResolvedTypeReference(fsig.params[i].type as ResolvedType).typeID);
                }
                else {
                    const lev = (opdecl.invoke.params[i].litexp as LiteralExpressionValue);

                    //compileTimeReduceConstantExpression
                    const cexp = this.m_assembly.reduceLiteralValueToCanonicalForm(lev.exp, env.terms, fsig.params[i].type as ResolvedType);
                    this.raiseErrorIf(sinfo, cexp === undefined, "Invalid literal argument");
                    
                    const [clexp, cltype, cltag] = cexp as [Expression, ResolvedType, string];
                    sigkeys.push(cltag)
                    
                    const lcreg = this.m_emitter.generateTmpRegister();    
                    this.checkExpression(env, clexp, lcreg, undefined);

                    //Should have same error if we fail to find suitable dynamic dispatch -- this is just a nice optimization
                    const ichkreg = this.m_emitter.generateTmpRegister();
                    const mirlhstype = this.m_emitter.registerResolvedTypeReference(fsig.params[i].type as ResolvedType);
                    const mirrhstype = this.m_emitter.registerResolvedTypeReference(cltype);
                    this.m_emitter.emitBinKeyEq(sinfo, mirlhstype, cargs[argidx], mirrhstype, lcreg, mirrhstype, ichkreg, undefined, mirlhstype, mirrhstype);
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
            this.m_emitter.emitInvokeVirtualOperator(sinfo, opkey.keyid, opkey.shortname, cargs, refinfo, trgt);
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
                    sigkeys.push(this.m_emitter.registerResolvedTypeReference(fsig.params[i].type as ResolvedType).typeID);
                }
                else {
                    const lev = (opdecl.invoke.params[i].litexp as LiteralExpressionValue);

                    //compileTimeReduceConstantExpression
                    const cexp = this.m_assembly.reduceLiteralValueToCanonicalForm(lev.exp, env.terms, fsig.params[i].type as ResolvedType);
                    this.raiseErrorIf(sinfo, cexp === undefined, "Invalid literal argument");
                    
                    const [clexp, cltype, cltag] = cexp as [Expression, ResolvedType, string];
                    sigkeys.push(cltag)
                    
                    const lcreg = this.m_emitter.generateTmpRegister();    
                    this.checkExpression(env, clexp, lcreg, undefined);

                    //Should have same error if we fail to find suitable dynamic dispatch -- this is just a nice optimization
                    const ichkreg = this.m_emitter.generateTmpRegister();
                    const mirlhstype = this.m_emitter.registerResolvedTypeReference(fsig.params[i].type as ResolvedType);
                    const mirrhstype = this.m_emitter.registerResolvedTypeReference(cltype);
                    this.m_emitter.emitBinKeyEq(sinfo, mirlhstype, cargs[argidx], mirrhstype, lcreg, mirrhstype, ichkreg, undefined, mirlhstype, mirrhstype);
                    this.m_emitter.emitAssertCheck(sinfo, "Failed to match literal tag on dynamic operator invoke", ichkreg);
                }
            }

            const opkey = this.m_emitter.registerStaticOperatorCall(ootype, [mirootype, oodecl, oobinds], opdecl.name, opdecl, sigkeys, oobinds, pcodes, cinfo);
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

            const opkey = this.m_emitter.registerVirtualStaticOperatorCall([ootype, mirootype, oodecl, oobinds], opdecl.name, oobinds, pcodes, cinfo);
            const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, refs);
            this.m_emitter.emitInvokeVirtualOperator(sinfo, opkey.keyid, opkey.shortname, cargs,  refinfo, trgt);
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

        this.raiseErrorIf(exp.sinfo, (fdecltry === undefined && opdecltry === undefined), `Static function/operator not defined for type ${fromtype.typeID}`);
        this.raiseErrorIf(exp.sinfo, (fdecltry !== undefined && opdecltry !== undefined), `Static function/operator multiply defined for type ${fromtype.typeID}`);

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
                this.m_emitter.emitBinKeyEq(exp.sinfo, this.m_emitter.registerResolvedTypeReference(tlhs.layout), lhsreg, this.m_emitter.registerResolvedTypeReference(trhs.layout), rhsreg, this.m_emitter.registerResolvedTypeReference(ktype), trgt, undefined, this.m_emitter.registerResolvedTypeReference(tlhs.flowtype), this.m_emitter.registerResolvedTypeReference(trhs.flowtype));
            }
            else {
                this.m_emitter.emitBinKeyLess(exp.sinfo, this.m_emitter.registerResolvedTypeReference(tlhs.layout), lhsreg, this.m_emitter.registerResolvedTypeReference(trhs.layout), rhsreg, this.m_emitter.registerResolvedTypeReference(ktype), trgt, undefined, this.m_emitter.registerResolvedTypeReference(tlhs.flowtype), this.m_emitter.registerResolvedTypeReference(trhs.flowtype));
            }

            return [env.setUniformResultExpression(this.m_assembly.getSpecialBoolType())];
        }
        else if(fromtype.typeID === "NSCore::Tuple" && exp.name === "append") {
            let eargs: [ResolvedType, ResolvedType, MIRRegisterArgument][] = [];
            let ttypes: ResolvedType[] = [];

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
                ttypes = [...ttypes, ...earg.flowtype.getUniqueTupleTargetType().types];
            }

            const rtupletype = ResolvedType.createSingle(ResolvedTupleAtomType.create(ttypes));
            const argstypes = eargs.map((arg) => {
                return { layout: this.m_emitter.registerResolvedTypeReference(arg[0]), flow: this.m_emitter.registerResolvedTypeReference(arg[1]) };
            });
            this.m_emitter.emitStructuredAppendTuple(exp.sinfo, this.m_emitter.registerResolvedTypeReference(rtupletype), eargs.map((ee) => ee[2]), argstypes, trgt);

            return [env.setUniformResultExpression(rtupletype)];
        }
        else if(fromtype.typeID === "NSCore::Record" && exp.name === "join") {
            let eargs: [ResolvedType, ResolvedType, MIRRegisterArgument][] = [];
            let ttypes: {pname: string, ptype: ResolvedType}[] = [];
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
                
                const erec = earg.flowtype.getUniqueRecordTargetType();

                this.raiseErrorIf(exp.sinfo, erec.entries.some((rr) => names.has(rr.pname)), "Cannot have (possibly) duplicate properties in join");
                erec.entries.forEach((rr) => names.add(rr.pname));

                ttypes.push(...erec.entries);
            }

            const rrecordtype = ResolvedType.createSingle(ResolvedRecordAtomType.create(ttypes));
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
                const ckey = this.m_emitter.registerStaticCall(this.resolveOOTypeFromDecls(fdecl.contiainingType, fdecl.binds), [ootype, fdecl.contiainingType, fdecl.binds], fdecl.decl, exp.name, callbinds, rargs.pcodes, rargs.cinfo);
                const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
                this.m_emitter.emitInvokeFixedFunction(exp.sinfo, ckey, rargs.args, rargs.fflag, refinfo, trgt);

                return this.updateEnvForOutParams(env.setUniformResultExpression(fsig.resultType), rargs.refs);
            }
        }
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
        this.m_emitter.emitInvokeFixedFunction(exp.sinfo, (pcode as PCode).ikey, [...margs.args, ...cargsext], undefined, refinfo, trgt);   

        return this.updateEnvForOutParams(env.setUniformResultExpression(pcode.ftype.resultType), margs.refs);
    }

    private checkIsTypeExpression_commondirect(sinfo: SourceInfo, env: TypeEnvironment, arg: MIRRegisterArgument, oftype: ResolvedType, trgt: MIRRegisterArgument): TypeEnvironment[] {
        const tsplits = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, oftype, [env]);
        this.m_emitter.emitTypeOf(sinfo, trgt, this.m_emitter.registerResolvedTypeReference(oftype), arg, this.m_emitter.registerResolvedTypeReference(env.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(env.getExpressionResult().valtype.flowtype), undefined);
        return [
            ...(tsplits.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))), 
            ...(tsplits.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
        ];
    } 

    private checkIsTypeExpression_common(sinfo: SourceInfo, env: TypeEnvironment, arg: Expression, oftype: ResolvedType, trgt: MIRRegisterArgument, refok: boolean): TypeEnvironment[] {
        const treg = this.m_emitter.generateTmpRegister();
        const fenv = this.checkExpression(env, arg, treg, oftype, { refok: refok, orok: false });

        return this.checkIsTypeExpression_commondirect(sinfo, fenv, treg, oftype, trgt);
    } 

    private checkIsTypeExpressionMulti(env: TypeEnvironment, exp: IsTypeExpression, trgt: MIRRegisterArgument, refok: boolean): TypeEnvironment[] {
        const oftype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.oftype, env.terms);
        return this.checkIsTypeExpression_common(exp.sinfo, env, exp.arg, oftype, trgt, refok);
    }

    private checkAsTypeExpression_commondirect(sinfo: SourceInfo, env: TypeEnvironment, arg: MIRRegisterArgument, oftype: ResolvedType, trgt: MIRRegisterArgument): TypeEnvironment[] {
        const tsplits = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, oftype, [env]);

        if (tsplits.tenvs.length === 0) {
            this.m_emitter.emitAbort(sinfo, "Never of required type");
            return [env.setAbort()];
        }
        else {
            if (tsplits.fenvs.length !== 0) {
                const creg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitTypeOf(sinfo, creg, this.m_emitter.registerResolvedTypeReference(oftype), arg, this.m_emitter.registerResolvedTypeReference(env.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(env.getExpressionResult().valtype.flowtype), undefined);
                this.m_emitter.emitAssertCheck(sinfo, "Failed type conversion", creg);
            }

            this.m_emitter.emitRegisterStore(sinfo, arg, this.emitInlineConvertIfNeeded(sinfo, trgt, env.getExpressionResult().valtype, oftype), this.m_emitter.registerResolvedTypeReference(oftype), undefined);
            return tsplits.tenvs;
        }
    }

    private checkAsTypeExpression_common(sinfo: SourceInfo, env: TypeEnvironment, arg: Expression, oftype: ResolvedType, trgt: MIRRegisterArgument, refok: boolean): TypeEnvironment[] {
        const treg = this.m_emitter.generateTmpRegister();
        const fenv = this.checkExpression(env, arg, treg, oftype, { refok: refok, orok: false });

        return this.checkAsTypeExpression_commondirect(sinfo, fenv, treg, oftype, trgt);
    } 

    private checkAsTypeExpressionMulti(env: TypeEnvironment, exp: AsTypeExpression, trgt: MIRRegisterArgument, refok: boolean): TypeEnvironment[] {
        const oftype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.oftype, env.terms);
        return this.checkAsTypeExpression_common(exp.sinfo, env, exp.arg, oftype, trgt, refok);
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

        let itype: ResolvedType[] | undefined = undefined;
        if (infertype !== undefined) {
            if (op.isEphemeralListResult) {
                const eitype = infertype.tryGetInferrableValueListConstructorType();
                itype = eitype !== undefined ? eitype.types : undefined;
            }
            else {
                const eitype = infertype.tryGetInferrableTupleConstructorType();
                itype = eitype !== undefined ? [...eitype.types] : undefined;
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

            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(ttype, etypes[i]), "Type of load is not compatible with infered type");
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
            const tupleatom = ResolvedTupleAtomType.create(etypes);
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
                const eitype = infertype.tryGetInferrableRecordConstructorType();
                this.raiseErrorIf(op.sinfo, eitype !== undefined && op.names.some((ln) => this.getInfoForHasProperty(op.sinfo, ResolvedType.createSingle(eitype), ln.name) !== "yes"), "Property may not be defined for all records");

                itype = eitype !== undefined ? op.names.map((nn) => (eitype.entries.find((entry) => entry.pname === nn.name) as {pname: string, ptype: ResolvedType}).ptype) : undefined;
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

                this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(ttype, etypes[i][1]), "Type of load is not compatible with infered type");
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
                const recordatom = ResolvedRecordAtomType.create(etypes.map((tt) => {
                    return { pname: tt[0], ptype: tt[1] };
                }));
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
                const recordatom = ResolvedRecordAtomType.create(rfields.map((tt) => {
                    return { pname: tt.decl.name, ptype: this.resolveOOTypeFromDecls(tt.contiainingType, tt.binds) };
                }));
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

            this.m_emitter.emitRegisterStore(op.sinfo, this.emitInlineConvertIfNeeded(op.sinfo, arg, new ValueType(texp.layout, astype), astype), trgt, this.m_emitter.registerResolvedTypeReference(astype), undefined);
            return tsplits.tenvs[0].setResultExpression(astype, astype, undefined, undefined);
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

    private checkPostfixGetIndexOption(env: TypeEnvironment, op: PostfixGetIndexOption, arg: MIRRegisterArgument, trgt: MIRRegisterArgument): TypeEnvironment {
        const texp = env.getExpressionResult().valtype;
        this.raiseErrorIf(op.sinfo, !texp.flowtype.isTupleTargetType(), "Can only load indecies from tuple types");

        const hpi = this.getInfoForHasIndex(op.sinfo, texp.flowtype, op.idx);
        if(hpi === "no") {
            this.m_emitter.emitLoadConstNothing(op.sinfo, trgt);
            return env.setUniformResultExpression(this.m_assembly.getSpecialNothingType());
        }
        else if(hpi === "yes") {
            const linfo = this.getInfoForLoadFromSafeIndex(op.sinfo, texp.flowtype, op.idx);
            const somethingtype = this.m_assembly.getSomethingType(linfo);
            const mirsomethingtype = this.m_emitter.registerResolvedTypeReference(somethingtype);

            const loadreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitLoadTupleIndex(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.idx, !texp.flowtype.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), loadreg);
            this.m_emitter.emitInject(op.sinfo, this.m_emitter.registerResolvedTypeReference(linfo), mirsomethingtype, loadreg, trgt);

            return env.setUniformResultExpression(somethingtype);
        }
        else {
            const linfo = this.getInfoForLoadFromSafeIndexOnly(op.sinfo, texp.flowtype, op.idx);
            const somethingtype = this.m_assembly.getSomethingType(linfo);
            const mirsomethingtype = this.m_emitter.registerResolvedTypeReference(somethingtype);
            const opttype = this.m_assembly.getOptionConceptType(linfo);
            const miropttype = this.m_emitter.registerResolvedTypeReference(opttype);

            this.m_emitter.emitRegisterStore(op.sinfo, this.emitInlineConvertIfNeeded(op.sinfo, new MIRConstantNothing(), ValueType.createUniform(this.m_assembly.getSpecialNothingType()), opttype), trgt, this.m_emitter.registerResolvedTypeReference(linfo), undefined);

            const loadreg = this.m_emitter.generateTmpRegister();
            const hasreg = this.m_emitter.generateTmpRegister();
            const guard = new MIRArgGuard(hasreg);
            this.m_emitter.emitLoadTupleIndexSetGuard(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.idx, !texp.flowtype.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), loadreg, guard);
            
            this.m_emitter.emitGuardedOptionInject(op.sinfo, this.m_emitter.registerResolvedTypeReference(linfo), mirsomethingtype, miropttype, loadreg, trgt, new MIRStatmentGuard(guard, "defaultonfalse", trgt));
            
            return env.setUniformResultExpression(opttype);
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

    private checkPostfixGetPropertyOption(env: TypeEnvironment, op: PostfixGetPropertyOption, arg: MIRRegisterArgument, trgt: MIRRegisterArgument): TypeEnvironment {
        const texp = env.getExpressionResult().valtype;
        this.raiseErrorIf(op.sinfo, !texp.flowtype.isRecordTargetType(), "Can only load indecies from tuple types");

        const hpi = this.getInfoForHasProperty(op.sinfo, texp.flowtype, op.pname);
        if(hpi === "no") {
            this.m_emitter.emitLoadConstNothing(op.sinfo, trgt);
            return env.setUniformResultExpression(this.m_assembly.getSpecialNothingType());
        }
        else if(hpi === "yes") {
            const linfo = this.getInfoForLoadFromSafePropertyOnly(op.sinfo, texp.flowtype, op.pname);
            const somethingtype = this.m_assembly.getSomethingType(linfo);
            const mirsomethingtype = this.m_emitter.registerResolvedTypeReference(somethingtype);

            const loadreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitLoadProperty(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.pname, !texp.flowtype.isUniqueRecordTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), loadreg);
            this.m_emitter.emitInject(op.sinfo, this.m_emitter.registerResolvedTypeReference(linfo), mirsomethingtype, loadreg, trgt);

            return env.setUniformResultExpression(somethingtype);
        }
        else {
            const linfo = this.getInfoForLoadFromSafePropertyOnly(op.sinfo, texp.flowtype, op.pname);
            const somethingtype = this.m_assembly.getSomethingType(linfo);
            const mirsomethingtype = this.m_emitter.registerResolvedTypeReference(somethingtype);
            const opttype = this.m_assembly.getOptionConceptType(linfo);
            const miropttype = this.m_emitter.registerResolvedTypeReference(opttype);

            this.m_emitter.emitRegisterStore(op.sinfo, this.emitInlineConvertIfNeeded(op.sinfo, new MIRConstantNothing(), ValueType.createUniform(this.m_assembly.getSpecialNothingType()), opttype), trgt, this.m_emitter.registerResolvedTypeReference(linfo), undefined);

            const loadreg = this.m_emitter.generateTmpRegister();
            const hasreg = this.m_emitter.generateTmpRegister();
            const guard = new MIRArgGuard(hasreg);
            this.m_emitter.emitLoadRecordPropertySetGuard(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.pname, !texp.flowtype.isUniqueRecordTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), loadreg, guard);
            
            this.m_emitter.emitGuardedOptionInject(op.sinfo, this.m_emitter.registerResolvedTypeReference(linfo), mirsomethingtype, miropttype, loadreg, trgt, new MIRStatmentGuard(guard, "defaultonfalse", trgt));
            
            return env.setUniformResultExpression(opttype);
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

            const ootyperesolved = this.resolveOOTypeFromDecls(knownimpl.contiainingType, knownimpl.binds);
            const ootype = this.m_emitter.registerResolvedTypeReference(ootyperesolved);
            const ckey = this.m_emitter.registerMethodCall(ootyperesolved, [ootype, knownimpl.contiainingType, knownimpl.binds], knownimpl.decl, op.name, callbinds, rargs.pcodes, rargs.cinfo);
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

                if(knownimpl.decl.invoke.body !== undefined && (typeof(knownimpl.decl.invoke.body) === "string") && ["special_nothing", "special_something", "special_extract"].includes(knownimpl.decl.invoke.body as string)) {
                    this.raiseErrorIf(op.sinfo, op.args.argList.length !== 0, "No arguments permitted on this method");
                    
                    const sinv = knownimpl.decl.invoke.body as string;
                    if(sinv === "special_nothing") {
                        return this.checkIsTypeExpression_commondirect(op.sinfo, env, arg, this.m_assembly.getSpecialNothingType(), trgt);
                    }
                    else if(sinv === "special_something") {
                        return this.checkIsTypeExpression_commondirect(op.sinfo, env, arg, this.m_assembly.getSpecialISomethingConceptType(), trgt);
                    }
                    else {
                        const restype = this.resolveAndEnsureTypeOnly(op.sinfo, knownimpl.decl.invoke.resultType, knownimpl.binds);
                        const mirrestype = this.m_emitter.registerResolvedTypeReference(restype);
                        const ctype = this.resolveOOTypeFromDecls(knownimpl.contiainingType, knownimpl.binds);
                        const mirctype = this.m_emitter.registerResolvedTypeReference(ctype);

                        const arge = this.emitInlineConvertIfNeeded(op.sinfo, arg, env.getExpressionResult().valtype, ctype);
                        this.m_emitter.emitExtract(op.sinfo, mirctype, mirrestype, arge, trgt);

                        return [env.setUniformResultExpression(restype)];
                    }
                }
                else {
                    let eev = env;
                    if (op.isBinder) {
                        eev = this.checkDeclareSingleVariable(op.sinfo, env, `$this_#${op.sinfo.pos}`, true, texp.layout, { etype: texp, etreg: arg });
                    }

                    const selfvar = [texp, knownimpl.decl.refRcvr ? env.getExpressionResult().expvar : undefined, arg] as [ValueType, string | undefined, MIRRegisterArgument];
                    const [fsig, callbinds, eargs] = this.inferAndCheckArguments(op.sinfo, eev, op.args, knownimpl.decl.invoke, op.terms.targs, knownimpl.binds, env.terms, selfvar, refok);
                    this.checkTemplateTypes(op.sinfo, knownimpl.decl.invoke.terms, callbinds, knownimpl.decl.invoke.termRestrictions);

                    const rargs = this.checkArgumentsSignature(op.sinfo, eev, op.name, fsig, eargs);
                    this.checkRecursion(op.sinfo, fsig, rargs.pcodes, op.rec);

                    const ootyperesolved = this.resolveOOTypeFromDecls(knownimpl.contiainingType, knownimpl.binds);
                    const ootype = this.m_emitter.registerResolvedTypeReference(ootyperesolved);
                    const ckey = this.m_emitter.registerMethodCall(ootyperesolved, [ootype, knownimpl.contiainingType, knownimpl.binds], knownimpl.decl, op.name, callbinds, rargs.pcodes, rargs.cinfo);
                    const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
                    this.m_emitter.emitInvokeFixedFunction(op.sinfo, ckey, rargs.args, rargs.fflag, refinfo, trgt);

                    if (op.isBinder) {
                        this.m_emitter.localLifetimeEnd(op.sinfo, `$this_#${op.sinfo.pos}`)
                    }

                    return this.updateEnvForOutParams(env.setUniformResultExpression(fsig.resultType), rargs.refs);
                }
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
                this.m_emitter.emitInvokeVirtualFunction(op.sinfo, ckey.keyid, ckey.shortname, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), rargs.args, rargs.fflag, refinfo, trgt);

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

    private checkPostfixExpression(env: TypeEnvironment, exp: PostfixOp, trgt: MIRRegisterArgument, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        let etgrt = this.m_emitter.generateTmpRegister();
        let itype = (exp.ops.length !== 0 && exp.ops[0] instanceof PostfixAs) ? this.resolveAndEnsureTypeOnly((exp.ops[0] as PostfixAs).sinfo, (exp.ops[0] as PostfixAs).astype, env.terms) : undefined;
        let cenv = this.checkExpression(env, exp.rootExp, etgrt, itype, {refok: refok, orok: false});

        let lenv: TypeEnvironment[] = [];
        for (let i = 0; i < exp.ops.length; ++i) {
            const lastop = (i + 1 === exp.ops.length);
            const itype = lastop ? infertype : ((exp.ops[i + 1] instanceof PostfixAs) ? this.resolveAndEnsureTypeOnly((exp.ops[i + 1] as PostfixAs).sinfo, (exp.ops[i + 1] as PostfixAs).astype, cenv.terms) : undefined);

            const ntgrt = this.m_emitter.generateTmpRegister();
            switch (exp.ops[i].op) {
                case PostfixOpTag.PostfixAccessFromIndex:
                    cenv = this.checkAccessFromIndex(cenv, exp.ops[i] as PostfixAccessFromIndex, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixProjectFromIndecies:
                    cenv = this.checkProjectFromIndecies(cenv, exp.ops[i] as PostfixProjectFromIndecies, etgrt, ntgrt, itype);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixAccessFromName:
                    cenv = this.checkAccessFromName(cenv, exp.ops[i] as PostfixAccessFromName, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixProjectFromNames:
                    cenv = this.checkProjectFromNames(cenv, exp.ops[i] as PostfixProjectFromNames, etgrt, ntgrt, itype);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixModifyWithIndecies:
                    cenv = this.checkModifyWithIndecies(cenv, exp.ops[i] as PostfixModifyWithIndecies, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixModifyWithNames:
                    cenv = this.checkModifyWithNames(cenv, exp.ops[i] as PostfixModifyWithNames, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixIs:
                    if (!lastop) {
                        cenv = this.checkPostfixIsMono(cenv, exp.ops[i] as PostfixIs, etgrt, ntgrt);
                    }
                    else {
                        lenv = this.checkPostfixIsMulti(cenv, exp.ops[i] as PostfixIs, etgrt, ntgrt);
                    }
                    break;
                case PostfixOpTag.PostfixAs:
                    cenv = this.checkPostfixAs(cenv, exp.ops[i] as PostfixAs, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixHasIndex:
                    if (!lastop) {
                        cenv = this.checkPostfixHasIndexMono(cenv, exp.ops[i] as PostfixHasIndex, etgrt, ntgrt);
                    }
                    else {
                        lenv = this.checkPostfixHasIndexMulti(cenv, exp.ops[i] as PostfixHasIndex, etgrt, ntgrt);
                    }
                    break;
                case PostfixOpTag.PostfixHasProperty:
                    if (!lastop) {
                        cenv = this.checkPostfixHasPropertyMono(cenv, exp.ops[i] as PostfixHasProperty, etgrt, ntgrt);
                    }
                    else {
                        lenv = this.checkPostfixHasPropertyMulti(cenv, exp.ops[i] as PostfixHasProperty, etgrt, ntgrt);
                    }
                    break;
                case PostfixOpTag.PostfixGetIndexOrNone:
                    cenv = this.checkPostfixGetIndexOrNone(cenv, exp.ops[i] as PostfixGetIndexOrNone, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixGetIndexOption:
                    cenv = this.checkPostfixGetIndexOption(cenv, exp.ops[i] as PostfixGetIndexOrNone, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixGetIndexTry:
                    if (!lastop) {
                        cenv = this.checkPostfixGetIndexTryMono(cenv, exp.ops[i] as PostfixGetIndexTry, etgrt, ntgrt);
                    }
                    else {
                        lenv = this.checkPostfixGetIndexTryMulti(cenv, exp.ops[i] as PostfixGetIndexTry, etgrt, ntgrt);
                    }
                    break;
                case PostfixOpTag.PostfixGetPropertyOrNone:
                    cenv = this.checkPostfixGetPropertyOrNone(cenv, exp.ops[i] as PostfixGetPropertyOrNone, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixGetPropertyOption:
                    cenv = this.checkPostfixGetPropertyOption(cenv, exp.ops[i] as PostfixGetPropertyOrNone, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixHasProperty:
                    if (!lastop) {
                        cenv = this.checkPostfixGetPropertyTryMono(cenv, exp.ops[i] as PostfixGetPropertyTry, etgrt, ntgrt);
                    }
                    else {
                        lenv = this.checkPostfixGetPropertyTryMulti(cenv, exp.ops[i] as PostfixGetPropertyTry, etgrt, ntgrt);
                    }
                    break;
                default:
                    this.raiseErrorIf(exp.sinfo, exp.ops[i].op !== PostfixOpTag.PostfixInvoke, "Unknown postfix op");
                    if (!lastop) {
                        cenv = this.checkInvokeMono(cenv, exp.ops[i] as PostfixInvoke, etgrt, ntgrt, refok);
                    }
                    else {
                        lenv = this.checkInvokeMulti(cenv, exp.ops[i] as PostfixInvoke, etgrt, ntgrt, refok);
                    }
                    break;
            }

            etgrt = ntgrt;
        }

        const lasttype = ValueType.join(this.m_assembly, ...lenv.map((ee) => ee.getExpressionResult().valtype));
        if (lenv.length === 0) {
            return [];
        }
        else {
            this.m_emitter.emitRegisterStore(exp.sinfo, etgrt, trgt, this.m_emitter.registerResolvedTypeReference(lasttype.layout), undefined);

            return lenv;
        }
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

    private strongEQ(sinfo: SourceInfo, env: TypeEnvironment, lhsarg: Expression, rhsarg: Expression, trgt: MIRRegisterArgument): TypeEnvironment[] {
        const lhsreg = this.m_emitter.generateTmpRegister();
        const lhs = this.checkExpression(env, lhsarg, lhsreg, undefined);
        let olhs = lhs.getExpressionResult().valtype;

        const rhsreg = this.m_emitter.generateTmpRegister();
        const rhs = this.checkExpression(env, rhsarg, rhsreg, undefined);
        let orhs = rhs.getExpressionResult().valtype;

        const action = this.checkValueEq(lhsarg, lhs.getExpressionResult().valtype.flowtype, rhsarg, rhs.getExpressionResult().valtype.flowtype);
        this.raiseErrorIf(sinfo, action === "err", "Compared types are not equivalent (or not unique modulo none)");

        if(action === "truealways" || action === "falsealways") {
            this.m_emitter.emitLoadConstBool(sinfo, action === "truealways" ? true : false, trgt);
            return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), action === "truealways" ? FlowTypeTruthValue.True : FlowTypeTruthValue.False)];
        }
        else if (action === "lhsnone") {
            this.m_emitter.emitTypeOf(sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()), rhsreg, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().valtype.flowtype), undefined);
            
            const renvs = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [rhs]);
            return [
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
        else if (action === "rhsnone") {
            this.m_emitter.emitTypeOf(sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()), lhsreg, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.flowtype), undefined);
            
            const renvs = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [lhs]);
            return [
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
        else if (action === "lhsnothing") {
            this.m_emitter.emitTypeOf(sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNothingType()), rhsreg, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().valtype.flowtype), undefined);
            
            const renvs = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNothingType(), [rhs]);
            return [
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
        else if (action === "rhsnothing") {
            this.m_emitter.emitTypeOf(sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNothingType()), lhsreg, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.flowtype), undefined);
            
            const renvs = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNothingType(), [lhs]);
            return [
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
        else {
            if (action === "lhssomekey") {
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(olhs.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()), "Type must be KeyType");
                this.raiseErrorIf(sinfo, !olhs.flowtype.isGroundedType(), "Type must be grounded");

                const oftypereg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitTypeOf(sinfo, oftypereg, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), rhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), this.m_emitter.registerResolvedTypeReference(orhs.flowtype), undefined);
                
                const sguard = new MIRStatmentGuard(new MIRArgGuard(oftypereg), "defaultonfalse", new MIRConstantFalse());
                this.m_emitter.emitBinKeyEq(sinfo, this.m_emitter.registerResolvedTypeReference(olhs.layout), lhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), rhsreg, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), trgt, sguard, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), this.m_emitter.registerResolvedTypeReference(orhs.flowtype));
                
                const renvs = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [rhs]);
                return [
                    ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False))),
                    ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.Unknown)))
                ];
            }
            else if (action === "rhssomekey") {
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(orhs.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()), "Type must be KeyType");
                this.raiseErrorIf(sinfo, !orhs.flowtype.isGroundedType(), "Type must be grounded");

                const oftypereg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitTypeOf(sinfo, oftypereg, this.m_emitter.registerResolvedTypeReference(orhs.flowtype), lhsreg, this.m_emitter.registerResolvedTypeReference(olhs.layout), this.m_emitter.registerResolvedTypeReference(olhs.flowtype), undefined);
                
                const sguard = new MIRStatmentGuard(new MIRArgGuard(oftypereg), "defaultonfalse", new MIRConstantFalse());
                this.m_emitter.emitBinKeyEq(sinfo, this.m_emitter.registerResolvedTypeReference(olhs.layout), lhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), rhsreg, this.m_emitter.registerResolvedTypeReference(orhs.flowtype), trgt, sguard, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), this.m_emitter.registerResolvedTypeReference(orhs.flowtype));

                const renvs = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [lhs]);
                return [
                    ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False))),
                    ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.Unknown)))
                ];
            }
            else {
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(olhs.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()), "Type must be KeyType");
                this.raiseErrorIf(sinfo, !olhs.flowtype.isGroundedType(), "Type must be grounded");

                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(orhs.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()), "Type must be KeyType");
                this.raiseErrorIf(sinfo, !orhs.flowtype.isGroundedType(), "Type must be grounded");

                this.m_emitter.emitBinKeyEq(sinfo, this.m_emitter.registerResolvedTypeReference(olhs.layout), lhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), rhsreg, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), trgt, undefined, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), this.m_emitter.registerResolvedTypeReference(orhs.flowtype));

                return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.Unknown)];
            }
        }
    }

    private strongNEQ(sinfo: SourceInfo, env: TypeEnvironment, lhsarg: Expression, rhsarg: Expression, trgt: MIRRegisterArgument): TypeEnvironment[] {
        const lhsreg = this.m_emitter.generateTmpRegister();
        const lhs = this.checkExpression(env, lhsarg, lhsreg, undefined);
        let olhs = lhs.getExpressionResult().valtype;

        const rhsreg = this.m_emitter.generateTmpRegister();
        const rhs = this.checkExpression(env, rhsarg, rhsreg, undefined);
        let orhs = rhs.getExpressionResult().valtype;

        const action = this.checkValueEq(lhsarg, lhs.getExpressionResult().valtype.flowtype, rhsarg, rhs.getExpressionResult().valtype.flowtype);
        this.raiseErrorIf(sinfo, action === "err", "Compared types are not equivalent (or not unique modulo none)");

        if(action === "truealways" || action === "falsealways") {
            this.m_emitter.emitLoadConstBool(sinfo, action === "falsealways" ? true : false, trgt);
            return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), action === "falsealways" ? FlowTypeTruthValue.True : FlowTypeTruthValue.False)];
        }
        else if (action === "lhsnone") {
            //note use of negation here
            const oftypereg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitTypeOf(sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()), rhsreg, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().valtype.flowtype), undefined);
            this.m_emitter.emitPrefixNotOp(sinfo, oftypereg, trgt);

            const renvs = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [rhs]);
            return [
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
        else if (action === "rhsnone") {
            //note use of negation here
            const oftypereg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitTypeOf(sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()), lhsreg, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.flowtype), undefined);
            this.m_emitter.emitPrefixNotOp(sinfo, oftypereg, trgt);

            const renvs = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [lhs]);
            return [
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
        else if (action === "lhsnothing") {
            //note use of negation here
            const oftypereg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitTypeOf(sinfo, oftypereg, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNothingType()), rhsreg, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().valtype.flowtype), undefined);
            this.m_emitter.emitPrefixNotOp(sinfo, oftypereg, trgt);

            const renvs = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNothingType(), [rhs]);
            return [
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
        else if (action === "rhsnothing") {
            //note use of negation here
            const oftypereg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitTypeOf(sinfo, oftypereg, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNothingType()), lhsreg, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.flowtype), undefined);
            this.m_emitter.emitPrefixNotOp(sinfo, oftypereg, trgt);

            const renvs = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNothingType(), [lhs]);
            return [
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
        else {
            if (action === "lhssomekey") {
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(olhs.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()), "Type must be KeyType");
                this.raiseErrorIf(sinfo, !olhs.flowtype.isGroundedType(), "Type must be grounded");

                const oftypereg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitTypeOf(sinfo, oftypereg, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), rhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), this.m_emitter.registerResolvedTypeReference(orhs.flowtype), undefined);
    
                const sguard = new MIRStatmentGuard(new MIRArgGuard(oftypereg), "defaultonfalse", new MIRConstantFalse());
                const treg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitBinKeyEq(sinfo, this.m_emitter.registerResolvedTypeReference(olhs.layout), lhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), rhsreg, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), treg, sguard, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), this.m_emitter.registerResolvedTypeReference(orhs.flowtype));
                this.m_emitter.emitPrefixNotOp(sinfo, treg, trgt);

                const renvs = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [rhs]);
                return [
                    ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False))),
                    ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.Unknown)))
                ];
            }
            else if (action === "rhssomekey") {
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(orhs.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()), "Type must be KeyType");
                this.raiseErrorIf(sinfo, !orhs.flowtype.isGroundedType(), "Type must be grounded");

                const oftypereg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitTypeOf(sinfo, oftypereg, this.m_emitter.registerResolvedTypeReference(orhs.flowtype), lhsreg, this.m_emitter.registerResolvedTypeReference(olhs.layout), this.m_emitter.registerResolvedTypeReference(olhs.flowtype), undefined);
                
                const sguard = new MIRStatmentGuard(new MIRArgGuard(oftypereg), "defaultonfalse", new MIRConstantFalse());
                const treg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitBinKeyEq(sinfo, this.m_emitter.registerResolvedTypeReference(olhs.layout), lhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), rhsreg, this.m_emitter.registerResolvedTypeReference(orhs.flowtype), treg, sguard, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), this.m_emitter.registerResolvedTypeReference(orhs.flowtype));
                this.m_emitter.emitPrefixNotOp(sinfo, treg, trgt);

                const renvs = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [lhs]);
                return [
                    ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False))),
                    ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.Unknown)))
                ];
            }
            else {
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(olhs.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()), "Type must be KeyType");
                this.raiseErrorIf(sinfo, !olhs.flowtype.isGroundedType(), "Type must be grounded");

                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(orhs.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()), "Type must be KeyType");
                this.raiseErrorIf(sinfo, !orhs.flowtype.isGroundedType(), "Type must be grounded");

                const treg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitBinKeyEq(sinfo, this.m_emitter.registerResolvedTypeReference(olhs.layout), lhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), rhsreg, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), treg, undefined, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), this.m_emitter.registerResolvedTypeReference(orhs.flowtype));
                this.m_emitter.emitPrefixNotOp(sinfo, treg, trgt);

                return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.Unknown)];
            }
        }
    }

    private checkBinLogic(env: TypeEnvironment, exp: BinLogicExpression, trgt: MIRRegisterArgument, refok: boolean): TypeEnvironment[] {
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

    private checkMapEntryConstructorExpression(env: TypeEnvironment, exp: MapEntryConstructorExpression, trgt: MIRRegisterArgument, infertype: ResolvedType | undefined): TypeEnvironment {
        const itype = infertype !== undefined ? infertype.tryGetInferrableTupleConstructorType() : undefined;
        const metype = (itype !== undefined && itype.types.length === 2) ? itype : undefined;

        const kreg = this.m_emitter.generateTmpRegister();
        const kinfer = metype !== undefined ? metype.types[0] : undefined;
        const ktype = this.checkExpression(env, exp.kexp, kreg, kinfer).getExpressionResult().valtype;

        this.raiseErrorIf(exp.kexp.sinfo, !this.m_assembly.subtypeOf(ktype.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()) || !ktype.flowtype.isGroundedType(), "Key must be a grounded KeyType value");

        const vreg = this.m_emitter.generateTmpRegister();
        const vinfer = metype !== undefined ? metype.types[1] : undefined;
        const vtype = this.checkExpression(env, exp.vexp, vreg, vinfer).getExpressionResult().valtype;

        const mtype = ResolvedType.createSingle(ResolvedTupleAtomType.create([ktype.flowtype, vtype.flowtype]));

        const targs = [ this.emitInlineConvertToFlow(exp.sinfo, kreg, ktype), this.emitInlineConvertToFlow(exp.sinfo, vreg, vtype)];
        this.m_emitter.emitConstructorTuple(exp.sinfo, this.m_emitter.registerResolvedTypeReference(mtype), targs, trgt);

        return env.setUniformResultExpression(mtype);
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

        let terminalenvironments: TypeEnvironment[] = [];
        let normalenvironments: TypeEnvironment[] = [];

        if(exp.cond === "none") {
            const finalreg = this.m_emitter.generateTmpRegister();
            let eeinfer = infertype !== undefined ? this.m_assembly.typeUpperBound([infertype, this.m_assembly.getSpecialNoneType()]) : undefined;
            const evalue = this.checkExpression(env, exp.exp, finalreg, eeinfer, {refok: extraok.refok, orok: false});

            const flows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [evalue]);
            let normalexps = flows.fenvs
            let terminalexps = flows.tenvs;

            if (normalexps.length === 0 || terminalexps.length === 0) {
                this.m_emitter.emitDirectJump(exp.sinfo, normalexps.length !== 0 ? regularblck : scblck);
            }
            else {
                this.m_emitter.emitNoneJump(exp.sinfo, finalreg, this.m_emitter.registerResolvedTypeReference(evalue.getExpressionResult().valtype.layout), scblck, regularblck);
            }

            if (terminalexps.length !== 0) {
                const terminaltype = ValueType.join(this.m_assembly, ...terminalexps.map((eev) => eev.getExpressionResult().valtype));
                this.m_emitter.setActiveBlock(scblck);
                if (env.isInYieldBlock()) {
                    this.m_emitter.getActiveYieldSet().push([this.m_emitter.getActiveBlockName(), finalreg, terminaltype]);
                    terminalenvironments = [env.setYield(this.m_assembly, this.m_assembly.getSpecialNoneType())];
                }
                else {
                    this.m_emitter.getActiveReturnSet().push([this.m_emitter.getActiveBlockName(), finalreg, terminaltype]);
                    terminalenvironments = [env.setReturn(this.m_assembly, this.m_assembly.getSpecialNoneType())];
                }
            }

            this.m_emitter.setActiveBlock(regularblck);
            if (normalexps.length !== 0) {
                const normaltype = this.m_assembly.typeUpperBound(normalexps.map((eev) => eev.getExpressionResult().valtype.flowtype));
                this.m_emitter.emitRegisterStore(exp.sinfo, this.emitInlineConvertIfNeeded(exp.sinfo, finalreg, evalue.getExpressionResult().valtype, normaltype), trgt, this.m_emitter.registerResolvedTypeReference(normaltype), undefined);

                normalenvironments = normalexps.map((eev) => eev.setUniformResultExpression(normaltype));
            }
        }
        else if(exp.cond === "nothing") {
            const finalreg = this.m_emitter.generateTmpRegister();
            let eeinfer = infertype !== undefined ? this.m_assembly.getOptionConceptType(infertype) : undefined;
            const evalue = this.checkExpression(env, exp.exp, finalreg, eeinfer, {refok: extraok.refok, orok: false});
            
            this.raiseErrorIf(exp.sinfo, !evalue.getExpressionResult().valtype.flowtype.isOptionType(), "Result must be an Option<T> type");
            const restype = this.getTBind(this.getUniqueTypeBinds(evalue.getExpressionResult().valtype.flowtype));

            const somethingtype = this.m_assembly.getSomethingType(restype);

            const flows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNothingType(), [evalue]);
            let normalexps = flows.fenvs
            let terminalexps = flows.tenvs;

            if (normalexps.length === 0 || terminalexps.length === 0) {
                this.m_emitter.emitDirectJump(exp.sinfo, normalexps.length !== 0 ? regularblck : scblck);
            }
            else {
                const treg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitTypeOf(exp.sinfo, treg, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNothingType()), finalreg, this.m_emitter.registerResolvedTypeReference(evalue.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(evalue.getExpressionResult().valtype.flowtype), undefined);
                this.m_emitter.emitBoolJump(exp.sinfo, treg, scblck, regularblck);
            }

            if (terminalexps.length !== 0) {
                const terminaltype = ValueType.join(this.m_assembly, ...terminalexps.map((eev) => eev.getExpressionResult().valtype));
                this.m_emitter.setActiveBlock(scblck);
                if (env.isInYieldBlock()) {
                    this.m_emitter.getActiveYieldSet().push([this.m_emitter.getActiveBlockName(), finalreg, terminaltype]);
                    terminalenvironments = [env.setYield(this.m_assembly, this.m_assembly.getSpecialNothingType())];
                }
                else {
                    this.m_emitter.getActiveReturnSet().push([this.m_emitter.getActiveBlockName(), finalreg, terminaltype]);
                    terminalenvironments = [env.setReturn(this.m_assembly, this.m_assembly.getSpecialNothingType())];
                }
            }

            this.m_emitter.setActiveBlock(regularblck);
            if (normalexps.length !== 0) {
                this.m_emitter.emitExtract(exp.sinfo, this.m_emitter.registerResolvedTypeReference(somethingtype), this.m_emitter.registerResolvedTypeReference(restype), this.emitInlineConvertIfNeeded(exp.sinfo, finalreg, evalue.getExpressionResult().valtype, somethingtype), trgt);
                normalenvironments = normalexps.map((eev) => eev.setUniformResultExpression(restype));
            }
        }
        else {
            const finalreg = this.m_emitter.generateTmpRegister();

            let eeinfer: ResolvedType | undefined = undefined;
            if(env.isInYieldBlock()) {
                eeinfer = infertype !== undefined ? this.m_assembly.getResultConceptType(infertype, this.m_assembly.getSpecialNoneType()) : undefined;
            }
            else {
                if(this.m_emitter.m_activeResultType !== undefined && this.m_emitter.m_activeResultType.isResultType()) {
                    eeinfer = this.m_emitter.m_activeResultType;
                }
                else {
                    eeinfer = infertype !== undefined ? this.m_assembly.getResultConceptType(infertype, this.m_assembly.getSpecialNoneType()) : undefined;
                }
            }

            const evalue = this.checkExpression(env, exp.exp, finalreg, eeinfer, {refok: extraok.refok, orok: false});
            
            this.raiseErrorIf(exp.sinfo, !evalue.getExpressionResult().valtype.flowtype.isResultType(), "Result must be an Result<T, E> type");
            const {T, E} = this.getTEBinds(this.getUniqueTypeBinds(evalue.getExpressionResult().valtype.flowtype));

            const oktype = this.m_assembly.getOkType(T, E);
            const errtype = this.m_assembly.getErrType(T, E);

            const flows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, errtype, [evalue]);
            let normalexps = flows.fenvs
            let terminalexps = flows.tenvs;

            if (normalexps.length === 0 || terminalexps.length === 0) {
                this.m_emitter.emitDirectJump(exp.sinfo, normalexps.length !== 0 ? regularblck : scblck);
            }
            else {
                const treg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitTypeOf(exp.sinfo, treg, this.m_emitter.registerResolvedTypeReference(errtype), finalreg, this.m_emitter.registerResolvedTypeReference(evalue.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(evalue.getExpressionResult().valtype.flowtype), undefined);
                this.m_emitter.emitBoolJump(exp.sinfo, treg, scblck, regularblck);
            }

            if (terminalexps.length !== 0) {
                const terminaltype = ValueType.join(this.m_assembly, ...terminalexps.map((eev) => eev.getExpressionResult().valtype));
                this.m_emitter.setActiveBlock(scblck);
                if (env.isInYieldBlock()) {
                    this.m_emitter.getActiveYieldSet().push([this.m_emitter.getActiveBlockName(), finalreg, terminaltype]);
                    terminalenvironments = [env.setYield(this.m_assembly, errtype)];
                }
                else {
                    this.m_emitter.getActiveReturnSet().push([this.m_emitter.getActiveBlockName(), finalreg, terminaltype]);
                    terminalenvironments = [env.setReturn(this.m_assembly, errtype)];
                }
            }

            this.m_emitter.setActiveBlock(regularblck);
            if (normalexps.length !== 0) {
                this.m_emitter.emitExtract(exp.sinfo, this.m_emitter.registerResolvedTypeReference(oktype), this.m_emitter.registerResolvedTypeReference(T), this.emitInlineConvertIfNeeded(exp.sinfo, finalreg, evalue.getExpressionResult().valtype, oktype), trgt);
                normalenvironments = normalexps.map((eev) => eev.setUniformResultExpression(T));
            }
        }

        return TypeEnvironment.join(this.m_assembly, ...normalenvironments, ...terminalenvironments);
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

    private checkSwitchExpression(env: TypeEnvironment, exp: SwitchExpression, trgt: MIRRegisterArgument, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment {
        const vreg = this.m_emitter.generateTmpRegister();
        const venv = this.checkExpression(env, exp.sval, vreg, undefined, { refok: refok, orok: false });

        const doneblck = this.m_emitter.createNewBlock("Lswitchexp_done");
        const matchvar = `$switch_#${exp.sinfo.pos}`;
        let cenv = this.checkDeclareSingleVariable(exp.sinfo, venv.pushLocalScope(), matchvar, true, venv.getExpressionResult().valtype.flowtype, {etype: ValueType.createUniform(venv.getExpressionResult().valtype.flowtype), etreg: vreg});

        let hasfalseflow = true;
        let results: TypeEnvironment[] = [];
        let rblocks: [string, MIRRegisterArgument, ValueType][] = [];
        for (let i = 0; i < exp.flow.length && !hasfalseflow; ++i) {
            const nextlabel = this.m_emitter.createNewBlock(`Lswitchexp_${i}next`);
            const actionlabel = this.m_emitter.createNewBlock(`Lswitchexp_${i}action`);

            const test = this.checkSwitchGuard(exp.sinfo, cenv, matchvar, exp.flow[i].check, nextlabel, actionlabel);

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
                rblocks.push([this.m_emitter.getActiveBlockName(), ttreg, truestate.getExpressionResult().valtype]);

                this.m_emitter.setActiveBlock(nextlabel);
                this.m_emitter.emitDeadBlock(exp.sinfo);

                hasfalseflow = false;
            }
            else {
                this.m_emitter.setActiveBlock(actionlabel);

                const ttreg = this.m_emitter.generateTmpRegister();
                const truestate = this.checkExpression(test.tenv, exp.flow[i].action, ttreg, infertype);

                results.push(truestate);
                rblocks.push([this.m_emitter.getActiveBlockName(), ttreg, truestate.getExpressionResult().valtype]);

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
            this.m_emitter.emitDirectJump(exp.sinfo, doneblck);
        }

        this.m_emitter.setActiveBlock(doneblck);
        
        return TypeEnvironment.join(this.m_assembly, ...results.map((eev) => eev.popLocalScope().setUniformResultExpression(etype)));
    }

    private checkMatchExpression(env: TypeEnvironment, exp: MatchExpression, trgt: MIRRegisterArgument, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment {
        const vreg = this.m_emitter.generateTmpRegister();
        const venv = this.checkExpression(env, exp.sval, vreg, undefined, { refok: refok, orok: false });
        const cvname = venv.getExpressionResult().expvar;

        const doneblck = this.m_emitter.createNewBlock("Lswitchexp_done");
        const matchvar = `$match_#${exp.sinfo.pos}`;
        let cenv = this.checkDeclareSingleVariable(exp.sinfo, venv.pushLocalScope(), matchvar, true, venv.getExpressionResult().valtype.flowtype, {etype: ValueType.createUniform(venv.getExpressionResult().valtype.flowtype), etreg: vreg});

        let hasfalseflow = true;
        let results: TypeEnvironment[] = [];
        let rblocks: [string, MIRRegisterArgument, ValueType, string[]][] = [];
        for (let i = 0; i < exp.flow.length && !hasfalseflow; ++i) {
            const nextlabel = this.m_emitter.createNewBlock(`Lswitchexp_${i}next`);
            const actionlabel = this.m_emitter.createNewBlock(`Lswitchexp_${i}action`);

            const test = this.checkMatchGuard(exp.sinfo, i, cenv, matchvar, cvname, exp.flow[i].check, nextlabel, actionlabel);

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
            case ExpressionTag.LiteralNothingExpression:
                return this.checkLiteralNothingExpression(env, exp as LiteralNothingExpression, trgt);
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
            case ExpressionTag.LiteralTypedStringExpression:
                return this.checkCreateTypedString(env, exp as LiteralTypedStringExpression, trgt);
            case ExpressionTag.LiteralTypedPrimitiveConstructorExpression:
                return this.checkTypedTypedNumericConstructor(env, exp as LiteralTypedPrimitiveConstructorExpression, trgt);
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
            case ExpressionTag.MapEntryConstructorExpression:
                return this.checkMapEntryConstructorExpression(env, exp as MapEntryConstructorExpression, trgt, infertype);
            case ExpressionTag.SelectExpression:
                return this.checkSelect(env, exp as SelectExpression, trgt, (extraok && extraok.refok) || false, infertype);
            case ExpressionTag.SwitchExpression:
                return this.checkSwitchExpression(env, exp as SwitchExpression, trgt, (extraok && extraok.refok) || false, infertype);
            case ExpressionTag.MatchExpression:
                return this.checkMatchExpression(env, exp as MatchExpression, trgt, (extraok && extraok.refok) || false, infertype);
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

                if (exp.tag === ExpressionTag.PCodeInvokeExpression) {
                    res = this.checkPCodeInvokeExpression(env, exp as PCodeInvokeExpression, trgt, (extraok && extraok.refok) || false);
                }
                else if (exp.tag === ExpressionTag.CallNamespaceFunctionOrOperatorExpression) {
                    res = this.checkCallNamespaceFunctionOrOperatorExpression(env, exp as CallNamespaceFunctionOrOperatorExpression, trgt, (extraok && extraok.refok) || false);
                }
                else if (exp.tag === ExpressionTag.CallStaticFunctionOrOperatorExpression) {
                    res = this.checkCallStaticFunctionOrOperatorExpression(env, exp as CallStaticFunctionOrOperatorExpression, trgt, (extraok && extraok.refok) || false);
                }
                else if (exp.tag === ExpressionTag.IsTypeExpression) {
                    res = this.checkIsTypeExpressionMulti(env, exp as IsTypeExpression, trgt, (extraok && extraok.refok) || false);
                }
                else if (exp.tag === ExpressionTag.AsTypeExpression) {
                    res = this.checkAsTypeExpressionMulti(env, exp as AsTypeExpression, trgt, (extraok && extraok.refok) || false);
                }
                else if (exp.tag === ExpressionTag.PostfixOpExpression) {
                    res = this.checkPostfixExpression(env, exp as PostfixOp, trgt, (extraok && extraok.refok) || false, infertype);
                }
                else if (exp.tag === ExpressionTag.PrefixNotOpExpression) {
                    res = this.checkPrefixNotOp(env, exp as PrefixNotOp, trgt, (extraok && extraok.refok) || false);
                }
                else if (exp.tag === ExpressionTag.BinKeyExpression) {
                    const bke = exp as BinKeyExpression;
                    if(bke.op === "===") {
                        res = this.strongEQ(bke.sinfo, env, bke.lhs, bke.rhs, trgt);
                    }
                    else {
                        res = this.strongNEQ(bke.sinfo, env, bke.lhs, bke.rhs, trgt);
                    }
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
        else if (exp.tag === ExpressionTag.IsTypeExpression) {
            return this.checkIsTypeExpressionMulti(env, exp as IsTypeExpression, trgt, (extraok && extraok.refok) || false);
        }
        else if (exp.tag === ExpressionTag.AsTypeExpression) {
            return this.checkAsTypeExpressionMulti(env, exp as AsTypeExpression, trgt, (extraok && extraok.refok) || false);
        }
        else if (exp.tag === ExpressionTag.PostfixOpExpression) {
            return this.checkPostfixExpression(env, exp as PostfixOp, trgt, (extraok && extraok.refok) || false, infertype);
        }
        else if (exp.tag === ExpressionTag.PrefixNotOpExpression) {
            return this.checkPrefixNotOp(env, exp as PrefixNotOp, trgt, (extraok && extraok.refok) || false);
        }
        else if (exp.tag === ExpressionTag.BinKeyExpression) {
            const bke = exp as BinKeyExpression;
            if (bke.op === "===") {
                return this.strongEQ(bke.sinfo, env, bke.lhs, bke.rhs, trgt);
            }
            else {
                return this.strongNEQ(bke.sinfo, env, bke.lhs, bke.rhs, trgt);
            }
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

                    cenv = cenv.multiVarUpdate(stmt.vars.map((vv) => [stmt.isConst, vv.name, this.resolveAndEnsureTypeOnly(stmt.sinfo, vv.vtype, env.terms), this.resolveAndEnsureTypeOnly(stmt.sinfo, vv.vtype, env.terms)]), []);
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

                cenv = cenv.multiVarUpdate([], stmt.names.map((vv) => [vv, (env.lookupVar(vv) as VarInfo).declaredType]));
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

    private getTypeOfStructuredAssignForMatch(sinfo: SourceInfo, env: TypeEnvironment, assign: StructuredAssignment): ResolvedType {
        if(assign instanceof TupleStructuredAssignment) {
            const ttypes = assign.assigns.map((asg) => this.resolveAndEnsureTypeOnly(sinfo, asg.assigntype, env.terms));
            return ResolvedType.createSingle(ResolvedTupleAtomType.create(ttypes));
        }
        else if(assign instanceof RecordStructuredAssignment) {
            const entries = assign.assigns.map((asg) => {
                return { pname: asg[0], ptype: this.resolveAndEnsureTypeOnly(sinfo, asg[1].assigntype, env.terms) };
            });
            return ResolvedType.createSingle(ResolvedRecordAtomType.create(entries));
        }
        else {
            this.raiseErrorIf(sinfo, !(assign instanceof NominalStructuredAssignment), "Can only destructure match on Tuples/Records/Entity types");

            const nassign = assign as NominalStructuredAssignment;
            return this.resolveAndEnsureTypeOnly(sinfo, nassign.atype, env.terms);
        }
    }

    private getTypeOfStructuredAssignForInfer(sinfo: SourceInfo, env: TypeEnvironment, assign: StructuredAssignment): ResolvedType | undefined {
        if(assign instanceof TupleStructuredAssignment) {
            if(assign.assigns.some((asg) => asg.assigntype instanceof AutoTypeSignature)) {
                return undefined;
            }
            else {
                const ttypes = assign.assigns.map((asg) => this.resolveAndEnsureTypeOnly(sinfo, asg.assigntype, env.terms));
                return ResolvedType.createSingle(ResolvedTupleAtomType.create(ttypes));
            }
        }
        else if(assign instanceof RecordStructuredAssignment) {
            if(assign.assigns.some((asg) => asg[1].assigntype instanceof AutoTypeSignature)) {
                return undefined;
            }
            else {
                const entries = assign.assigns.map((asg) => {
                    return { pname: asg[0], ptype: this.resolveAndEnsureTypeOnly(sinfo, asg[1].assigntype, env.terms) };
                });
                return ResolvedType.createSingle(ResolvedRecordAtomType.create(entries));
            }
        }
        else if(assign instanceof ValueListStructuredAssignment) {
            if(assign.assigns.some((asg) => asg.assigntype instanceof AutoTypeSignature)) {
                return undefined;
            }
            else {
                const ttypes = assign.assigns.map((asg) => this.resolveAndEnsureTypeOnly(sinfo, asg.assigntype, env.terms));
                return ResolvedType.createSingle(ResolvedEphemeralListType.create(ttypes));
            }
        }
        else {
            assert(assign instanceof NominalStructuredAssignment);

            const nassign = assign as NominalStructuredAssignment;
            const ntype = this.resolveAndEnsureTypeOnly(sinfo, nassign.atype, env.terms);
            if(ntype.options.length !== 1) {
                return undefined;
            }

            const entityorconcept = (ntype.options[0] instanceof ResolvedEntityAtomType) || (ntype.options[0] instanceof ResolvedConceptAtomType);
            if(!entityorconcept) {
                return undefined
            }

            return ntype;
        }
    }

    private getTypeOfStructuredAssignForAssign(sinfo: SourceInfo, env: TypeEnvironment, assign: StructuredAssignment, rhsflow: ResolvedType): ResolvedType {
        if(assign instanceof TupleStructuredAssignment) {
            this.raiseErrorIf(sinfo, !rhsflow.isUniqueTupleTargetType(), "Expected unique tuple type to assign from");
            this.raiseErrorIf(sinfo, rhsflow.getUniqueTupleTargetType().types.length !== assign.assigns.length, "Tuple length does not match assignment");

            const ttypes = assign.assigns.map((asg, i) => !(asg.assigntype instanceof AutoTypeSignature) ? this.resolveAndEnsureTypeOnly(sinfo, asg.assigntype, env.terms) : rhsflow.getUniqueTupleTargetType().types[i]);
            return ResolvedType.createSingle(ResolvedTupleAtomType.create(ttypes));
        }
        else if(assign instanceof RecordStructuredAssignment) {
            this.raiseErrorIf(sinfo, !rhsflow.isUniqueRecordTargetType(), "Expected unique record type to assign from");
            this.raiseErrorIf(sinfo, rhsflow.getUniqueRecordTargetType().entries.length !== assign.assigns.length, "Record property counts do not match assignment");
            this.raiseErrorIf(sinfo, rhsflow.getUniqueRecordTargetType().entries.some((v) => assign.assigns.find((entry) => entry[0] === v.pname) === undefined), "Mismatched property name in assignment");

            const entries = assign.assigns.map((asg) => {
                const entrytype = !(asg[1].assigntype instanceof AutoTypeSignature) ? this.resolveAndEnsureTypeOnly(sinfo, asg[1].assigntype, env.terms) : (rhsflow.getUniqueRecordTargetType().entries.find((entry) => entry.pname === asg[0]) as {pname: string, ptype: ResolvedType}).ptype;
                return { pname: asg[0], ptype: entrytype };
            });
            return ResolvedType.createSingle(ResolvedRecordAtomType.create(entries));
        }
        else if(assign instanceof ValueListStructuredAssignment) {
            const ttypes = assign.assigns.map((asg) => this.resolveAndEnsureTypeOnly(sinfo, asg.assigntype, env.terms));
            return ResolvedType.createSingle(ResolvedEphemeralListType.create(ttypes));
        }
        else {
            assert(assign instanceof NominalStructuredAssignment);

            const nassign = assign as NominalStructuredAssignment;
            return this.resolveAndEnsureTypeOnly(sinfo, nassign.atype, env.terms);
        }
    }

    private generateStructuredAssignOperations(sinfo: SourceInfo, env: TypeEnvironment, assign: StructuredAssignment, arg: MIRRegisterArgument, arglayouttype: ResolvedType, argoftype: ResolvedType): TypeEnvironment {
        const elreg = this.m_emitter.generateTmpRegister();
        let eltypes: ResolvedType[] = [];
        let elatom: ResolvedEphemeralListType | undefined = undefined;
        let declaredvars: [boolean, string, ResolvedType, ResolvedType][] = [];

        if(assign instanceof TupleStructuredAssignment) {
            let rindecies: number[] = [];
            let trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRType }[] = [];
            assign.assigns.forEach((ap, i) => {
                const aptype = argoftype.getUniqueTupleTargetType().types[i];
                if(ap instanceof VariableDeclarationStructuredAssignment) {
                    eltypes.push(aptype);
                    declaredvars.push([true, ap.vname, aptype, aptype]);
                    rindecies.push(i);
                    trgts.push({pos: i, into: new MIRRegisterArgument(ap.vname), oftype: this.m_emitter.registerResolvedTypeReference(aptype)});
                }
            });

            elatom = ResolvedEphemeralListType.create(eltypes);
            this.m_emitter.emitTupleProjectToEphemeral(sinfo, arg, this.m_emitter.registerResolvedTypeReference(arglayouttype), this.m_emitter.registerResolvedTypeReference(argoftype), rindecies, !argoftype.isUniqueTupleTargetType(), elatom, elreg);
            this.m_emitter.emitMultiLoadFromEpehmeralList(sinfo, elreg, this.m_emitter.registerResolvedTypeReference(ResolvedType.createSingle(elatom)), trgts);

            return env.multiVarUpdate(declaredvars, []);
        }
        else if(assign instanceof RecordStructuredAssignment) {
            let pnames: string[] = [];
            let trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRType }[] = [];
            assign.assigns.forEach((ap, i) => {
                const aptype = (argoftype.getUniqueRecordTargetType().entries.find((ee) => ee.pname === ap[0]) as {pname: string, ptype: ResolvedType}).ptype;
                if(ap[1] instanceof VariableDeclarationStructuredAssignment) {
                    eltypes.push(aptype);
                    declaredvars.push([true, ap[1].vname, aptype, aptype]);
                    pnames.push(ap[0]);
                    trgts.push({pos: i, into: new MIRRegisterArgument(ap[1].vname), oftype: this.m_emitter.registerResolvedTypeReference(aptype)});
                }
            });

            elatom = ResolvedEphemeralListType.create(eltypes);
            this.m_emitter.emitRecordProjectToEphemeral(sinfo, arg, this.m_emitter.registerResolvedTypeReference(arglayouttype), this.m_emitter.registerResolvedTypeReference(argoftype), pnames, !argoftype.isUniqueRecordTargetType(), elatom, elreg);
            this.m_emitter.emitMultiLoadFromEpehmeralList(sinfo, elreg, this.m_emitter.registerResolvedTypeReference(ResolvedType.createSingle(elatom)), trgts);

            return env.multiVarUpdate(declaredvars, []);
        }
        else if(assign instanceof ValueListStructuredAssignment) {
            let trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRType }[] = [];
            assign.assigns.forEach((ap, i) => {
                const aptype = (argoftype.options[0] as ResolvedEphemeralListType).types[i];
                if(ap instanceof VariableDeclarationStructuredAssignment) {
                    eltypes.push(aptype);
                    declaredvars.push([true, ap.vname, aptype, aptype]);
                    trgts.push({pos: i, into: new MIRRegisterArgument(ap.vname), oftype: this.m_emitter.registerResolvedTypeReference(aptype)});
                }
            });

            this.m_emitter.emitMultiLoadFromEpehmeralList(sinfo, arg, this.m_emitter.registerResolvedTypeReference(arglayouttype), trgts);

            return env.multiVarUpdate(declaredvars, []);
        }
        else {
            assert(assign instanceof NominalStructuredAssignment);

            const nassign = assign as NominalStructuredAssignment;

            this.raiseErrorIf(sinfo, argoftype.options.length !== 1, "Must be unique concept or entity");
            this.raiseErrorIf(sinfo, !(argoftype.options[0] instanceof ResolvedEntityAtomType) && (argoftype.options[0] as ResolvedConceptAtomType).conceptTypes.length !== 1, "Must be unique concept or entity");

            const ootype = ((argoftype.options[0] instanceof ResolvedEntityAtomType) ? (argoftype.options[0] as ResolvedEntityAtomType).object : (argoftype.options[0] as ResolvedConceptAtomType).conceptTypes[0].concept) as OOPTypeDecl;
            const oobinds = (argoftype.options[0] instanceof ResolvedEntityAtomType) ? (argoftype.options[0] as ResolvedEntityAtomType).binds : (argoftype.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds;
            
            if (ootype.attributes.includes("__constructable")) {
                //check for constructable special case here
                this.raiseErrorIf(sinfo, nassign.assigns.length === 1, "Missing destructor variable");
                this.raiseErrorIf(sinfo, nassign.assigns[0][0] !== undefined, "Named destructors not allowed on primitive constructable types");

                const ap = nassign.assigns[0];
                const apv = new MIRRegisterArgument((ap[1] as VariableDeclarationStructuredAssignment).vname);

                const atype = (ootype.memberMethods.find((mm) => mm.name === "value") as MemberMethodDecl).invoke.resultType;
                const ratype = this.resolveAndEnsureTypeOnly(sinfo, atype, oobinds);

                this.m_emitter.emitExtract(sinfo, this.m_emitter.registerResolvedTypeReference(argoftype), this.m_emitter.registerResolvedTypeReference(ratype), arg, apv)
                return env.addVar(apv.nameID, true, ratype, true, ratype);
            }
            else {
                this.raiseErrorIf(sinfo, ootype.attributes.includes("__internal"), "Cannot deconstruct primitive values");

                const allfields = this.m_assembly.getAllOOFieldsConstructors(ootype, oobinds);
                const selectfields = [...allfields.req, ...allfields.opt].map((fe) => fe[1]);

                let usenames = nassign.assigns.every((ap) => ap[0] !== undefined);
                let usepos = nassign.assigns.every((ap) => ap[0] === undefined);
                this.raiseErrorIf(sinfo, !usenames || usepos, "Cannot mix named and positional destructor vars -- may want to allow later though");

                //
                //TODO: need to do checks that we are not hitting private or hidden fields here unless our scope is otherwise ok
                //      also do same in get, project, update, etc.
                //

                let pnames: MIRFieldKey[] = [];
                let trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRType }[] = [];
                if (usepos) {
                    nassign.assigns.forEach((ap, i) => {
                        if (ap[1] instanceof VariableDeclarationStructuredAssignment) {
                            const ffi = selectfields[i];
                            const fkey = MIRKeyGenerator.generateFieldKey(this.resolveOOTypeFromDecls(ffi[0], ffi[2]), ffi[1].name)
                            const aptype = this.resolveAndEnsureTypeOnly(sinfo, ffi[1].declaredType, ffi[2]);

                            eltypes.push(aptype);
                            declaredvars.push([true, ap[1].vname, aptype, aptype]);
                            pnames.push(fkey);
                            trgts.push({pos: i, into: new MIRRegisterArgument(ap[1].vname), oftype: this.m_emitter.registerResolvedTypeReference(aptype)});
                        }
                    });
                }
                else {
                    nassign.assigns.forEach((ap, i) => {
                        if (ap[1] instanceof VariableDeclarationStructuredAssignment) {
                            const ffix = selectfields.find((ff) => ff[1].name === ap[0]);
                            this.raiseErrorIf(sinfo, ffix === undefined, "Could not match field with destructor variable");

                            const ffi = ffix as [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>];
                            const fkey = MIRKeyGenerator.generateFieldKey(this.resolveOOTypeFromDecls(ffi[0], ffi[2]), ffi[1].name)
                            const aptype = this.resolveAndEnsureTypeOnly(sinfo, ffi[1].declaredType, ffi[2]);

                            eltypes.push(aptype);
                            declaredvars.push([true, ap[1].vname, aptype, aptype]);
                            pnames.push(fkey);
                            trgts.push({pos: i, into: new MIRRegisterArgument(ap[1].vname), oftype: this.m_emitter.registerResolvedTypeReference(aptype)});
                        }
                    });
                }

                elatom = ResolvedEphemeralListType.create(eltypes);
                this.m_emitter.emitEntityProjectToEphemeral(sinfo, arg, this.m_emitter.registerResolvedTypeReference(arglayouttype), this.m_emitter.registerResolvedTypeReference(argoftype), pnames, !argoftype.isUniqueRecordTargetType(), elatom, elreg);
                this.m_emitter.emitMultiLoadFromEpehmeralList(sinfo, elreg, this.m_emitter.registerResolvedTypeReference(ResolvedType.createSingle(elatom)), trgts);

                return env.multiVarUpdate(declaredvars, []);
            }
        }
    }

    private checkStructuredVariableAssignmentStatement(env: TypeEnvironment, stmt: StructuredVariableAssignmentStatement): TypeEnvironment {
        const inferassign = this.getTypeOfStructuredAssignForInfer(stmt.sinfo, env, stmt.assign);

        const expreg = this.m_emitter.generateTmpRegister();
        const eenv = this.checkExpression(env, stmt.exp, expreg, inferassign, { refok: true, orok: true });

        const ofassigntype = this.getTypeOfStructuredAssignForAssign(stmt.sinfo, env, stmt.assign, eenv.getExpressionResult().valtype.flowtype);
        this.raiseErrorIf(stmt.sinfo, !this.m_assembly.subtypeOf(ofassigntype, eenv.getExpressionResult().valtype.flowtype), "Not sure what happened but types don't match here");

        return this.generateStructuredAssignOperations(stmt.sinfo, env, stmt.assign, expreg, eenv.getExpressionResult().valtype.layout, ofassigntype);
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

    private checkSwitchGuard(sinfo: SourceInfo, env: TypeEnvironment, switchvname: string, guard: SwitchGuard, nextlabel: string, actionlabel: string): { tenv: TypeEnvironment | undefined, fenv: TypeEnvironment | undefined } {
        let opts: { tenv: TypeEnvironment | undefined, fenv: TypeEnvironment | undefined } = { tenv: undefined, fenv: undefined };
        let mreg = this.m_emitter.generateTmpRegister();

        if (guard instanceof WildcardSwitchGuard) {
            this.m_emitter.emitLoadConstBool(sinfo, true, mreg);
            opts = { tenv: env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True), fenv: undefined };
        }
        else {
            const lguard = guard as LiteralSwitchGuard;

            const lexpx = this.m_assembly.reduceLiteralValueToCanonicalForm(lguard.litmatch.exp, env.terms, undefined);
            this.raiseErrorIf(sinfo, lexpx === undefined);

            const lexp = lexpx as [Expression, ResolvedType, string];
            const eqreg = this.m_emitter.generateTmpRegister();
            const eqs = this.strongEQ(sinfo, env, lexp[0], new AccessVariableExpression(sinfo, switchvname), eqreg);

            const fflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, eqs);
            opts = {
                tenv: fflows.tenvs.length !== 0 ? TypeEnvironment.join(this.m_assembly, ...fflows.tenvs) : undefined,
                fenv: fflows.fenvs.length !== 0 ? TypeEnvironment.join(this.m_assembly, ...fflows.fenvs) : undefined
            };
        }

        if(opts.tenv === undefined) {
            this.m_emitter.emitDirectJump(sinfo, nextlabel);
        }
        else if (opts.fenv === undefined) {
            this.m_emitter.emitDirectJump(sinfo, actionlabel);
        }
        else {
            this.m_emitter.emitBoolJump(sinfo, mreg, actionlabel, nextlabel);
        }

        return opts;
    }

    private checkMatchGuard(sinfo: SourceInfo, midx: number, env: TypeEnvironment, matchvname: string, cvname: string | undefined, guard: MatchGuard, nextlabel: string, actionlabel: string): { newlive: string[], tenv: TypeEnvironment | undefined, fenv: TypeEnvironment | undefined } {
        let opts: { tenv: TypeEnvironment | undefined, fenv: TypeEnvironment | undefined } = { tenv: undefined, fenv: undefined };
        let mreg = this.m_emitter.generateTmpRegister();

        const vspecial = new MIRRegisterArgument(matchvname);
        const vspecialinfo = env.getLocalVarInfo(matchvname) as VarInfo;
        env = env.setResultExpression(vspecialinfo.declaredType, vspecialinfo.flowType, undefined, undefined);

        let lifetimes: string[] = [];
        if (guard instanceof WildcardMatchGuard) {
            this.m_emitter.emitLoadConstBool(sinfo, true, mreg);
            opts = { tenv: env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True), fenv: undefined };

            this.m_emitter.emitDirectJump(sinfo, actionlabel);
        }
        else if (guard instanceof TypeMatchGuard) {
            const tmatch = this.resolveAndEnsureTypeOnly(sinfo, guard.oftype, env.terms);
            this.m_emitter.emitTypeOf(sinfo, mreg, this.m_emitter.registerResolvedTypeReference(tmatch), vspecial, this.m_emitter.registerResolvedTypeReference(vspecialinfo.declaredType), this.m_emitter.registerResolvedTypeReference(vspecialinfo.flowType), undefined);
            
            const fflows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, tmatch, [env]);
            const okenvs = fflows.tenvs.map((eev) => eev.inferVarsOfType(eev.getExpressionResult().valtype.flowtype, matchvname, cvname).setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True));
            const failenvs = fflows.fenvs.map((eev) => eev.inferVarsOfType(eev.getExpressionResult().valtype.flowtype, matchvname, cvname).setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False));

            opts = {
                tenv: okenvs.length !== 0 ? TypeEnvironment.join(this.m_assembly, ...okenvs) : undefined,
                fenv: failenvs.length !== 0 ? TypeEnvironment.join(this.m_assembly, ...failenvs) : undefined
            };

            if (opts.tenv === undefined) {
                this.m_emitter.emitDirectJump(sinfo, nextlabel);
            }
            else if (opts.fenv === undefined) {
                this.m_emitter.emitDirectJump(sinfo, actionlabel);
            }
            else {
                this.m_emitter.emitBoolJump(sinfo, mreg, actionlabel, nextlabel);
            }
        }
        else {
            const sguard = guard as StructureMatchGuard;

            const assigntype = this.getTypeOfStructuredAssignForMatch(sinfo, env, sguard.match);
            const tmatch = this.resolveAndEnsureTypeOnly(sinfo, assigntype, env.terms);
            this.m_emitter.emitTypeOf(sinfo, mreg, this.m_emitter.registerResolvedTypeReference(tmatch), vspecial, this.m_emitter.registerResolvedTypeReference(vspecialinfo.declaredType), this.m_emitter.registerResolvedTypeReference(vspecialinfo.flowType), undefined);
            
            const fflows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, tmatch, [env]);
            const okenvs = fflows.tenvs.map((eev) => eev.inferVarsOfType(eev.getExpressionResult().valtype.flowtype, matchvname, cvname).setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True));
            const failenvs = fflows.fenvs.map((eev) => eev.inferVarsOfType(eev.getExpressionResult().valtype.flowtype, matchvname, cvname).setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False));

            opts = {
                tenv: okenvs.length !== 0 ? TypeEnvironment.join(this.m_assembly, ...okenvs) : undefined,
                fenv: failenvs.length !== 0 ? TypeEnvironment.join(this.m_assembly, ...failenvs) : undefined
            };

            if (opts.tenv === undefined) {
                this.m_emitter.emitDirectJump(sinfo, nextlabel);
            }
            else if (opts.fenv === undefined) {
                this.m_emitter.emitDirectJump(sinfo, actionlabel);
            }
            else {
                this.m_emitter.emitBoolJump(sinfo, mreg, actionlabel, nextlabel);
            }

            if (opts.tenv !== undefined) {
                lifetimes = [...sguard.decls].sort();
                this.m_emitter.setActiveBlock(actionlabel);

                this.generateStructuredAssignOperations(sinfo, opts.tenv, sguard.match, vspecial, vspecialinfo.declaredType, assigntype);
            }
        }

        return {
            newlive: lifetimes,
            tenv: opts.tenv,
            fenv: opts.fenv
        };
    }

    private checkSwitchStatement(env: TypeEnvironment, stmt: SwitchStatement): TypeEnvironment {
        const vreg = this.m_emitter.generateTmpRegister();
        const venv = this.checkExpression(env, stmt.sval, vreg, undefined, { refok: true, orok: false });
        const cvname = venv.getExpressionResult().expvar;

        const doneblck = this.m_emitter.createNewBlock("Lswitchstmt_done");
        const matchvar = `$switch_#${stmt.sinfo.pos}`;
        let cenv = this.checkDeclareSingleVariable(stmt.sinfo, venv.pushLocalScope(), matchvar, true, venv.getExpressionResult().valtype.flowtype, {etype: ValueType.createUniform(venv.getExpressionResult().valtype.flowtype), etreg: vreg});

        let hasfalseflow = true;
        let results: TypeEnvironment[] = [];
        let rblocks: [string, string[]][] = [];
        for (let i = 0; i < stmt.flow.length && !hasfalseflow; ++i) {
            const nextlabel = this.m_emitter.createNewBlock(`Lswitchstmt_${i}next`);
            const actionlabel = this.m_emitter.createNewBlock(`Lswitchstmt_${i}action`);

            const test = this.checkMatchGuard(stmt.sinfo, i, cenv, matchvar, cvname, stmt.flow[i].check, nextlabel, actionlabel);

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

    private checkMatchStatement(env: TypeEnvironment, stmt: MatchStatement): TypeEnvironment {
        const vreg = this.m_emitter.generateTmpRegister();
        const venv = this.checkExpression(env, stmt.sval, vreg, undefined, { refok: true, orok: false });
        const cvname = venv.getExpressionResult().expvar;

        const doneblck = this.m_emitter.createNewBlock("Lswitchstmt_done");
        const matchvar = `$match_#${stmt.sinfo.pos}`;
        let cenv = this.checkDeclareSingleVariable(stmt.sinfo, venv.pushLocalScope(), matchvar, true, venv.getExpressionResult().valtype.flowtype, {etype: ValueType.createUniform(venv.getExpressionResult().valtype.flowtype), etreg: vreg});

        let hasfalseflow = true;
        let results: TypeEnvironment[] = [];
        let rblocks: [string, string[]][] = [];
        for (let i = 0; i < stmt.flow.length && !hasfalseflow; ++i) {
            const nextlabel = this.m_emitter.createNewBlock(`Lswitchstmt_${i}next`);
            const actionlabel = this.m_emitter.createNewBlock(`Lswitchstmt_${i}action`);

            const test = this.checkMatchGuard(stmt.sinfo, i, cenv, matchvar, cvname, stmt.flow[i].check, nextlabel, actionlabel);

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

            this.raiseErrorIf(stmt.sinfo, !rrtype.isResultType(), "Result must be an Result<T, E> type");
            const {T, E} = this.getTEBinds(this.getUniqueTypeBinds(rrtype));
            const errtype = this.m_assembly.getErrType(T, E);

            const doneblck = this.m_emitter.createNewBlock("Lcheck_done");
            const failblck = this.m_emitter.createNewBlock("Lcheck_fail");
            
            this.m_emitter.emitBoolJump(stmt.sinfo, testreg, doneblck, failblck);
            this.m_emitter.setActiveBlock(failblck);

            const errreg = this.m_emitter.generateTmpRegister();
            const errflow = TypeEnvironment.join(this.m_assembly, ...flow.fenvs.map((te) => te.setReturn(this.m_assembly, rrtype)));
           
            let errenv = errflow;
            if (stmt.err instanceof LiteralNoneExpression) {
                this.raiseErrorIf(stmt.sinfo, !this.m_assembly.subtypeOf(E, this.m_assembly.getSpecialNoneType()));

                const ctarg = new MIRConstantNone();
                this.m_emitter.emitInject(stmt.sinfo, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()), this.m_emitter.registerResolvedTypeReference(errtype), ctarg, errreg);
            }
            else {
                const terrreg = this.m_emitter.generateTmpRegister();
                const errevalenv = this.checkExpression(errflow, stmt.err, terrreg, rrtype);
                const errres = errevalenv.getExpressionResult().valtype;
                this.raiseErrorIf(stmt.sinfo, !this.m_assembly.subtypeOf(E, rrtype), "Error result must evaluate to Result<T, E>");

                const ctarg = this.emitInlineConvertToFlow(stmt.sinfo, terrreg, errres);
                this.m_emitter.emitInject(stmt.sinfo, this.m_emitter.registerResolvedTypeReference(errres.flowtype), this.m_emitter.registerResolvedTypeReference(errtype), ctarg, errreg);
            }

            this.m_emitter.emitReturnAssign(stmt.sinfo, errreg, this.m_emitter.registerResolvedTypeReference(rrtype));
            this.m_emitter.emitDirectJump(stmt.sinfo, "returnassign");

            this.m_emitter.setActiveBlock(doneblck);

            errenv = errflow.setReturn(this.m_assembly, rrtype);
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
            case StatementTag.SwitchStatement:
                return this.checkSwitchStatement(env, stmt as SwitchStatement).clearExpressionResult();
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

    private checkBodyExpression(srcFile: string, env: TypeEnvironment, body: Expression, activeResultType: ResolvedType | undefined, outparaminfo: { pname: string, ptype: ResolvedType }[]): MIRBody | undefined {
        this.m_emitter.initializeBodyEmitter(activeResultType);

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

    private checkBodyStatement(srcFile: string, env: TypeEnvironment, body: BlockStatement, activeResultType: ResolvedType | undefined, optparaminfo: { pname: string, ptype: ResolvedType, maskidx: number, initaction: InitializerEvaluationAction }[], outparaminfo: { pname: string, defonentry: boolean, ptype: ResolvedType }[], preject: [{ ikey: string, sinfo: SourceInfo, srcFile: string }[], string[]] | undefined, postject: [{ ikey: string, sinfo: SourceInfo, srcFile: string }[], string[]] | undefined | undefined): MIRBody | undefined {
        this.m_emitter.initializeBodyEmitter(activeResultType);

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
                this.m_emitter.emitRegisterStore(body.sinfo, storevar, storevar, this.m_emitter.registerResolvedTypeReference(oftype), new MIRStatmentGuard(guard, "defaultonfalse", new MIRGlobalVariable(iv.gkey, iv.shortgkey)));
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
        //if (this.m_errors.length > 20) {
        //    throw new Error("More than 20 errors ... halting type checker");
        //}

        //
        //TODO: when we don't emit bodies we return undefined from exp to body -- this can spread and result in undefined refs in some body positions
        //      for now just abort on first error and be done to prevent this
        //

        throw new Error("Halting on type error");
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
        const ikeyinfo = MIRKeyGenerator.generateFunctionKeyWType(this.resolveOOTypeFromDecls(containingType, binds), decl.name, binds, [], "initfield");
        const bodyid = this.generateBodyID(decl.sourceLocation, decl.srcFile, "initfield");

        try {
            const cexp = decl.value as ConstantExpressionValue;
            if (cexp.captured.size === 0) {
                const lexp = this.m_assembly.compileTimeReduceConstantExpression(cexp.exp, binds, ddecltype);
                if(lexp !== undefined) {
                    return new InitializerEvaluationLiteralExpression(lexp);
                }
                else {
                    const gkey = MIRKeyGenerator.generateGlobalKeyWType(this.resolveOOTypeFromDecls(containingType, binds), decl.name, "initfield");
                    if (!this.m_emitter.masm.constantDecls.has(gkey.keyid)) {
                        const idecl = this.processInvokeInfo_ExpressionIsolated(bodyid, decl.srcFile, cexp.exp, ikeyinfo.keyid, ikeyinfo.shortname, decl.sourceLocation, ["static_initializer", "private"], ddecltype, binds);
                        this.m_emitter.masm.invokeDecls.set(ikeyinfo.keyid, idecl as MIRInvokeBodyDecl);

                        const dtype = this.m_emitter.registerResolvedTypeReference(ddecltype);
                        const mirglobal = new MIRConstantDecl(enclosingType.keyid, gkey.keyid, gkey.shortname, [], decl.sourceLocation, decl.srcFile, dtype.typeID, ikeyinfo.keyid);

                        this.m_emitter.masm.constantDecls.set(gkey.keyid, mirglobal);
                    }

                    return new InitializerEvaluationConstantLoad(gkey.keyid, gkey.shortname);
                }
            }
            else {
                if (!this.m_emitter.masm.invokeDecls.has(ikeyinfo.keyid)) {
                    const capturedtypes = this.getCapturedTypeInfoForFields(decl.sourceLocation, cexp.captured, allfieldstypes);
                    const fparams = [...cexp.captured].sort().map((cp) => {
                        return { name: cp, refKind: undefined, ptype: capturedtypes.get(cp) as ResolvedType };
                    });

                    const idecl = this.processInvokeInfo_ExpressionLimitedArgs(bodyid, decl.srcFile, cexp.exp, ikeyinfo.keyid, ikeyinfo.shortname, decl.sourceLocation, ["dynamic_initializer", "private", ...decl.attributes], fparams, ddecltype, binds);
                    this.m_emitter.masm.invokeDecls.set(ikeyinfo.keyid, idecl as MIRInvokeBodyDecl);
                }

                return new InitializerEvaluationCallAction(ikeyinfo.keyid, ikeyinfo.shortname, [...cexp.captured].sort().map((cp) => new MIRRegisterArgument(cp)));
            }
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();

            return new InitializerEvaluationCallAction(ikeyinfo.keyid, ikeyinfo.shortname, []);
        }
    }

    private processExpressionForOptParamDefault(srcFile: string, pname: string, ptype: ResolvedType, cexp: ConstantExpressionValue, binds: Map<string, ResolvedType>, enclosingDecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, invoke: InvokeDecl): InitializerEvaluationAction {
        const bodyid = this.generateBodyID(cexp.exp.sinfo, srcFile, "pdefault");
        const ikeyinfo = MIRKeyGenerator.generateFunctionKeyWNamespace(bodyid /*not ns but sure*/, pname, binds, [], "pdefault");

        try {
            if (cexp.captured.size === 0) {
                const lexp = this.m_assembly.compileTimeReduceConstantExpression(cexp.exp, binds, ptype);
                if (lexp !== undefined) {
                    return new InitializerEvaluationLiteralExpression(lexp);
                }
                else {
                    const gkey =  MIRKeyGenerator.generateGlobalKeyWNamespace(bodyid /*not ns but sure*/, pname, "pdefault");
                    const idecl = this.processInvokeInfo_ExpressionIsolated(bodyid, srcFile, cexp.exp, ikeyinfo.keyid, ikeyinfo.shortname, cexp.exp.sinfo, ["static_initializer", "private"], ptype, binds);
                    this.m_emitter.masm.invokeDecls.set(ikeyinfo.keyid, idecl as MIRInvokeBodyDecl);

                    const dtype = this.m_emitter.registerResolvedTypeReference(ptype);
                    const mirglobal = new MIRConstantDecl(undefined, gkey.keyid, gkey.shortname, [], cexp.exp.sinfo, srcFile, dtype.typeID, ikeyinfo.keyid);

                    this.m_emitter.masm.constantDecls.set(gkey.keyid, mirglobal);

                    return new InitializerEvaluationConstantLoad(gkey.keyid, gkey.shortname);
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

                const idecl = this.processInvokeInfo_ExpressionGeneral(bodyid, srcFile, cexp.exp, ikeyinfo.keyid, ikeyinfo.shortname, cexp.exp.sinfo, ["dynamic_initializer", "private"], fparams, ptype, binds, new Map<string, { pcode: PCode, captured: string[] }>(), []);
                this.m_emitter.masm.invokeDecls.set(ikeyinfo.keyid, idecl as MIRInvokeBodyDecl);

                return new InitializerEvaluationCallAction(ikeyinfo.keyid, ikeyinfo.shortname, [...cexp.captured].sort().map((cp) => new MIRRegisterArgument(cp !== "%this_captured" ? cp : "this")));
            }
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();

            return new InitializerEvaluationCallAction(ikeyinfo.keyid, ikeyinfo.shortname, []);
        }
    }

    private processGenerateSpecialInvariantDirectFunction(exps: [ConstantExpressionValue, OOPTypeDecl, Map<string, ResolvedType>][], allfieldstypes: Map<string, ResolvedType>): { ikey: string, sinfo: SourceInfo, srcFile: string, args: string[] }[] {
        try {
            const clauses = exps.map((cev, i) => {
                const bodyid = this.generateBodyID(cev[0].exp.sinfo, cev[1].srcFile, `invariant@${i}`);
                const ikeyinfo = MIRKeyGenerator.generateFunctionKeyWNamespace(bodyid /*not ns but sure*/, `invariant@${i}`, cev[2], []);

                const capturedtypes = this.getCapturedTypeInfoForFields(cev[0].exp.sinfo, cev[0].captured, allfieldstypes);
                const fparams = [...cev[0].captured].sort().map((cp) => {
                    return { name: cp, refKind: undefined, ptype: capturedtypes.get(cp) as ResolvedType };
                });

                const idecl = this.processInvokeInfo_ExpressionLimitedArgs(bodyid, cev[1].srcFile, cev[0].exp, ikeyinfo.keyid, ikeyinfo.shortname, cev[1].sourceLocation, ["invariant_clause", "private"], fparams, this.m_assembly.getSpecialBoolType(), cev[2]);
                this.m_emitter.masm.invokeDecls.set(ikeyinfo.keyid, idecl as MIRInvokeBodyDecl);

                return { ikey: ikeyinfo.keyid, sinfo: cev[0].exp.sinfo, srcFile: cev[1].srcFile, args: [...cev[0].captured].sort() };
            });

            return clauses;
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();

            return [];
        }
    }

    private generateConstructor(bodyid: string, env: TypeEnvironment, conskey: MIRInvokeKey, conskeyshort: string, tdecl: EntityTypeDecl, binds: Map<string, ResolvedType>) {
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
        const clauses = this.processGenerateSpecialInvariantDirectFunction(invs, allfieldstypes);

        const optfields = [...allfields].filter((ff) => ff[1][1].value !== undefined).map((af) => af[1]);
        const fieldparams = this.m_assembly.getAllOOFieldsConstructors(tdecl, binds);

        const optinits = optfields.map((opf) => {
            return this.processExpressionForFieldInitializer(opf[0], opf[1], opf[2], allfieldstypes);
        });

        this.m_emitter.initializeBodyEmitter(undefined);

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
                this.m_emitter.emitRegisterStore(ofi[1].sourceLocation, storevar, storevar, this.m_emitter.registerResolvedTypeReference(oftype), new MIRStatmentGuard(guard, "defaultonfalse", new MIRGlobalVariable(iv.gkey, iv.shortgkey)));
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
            params.push(new MIRFunctionParameter(`$${fpi[0]}`, ftype.typeID));
        });

        const consbody = this.m_emitter.getBody(tdecl.srcFile, tdecl.sourceLocation);
        if (consbody !== undefined) {
            const consinv = new MIRInvokeBodyDecl(this.m_emitter.registerResolvedTypeReference(constype).typeID, bodyid, conskey, conskeyshort, ["constructor", "private"], false, tdecl.sourceLocation, tdecl.srcFile, params, optfields.length, this.m_emitter.registerResolvedTypeReference(constype).typeID, undefined, undefined, consbody);
            this.m_emitter.masm.invokeDecls.set(conskey, consinv);
        }
    }

    private generateInjectableConstructor(bodyid: string, conskey: MIRInvokeKey, conskeyshort: string, tdecl: EntityTypeDecl, binds: Map<string, ResolvedType>, oftype: ResolvedType) {
        const constype = this.resolveOOTypeFromDecls(tdecl, binds);
        const invs = ([] as [ConstantExpressionValue, OOPTypeDecl, Map<string, ResolvedType>][]).concat(...
            this.m_assembly.getAllInvariantProvidingTypes(tdecl, binds).map((ipt) => 
            ipt[1].invariants
            .filter((inv) => isBuildLevelEnabled(inv.level, this.m_buildLevel))
            .map((inv) => [inv.exp, ipt[1], ipt[2]] as [ConstantExpressionValue, OOPTypeDecl, Map<string, ResolvedType>]))
        );

        const implicitfield = new Map<string, ResolvedType>().set("value", oftype);
        const clauses = this.processGenerateSpecialInvariantDirectFunction(invs, implicitfield);

        this.m_emitter.initializeBodyEmitter(undefined);

        for (let i = 0; i < clauses.length; ++i) {
            const ttarg = this.m_emitter.generateTmpRegister();
            const chkargs = clauses[i].args.map((cv) => new MIRRegisterArgument(cv));
            this.m_emitter.emitInvokeFixedFunction(clauses[i].sinfo, clauses[i].ikey, chkargs, undefined, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), ttarg);
            this.m_emitter.emitAssertCheck(clauses[i].sinfo, `Failed invariant on line ${clauses[i].srcFile}::${clauses[i].sinfo.line}`, ttarg);
        }
        
        const trgt = this.m_emitter.generateTmpRegister();
        this.m_emitter.emitInject(tdecl.sourceLocation, this.m_emitter.registerResolvedTypeReference(oftype), this.m_emitter.registerResolvedTypeReference(constype), new MIRRegisterArgument("$value"), trgt);
        this.m_emitter.emitReturnAssign(tdecl.sourceLocation, trgt, this.m_emitter.registerResolvedTypeReference(constype));
        this.m_emitter.emitDirectJump(tdecl.sourceLocation, "returnassign");

        this.m_emitter.setActiveBlock("returnassign");

        const rrinfo = this.generateRefInfoForReturnEmit(constype, []);
        this.emitPrologForReturn(tdecl.sourceLocation, rrinfo, false);
        this.m_emitter.emitDirectJump(tdecl.sourceLocation, "exit");

        const params: MIRFunctionParameter[] = [new MIRFunctionParameter("$value", constype.typeID)];
        const consbody = this.m_emitter.getBody(tdecl.srcFile, tdecl.sourceLocation);
        if (consbody !== undefined) {
            const consinv = new MIRInvokeBodyDecl(this.m_emitter.registerResolvedTypeReference(constype).typeID, bodyid, conskey, conskeyshort, ["constructor", "private"], false, tdecl.sourceLocation, tdecl.srcFile, params, 0, this.m_emitter.registerResolvedTypeReference(constype).typeID, undefined, undefined, consbody);
            this.m_emitter.masm.invokeDecls.set(conskey, consinv);
        }
    }

    private processGenerateSpecialPreFunction_FailFast(invkparams: {name: string, refKind: "ref" | "out" | "out?" | undefined, ptype: ResolvedType}[], pcodes: Map<string, { pcode: PCode, captured: string[] }>, pargs: [string, ResolvedType][], exps: PreConditionDecl[], binds: Map<string, ResolvedType>, srcFile: string): { ikey: string, sinfo: SourceInfo, srcFile: string }[] {
        try {
            const clauses = exps
            .filter((cev) => isBuildLevelEnabled(cev.level, this.m_buildLevel))
            .map((cev, i) => {
                const bodyid = this.generateBodyID(cev.sinfo, srcFile, `pre@${i}`);
                const ikeyinfo = MIRKeyGenerator.generateFunctionKeyWNamespace(bodyid /*not ns but sure*/, `pre@${i}`, binds, []);

                const idecl = this.processInvokeInfo_ExpressionGeneral(bodyid, srcFile, cev.exp, ikeyinfo.keyid, ikeyinfo.shortname, cev.sinfo, ["precondition", "private"], invkparams, this.m_assembly.getSpecialBoolType(), binds, pcodes, pargs);
                this.m_emitter.masm.invokeDecls.set(ikeyinfo.keyid, idecl as MIRInvokeBodyDecl);

                return { ikey: ikeyinfo.keyid, sinfo: cev.sinfo, srcFile: srcFile };
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

    private processGenerateSpecialPostFunction(invkparams: {name: string, refKind: "ref" | "out" | "out?" | undefined, ptype: ResolvedType}[], pcodes: Map<string, { pcode: PCode, captured: string[] }>, pargs: [string, ResolvedType][], exps: PostConditionDecl[], binds: Map<string, ResolvedType>, srcFile: string): { ikey: string, sinfo: SourceInfo, srcFile: string }[] {
        try {
            const clauses = exps
            .filter((cev) => isBuildLevelEnabled(cev.level, this.m_buildLevel))
            .map((cev, i) => {
                const bodyid = this.generateBodyID(cev.sinfo, srcFile, `post@${i}`);
                const ikeyinfo = MIRKeyGenerator.generateFunctionKeyWNamespace(bodyid /*not ns but sure*/, `post@${i}`, binds, []);

                const idecl = this.processInvokeInfo_ExpressionGeneral(bodyid, srcFile, cev.exp, ikeyinfo.keyid, ikeyinfo.shortname, cev.sinfo, ["postcondition", "private"], invkparams, this.m_assembly.getSpecialBoolType(), binds, pcodes, pargs);
                this.m_emitter.masm.invokeDecls.set(ikeyinfo.keyid, idecl as MIRInvokeBodyDecl);

                return { ikey: ikeyinfo.keyid, sinfo: cev.sinfo, srcFile: srcFile };
            });

            return clauses;
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();

            return [];
        }
    }

    processOOType(tkey: MIRResolvedTypeKey, shortname: string, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>) {
        try {
            this.m_file = tdecl.srcFile;

            let terms = new Map<string, MIRType>();
            tdecl.terms.forEach((term) => terms.set(term.name, this.m_emitter.registerResolvedTypeReference(binds.get(term.name) as ResolvedType)));

            const provides = this.m_assembly.resolveProvides(tdecl, binds).map((provide) => {
                const ptype = this.resolveAndEnsureTypeOnly(new SourceInfo(0, 0, 0, 0), provide, binds);
                return this.m_emitter.registerResolvedTypeReference(ptype).typeID;
            });

            if (tdecl instanceof EntityTypeDecl) {
                if(tdecl.attributes.includes("__enum_type")) {
                    const consbodyid = this.generateBodyID(tdecl.sourceLocation, tdecl.srcFile, "@@constructor");
                    const conskey = MIRKeyGenerator.generateFunctionKeyWType(this.resolveOOTypeFromDecls(tdecl, binds), "@@constructor", new Map<string, ResolvedType>(), []);
                    this.generateInjectableConstructor(consbodyid, conskey.keyid, conskey.shortname, tdecl, binds, this.m_assembly.getSpecialNatType());

                    const enums = tdecl.staticMembers.map((sdecl) => { 
                        const vve = (((sdecl.value as ConstantExpressionValue).exp as ConstructorPrimaryExpression).args.argList[0] as PositionalArgument).value as LiteralIntegralExpression;
                        const v = Number.parseInt(vve.value.slice(0, vve.value.length - 1));
                        return {ename: sdecl.name, value: v}; 
                    });

                    const mirentity = new MIREnumEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, shortname, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, conskey.keyid, enums);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);
                }
                else if(tdecl.attributes.includes("__typedprimitive")) {
                    const rrtype = (tdecl.memberMethods.find((mm) => mm.name === "value") as MemberMethodDecl).invoke.resultType;
                    const oftype = this.resolveAndEnsureTypeOnly(tdecl.sourceLocation, rrtype, binds);

                    let conskey: string | undefined = undefined;
                    if(tdecl.invariants.length !== 0) {
                        const consbodyid = this.generateBodyID(tdecl.sourceLocation, tdecl.srcFile, "@@constructor");
                        const conskeyid = MIRKeyGenerator.generateFunctionKeyWType(this.resolveOOTypeFromDecls(tdecl, binds), "@@constructor", new Map<string, ResolvedType>(), []);
                        this.generateInjectableConstructor(consbodyid, conskeyid.keyid, conskeyid.shortname, tdecl, binds, oftype);

                        conskey = conskeyid.keyid;
                    }
                    const mirentity = new MIRConstructableEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, shortname, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, oftype.typeID, conskey, new Map<string, MIRType>());
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);
                }
                else if(tdecl.attributes.includes("__stringof_type") || tdecl.attributes.includes("__datastring_type")) {
                    const miroftype = this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType);
                    const mirbinds = new Map<string, MIRType>().set("T", this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType));

                    let optparse: MIRInvokeKey | undefined = undefined;
                    if (tdecl.attributes.includes("__datastring_type")) {
                        const sf = (tdecl.staticFunctions.find((sfv) => sfv.name === "accepts") as StaticFunctionDecl);
                        const mirencltype = this.m_emitter.registerResolvedTypeReference(this.resolveOOTypeFromDecls(tdecl, binds));
                        optparse = this.m_emitter.registerStaticCall(this.resolveOOTypeFromDecls(tdecl, binds), [mirencltype, tdecl, binds], sf, "accepts", binds, [], []);
                    }

                    const mirentity = new MIRConstructableInternalEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, shortname, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, miroftype.typeID, mirbinds, optparse);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);
                }
                else if(tdecl.attributes.includes("__bufferof_type") || tdecl.attributes.includes("__databuffer_type")) {
                    const miroftype = this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType);
                    const mirbinds = new Map<string, MIRType>().set("T", this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType));

                    let optparse: MIRInvokeKey | undefined = undefined;
                    if (tdecl.attributes.includes("__databuffer_type")) {
                        const sf = (tdecl.staticFunctions.find((sfv) => sfv.name === "accepts") as StaticFunctionDecl);
                        const mirencltype = this.m_emitter.registerResolvedTypeReference(this.resolveOOTypeFromDecls(tdecl, binds));
                        optparse = this.m_emitter.registerStaticCall(this.resolveOOTypeFromDecls(tdecl, binds), [mirencltype, tdecl, binds], sf, "accepts", binds, [], []);
                    }

                    const mirentity = new MIRConstructableInternalEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, shortname, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, miroftype.typeID, mirbinds, optparse);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);

                }
                else if(tdecl.attributes.includes("__ok_type")) {
                    const miroftype = this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType);
                    const mirbinds = new Map<string, MIRType>().set("T", this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType)).set("E", this.m_emitter.registerResolvedTypeReference(binds.get("E") as ResolvedType));

                    const mirentity = new MIRConstructableInternalEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, shortname, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, miroftype.typeID, mirbinds, undefined);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);

                }
                else if(tdecl.attributes.includes("__err_type")) {
                    const miroftype = this.m_emitter.registerResolvedTypeReference(binds.get("E") as ResolvedType);
                    const mirbinds = new Map<string, MIRType>().set("T", this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType)).set("E", this.m_emitter.registerResolvedTypeReference(binds.get("E") as ResolvedType));

                    const mirentity = new MIRConstructableInternalEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, shortname, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, miroftype.typeID, mirbinds, undefined);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);
                }
                else if(tdecl.attributes.includes("__something_type")) {
                    const miroftype = this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType);
                    const mirbinds = new Map<string, MIRType>().set("T", this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType));

                    const mirentity = new MIRConstructableInternalEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, shortname, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, miroftype.typeID, mirbinds, undefined);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);
                }
                else if(tdecl.attributes.includes("__list_type")) {
                    const miroftype = this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType);
                    const mirbinds = new Map<string, MIRType>().set("T", this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType));

                    const mirentity = new MIRPrimitiveListEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, shortname, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, miroftype.typeID, mirbinds);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);
                }
                else if(tdecl.attributes.includes("__stack_type")) {
                    assert(false);
                    //MIRPrimitiveStackEntityTypeDecl
                }
                else if(tdecl.attributes.includes("__queue_type")) {
                    assert(false);
                    //MIRPrimitiveQueueEntityTypeDecl
                }
                else if(tdecl.attributes.includes("__set_type")) {
                    assert(false);
                    //MIRPrimitiveSetEntityTypeDecl
                }
                else if(tdecl.attributes.includes("__map_type")) {
                    const maptype = this.m_emitter.registerResolvedTypeReference(this.resolveOOTypeFromDecls(tdecl, binds));
                    const oftype = ResolvedType.createSingle(ResolvedTupleAtomType.create([binds.get("K") as ResolvedType, binds.get("V") as ResolvedType]));
                    const miroftype = this.m_emitter.registerResolvedTypeReference(oftype);
                    const mirbinds = new Map<string, MIRType>().set("K", this.m_emitter.registerResolvedTypeReference(binds.get("K") as ResolvedType)).set("V", this.m_emitter.registerResolvedTypeReference(binds.get("V") as ResolvedType));
                    const ultype = this.m_assembly.getListType(oftype);
                    const mirultype = this.m_emitter.registerResolvedTypeReference(ultype);
                    const funq = (ultype.options[0] as ResolvedEntityAtomType).object.staticFunctions.find((ff) => ff.name === "s_uniqinv") as StaticFunctionDecl;
                    const unqchkinv = this.m_emitter.registerStaticCall(this.resolveOOTypeFromDecls(tdecl, binds), [maptype, tdecl, binds], funq, "s_uniqinv", binds, [], []);
                    
                    const mirentity = new MIRPrimitiveMapEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, shortname, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, miroftype.typeID, mirbinds, mirultype.typeID, unqchkinv);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);
                }
                else if(tdecl.attributes.includes("__internal")) { 
                    const mirentity = new MIRPrimitiveInternalEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, shortname, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);
                }
                else {
                    const consbodyid = this.generateBodyID(tdecl.sourceLocation, tdecl.srcFile, "@@constructor");
                    const conskey = MIRKeyGenerator.generateFunctionKeyWType(this.resolveOOTypeFromDecls(tdecl, binds), "@@constructor", new Map<string, ResolvedType>(), []);
                    const consenvargs = new Map<string, VarInfo>();
                    const ccfields = this.m_assembly.getAllOOFieldsConstructors(tdecl, binds);
                    [...ccfields.req, ...ccfields.opt].forEach((ff) => {
                        const fdi = ff[1];
                        const ftype = this.resolveAndEnsureTypeOnly(fdi[1].sourceLocation, fdi[1].declaredType, fdi[2]);
                        consenvargs.set(`$${fdi[1].name}`, new VarInfo(ftype, fdi[1].value === undefined, false, true, ftype));
                    });
                    const consfuncfields = [...ccfields.req, ...ccfields.opt].map((ccf) => MIRKeyGenerator.generateFieldKey(this.resolveOOTypeFromDecls(ccf[1][0], ccf[1][2]), ccf[1][1].name));

                    const consenv = TypeEnvironment.createInitialEnvForCall(conskey.keyid, consbodyid, binds, new Map<string, { pcode: PCode, captured: string[] }>(), consenvargs, undefined);
                    this.generateConstructor(consbodyid, consenv, conskey.keyid, conskey.shortname, tdecl, binds);

                    const fields: MIRFieldDecl[] = [];
                    const finfos = [...this.m_assembly.getAllOOFieldsLayout(tdecl, binds)];
                    finfos.forEach((ff) => {
                        const fi = ff[1];
                        const f = fi[1];

                        const fkey = MIRKeyGenerator.generateFieldKey(this.resolveOOTypeFromDecls(fi[0], fi[2]), f.name);
                        if (!this.m_emitter.masm.fieldDecls.has(fkey)) {
                            const dtypeResolved = this.resolveAndEnsureTypeOnly(f.sourceLocation, f.declaredType, binds);
                            const dtype = this.m_emitter.registerResolvedTypeReference(dtypeResolved);

                            const mfield = new MIRFieldDecl(tkey, f.attributes, f.sourceLocation, f.srcFile, fkey, f.name, dtype.typeID);
                            this.m_emitter.masm.fieldDecls.set(fkey, mfield);
                        }

                        fields.push(this.m_emitter.masm.fieldDecls.get(fkey) as MIRFieldDecl);
                    });

                    const mirentity = new MIRObjectEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, shortname, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, conskey !== undefined ? conskey.keyid : undefined, consfuncfields, fields);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);
                }
            }
            else {
                const mirconcept = new MIRConceptTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, shortname, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides);
                this.m_emitter.masm.conceptDecls.set(tkey, mirconcept);
            }
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();
        }
    }

    //e.g. expressions in match-case which must be constantly evaluatable
    private processInvokeInfo_ExpressionIsolated(bodyID: string, srcFile: string, exp: Expression, ikey: MIRInvokeKey, ishort: string, sinfo: SourceInfo, attributes: string[], declaredResult: ResolvedType, binds: Map<string, ResolvedType>): MIRInvokeDecl {
        const resultType = this.generateExpandedReturnSig(sinfo, declaredResult, []);

        const env = TypeEnvironment.createInitialEnvForCall(ikey, bodyID, binds, new Map<string, { pcode: PCode, captured: string[] }>(), new Map<string, VarInfo>(), declaredResult);
            
        const mirbody = this.checkBodyExpression(srcFile, env, exp, declaredResult, []);
        return new MIRInvokeBodyDecl(undefined, bodyID, ikey, ishort, attributes, false, sinfo, this.m_file, [], 0, resultType.typeID, undefined, undefined, mirbody as MIRBody);
    }

    //e.g. expressions as default arguments or field values which can only have other specific refs (but not pcodes or random other values)
    private processInvokeInfo_ExpressionLimitedArgs(bodyID: string, srcFile: string, exp: Expression, ikey: MIRInvokeKey, ishort: string, sinfo: SourceInfo, attributes: string[], invkparams: {name: string, refKind: "ref" | "out" | "out?" | undefined, ptype: ResolvedType}[], declaredResult: ResolvedType, binds: Map<string, ResolvedType>): MIRInvokeDecl {
        let cargs = new Map<string, VarInfo>();
        let params: MIRFunctionParameter[] = [];

        invkparams.forEach((p) => {
            assert(p.refKind === undefined);
            const mtype = this.m_emitter.registerResolvedTypeReference(p.ptype);

            cargs.set(p.name, new VarInfo(p.ptype, true, false, true, p.ptype));
            params.push(new MIRFunctionParameter(p.name, mtype.typeID));
        });

        const resultType = this.generateExpandedReturnSig(sinfo, declaredResult, invkparams);
        const env = TypeEnvironment.createInitialEnvForCall(ikey, bodyID, binds, new Map<string, { pcode: PCode, captured: string[] }>(), cargs, declaredResult);
        
        const mirbody = this.checkBodyExpression(srcFile, env, exp, declaredResult, []);
        return new MIRInvokeBodyDecl(undefined, bodyID, ikey, ishort, attributes, false, sinfo, this.m_file, params, 0, resultType.typeID, undefined, undefined, mirbody as MIRBody);
    }

    //e.g. things like pre and post conditions
    private processInvokeInfo_ExpressionGeneral(bodyID: string, srcFile: string, exp: Expression, ikey: MIRInvokeKey, ishort: string, sinfo: SourceInfo, attributes: string[], invkparams: {name: string, refKind: "ref" | "out" | "out?" | undefined, ptype: ResolvedType}[], declaredResult: ResolvedType, binds: Map<string, ResolvedType>, pcodes: Map<string, { pcode: PCode, captured: string[] }>, pargs: [string, ResolvedType][]): MIRInvokeDecl {
        let cargs = new Map<string, VarInfo>();
        let params: MIRFunctionParameter[] = [];

        invkparams.forEach((p) => {
            assert(p.refKind === undefined);
            const mtype = this.m_emitter.registerResolvedTypeReference(p.ptype);

            cargs.set(p.name, new VarInfo(p.ptype, true, false, true, p.ptype));
            params.push(new MIRFunctionParameter(p.name, mtype.typeID));
        });

        for (let i = 0; i < pargs.length; ++i) {
            cargs.set(pargs[i][0], new VarInfo(pargs[i][1], true, true, true, pargs[i][1]));

            const ctype = this.m_emitter.registerResolvedTypeReference(pargs[i][1]);
            params.push(new MIRFunctionParameter(this.m_emitter.generateCapturedVarName(bodyID, pargs[i][0]), ctype.typeID));
        }

        const resultType = this.generateExpandedReturnSig(sinfo, declaredResult, invkparams);
        const env = TypeEnvironment.createInitialEnvForCall(ikey, bodyID, binds, pcodes, cargs, declaredResult);
        
        const mirbody = this.checkBodyExpression(srcFile, env, exp, declaredResult, []);
        return new MIRInvokeBodyDecl(undefined, bodyID, ikey, ishort, attributes, false, sinfo, this.m_file, params, 0, resultType.typeID, undefined, undefined, mirbody as MIRBody);
    }

    private processInvokeInfo(name: string, ikey: MIRInvokeKey, shortname: string, enclosingDecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, kind: "namespace" | "static" | "member" | "operator", invoke: InvokeDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], pargs: [string, ResolvedType][]): MIRInvokeDecl {
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
                    params.push(new MIRFunctionParameter(p.name, mtype.typeID));
                }
            }
        });

        if (invoke.optRestType !== undefined) {
            const rtype = this.resolveAndEnsureTypeOnly(invoke.sourceLocation, invoke.optRestType, binds);
            cargs.set(invoke.optRestName as string, new VarInfo(rtype, true, false, true, rtype));

            const resttype = this.m_emitter.registerResolvedTypeReference(rtype);

            entrycallparams.push({name: invoke.optRestName as string, refKind: undefined, ptype: rtype});
            params.push(new MIRFunctionParameter(invoke.optRestName as string, resttype.typeID));
        }

        let prepostcapturednames: string[] = [];
        for (let i = 0; i < pargs.length; ++i) {
            cargs.set(pargs[i][0], new VarInfo(pargs[i][1], true, true, true, pargs[i][1]));

            const ctype = this.m_emitter.registerResolvedTypeReference(pargs[i][1]);
            params.push(new MIRFunctionParameter(this.m_emitter.generateCapturedVarName(pargs[i][0], invoke.bodyID), ctype.typeID));

            prepostcapturednames.push(this.m_emitter.generateCapturedVarName(pargs[i][0], invoke.bodyID));
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
                    const ii = this.processExpressionForOptParamDefault(invoke.srcFile, p.name, pdecltype, p.defaultexp, binds, enclosingDecl, invoke);
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
                    const preclauses = this.processGenerateSpecialPreFunction_FailFast(entrycallparams, fargs, pargs, invoke.preconditions, binds, invoke.srcFile);
                    preject = [preclauses, [...entrycallparams.map((pp) => pp.name), ...prepostcapturednames]];
                }
            }

            if (invoke.postconditions.length !== 0) {
                const postcluases = this.processGenerateSpecialPostFunction([...entrycallparams, ...rprs, ...rreforig], fargs, pargs, invoke.postconditions, binds, invoke.srcFile);
                postject = [postcluases, [...[...entrycallparams, ...rprs, ...rreforig].map((pp) => pp.name), ...prepostcapturednames]];
            }
        }
        else {
            const ootype = (enclosingDecl as [MIRType, OOPTypeDecl, Map<string, ResolvedType>])[1];
            const oobinds = (enclosingDecl as [MIRType, OOPTypeDecl, Map<string, ResolvedType>])[2];
            const absconds = this.m_assembly.getAbstractPrePostConds(name, ootype, oobinds, binds);

            if ((absconds !== undefined && absconds.pre[0].length !== 0) || invoke.preconditions.length !== 0) {
                this.raiseErrorIf(invoke.sourceLocation, invoke.preconditions.some((pre) => pre.isvalidate) || (absconds !== undefined && absconds.pre[0].some((pre) => pre.isvalidate)), "Cannot use validate preconditions on non-entrypoint functions");

                const abspreclauses = absconds !== undefined ? this.processGenerateSpecialPreFunction_FailFast(entrycallparams, fargs, pargs, absconds.pre[0], absconds.pre[1], invoke.srcFile) : [];
                const preclauses = this.processGenerateSpecialPreFunction_FailFast(entrycallparams, fargs, pargs, invoke.preconditions, binds, invoke.srcFile);
                preject = [[...abspreclauses, ...preclauses], [...entrycallparams.map((pp) => pp.name), ...prepostcapturednames]];
            }

            if ((absconds !== undefined && absconds.post[0].length !== 0) || invoke.postconditions.length !== 0) {
                const abspostclauses = absconds !== undefined ? this.processGenerateSpecialPostFunction([...entrycallparams, ...rprs, ...rreforig], fargs, pargs, absconds.post[0], absconds.post[1], invoke.srcFile) : [];
                const postcluases = this.processGenerateSpecialPostFunction([...entrycallparams, ...rprs, ...rreforig], fargs, pargs, invoke.postconditions, binds, invoke.srcFile);
                postject = [[...abspostclauses, ...postcluases], [...[...entrycallparams, ...rprs, ...rreforig].map((pp) => pp.name), ...prepostcapturednames]];
            }
        }

        const encdecl = enclosingDecl !== undefined ? enclosingDecl[0].typeID : undefined;
        if (typeof ((invoke.body as BodyImplementation).body) === "string") {
            if ((invoke.body as BodyImplementation).body !== "default" || OOPTypeDecl.attributeSetContains("__primitive", invoke.attributes)) {
                let mpc = new Map<string, MIRPCode>();
                fargs.forEach((v, k) => mpc.set(k, { code: MIRKeyGenerator.generatePCodeKey(v.pcode.code.isPCodeFn, v.pcode.code.bodyID), cargs: [...v.captured].map((cname) => this.m_emitter.generateCapturedVarName(cname, v.pcode.code.bodyID)) }));

                let mbinds = new Map<string, MIRResolvedTypeKey>();
                binds.forEach((v, k) => mbinds.set(k, this.m_emitter.registerResolvedTypeReference(v).typeID));

                const scalarslots = invoke.optscalarslots.map((sslot) => {
                    const rtype = this.resolveAndEnsureTypeOnly(invoke.sourceLocation, sslot.vtype, binds);
                    return { vname: sslot.vname, vtype: this.m_emitter.registerResolvedTypeReference(rtype).typeID };
                });
                const mixedslots = invoke.optmixedslots.map((mslot) => {
                    const rtype = this.resolveAndEnsureTypeOnly(invoke.sourceLocation, mslot.vtype, binds);
                    return { vname: mslot.vname, vtype: this.m_emitter.registerResolvedTypeReference(rtype).typeID };
                });

                return new MIRInvokePrimitiveDecl(encdecl, invoke.bodyID, ikey, shortname, invoke.attributes, recursive, invoke.sourceLocation, invoke.srcFile, mbinds, params, resultType.typeID, (invoke.body as BodyImplementation).body as string, mpc, scalarslots, mixedslots);
            }
            else {
                //
                //TODO: should do some checking that this is a valid thing to default implement
                //

                const env = TypeEnvironment.createInitialEnvForCall(ikey, invoke.bodyID, binds, fargs, cargs, declaredResult);

                const vops = invoke.params.map((p) => {
                    const bvar = new AccessVariableExpression(invoke.sourceLocation, p.name);
                    const faccess = new PostfixAccessFromName(invoke.sourceLocation, "v");
                    return new PositionalArgument(undefined, false, new PostfixOp(invoke.sourceLocation, bvar, [faccess]));
                });
                const opexp = new CallNamespaceFunctionOrOperatorExpression(invoke.sourceLocation, "NSCore", name, new TemplateArguments([]), "no", new Arguments(vops), OOPTypeDecl.attributeSetContains("prefix", invoke.attributes) ? "prefix" : "infix");
                const consexp = new CallStaticFunctionOrOperatorExpression(invoke.sourceLocation, invoke.resultType, "create", new TemplateArguments([]), "no", new Arguments([new PositionalArgument(undefined, false, opexp)]), "std");

                const mirbody = this.checkBodyExpression(invoke.srcFile, env, consexp, declaredResult, []) as MIRBody;
                return new MIRInvokeBodyDecl(encdecl, invoke.bodyID, ikey, shortname, invoke.attributes, recursive, invoke.sourceLocation, invoke.srcFile, params, 0, resultType.typeID, undefined, undefined, mirbody);
            }
        }
        else {
            const env = TypeEnvironment.createInitialEnvForCall(ikey, invoke.bodyID, binds, fargs, cargs, declaredResult);

            const mirbody = this.checkBodyStatement(invoke.srcFile, env, (realbody as BodyImplementation).body as BlockStatement, declaredResult, optparaminfo, outparaminfo, preject, postject);
            return new MIRInvokeBodyDecl(encdecl, invoke.bodyID, ikey, shortname, invoke.attributes, recursive, invoke.sourceLocation, invoke.srcFile, params, optparaminfo.length, resultType.typeID, preject !== undefined ? preject[0].map((pc) => pc.ikey) : undefined, postject !== undefined ? postject[0].map((pc) => pc.ikey) : undefined, mirbody as MIRBody);
        }
    }

    private processPCodeInfo(ikey: MIRInvokeKey, shortname: string, sinfo: SourceInfo, pci: InvokeDecl, binds: Map<string, ResolvedType>, fsig: ResolvedFunctionType, pargs: [string, ResolvedType][], capturedpcodes: [string, { pcode: PCode, captured: string[] }][]): MIRInvokeDecl {
        this.checkPCodeDecl(sinfo, fsig, pci.recursive, capturedpcodes.map((cpc) => cpc[1].pcode));

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
                params.push(new MIRFunctionParameter(p.name, mtype.typeID));
            }
        });

        if (pci.optRestType !== undefined) {
            const rtype = fsig.optRestParamType as ResolvedType;
            cargs.set(pci.optRestName as string, new VarInfo(rtype, true, false, true, rtype));

            const resttype = this.m_emitter.registerResolvedTypeReference(rtype);
            entrycallparams.push({name: pci.optRestName as string, refKind: undefined, ptype: rtype});
            params.push(new MIRFunctionParameter(pci.optRestName as string, resttype.typeID));
        }

        for (let i = 0; i < pargs.length; ++i) {
            cargs.set(pargs[i][0], new VarInfo(pargs[i][1], true, true, true, pargs[i][1]));

            const ctype = this.m_emitter.registerResolvedTypeReference(pargs[i][1]);
            params.push(new MIRFunctionParameter(this.m_emitter.generateCapturedVarName(pargs[i][0], pci.bodyID), ctype.typeID));
        }

        let resolvedResult = fsig.resultType;
        const resultType = this.generateExpandedReturnSig(sinfo, resolvedResult, entrycallparams);

        const realbody = ((pci.body as BodyImplementation).body instanceof Expression) 
            ? new BlockStatement(sinfo, [new ReturnStatement(sinfo, [(pci.body as BodyImplementation).body as Expression])])
            : ((pci.body as BodyImplementation).body as BlockStatement);


        let pcodes = new Map<string, { pcode: PCode, captured: string[] }>();
        capturedpcodes.forEach((cpc) => {
            pcodes.set(cpc[0], cpc[1]);
        });
        const env = TypeEnvironment.createInitialEnvForCall(ikey, pci.bodyID, binds, pcodes, cargs, fsig.resultType);

        const mirbody = this.checkBodyStatement(pci.srcFile, env, realbody, fsig.resultType, [], outparaminfo, undefined, undefined);
        return new MIRInvokeBodyDecl(undefined, pci.bodyID, ikey, shortname, pci.attributes, pci.recursive === "yes", sinfo, pci.srcFile, params, 0, resultType.typeID, undefined, undefined, mirbody as MIRBody);
    }

    processConstExpr(gkey: MIRGlobalKey, shortname: string, name: string, srcFile: string, containingType: [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, cexp: ConstantExpressionValue, attribs: string[], binds: Map<string, ResolvedType>, ddecltype: ResolvedType) {
        try {
            const bodyid = this.generateBodyID(cexp.exp.sinfo, srcFile, "constexp");
            const ikeyinfo = MIRKeyGenerator.generateFunctionKeyWNamespace(bodyid /*not ns but sure*/, name, binds, [], "pdefault");

            const idecl = this.processInvokeInfo_ExpressionIsolated(bodyid, srcFile, cexp.exp, ikeyinfo.keyid, ikeyinfo.shortname, cexp.exp.sinfo, attribs, ddecltype, binds);
            this.m_emitter.masm.invokeDecls.set(ikeyinfo.keyid, idecl as MIRInvokeBodyDecl);

            const dtype = this.m_emitter.registerResolvedTypeReference(ddecltype);
            const mirconst = new MIRConstantDecl(containingType !== undefined ? containingType[0].typeID : undefined, gkey, shortname, attribs, cexp.exp.sinfo, srcFile, dtype.typeID, ikeyinfo.keyid);

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
            const invinfo = this.processInvokeInfo(name, fkey, shortname, enclosingdecl, enclosingdecl === undefined ? "namespace" : "static", invoke, binds, pcodes, cargs);

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

    processLambdaFunction(lkey: MIRInvokeKey, lshort: string, invoke: InvokeDecl, sigt: ResolvedFunctionType, bodybinds: Map<string, ResolvedType>, cargs: [string, ResolvedType][], capturedpcodes: [string, { pcode: PCode, captured: string[] }][]) {
        try {
            this.m_file = invoke.srcFile;
            const invinfo = this.processPCodeInfo(lkey, lshort, invoke.sourceLocation, invoke, bodybinds, sigt, cargs, capturedpcodes);

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
            const invinfo = this.processInvokeInfo(name, mkey, shortname, enclosingDecl, "member", mdecl.invoke, binds, pcodes, cargs);

            this.m_emitter.masm.invokeDecls.set(mkey, invinfo as MIRInvokeBodyDecl);

            if(mdecl.invoke.attributes.includes("override") || mdecl.invoke.attributes.includes("virtual")) {
                const tkey = MIRKeyGenerator.generateTypeKey(this.resolveOOTypeFromDecls(enclosingDecl[1], enclosingDecl[2]));
                (this.m_emitter.masm.entityDecls.get(tkey.keyid) as MIRObjectEntityTypeDecl).vcallMap.set(vkey, mkey);
            }
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();
        }
    }

    processVirtualOperator(vkey: MIRVirtualMethodKey, mkey: MIRInvokeKey, shortname: string, name: string, enclosingDecl: [ResolvedType, MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, invoke: InvokeDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
        try {
            this.m_file = invoke.srcFile;
            const vopencl = enclosingDecl !== undefined ? ([enclosingDecl[1], enclosingDecl[2], enclosingDecl[3]] as [MIRType, OOPTypeDecl, Map<string, ResolvedType>]) : undefined;
            const invinfo = this.processInvokeInfo(name, mkey, shortname, vopencl, "operator", invoke, binds, pcodes, cargs);

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

    private resolveREExp(sinfo: SourceInfo, cre: RegexConstClass): RegexComponent {
        this.raiseErrorIf(sinfo, !this.m_assembly.hasNamespace(cre.ns), "Namespace not found");
        const ns = this.m_assembly.getNamespace(cre.ns);

        this.raiseErrorIf(sinfo, !ns.consts.has(cre.ccname), "Const name not found");
        const cc = ns.consts.get(cre.ccname) as NamespaceConstDecl;

        if(cc.value.exp instanceof LiteralRegexExpression) {
            return cc.value.exp.value.re;
        }
        else {
            this.raiseErrorIf(sinfo, !(cc.value.exp instanceof AccessNamespaceConstantExpression), "Only literals and other const references allowed");

            const cca = cc.value.exp as AccessNamespaceConstantExpression;
            return this.resolveREExp(sinfo, new RegexConstClass(cca.ns, cca.name));
        }
    }

    private processRegexComponent(sinfo: SourceInfo, rr: RegexComponent): RegexComponent {
        if((rr instanceof RegexLiteral) || (rr instanceof RegexCharRange) || (rr instanceof RegexDotCharClass)) {
            return rr;
        } 
        else if (rr instanceof RegexConstClass) {
            return this.resolveREExp(sinfo, rr);
        } 
        else if (rr instanceof RegexStarRepeat) {
            return new RegexStarRepeat(this.processRegexComponent(sinfo, rr.repeat));
        } 
        else if (rr instanceof RegexPlusRepeat) {
            return new RegexPlusRepeat(this.processRegexComponent(sinfo, rr.repeat));
        } 
        else if (rr instanceof RegexRangeRepeat) {
            return new RegexRangeRepeat(this.processRegexComponent(sinfo, rr.repeat), rr.min, rr.max);
        } 
        else if (rr instanceof RegexOptional) {
            return new RegexOptional(this.processRegexComponent(sinfo, rr.opt));
        } 
        else if (rr instanceof RegexAlternation) {
            return new RegexAlternation(rr.opts.map((ropt) => this.processRegexComponent(sinfo, ropt)));
        } 
        else {
            assert(rr instanceof RegexSequence);
            return new RegexSequence((rr as RegexSequence).elems.map((relem) => this.processRegexComponent(sinfo, relem)));
        }
    }

    processRegexInfo() {
        const emptysinfo = new SourceInfo(-1, -1, -1, -1);
        this.m_assembly.getAllLiteralRegexs().forEach((lre) => {
            const rr = this.processRegexComponent(emptysinfo, lre.re);
            this.m_emitter.masm.literalRegexs.push(new BSQRegex(lre.restr, rr));
        });

        this.m_assembly.getAllValidators().forEach((vre) => {
            const rr = this.processRegexComponent(emptysinfo, vre[1].re);

            const vkey = MIRKeyGenerator.generateTypeKey(ResolvedType.createSingle(vre[0]));
            this.m_emitter.masm.validatorRegexs.set(vkey.keyid, new BSQRegex(vre[1].restr, rr));
        });
    }
}

export { TypeError, TypeChecker };
