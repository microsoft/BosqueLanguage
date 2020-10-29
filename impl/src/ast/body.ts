//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo } from "./parser";
import { TypeSignature, TemplateTypeSignature } from "./type_signature";
import { InvokeDecl, BuildLevel } from "./assembly";
import { BSQRegex } from "./bsqregex";

class InvokeArgument {
    readonly value: Expression;
    readonly ref: "ref" | "out" | "out?" | undefined;

    constructor(value: Expression, ref: "ref" | "out" | "out?" | undefined) {
        this.value = value;
        this.ref = ref;
    }
}

class NamedArgument extends InvokeArgument {
    readonly name: string;

    constructor(ref: "ref" | "out" | "out?" | undefined, name: string, value: Expression) {
        super(value, ref);
        this.name = name;
    }
}

class PositionalArgument extends InvokeArgument {
    readonly isSpread: boolean;

    constructor(ref: "ref" | "out" | "out?" | undefined, isSpread: boolean, value: Expression) {
        super(value, ref);
        this.isSpread = isSpread;
    }
}

class Arguments {
    readonly argList: InvokeArgument[];

    constructor(args: InvokeArgument[]) {
        this.argList = args;
    }
}

class TemplateArguments {
    readonly targs: TypeSignature[];

    constructor(targs: TypeSignature[]) {
        this.targs = targs;
    }
}

class PragmaArguments {
    readonly recursive: "yes" | "no" | "cond";
    readonly pragmas: [TypeSignature, string][];

    constructor(rec: "yes" | "no" | "cond", pragmas: [TypeSignature, string][]) {
        this.recursive = rec;
        this.pragmas = pragmas;
    }
}

class CondBranchEntry<T> {
    readonly cond: Expression;
    readonly action: T;

    constructor(cond: Expression, action: T) {
        this.cond = cond;
        this.action = action;
    }
}

class IfElse<T> {
    readonly conds: CondBranchEntry<T>[];
    readonly elseAction: T | undefined;

    constructor(conds: CondBranchEntry<T>[], elseAction: T | undefined) {
        this.conds = conds;
        this.elseAction = elseAction;
    }
}

abstract class MatchGuard {
    readonly optionalWhen: Expression | undefined;

    constructor(optionalWhen: Expression | undefined) {
        this.optionalWhen = optionalWhen;
    }
}

class WildcardMatchGuard extends MatchGuard {
    constructor() {
        super(undefined);
    }
}

class TypeMatchGuard extends MatchGuard {
    readonly oftype: TypeSignature;

    constructor(oftype: TypeSignature, optionalWhen: Expression | undefined) {
        super(optionalWhen);
        this.oftype = oftype;
    }
}

class StructureMatchGuard extends MatchGuard {
    readonly match: StructuredAssignment;
    readonly decls: Set<string>;

    constructor(match: StructuredAssignment, decls: Set<string>, optionalWhen: Expression | undefined) {
        super(optionalWhen);
        this.match = match;
        this.decls = decls;
    }
}

class MatchEntry<T> {
    readonly check: MatchGuard;
    readonly action: T;

    constructor(check: MatchGuard, action: T) {
        this.check = check;
        this.action = action;
    }
}

enum ExpressionTag {
    Clear = "[CLEAR]",
    InvalidExpresion = "[INVALID]",

    LiteralNoneExpression = "LiteralNoneExpression",
    LiteralBoolExpression = "LiteralBoolExpression",
    LiteralNumberinoExpression = "LiteralNumberinoExpression",
    LiteralIntegralExpression = "LiteralIntegralExpression",
    LiteralRationalExpression = "LiteralRationalExpression",
    LiteralFloatPointExpression = "LiteralFloatExpression",
    LiteralComplexExpression = "LiteralComplexExpression",
    LiteralStringExpression = "LiteralStringExpression",
    LiteralRegexExpression = "LiteralRegexExpression",
    LiteralParamerterValueExpression = "LiteralParamerterValueExpression",
    LiteralTypedStringExpression = "LiteralTypedStringExpression",

    LiteralTypedNumericConstructorExpression = "LiteralTypedNumericConstructorExpression",
    LiteralTypedComplexConstructorExpression = "LiteralTypedComplexConstructorExpression",
    LiteralTypedStringConstructorExpression = "LiteralTypedStringConstructorExpression",

    AccessNamespaceConstantExpression = "AccessNamespaceConstantExpression",
    AccessStaticFieldExpression = " AccessStaticFieldExpression",
    AccessVariableExpression = "AccessVariableExpression",

    ConstructorPrimaryExpression = "ConstructorPrimaryExpression",
    ConstructorPrimaryWithFactoryExpression = "ConstructorPrimaryWithFactoryExpression",
    ConstructorTupleExpression = "ConstructorTupleExpression",
    ConstructorRecordExpression = "ConstructorRecordExpression",
    ConstructorEphemeralValueList = "ConstructorEphemeralValueList",
    ConstructorPCodeExpression = "ConstructorPCodeExpression",

    PCodeInvokeExpression = "PCodeInvokeExpression",
    SpecialConstructorExpression = "SpecialConstructorExpression",
    CallNamespaceFunctionOrOperatorExpression = "CallNamespaceFunctionOrOperatorExpression",
    CallStaticFunctionOrOperatorExpression = "CallStaticFunctionOrOperatorExpression",

    OfTypeConvertExpression = "OfTypeConvertExpression",

    PostfixOpExpression = "PostfixOpExpression",

    PrefixNotOpExpression = "PrefixNotOpExpression",
    
    BinCmpExpression = "BinCmpExpression",
    BinEqExpression = "BinEqExpression",
    BinLogicExpression = "BinLogicExpression",

    MapEntryConstructorExpression = "MapEntryConstructorExpression",

    NonecheckExpression = "NonecheckExpression",
    CoalesceExpression = "CoalesceExpression",
    SelectExpression = "SelectExpression",

    ExpOrExpression = "ExpOrExpression",

    BlockStatementExpression = "BlockStatementExpression",
    IfExpression = "IfExpression",
    MatchExpression = "MatchExpression",
    //    ProroguedExpression
}

abstract class Expression {
    readonly tag: ExpressionTag;
    readonly sinfo: SourceInfo;

    constructor(tag: ExpressionTag, sinfo: SourceInfo) {
        this.tag = tag;
        this.sinfo = sinfo;
    }

    isCompileTimeInlineValue(): boolean {
        return false;
    }
}

//This just holds an expression (for use in literal types) but not a subtype of Expression so we can distinguish as types
class LiteralExpressionValue {
    readonly exp: Expression;

    constructor(exp: Expression) {
        this.exp = exp;
    }
}


//This just holds an expression (for use where we expect and constant -- or restricted constant expression) but not a subtype of Expression so we can distinguish as types
class ConstantExpressionValue {
    readonly exp: Expression;
    readonly captured: Set<string>;

    constructor(exp: Expression, captured: Set<string>) {
        this.exp = exp;
        this.captured = captured;
    }
}

class InvalidExpression extends Expression {
    constructor(sinfo: SourceInfo) {
        super(ExpressionTag.InvalidExpresion, sinfo);
    }
}

class LiteralNoneExpression extends Expression {
    constructor(sinfo: SourceInfo) {
        super(ExpressionTag.LiteralNoneExpression, sinfo);
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }
}

class LiteralBoolExpression extends Expression {
    readonly value: boolean;

    constructor(sinfo: SourceInfo, value: boolean) {
        super(ExpressionTag.LiteralBoolExpression, sinfo);
        this.value = value;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }
}

class LiteralNumberinoExpression extends Expression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string) {
        super(ExpressionTag.LiteralNumberinoExpression, sinfo);
        this.value = value;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }
}

class LiteralIntegralExpression extends Expression {
    readonly value: string;
    readonly itype: TypeSignature;

    constructor(sinfo: SourceInfo, value: string, itype: TypeSignature) {
        super(ExpressionTag.LiteralIntegralExpression, sinfo);
        this.value = value;
        this.itype = itype;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }
}

class LiteralRationalExpression extends Expression {
    readonly value: string;
    readonly rtype: TypeSignature;

    constructor(sinfo: SourceInfo, value: string, rtype: TypeSignature) {
        super(ExpressionTag.LiteralRationalExpression, sinfo);
        this.value = value;
        this.rtype = rtype;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }
}

class LiteralComplexExpression extends Expression {
    readonly rvalue: string;
    readonly jvalue: string;
    readonly rtype: TypeSignature;

    constructor(sinfo: SourceInfo, rvalue: string, jvalue: string, rtype: TypeSignature) {
        super(ExpressionTag.LiteralComplexExpression, sinfo);
        this.rvalue = rvalue;
        this.jvalue = jvalue;
        this.rtype = rtype;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }
}

class LiteralFloatPointExpression extends Expression {
    readonly value: string;
    readonly fptype: TypeSignature;

    constructor(sinfo: SourceInfo, value: string, fptype: TypeSignature) {
        super(ExpressionTag.LiteralFloatPointExpression, sinfo);
        this.value = value;
        this.fptype = fptype;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }
}

class LiteralStringExpression extends Expression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string) {
        super(ExpressionTag.LiteralStringExpression, sinfo);
        this.value = value;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }
}

class LiteralRegexExpression extends Expression {
    readonly value: BSQRegex;

    constructor(sinfo: SourceInfo, value: BSQRegex) {
        super(ExpressionTag.LiteralRegexExpression, sinfo);
        this.value = value;
    }
}

class LiteralParamerterValueExpression extends Expression {
    readonly ltype: TemplateTypeSignature;

    constructor(sinfo: SourceInfo, ltype: TemplateTypeSignature) {
        super(ExpressionTag.LiteralParamerterValueExpression, sinfo);
        this.ltype = ltype;
    }
}

class LiteralTypedStringExpression extends Expression {
    readonly value: string;
    readonly stype: TypeSignature;

    constructor(sinfo: SourceInfo, value: string, stype: TypeSignature) {
        super(ExpressionTag.LiteralTypedStringExpression, sinfo);
        this.value = value;
        this.stype = stype;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }
}

class LiteralTypedNumericConstructorExpression extends Expression {
    readonly value: string;
    readonly ntype: TypeSignature;
    readonly vtype: TypeSignature;

    constructor(sinfo: SourceInfo, value: string, ntype: TypeSignature, vtype: TypeSignature) {
        super(ExpressionTag.LiteralTypedNumericConstructorExpression, sinfo);
        this.value = value;
        this.ntype = ntype;
        this.vtype = vtype;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }
}

class LiteralTypedComplexConstructorExpression extends Expression {
    readonly rvalue: string;
    readonly jvalue: string;
    readonly ntype: TypeSignature;
    readonly vtype: TypeSignature;

    constructor(sinfo: SourceInfo, rvalue: string, jvalue: string, ntype: TypeSignature, vtype: TypeSignature) {
        super(ExpressionTag.LiteralTypedComplexConstructorExpression, sinfo);
        this.rvalue = rvalue;
        this.jvalue = jvalue;
        this.ntype = ntype;
        this.vtype = vtype;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }
}

class LiteralTypedStringConstructorExpression extends Expression {
    readonly value: string;
    readonly stype: TypeSignature;
    readonly isvalue: boolean;
    
    constructor(sinfo: SourceInfo, isvalue: boolean, value: string, stype: TypeSignature) {
        super(ExpressionTag.LiteralTypedStringConstructorExpression, sinfo);
        this.value = value;
        this.stype = stype;
        this.isvalue = isvalue;
    }
}

class AccessNamespaceConstantExpression extends Expression {
    readonly ns: string;
    readonly name: string;

    constructor(sinfo: SourceInfo, ns: string, name: string) {
        super(ExpressionTag.AccessNamespaceConstantExpression, sinfo);
        this.ns = ns;
        this.name = name;
    }
}

class AccessStaticFieldExpression extends Expression {
    readonly stype: TypeSignature;
    readonly name: string;

    constructor(sinfo: SourceInfo, stype: TypeSignature, name: string) {
        super(ExpressionTag.AccessStaticFieldExpression, sinfo);
        this.stype = stype;
        this.name = name;
    }
}

class AccessVariableExpression extends Expression {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string) {
        super(ExpressionTag.AccessVariableExpression, sinfo);
        this.name = name;
    }
}

class ConstructorPrimaryExpression extends Expression {
    readonly isvalue: boolean;
    readonly ctype: TypeSignature;
    readonly args: Arguments;

    constructor(sinfo: SourceInfo, isvalue: boolean, ctype: TypeSignature, args: Arguments) {
        super(ExpressionTag.ConstructorPrimaryExpression, sinfo);
        this.isvalue = isvalue;
        this.ctype = ctype;
        this.args = args;
    }
}

class ConstructorPrimaryWithFactoryExpression extends Expression {
    readonly isvalue: boolean;
    readonly ctype: TypeSignature;
    readonly factoryName: string;
    readonly terms: TemplateArguments;
    readonly pragmas: PragmaArguments;
    readonly args: Arguments;

    constructor(sinfo: SourceInfo, isvalue: boolean,  ctype: TypeSignature, factory: string, pragmas: PragmaArguments, terms: TemplateArguments, args: Arguments) {
        super(ExpressionTag.ConstructorPrimaryWithFactoryExpression, sinfo);
        this.isvalue = isvalue;
        this.ctype = ctype;
        this.factoryName = factory;
        this.pragmas = pragmas;
        this.terms = terms;
        this.args = args;
    }
}

class ConstructorTupleExpression extends Expression {
    readonly isvalue: boolean;
    readonly args: Arguments;

    constructor(sinfo: SourceInfo, isvalue: boolean, args: Arguments) {
        super(ExpressionTag.ConstructorTupleExpression, sinfo);
        this.isvalue = isvalue;
        this.args = args;
    }
}

class ConstructorRecordExpression extends Expression {
    readonly isvalue: boolean;
    readonly args: Arguments;

    constructor(sinfo: SourceInfo, isvalue: boolean, args: Arguments) {
        super(ExpressionTag.ConstructorRecordExpression, sinfo);
        this.isvalue = isvalue;
        this.args = args;
    }
}

class ConstructorEphemeralValueList extends Expression {
    readonly args: Arguments;

    constructor(sinfo: SourceInfo, args: Arguments) {
        super(ExpressionTag.ConstructorEphemeralValueList, sinfo);
        this.args = args;
    }
}

class ConstructorPCodeExpression extends Expression {
    readonly isAuto: boolean;
    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, isAuto: boolean, invoke: InvokeDecl) {
        super(ExpressionTag.ConstructorPCodeExpression, sinfo);
        this.isAuto = isAuto;
        this.invoke = invoke;
    }
}

class PCodeInvokeExpression extends Expression {
    readonly pcode: string;
    readonly pragmas: PragmaArguments;
    readonly args: Arguments;

    constructor(sinfo: SourceInfo, pcode: string, pragmas: PragmaArguments, args: Arguments) {
        super(ExpressionTag.PCodeInvokeExpression, sinfo);
        this.pcode = pcode;
        this.pragmas = pragmas;
        this.args = args;
    }
}

class SpecialConstructorExpression extends Expression {
    readonly rtype: TypeSignature;
    readonly rop: "ok" | "err";
    readonly arg: Expression;

    constructor(sinfo: SourceInfo, rtype: TypeSignature, rop: "ok" | "err", arg: Expression) {
        super(ExpressionTag.SpecialConstructorExpression, sinfo); 
        this.rtype = rtype;
        this.rop = rop;
        this.arg = arg;
    }
}

class CallNamespaceFunctionOrOperatorExpression extends Expression {
    readonly ns: string;
    readonly name: string;
    readonly pragmas: PragmaArguments;
    readonly terms: TemplateArguments;
    readonly args: Arguments;

    constructor(sinfo: SourceInfo, ns: string, name: string, terms: TemplateArguments, pragmas: PragmaArguments, args: Arguments) {
        super(ExpressionTag.CallStaticFunctionOrOperatorExpression, sinfo);
        this.ns = ns;
        this.name = name;
        this.pragmas = pragmas;
        this.terms = terms;
        this.args = args;
    }
}

class CallStaticFunctionOrOperatorExpression extends Expression {
    readonly ttype: TypeSignature;
    readonly name: string;
    readonly pragmas: PragmaArguments;
    readonly terms: TemplateArguments;
    readonly args: Arguments;

    constructor(sinfo: SourceInfo, ttype: TypeSignature, name: string, terms: TemplateArguments, pragmas: PragmaArguments, args: Arguments) {
        super(ExpressionTag.CallStaticFunctionOrOperatorExpression, sinfo);
        this.ttype = ttype;
        this.name = name;
        this.pragmas = pragmas;
        this.terms = terms;
        this.args = args;
    }
}

class OfTypeConvertExpression extends Expression {
    readonly arg: Expression;
    readonly oftype: TypeSignature;

    constructor(sinfo: SourceInfo, arg: Expression, oftype: TypeSignature) {
        super(ExpressionTag.OfTypeConvertExpression, sinfo);
        this.arg = arg;
        this.oftype = oftype;
    }
}

enum PostfixOpTag {
    PostfixAccessFromIndex = "PostfixAccessFromIndex",
    PostfixProjectFromIndecies = "PostfixProjectFromIndecies",
    PostfixAccessFromName = "PostfixAccessFromName",
    PostfixProjectFromNames = "PostfixProjectFromNames",

    PostfixModifyWithIndecies = "PostfixModifyWithIndecies",
    PostfixModifyWithNames = "PostfixModifyWithNames",

    PostfixIs = "PostfixIs",
    PostfixAs = "PostfixAs",
    PostfixHasIndex = "PostfixHasIndex",
    PostfixHasProperty = "PostfixHasProperty",
    PostfixGetIndexOrNone = "PostfixGetIndexOrNone",
    PostfixGetIndexTry = "PostfixGetIndexTry",
    PostfixGetPropertyOrNone = "PostfixGetPropertyOrNone",
    PostfixGetPropertyTry = "PostfixGetPropertyTry",
    PostfixInvoke = "PostfixInvoke"
}

abstract class PostfixOperation {
    readonly sinfo: SourceInfo;

    readonly isElvis: boolean;
    readonly customCheck: Expression | undefined;
    readonly op: PostfixOpTag;

    constructor(sinfo: SourceInfo, isElvis: boolean, customCheck: Expression | undefined, op: PostfixOpTag) {
        this.sinfo = sinfo;
        this.isElvis = isElvis;
        this.customCheck = customCheck;
        this.op = op;
    }
}

class PostfixOp extends Expression {
    readonly rootExp: Expression;
    readonly ops: PostfixOperation[];

    constructor(sinfo: SourceInfo, root: Expression, ops: PostfixOperation[]) {
        super(ExpressionTag.PostfixOpExpression, sinfo);
        this.rootExp = root;
        this.ops = ops;
    }
}

class PostfixAccessFromIndex extends PostfixOperation {
    readonly index: number;

    constructor(sinfo: SourceInfo, isElvis: boolean, customCheck: Expression | undefined, index: number) {
        super(sinfo, isElvis, customCheck, PostfixOpTag.PostfixAccessFromIndex);
        this.index = index;
    }
}

class PostfixProjectFromIndecies extends PostfixOperation {
    readonly isValue: boolean;
    readonly isEphemeralListResult: boolean;
    readonly indecies: {index: number, reqtype: TypeSignature | undefined}[];

    constructor(sinfo: SourceInfo, isElvis: boolean, customCheck: Expression | undefined, isValue: boolean, isEphemeralListResult: boolean, indecies: {index: number, reqtype: TypeSignature | undefined }[]) {
        super(sinfo, isElvis, customCheck, PostfixOpTag.PostfixProjectFromIndecies);
        this.isValue = isValue;
        this.isEphemeralListResult = isEphemeralListResult
        this.indecies = indecies;
    }
}

class PostfixAccessFromName extends PostfixOperation {
    readonly name: string;

    constructor(sinfo: SourceInfo, isElvis: boolean, customCheck: Expression | undefined, name: string) {
        super(sinfo, isElvis, customCheck, PostfixOpTag.PostfixAccessFromName);
        this.name = name;
    }
}

class PostfixProjectFromNames extends PostfixOperation {
    readonly isValue: boolean;
    readonly isEphemeralListResult: boolean;
    readonly names: { name: string, reqtype: TypeSignature | undefined }[];

    constructor(sinfo: SourceInfo, isElvis: boolean, customCheck: Expression | undefined, isValue: boolean, isEphemeralListResult: boolean, names: { name: string, reqtype: TypeSignature | undefined }[]) {
        super(sinfo, isElvis, customCheck, PostfixOpTag.PostfixProjectFromNames);
        this.isValue = isValue;
        this.isEphemeralListResult = isEphemeralListResult;
        this.names = names;
    }
}

class PostfixModifyWithIndecies extends PostfixOperation {
    readonly isBinder: boolean;
    readonly updates: { index: number, value: Expression }[];

    constructor(sinfo: SourceInfo, isElvis: boolean, customCheck: Expression | undefined, isBinder: boolean, updates: { index: number, value: Expression }[]) {
        super(sinfo, isElvis, customCheck, PostfixOpTag.PostfixModifyWithIndecies);
        this.isBinder = isBinder;
        this.updates = updates;
    }
}

class PostfixModifyWithNames extends PostfixOperation {
    readonly isBinder: boolean;
    readonly updates: { name: string, value: Expression }[];

    constructor(sinfo: SourceInfo, isElvis: boolean, customCheck: Expression | undefined, isBinder: boolean, updates: { name: string, value: Expression }[]) {
        super(sinfo, isElvis, customCheck, PostfixOpTag.PostfixModifyWithNames);
        this.isBinder = isBinder;
        this.updates = updates;
    }
}

class PostfixIs extends PostfixOperation {
    readonly istype: TypeSignature;

    constructor(sinfo: SourceInfo, isElvis: boolean, customCheck: Expression | undefined, istype: TypeSignature) {
        super(sinfo, isElvis, customCheck, PostfixOpTag.PostfixIs);
        this.istype = istype;
    }
}

class PostfixAs extends PostfixOperation {
    readonly astype: TypeSignature;

    constructor(sinfo: SourceInfo, isElvis: boolean, customCheck: Expression | undefined, astype: TypeSignature) {
        super(sinfo, isElvis, customCheck, PostfixOpTag.PostfixAs);
        this.astype = astype;
    }
}

class PostfixHasIndex extends PostfixOperation {
    readonly idx: number;

    constructor(sinfo: SourceInfo, isElvis: boolean, customCheck: Expression | undefined, idx: number) {
        super(sinfo, isElvis, customCheck, PostfixOpTag.PostfixHasIndex);
        this.idx = idx;
    }
}

class PostfixHasProperty extends PostfixOperation {
    readonly pname: string;

    constructor(sinfo: SourceInfo, isElvis: boolean, customCheck: Expression | undefined, pname: string) {
        super(sinfo, isElvis, customCheck, PostfixOpTag.PostfixHasProperty);
        this.pname = pname;
    }
}

class PostfixGetIndexOrNone extends PostfixOperation {
    readonly idx: number;

    constructor(sinfo: SourceInfo, isElvis: boolean, customCheck: Expression | undefined, idx: number) {
        super(sinfo, isElvis, customCheck, PostfixOpTag.PostfixGetIndexOrNone);
        this.idx = idx;
    }
}

class PostfixGetIndexTry extends PostfixOperation {
    readonly idx: number;
    readonly vname: string;

    constructor(sinfo: SourceInfo, isElvis: boolean, customCheck: Expression | undefined, idx: number, vname: string) {
        super(sinfo, isElvis, customCheck, PostfixOpTag.PostfixGetIndexTry);
        this.idx = idx;
        this.vname = vname;
    }
}

class PostfixGetPropertyOrNone extends PostfixOperation {
    readonly pname: string;

    constructor(sinfo: SourceInfo, isElvis: boolean, customCheck: Expression | undefined, pname: string) {
        super(sinfo, isElvis, customCheck, PostfixOpTag.PostfixGetPropertyOrNone);
        this.pname = pname;
    }
}

class PostfixGetPropertyTry extends PostfixOperation {
    readonly pname: string;
    readonly vname: string;

    constructor(sinfo: SourceInfo, isElvis: boolean, customCheck: Expression | undefined, pname: string, vname: string) {
        super(sinfo, isElvis, customCheck, PostfixOpTag.PostfixGetPropertyTry);
        this.pname = pname;
        this.vname = vname;
    }
}

class PostfixInvoke extends PostfixOperation {
    readonly isBinder: boolean;
    readonly specificResolve: TypeSignature | undefined;
    readonly name: string;
    readonly pragmas: PragmaArguments;
    readonly terms: TemplateArguments;
    readonly args: Arguments;

    constructor(sinfo: SourceInfo, isElvis: boolean, customCheck: Expression | undefined, isBinder: boolean, specificResolve: TypeSignature | undefined, name: string, terms: TemplateArguments, pragmas: PragmaArguments, args: Arguments) {
        super(sinfo, isElvis, customCheck, PostfixOpTag.PostfixInvoke);
        this.isBinder = isBinder;
        this.specificResolve = specificResolve;
        this.name = name;
        this.pragmas = pragmas;
        this.terms = terms;
        this.args = args;
    }
}

class PrefixNotOp extends Expression {
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, exp: Expression) {
        super(ExpressionTag.PrefixNotOpExpression, sinfo);
        this.exp = exp;
    }
}

class BinEqExpression extends Expression {
    readonly lhs: Expression;
    readonly op: string; //==, !=
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, op: string, rhs: Expression) {
        super(ExpressionTag.BinEqExpression, sinfo);
        this.lhs = lhs;
        this.op = op;
        this.rhs = rhs;
    }
}

class BinCmpExpression extends Expression {
    readonly lhs: Expression;
    readonly op: string; //<, >, <=, >=
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, op: string, rhs: Expression) {
        super(ExpressionTag.BinCmpExpression, sinfo);
        this.lhs = lhs;
        this.op = op;
        this.rhs = rhs;
    }
}

class BinLogicExpression extends Expression {
    readonly lhs: Expression;
    readonly op: string; //==>, &&, ||
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, op: string, rhs: Expression) {
        super(ExpressionTag.BinLogicExpression, sinfo);
        this.lhs = lhs;
        this.op = op;
        this.rhs = rhs;
    }
}

class MapEntryConstructorExpression extends Expression {
    readonly kexp: Expression;
    readonly vexp: Expression;

    constructor(sinfo: SourceInfo, kexp: Expression, vexp: Expression) {
        super(ExpressionTag.MapEntryConstructorExpression, sinfo);
        this.kexp = kexp;
        this.vexp = vexp;
    }
}

class NonecheckExpression extends Expression {
    readonly lhs: Expression;
    readonly customCheck: Expression | undefined;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, customCheck: Expression | undefined, rhs: Expression) {
        super(ExpressionTag.NonecheckExpression, sinfo);
        this.lhs = lhs;
        this.customCheck = customCheck;
        this.rhs = rhs;
    }
}

class CoalesceExpression extends Expression {
    readonly lhs: Expression;
    readonly customCheck: Expression | undefined;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, customCheck: Expression | undefined, rhs: Expression) {
        super(ExpressionTag.CoalesceExpression, sinfo);
        this.lhs = lhs;
        this.customCheck = customCheck;
        this.rhs = rhs;
    }
}

class SelectExpression extends Expression {
    readonly test: Expression;
    readonly option1: Expression;
    readonly option2: Expression;

    constructor(sinfo: SourceInfo, test: Expression, option1: Expression, option2: Expression) {
        super(ExpressionTag.SelectExpression, sinfo);
        this.test = test;
        this.option1 = option1;
        this.option2 = option2;
    }
}

class ExpOrExpression extends Expression {
    readonly exp: Expression;
    readonly action: "return" | "yield";
    readonly result: Expression[] | undefined;
    readonly cond: Expression | "none" | "err";

    constructor(sinfo: SourceInfo, exp: Expression, action: "return" | "yield", result: Expression[] | undefined, cond: Expression | "none" | "err") {
        super(ExpressionTag.ExpOrExpression, sinfo);
        this.exp = exp;
        this.action = action;
        this.result = result;
        this.cond = cond;
    }
}

class BlockStatementExpression extends Expression {
    readonly ops: Statement[];

    constructor(sinfo: SourceInfo, ops: Statement[]) {
        super(ExpressionTag.BlockStatementExpression, sinfo);
        this.ops = ops;
    }
}

class IfExpression extends Expression {
    readonly flow: IfElse<Expression>;

    constructor(sinfo: SourceInfo, flow: IfElse<Expression>) {
        super(ExpressionTag.IfExpression, sinfo);
        this.flow = flow;
    }
}

class MatchExpression extends Expression {
    readonly sval: Expression;
    readonly flow: MatchEntry<Expression>[];

    constructor(sinfo: SourceInfo, sval: Expression, flow: MatchEntry<Expression>[]) {
        super(ExpressionTag.MatchExpression, sinfo);
        this.sval = sval;
        this.flow = flow;
    }
}

enum StatementTag {
    Clear = "[CLEAR]",
    InvalidStatement = "[INVALID]",

    EmptyStatement = "EmptyStatement",

    VariableDeclarationStatement = "VariableDeclarationStatement",
    VariablePackDeclarationStatement = "VariablePackDeclarationStatement",
    VariableAssignmentStatement = "VariableAssignmentStatement",
    VariablePackAssignmentStatement = "VariablePackAssignmentStatement",
    StructuredVariableAssignmentStatement = "StructuredVariableAssignmentStatement",

    ReturnStatement = "ReturnStatement",
    YieldStatement = "YieldStatement",

    IfElseStatement = "IfElseStatement",
    MatchStatement = "MatchStatement",

    AbortStatement = "AbortStatement",
    AssertStatement = "AssertStatement", //assert(x > 0)
    CheckStatement = "CheckStatement", //check(x > 0)
    ValidateStatement = "ValidateStatement", //validate exp or err -> if (!exp) return Result<INVOKE_RESULT>@error(err);

    DebugStatement = "DebugStatement", //print an arg or if empty attach debugger
    NakedCallStatement = "NakedCallStatement",

    BlockStatement = "BlockStatement"
}

abstract class Statement {
    readonly tag: StatementTag;
    readonly sinfo: SourceInfo;

    constructor(tag: StatementTag, sinfo: SourceInfo) {
        this.tag = tag;
        this.sinfo = sinfo;
    }
}

class InvalidStatement extends Statement {
    constructor(sinfo: SourceInfo) {
        super(StatementTag.InvalidStatement, sinfo);
    }
}

class EmptyStatement extends Statement {
    constructor(sinfo: SourceInfo) {
        super(StatementTag.EmptyStatement, sinfo);
    }
}

class VariableDeclarationStatement extends Statement {
    readonly name: string;
    readonly isConst: boolean;
    readonly vtype: TypeSignature; //may be auto
    readonly exp: Expression | undefined; //may be undef

    constructor(sinfo: SourceInfo, name: string, isConst: boolean, vtype: TypeSignature, exp: Expression | undefined) {
        super(StatementTag.VariableDeclarationStatement, sinfo);
        this.name = name;
        this.isConst = isConst;
        this.vtype = vtype;
        this.exp = exp;
    }
}

class VariablePackDeclarationStatement extends Statement {
    readonly isConst: boolean;
    readonly vars: {name: string, vtype: TypeSignature /*may be auto*/}[];
    readonly exp: Expression[] | undefined; //may be undef

    constructor(sinfo: SourceInfo, isConst: boolean, vars: {name: string, vtype: TypeSignature /*may be auto*/}[], exp: Expression[] | undefined) {
        super(StatementTag.VariablePackDeclarationStatement, sinfo);
        this.isConst = isConst;
        this.vars = vars;
        this.exp = exp;
    }
}

class VariableAssignmentStatement extends Statement {
    readonly name: string;
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, name: string, exp: Expression) {
        super(StatementTag.VariableAssignmentStatement, sinfo);
        this.name = name;
        this.exp = exp;
    }
}

class VariablePackAssignmentStatement extends Statement {
    readonly names: string[];
    readonly exp: Expression[];

    constructor(sinfo: SourceInfo, names: string[], exp: Expression[]) {
        super(StatementTag.VariablePackAssignmentStatement, sinfo);
        this.names = names;
        this.exp = exp;
    }
}

class StructuredAssignment {
}

class IgnoreTermStructuredAssignment extends StructuredAssignment {
    readonly isOptional: boolean;
    readonly termType: TypeSignature;

    constructor(isOptional: boolean, termType: TypeSignature) {
        super();
        this.isOptional = isOptional;
        this.termType = termType;
    }
}

class ConstValueStructuredAssignment extends StructuredAssignment {
    readonly constValue: ConstantExpressionValue;

    constructor(constValue: ConstantExpressionValue) {
        super();
        this.constValue = constValue;
    }
}

class VariableDeclarationStructuredAssignment extends StructuredAssignment {
    readonly vname: string;
    readonly vtype: TypeSignature;

    constructor(vname: string, vtype: TypeSignature) {
        super();
        this.vname = vname;
        this.vtype = vtype;
    }
}

class VariableAssignmentStructuredAssignment extends StructuredAssignment {
    readonly vname: string;

    constructor(vname: string) {
        super();
        this.vname = vname;
    }
}

class TupleStructuredAssignment extends StructuredAssignment {
    readonly isvalue: boolean;
    readonly assigns: StructuredAssignment[];

    constructor(isvalue: boolean, assigns: StructuredAssignment[]) {
        super();
        this.isvalue = isvalue;
        this.assigns = assigns;
    }
}

class RecordStructuredAssignment extends StructuredAssignment {
    readonly isvalue: boolean;
    readonly assigns: [string, StructuredAssignment][];

    constructor(isvalue: boolean, assigns: [string, StructuredAssignment][]) {
        super();
        this.isvalue = isvalue;
        this.assigns = assigns;
    }
}

class NominalStructuredAssignment extends StructuredAssignment {
    readonly isvalue: boolean;
    readonly atype: TypeSignature;
    readonly assigns: [string, StructuredAssignment][];

    constructor(isvalue: boolean, atype: TypeSignature, assigns: [string, StructuredAssignment][]) {
        super();
        this.isvalue = isvalue;
        this.atype = atype;
        this.assigns = assigns;
    }
}

class ValueListStructuredAssignment extends StructuredAssignment {
    readonly assigns: StructuredAssignment[];

    constructor(assigns: StructuredAssignment[]) {
        super();
        this.assigns = assigns;
    }
}

class StructuredVariableAssignmentStatement extends Statement {
    readonly isConst: boolean;
    readonly assign: StructuredAssignment;
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, isConst: boolean, assign: StructuredAssignment, exp: Expression) {
        super(StatementTag.StructuredVariableAssignmentStatement, sinfo);
        this.isConst = isConst;
        this.assign = assign;
        this.exp = exp;
    }
}

class ReturnStatement extends Statement {
    readonly values: Expression[];

    constructor(sinfo: SourceInfo, values: Expression[]) {
        super(StatementTag.ReturnStatement, sinfo);
        this.values = values;
    }
}

class YieldStatement extends Statement {
    readonly values: Expression[];

    constructor(sinfo: SourceInfo, values: Expression[]) {
        super(StatementTag.YieldStatement, sinfo);
        this.values = values;
    }
}

class IfElseStatement extends Statement {
    readonly flow: IfElse<BlockStatement>;

    constructor(sinfo: SourceInfo, flow: IfElse<BlockStatement>) {
        super(StatementTag.IfElseStatement, sinfo);
        this.flow = flow;
    }
}

class MatchStatement extends Statement {
    readonly sval: Expression;
    readonly flow: MatchEntry<BlockStatement>[];

    constructor(sinfo: SourceInfo, sval: Expression, flow: MatchEntry<BlockStatement>[]) {
        super(StatementTag.MatchStatement, sinfo);
        this.sval = sval;
        this.flow = flow;
    }
}

class AbortStatement extends Statement {
    constructor(sinfo: SourceInfo) {
        super(StatementTag.AbortStatement, sinfo);
    }
}

class AssertStatement extends Statement {
    readonly cond: Expression;
    readonly level: BuildLevel;

    constructor(sinfo: SourceInfo, cond: Expression, level: BuildLevel) {
        super(StatementTag.AssertStatement, sinfo);
        this.cond = cond;
        this.level = level;
    }
}

class CheckStatement extends Statement {
    readonly cond: Expression;

    constructor(sinfo: SourceInfo, cond: Expression) {
        super(StatementTag.CheckStatement, sinfo);
        this.cond = cond;
    }
}

class ValidateStatement extends Statement {
    readonly cond: Expression;
    readonly err: Expression;

    constructor(sinfo: SourceInfo, cond: Expression, err: Expression) {
        super(StatementTag.ValidateStatement, sinfo);
        this.cond = cond;
        this.err = err;
    }
}

class DebugStatement extends Statement {
    readonly value: Expression | undefined;

    constructor(sinfo: SourceInfo, value: Expression | undefined) {
        super(StatementTag.DebugStatement, sinfo);
        this.value = value;
    }
}

class NakedCallStatement extends Statement {
    readonly call: CallNamespaceFunctionOrOperatorExpression | CallStaticFunctionOrOperatorExpression;

    constructor(sinfo: SourceInfo, call: CallNamespaceFunctionOrOperatorExpression | CallStaticFunctionOrOperatorExpression) {
        super(StatementTag.NakedCallStatement, sinfo);
        this.call = call;
    }
}

class BlockStatement extends Statement {
    readonly statements: Statement[];

    constructor(sinfo: SourceInfo, statements: Statement[]) {
        super(StatementTag.BlockStatement, sinfo);
        this.statements = statements;
    }
}

class BodyImplementation {
    readonly id: string;
    readonly file: string;
    readonly body: string | BlockStatement | Expression | undefined;

    constructor(bodyid: string, file: string, body: string | BlockStatement | Expression | undefined) {
        this.id = bodyid;
        this.file = file;
        this.body = body;
    }
}

export {
    InvokeArgument, NamedArgument, PositionalArgument, Arguments, TemplateArguments, PragmaArguments, CondBranchEntry, IfElse,
    ExpressionTag, Expression, LiteralExpressionValue, ConstantExpressionValue, InvalidExpression,
    LiteralNoneExpression, LiteralBoolExpression, 
    LiteralNumberinoExpression, LiteralIntegralExpression, LiteralFloatPointExpression, LiteralRationalExpression, LiteralComplexExpression,
    LiteralStringExpression, LiteralRegexExpression, LiteralParamerterValueExpression, LiteralTypedStringExpression, 
    LiteralTypedNumericConstructorExpression, LiteralTypedComplexConstructorExpression, LiteralTypedStringConstructorExpression,
    AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression,
    ConstructorPrimaryExpression, ConstructorPrimaryWithFactoryExpression, ConstructorTupleExpression, ConstructorRecordExpression, ConstructorEphemeralValueList, 
    ConstructorPCodeExpression, SpecialConstructorExpression,
    CallNamespaceFunctionOrOperatorExpression, CallStaticFunctionOrOperatorExpression,
    OfTypeConvertExpression,
    PostfixOpTag, PostfixOperation, PostfixOp,
    PostfixAccessFromIndex, PostfixProjectFromIndecies, PostfixAccessFromName, PostfixProjectFromNames, PostfixModifyWithIndecies, PostfixModifyWithNames,
    PostfixIs, PostfixAs, PostfixHasIndex, PostfixHasProperty, PostfixGetIndexOrNone, PostfixGetIndexTry, PostfixGetPropertyOrNone, PostfixGetPropertyTry,
    PostfixInvoke, PCodeInvokeExpression,
    PrefixNotOp, 
    BinCmpExpression, BinEqExpression, BinLogicExpression,
    MapEntryConstructorExpression,
    NonecheckExpression, CoalesceExpression, SelectExpression, ExpOrExpression,
    BlockStatementExpression, IfExpression, MatchExpression,
    StatementTag, Statement, InvalidStatement, EmptyStatement,
    VariableDeclarationStatement, VariablePackDeclarationStatement, VariableAssignmentStatement, VariablePackAssignmentStatement,
    StructuredAssignment, IgnoreTermStructuredAssignment, ConstValueStructuredAssignment, VariableDeclarationStructuredAssignment, VariableAssignmentStructuredAssignment, StructuredVariableAssignmentStatement, 
    TupleStructuredAssignment, RecordStructuredAssignment, NominalStructuredAssignment, ValueListStructuredAssignment,
    ReturnStatement, YieldStatement,
    IfElseStatement, AbortStatement, AssertStatement, CheckStatement, ValidateStatement, DebugStatement, NakedCallStatement,
    MatchGuard, WildcardMatchGuard, TypeMatchGuard, StructureMatchGuard, MatchEntry, MatchStatement,
    BlockStatement, BodyImplementation
};
