//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo } from "./parser";
import { TypeSignature } from "./type_signature";
import { InvokeDecl } from "./assembly";

class InvokeArgument {
    readonly value: Expression;

    constructor(value: Expression) {
        this.value = value;
    }
}

class NamedArgument extends InvokeArgument {
    readonly name: string;

    constructor(name: string, value: Expression) {
        super(value);
        this.name = name;
    }
}

class PositionalArgument extends InvokeArgument {
    readonly isSpread: boolean;

    constructor(isSpread: boolean, value: Expression) {
        super(value);
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
    LiteralIntegerExpression = "LiteralIntegerExpression",
    LiteralStringExpression = "LiteralStringExpression",
    LiteralTypedStringExpression = "LiteralTypedStringExpression",
    LiteralTypedStringConstructorExpression = "LiteralTypedStringConstructorExpression",

    AccessNamespaceConstantExpression = "AccessNamespaceConstantExpression",
    AccessStaticFieldExpression = " AccessStaticFieldExpression",
    AccessVariableExpression = "AccessVariableExpression",

    ConstructorPrimaryExpression = "ConstructorPrimaryExpression",
    ConstructorPrimaryWithFactoryExpression = "ConstructorPrimaryWithFactoryExpression",
    ConstructorTupleExpression = "ConstructorTupleExpression",
    ConstructorRecordExpression = "ConstructorRecordExpression",
    ConstructorLambdaExpression = "ConstructorLambdaExpression",

    CallNamespaceFunctionExpression = "CallNamespaceFunctionExpression",
    CallStaticFunctionExpression = "CallStaticFunctionExpression",

    PostfixOpExpression = "PostfixOpExpression",

    PrefixOpExpression = "PrefixOpExpression",

    BinOpExpression = "BinOpExpression",
    BinCmpExpression = "BinCmpExpression",
    BinEqExpression = "BinEqExpression",
    BinLogicExpression = "BinLogicExpression",

    NonecheckExpression = "NonecheckExpression",
    CoalesceExpression = "CoalesceExpression",
    SelectExpression = "SelectExpression",

    BlockStatementExpression = "BlockStatementExpression",
    IfExpression = "IfExpression",
    MatchExpression = "MatchExpression",
    //    ProroguedExpression,

    //    LazyExpression
}

abstract class Expression {
    readonly tag: ExpressionTag;
    readonly sinfo: SourceInfo;

    constructor(tag: ExpressionTag, sinfo: SourceInfo) {
        this.tag = tag;
        this.sinfo = sinfo;
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
}

class LiteralBoolExpression extends Expression {
    readonly value: boolean;

    constructor(sinfo: SourceInfo, value: boolean) {
        super(ExpressionTag.LiteralBoolExpression, sinfo);
        this.value = value;
    }
}

class LiteralIntegerExpression extends Expression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string) {
        super(ExpressionTag.LiteralIntegerExpression, sinfo);
        this.value = value;
    }
}

class LiteralStringExpression extends Expression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string) {
        super(ExpressionTag.LiteralStringExpression, sinfo);
        this.value = value;
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
}

class LiteralTypedStringConstructorExpression extends Expression {
    readonly value: string;
    readonly stype: TypeSignature;

    constructor(sinfo: SourceInfo, value: string, stype: TypeSignature) {
        super(ExpressionTag.LiteralTypedStringConstructorExpression, sinfo);
        this.value = value;
        this.stype = stype;
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
    readonly ctype: TypeSignature;
    readonly args: Arguments;

    constructor(sinfo: SourceInfo, ctype: TypeSignature, args: Arguments) {
        super(ExpressionTag.ConstructorPrimaryExpression, sinfo);
        this.ctype = ctype;
        this.args = args;
    }
}

class ConstructorPrimaryWithFactoryExpression extends Expression {
    readonly ctype: TypeSignature;
    readonly factoryName: string;
    readonly terms: TemplateArguments;
    readonly args: Arguments;

    constructor(sinfo: SourceInfo, ctype: TypeSignature, factory: string, terms: TemplateArguments, args: Arguments) {
        super(ExpressionTag.ConstructorPrimaryWithFactoryExpression, sinfo);
        this.ctype = ctype;
        this.factoryName = factory;
        this.terms = terms;
        this.args = args;
    }
}

class ConstructorTupleExpression extends Expression {
    readonly args: Arguments;

    constructor(sinfo: SourceInfo, args: Arguments) {
        super(ExpressionTag.ConstructorTupleExpression, sinfo);
        this.args = args;
    }
}

class ConstructorRecordExpression extends Expression {
    readonly args: Arguments;

    constructor(sinfo: SourceInfo, args: Arguments) {
        super(ExpressionTag.ConstructorRecordExpression, sinfo);
        this.args = args;
    }
}

class ConstructorLambdaExpression extends Expression {
    readonly isAuto: boolean;
    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, isAuto: boolean, invoke: InvokeDecl) {
        super(ExpressionTag.ConstructorLambdaExpression, sinfo);
        this.isAuto = isAuto;
        this.invoke = invoke;
    }
}

class CallNamespaceFunctionExpression extends Expression {
    readonly ns: string;
    readonly name: string;
    readonly terms: TemplateArguments;
    readonly args: Arguments;

    constructor(sinfo: SourceInfo, ns: string, name: string, terms: TemplateArguments, args: Arguments) {
        super(ExpressionTag.CallNamespaceFunctionExpression, sinfo);
        this.ns = ns;
        this.name = name;
        this.terms = terms;
        this.args = args;
    }
}

class CallStaticFunctionExpression extends Expression {
    readonly ttype: TypeSignature;
    readonly name: string;
    readonly terms: TemplateArguments;
    readonly args: Arguments;

    constructor(sinfo: SourceInfo, ttype: TypeSignature, name: string, terms: TemplateArguments, args: Arguments) {
        super(ExpressionTag.CallStaticFunctionExpression, sinfo);
        this.ttype = ttype;
        this.name = name;
        this.terms = terms;
        this.args = args;
    }
}

enum PostfixOpTag {
    PostfixAccessFromIndex = "PostfixAccessFromIndex",
    PostfixProjectFromIndecies = "PostfixProjectFromIndecies",
    PostfixAccessFromName = "PostfixAccessFromName",
    PostfixProjectFromNames = "PostfixProjectFromNames",
    PostfixProjectFromType = "PostfixProjectFromType",

    PostfixModifyWithIndecies = "PostfixModifyWithIndecies",
    PostfixModifyWithNames = "PostfixModifyWithNames",
    PostfixStructuredExtend = "PostfixStructuredExtend",

    //    PostfixDifferenceWithIndecies,
    //    PostfixDifferenceWithNames,
    //    PostfixDifferenceWithType,

    PostfixInvoke = "PostfixInvoke",
    PostfixCallLambda = "PostfixCallLambda"
}

abstract class PostfixOperation {
    readonly sinfo: SourceInfo;

    readonly isElvis: boolean;
    readonly op: PostfixOpTag;

    constructor(sinfo: SourceInfo, isElvis: boolean, op: PostfixOpTag) {
        this.sinfo = sinfo;
        this.isElvis = isElvis;
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

    constructor(sinfo: SourceInfo, isElvis: boolean, index: number) {
        super(sinfo, isElvis, PostfixOpTag.PostfixAccessFromIndex);
        this.index = index;
    }
}

class PostfixProjectFromIndecies extends PostfixOperation {
    readonly indecies: number[];

    constructor(sinfo: SourceInfo, isElvis: boolean, indecies: number[]) {
        super(sinfo, isElvis, PostfixOpTag.PostfixProjectFromIndecies);
        this.indecies = indecies;
    }
}

class PostfixAccessFromName extends PostfixOperation {
    readonly name: string;

    constructor(sinfo: SourceInfo, isElvis: boolean, name: string) {
        super(sinfo, isElvis, PostfixOpTag.PostfixAccessFromName);
        this.name = name;
    }
}

class PostfixProjectFromNames extends PostfixOperation {
    readonly names: string[];

    constructor(sinfo: SourceInfo, isElvis: boolean, names: string[]) {
        super(sinfo, isElvis, PostfixOpTag.PostfixProjectFromNames);
        this.names = names;
    }
}

class PostfixProjectFromType extends PostfixOperation {
    readonly ptype: TypeSignature;

    constructor(sinfo: SourceInfo, isElvis: boolean, ptype: TypeSignature) {
        super(sinfo, isElvis, PostfixOpTag.PostfixProjectFromType);
        this.ptype = ptype;
    }
}

class PostfixModifyWithIndecies extends PostfixOperation {
    readonly updates: [number, Expression][];

    constructor(sinfo: SourceInfo, isElvis: boolean, updates: [number, Expression][]) {
        super(sinfo, isElvis, PostfixOpTag.PostfixModifyWithIndecies);
        this.updates = updates;
    }
}

class PostfixModifyWithNames extends PostfixOperation {
    readonly updates: [string, Expression][];

    constructor(sinfo: SourceInfo, isElvis: boolean, updates: [string, Expression][]) {
        super(sinfo, isElvis, PostfixOpTag.PostfixModifyWithNames);
        this.updates = updates;
    }
}

class PostfixStructuredExtend extends PostfixOperation {
    readonly extension: Expression;

    constructor(sinfo: SourceInfo, isElvis: boolean, extension: Expression) {
        super(sinfo, isElvis, PostfixOpTag.PostfixStructuredExtend);
        this.extension = extension;
    }
}

class PostfixInvoke extends PostfixOperation {
    readonly specificResolve: TypeSignature | undefined;
    readonly name: string;
    readonly terms: TemplateArguments;
    readonly args: Arguments;

    constructor(sinfo: SourceInfo, isElvis: boolean, specificResolve: TypeSignature | undefined, name: string, terms: TemplateArguments, args: Arguments) {
        super(sinfo, isElvis, PostfixOpTag.PostfixInvoke);
        this.specificResolve = specificResolve;
        this.name = name;
        this.terms = terms;
        this.args = args;
    }
}

class PostfixCallLambda extends PostfixOperation {
    readonly args: Arguments;

    constructor(sinfo: SourceInfo, isElvis: boolean, args: Arguments) {
        super(sinfo, isElvis, PostfixOpTag.PostfixCallLambda);
        this.args = args;
    }
}

class PrefixOp extends Expression {
    readonly op: string; //+, -, !
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, op: string, exp: Expression) {
        super(ExpressionTag.PrefixOpExpression, sinfo);
        this.op = op;
        this.exp = exp;
    }
}

class BinOpExpression extends Expression {
    readonly lhs: Expression;
    readonly op: string; //+, -, *, /, %
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, op: string, rhs: Expression) {
        super(ExpressionTag.BinOpExpression, sinfo);
        this.lhs = lhs;
        this.op = op;
        this.rhs = rhs;
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

class NonecheckExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NonecheckExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class CoalesceExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.CoalesceExpression, sinfo);
        this.lhs = lhs;
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
    VariableAssignmentStatement = "VariableAssignmentStatement",
    StructuredVariableAssignmentStatement = "StructuredVariableAssignmentStatement",

    ReturnStatement = "ReturnStatement",
    YieldStatement = "YieldStatement",

    IfElseStatement = "IfElseStatement",
    MatchStatement = "MatchStatement",

    AbortStatement = "AbortStatement",
    AssertStatement = "AssertStatement", //assert(x > 0)
    CheckStatement = "CheckStatement", //check(x > 0)

    DebugStatement = "DebugStatement", //print an arg or if empty attach debugger

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

class VariableAssignmentStatement extends Statement {
    readonly name: string;
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, name: string, exp: Expression) {
        super(StatementTag.VariableAssignmentStatement, sinfo);
        this.name = name;
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
    readonly constValue: Expression; //this should always be a constant evaluateable expression (literal, const, statics only)

    constructor(constValue: Expression) {
        super();
        this.constValue = constValue;
    }
}

class VariableDeclarationStructuredAssignment extends StructuredAssignment {
    readonly isOptional: boolean;
    readonly vname: string;
    readonly isConst: boolean;
    readonly vtype: TypeSignature;

    constructor(isOptional: boolean, vname: string, isConst: boolean, vtype: TypeSignature) {
        super();
        this.isOptional = isOptional;
        this.vname = vname;
        this.isConst = isConst;
        this.vtype = vtype;
    }
}

class VariableAssignmentStructuredAssignment extends StructuredAssignment {
    readonly isOptional: boolean;
    readonly vname: string;

    constructor(isOptional: boolean, vname: string) {
        super();
        this.isOptional = isOptional;
        this.vname = vname;
    }
}

class TupleStructuredAssignment extends StructuredAssignment {
    readonly assigns: StructuredAssignment[];
    readonly isOpen: boolean;

    constructor(assigns: StructuredAssignment[], isOpen: boolean) {
        super();
        this.assigns = assigns;
        this.isOpen = isOpen;
    }
}

class RecordStructuredAssignment extends StructuredAssignment {
    readonly assigns: [string, StructuredAssignment][];
    readonly isOpen: boolean;

    constructor(assigns: [string, StructuredAssignment][], isOpen: boolean) {
        super();
        this.assigns = assigns;
        this.isOpen = isOpen;
    }
}

class StructuredVariableAssignmentStatement extends Statement {
    readonly assign: StructuredAssignment;
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, assign: StructuredAssignment, exp: Expression) {
        super(StatementTag.StructuredVariableAssignmentStatement, sinfo);
        this.assign = assign;
        this.exp = exp;
    }
}

class ReturnStatement extends Statement {
    readonly value: Expression;

    constructor(sinfo: SourceInfo, value: Expression) {
        super(StatementTag.ReturnStatement, sinfo);
        this.value = value;
    }
}

class YieldStatement extends Statement {
    readonly value: Expression;

    constructor(sinfo: SourceInfo, value: Expression) {
        super(StatementTag.YieldStatement, sinfo);
        this.value = value;
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

    constructor(sinfo: SourceInfo, cond: Expression) {
        super(StatementTag.AssertStatement, sinfo);
        this.cond = cond;
    }
}

class CheckStatement extends Statement {
    readonly cond: Expression;

    constructor(sinfo: SourceInfo, cond: Expression) {
        super(StatementTag.CheckStatement, sinfo);
        this.cond = cond;
    }
}

class DebugStatement extends Statement {
    readonly value: Expression | undefined;

    constructor(sinfo: SourceInfo, value: Expression | undefined) {
        super(StatementTag.DebugStatement, sinfo);
        this.value = value;
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
    readonly body: string | BlockStatement | Expression;

    constructor(bodyid: string, file: string, body: string | BlockStatement | Expression) {
        this.id = bodyid;
        this.file = file;
        this.body = body;
    }
}

export {
    InvokeArgument, NamedArgument, PositionalArgument, Arguments, TemplateArguments, CondBranchEntry, IfElse,
    ExpressionTag, Expression, InvalidExpression,
    LiteralNoneExpression, LiteralBoolExpression, LiteralIntegerExpression, LiteralStringExpression, LiteralTypedStringExpression, LiteralTypedStringConstructorExpression,
    AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression,
    ConstructorPrimaryExpression, ConstructorPrimaryWithFactoryExpression, ConstructorTupleExpression, ConstructorRecordExpression, ConstructorLambdaExpression, CallNamespaceFunctionExpression, CallStaticFunctionExpression,
    PostfixOpTag, PostfixOperation, PostfixOp,
    PostfixAccessFromIndex, PostfixProjectFromIndecies, PostfixAccessFromName, PostfixProjectFromNames, PostfixProjectFromType, PostfixModifyWithIndecies, PostfixModifyWithNames, PostfixStructuredExtend,
    PostfixInvoke, PostfixCallLambda,
    PrefixOp, BinOpExpression, BinCmpExpression, BinEqExpression, BinLogicExpression,
    NonecheckExpression, CoalesceExpression, SelectExpression,
    BlockStatementExpression, IfExpression, MatchExpression,
    StatementTag, Statement, InvalidStatement, EmptyStatement,
    VariableDeclarationStatement, VariableAssignmentStatement,
    StructuredAssignment, IgnoreTermStructuredAssignment, ConstValueStructuredAssignment, VariableDeclarationStructuredAssignment, VariableAssignmentStructuredAssignment, TupleStructuredAssignment, RecordStructuredAssignment, StructuredVariableAssignmentStatement,
    ReturnStatement, YieldStatement,
    IfElseStatement, AbortStatement, AssertStatement, CheckStatement, DebugStatement,
    MatchGuard, WildcardMatchGuard, TypeMatchGuard, StructureMatchGuard, MatchEntry, MatchStatement,
    BlockStatement, BodyImplementation
};
