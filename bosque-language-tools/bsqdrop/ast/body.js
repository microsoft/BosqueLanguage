"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
class InvokeArgument {
    constructor(value, isRef) {
        this.value = value;
        this.isRef = isRef;
    }
}
exports.InvokeArgument = InvokeArgument;
class NamedArgument extends InvokeArgument {
    constructor(isRef, name, value) {
        super(value, isRef);
        this.name = name;
    }
}
exports.NamedArgument = NamedArgument;
class PositionalArgument extends InvokeArgument {
    constructor(isRef, isSpread, value) {
        super(value, isRef);
        this.isSpread = isSpread;
    }
}
exports.PositionalArgument = PositionalArgument;
class MapArgument extends InvokeArgument {
    constructor(key, value) {
        super(value, false);
        this.key = key;
    }
}
exports.MapArgument = MapArgument;
class Arguments {
    constructor(args) {
        this.argList = args;
    }
}
exports.Arguments = Arguments;
class TemplateArguments {
    constructor(targs) {
        this.targs = targs;
    }
}
exports.TemplateArguments = TemplateArguments;
class PragmaArguments {
    constructor(rec, pragmas) {
        this.recursive = rec;
        this.pragmas = pragmas;
    }
}
exports.PragmaArguments = PragmaArguments;
class CondBranchEntry {
    constructor(cond, action) {
        this.cond = cond;
        this.action = action;
    }
}
exports.CondBranchEntry = CondBranchEntry;
class IfElse {
    constructor(conds, elseAction) {
        this.conds = conds;
        this.elseAction = elseAction;
    }
}
exports.IfElse = IfElse;
class MatchGuard {
    constructor(optionalWhen) {
        this.optionalWhen = optionalWhen;
    }
}
exports.MatchGuard = MatchGuard;
class WildcardMatchGuard extends MatchGuard {
    constructor() {
        super(undefined);
    }
}
exports.WildcardMatchGuard = WildcardMatchGuard;
class TypeMatchGuard extends MatchGuard {
    constructor(oftype, optionalWhen) {
        super(optionalWhen);
        this.oftype = oftype;
    }
}
exports.TypeMatchGuard = TypeMatchGuard;
class StructureMatchGuard extends MatchGuard {
    constructor(match, decls, optionalWhen) {
        super(optionalWhen);
        this.match = match;
        this.decls = decls;
    }
}
exports.StructureMatchGuard = StructureMatchGuard;
class MatchEntry {
    constructor(check, action) {
        this.check = check;
        this.action = action;
    }
}
exports.MatchEntry = MatchEntry;
var ExpressionTag;
(function (ExpressionTag) {
    ExpressionTag["Clear"] = "[CLEAR]";
    ExpressionTag["InvalidExpresion"] = "[INVALID]";
    ExpressionTag["LiteralNoneExpression"] = "LiteralNoneExpression";
    ExpressionTag["LiteralBoolExpression"] = "LiteralBoolExpression";
    ExpressionTag["LiteralIntegerExpression"] = "LiteralIntegerExpression";
    ExpressionTag["LiteralStringExpression"] = "LiteralStringExpression";
    ExpressionTag["LiteralRegexExpression"] = "LiteralRegexExpression";
    ExpressionTag["LiteralTypedStringExpression"] = "LiteralTypedStringExpression";
    ExpressionTag["LiteralTypedStringConstructorExpression"] = "LiteralTypedStringConstructorExpression";
    ExpressionTag["AccessNamespaceConstantExpression"] = "AccessNamespaceConstantExpression";
    ExpressionTag["AccessStaticFieldExpression"] = " AccessStaticFieldExpression";
    ExpressionTag["AccessVariableExpression"] = "AccessVariableExpression";
    ExpressionTag["ConstructorPrimaryExpression"] = "ConstructorPrimaryExpression";
    ExpressionTag["ConstructorPrimaryWithFactoryExpression"] = "ConstructorPrimaryWithFactoryExpression";
    ExpressionTag["ConstructorTupleExpression"] = "ConstructorTupleExpression";
    ExpressionTag["ConstructorRecordExpression"] = "ConstructorRecordExpression";
    ExpressionTag["ConstructorEphemeralValueList"] = "ConstructorEphemeralValueList";
    ExpressionTag["ConstructorPCodeExpression"] = "ConstructorPCodeExpression";
    ExpressionTag["PCodeInvokeExpression"] = "PCodeInvokeExpression";
    ExpressionTag["CallNamespaceFunctionExpression"] = "CallNamespaceFunctionExpression";
    ExpressionTag["CallStaticFunctionExpression"] = "CallStaticFunctionExpression";
    ExpressionTag["PostfixOpExpression"] = "PostfixOpExpression";
    ExpressionTag["PrefixOpExpression"] = "PrefixOpExpression";
    ExpressionTag["BinOpExpression"] = "BinOpExpression";
    ExpressionTag["BinCmpExpression"] = "BinCmpExpression";
    ExpressionTag["BinEqExpression"] = "BinEqExpression";
    ExpressionTag["BinLogicExpression"] = "BinLogicExpression";
    ExpressionTag["NonecheckExpression"] = "NonecheckExpression";
    ExpressionTag["CoalesceExpression"] = "CoalesceExpression";
    ExpressionTag["SelectExpression"] = "SelectExpression";
    ExpressionTag["ExpOrExpression"] = "ExpOrExpression";
    ExpressionTag["BlockStatementExpression"] = "BlockStatementExpression";
    ExpressionTag["IfExpression"] = "IfExpression";
    ExpressionTag["MatchExpression"] = "MatchExpression";
    //    ProroguedExpression
})(ExpressionTag || (ExpressionTag = {}));
exports.ExpressionTag = ExpressionTag;
class Expression {
    constructor(tag, sinfo) {
        this.tag = tag;
        this.sinfo = sinfo;
    }
}
exports.Expression = Expression;
class InvalidExpression extends Expression {
    constructor(sinfo) {
        super(ExpressionTag.InvalidExpresion, sinfo);
    }
}
exports.InvalidExpression = InvalidExpression;
class LiteralNoneExpression extends Expression {
    constructor(sinfo) {
        super(ExpressionTag.LiteralNoneExpression, sinfo);
    }
}
exports.LiteralNoneExpression = LiteralNoneExpression;
class LiteralBoolExpression extends Expression {
    constructor(sinfo, value) {
        super(ExpressionTag.LiteralBoolExpression, sinfo);
        this.value = value;
    }
}
exports.LiteralBoolExpression = LiteralBoolExpression;
class LiteralIntegerExpression extends Expression {
    constructor(sinfo, value) {
        super(ExpressionTag.LiteralIntegerExpression, sinfo);
        this.value = value;
    }
}
exports.LiteralIntegerExpression = LiteralIntegerExpression;
class LiteralStringExpression extends Expression {
    constructor(sinfo, value) {
        super(ExpressionTag.LiteralStringExpression, sinfo);
        this.value = value;
    }
}
exports.LiteralStringExpression = LiteralStringExpression;
class LiteralRegexExpression extends Expression {
    constructor(sinfo, value) {
        super(ExpressionTag.LiteralRegexExpression, sinfo);
        this.value = value;
    }
}
exports.LiteralRegexExpression = LiteralRegexExpression;
class LiteralTypedStringExpression extends Expression {
    constructor(sinfo, value, stype) {
        super(ExpressionTag.LiteralTypedStringExpression, sinfo);
        this.value = value;
        this.stype = stype;
    }
}
exports.LiteralTypedStringExpression = LiteralTypedStringExpression;
class LiteralTypedStringConstructorExpression extends Expression {
    constructor(sinfo, value, asValue, stype) {
        super(ExpressionTag.LiteralTypedStringConstructorExpression, sinfo);
        this.value = value;
        this.asValue = asValue;
        this.stype = stype;
    }
}
exports.LiteralTypedStringConstructorExpression = LiteralTypedStringConstructorExpression;
class AccessNamespaceConstantExpression extends Expression {
    constructor(sinfo, ns, name) {
        super(ExpressionTag.AccessNamespaceConstantExpression, sinfo);
        this.ns = ns;
        this.name = name;
    }
}
exports.AccessNamespaceConstantExpression = AccessNamespaceConstantExpression;
class AccessStaticFieldExpression extends Expression {
    constructor(sinfo, stype, name) {
        super(ExpressionTag.AccessStaticFieldExpression, sinfo);
        this.stype = stype;
        this.name = name;
    }
}
exports.AccessStaticFieldExpression = AccessStaticFieldExpression;
class AccessVariableExpression extends Expression {
    constructor(sinfo, name) {
        super(ExpressionTag.AccessVariableExpression, sinfo);
        this.name = name;
    }
}
exports.AccessVariableExpression = AccessVariableExpression;
class ConstructorPrimaryExpression extends Expression {
    constructor(sinfo, ctype, asvalue, args) {
        super(ExpressionTag.ConstructorPrimaryExpression, sinfo);
        this.ctype = ctype;
        this.asValue = asvalue;
        this.args = args;
    }
}
exports.ConstructorPrimaryExpression = ConstructorPrimaryExpression;
class ConstructorPrimaryWithFactoryExpression extends Expression {
    constructor(sinfo, ctype, asvalue, factory, pragmas, terms, args) {
        super(ExpressionTag.ConstructorPrimaryWithFactoryExpression, sinfo);
        this.ctype = ctype;
        this.asValue = asvalue;
        this.factoryName = factory;
        this.pragmas = pragmas;
        this.terms = terms;
        this.args = args;
    }
}
exports.ConstructorPrimaryWithFactoryExpression = ConstructorPrimaryWithFactoryExpression;
class ConstructorTupleExpression extends Expression {
    constructor(sinfo, args) {
        super(ExpressionTag.ConstructorTupleExpression, sinfo);
        this.args = args;
    }
}
exports.ConstructorTupleExpression = ConstructorTupleExpression;
class ConstructorRecordExpression extends Expression {
    constructor(sinfo, args) {
        super(ExpressionTag.ConstructorRecordExpression, sinfo);
        this.args = args;
    }
}
exports.ConstructorRecordExpression = ConstructorRecordExpression;
class ConstructorEphemeralValueList extends Expression {
    constructor(sinfo, args) {
        super(ExpressionTag.ConstructorEphemeralValueList, sinfo);
        this.args = args;
    }
}
exports.ConstructorEphemeralValueList = ConstructorEphemeralValueList;
class ConstructorPCodeExpression extends Expression {
    constructor(sinfo, isAuto, invoke) {
        super(ExpressionTag.ConstructorPCodeExpression, sinfo);
        this.isAuto = isAuto;
        this.invoke = invoke;
    }
}
exports.ConstructorPCodeExpression = ConstructorPCodeExpression;
class PCodeInvokeExpression extends Expression {
    constructor(sinfo, pcode, pragmas, args) {
        super(ExpressionTag.PCodeInvokeExpression, sinfo);
        this.pcode = pcode;
        this.pragmas = pragmas;
        this.args = args;
    }
}
exports.PCodeInvokeExpression = PCodeInvokeExpression;
class CallNamespaceFunctionExpression extends Expression {
    constructor(sinfo, ns, name, terms, pragmas, args) {
        super(ExpressionTag.CallNamespaceFunctionExpression, sinfo);
        this.ns = ns;
        this.name = name;
        this.pragmas = pragmas;
        this.terms = terms;
        this.args = args;
    }
}
exports.CallNamespaceFunctionExpression = CallNamespaceFunctionExpression;
class CallStaticFunctionExpression extends Expression {
    constructor(sinfo, ttype, name, terms, pragmas, args) {
        super(ExpressionTag.CallStaticFunctionExpression, sinfo);
        this.ttype = ttype;
        this.name = name;
        this.pragmas = pragmas;
        this.terms = terms;
        this.args = args;
    }
}
exports.CallStaticFunctionExpression = CallStaticFunctionExpression;
var PostfixOpTag;
(function (PostfixOpTag) {
    PostfixOpTag["PostfixAccessFromIndex"] = "PostfixAccessFromIndex";
    PostfixOpTag["PostfixProjectFromIndecies"] = "PostfixProjectFromIndecies";
    PostfixOpTag["PostfixAccessFromName"] = "PostfixAccessFromName";
    PostfixOpTag["PostfixProjectFromNames"] = "PostfixProjectFromNames";
    PostfixOpTag["PostfixProjectFromType"] = "PostfixProjectFromType";
    PostfixOpTag["PostfixModifyWithIndecies"] = "PostfixModifyWithIndecies";
    PostfixOpTag["PostfixModifyWithNames"] = "PostfixModifyWithNames";
    PostfixOpTag["PostfixStructuredExtend"] = "PostfixStructuredExtend";
    //    PostfixDifferenceWithIndecies,
    //    PostfixDifferenceWithNames,
    //    PostfixDifferenceWithType,
    PostfixOpTag["PostfixInvoke"] = "PostfixInvoke";
})(PostfixOpTag || (PostfixOpTag = {}));
exports.PostfixOpTag = PostfixOpTag;
class PostfixOperation {
    constructor(sinfo, isElvis, op) {
        this.sinfo = sinfo;
        this.isElvis = isElvis;
        this.op = op;
    }
}
exports.PostfixOperation = PostfixOperation;
class PostfixOp extends Expression {
    constructor(sinfo, root, ops) {
        super(ExpressionTag.PostfixOpExpression, sinfo);
        this.rootExp = root;
        this.ops = ops;
    }
}
exports.PostfixOp = PostfixOp;
class PostfixAccessFromIndex extends PostfixOperation {
    constructor(sinfo, isElvis, index) {
        super(sinfo, isElvis, PostfixOpTag.PostfixAccessFromIndex);
        this.index = index;
    }
}
exports.PostfixAccessFromIndex = PostfixAccessFromIndex;
class PostfixProjectFromIndecies extends PostfixOperation {
    constructor(sinfo, isElvis, isEphemeralListResult, indecies) {
        super(sinfo, isElvis, PostfixOpTag.PostfixProjectFromIndecies);
        this.isEphemeralListResult = isEphemeralListResult;
        this.indecies = indecies;
    }
}
exports.PostfixProjectFromIndecies = PostfixProjectFromIndecies;
class PostfixAccessFromName extends PostfixOperation {
    constructor(sinfo, isElvis, name) {
        super(sinfo, isElvis, PostfixOpTag.PostfixAccessFromName);
        this.name = name;
    }
}
exports.PostfixAccessFromName = PostfixAccessFromName;
class PostfixProjectFromNames extends PostfixOperation {
    constructor(sinfo, isElvis, isEphemeralListResult, names) {
        super(sinfo, isElvis, PostfixOpTag.PostfixProjectFromNames);
        this.isEphemeralListResult = isEphemeralListResult;
        this.names = names;
    }
}
exports.PostfixProjectFromNames = PostfixProjectFromNames;
class PostfixProjectFromType extends PostfixOperation {
    constructor(sinfo, isElvis, istry, ptype) {
        super(sinfo, isElvis, PostfixOpTag.PostfixProjectFromType);
        this.istry = istry;
        this.ptype = ptype;
    }
}
exports.PostfixProjectFromType = PostfixProjectFromType;
class PostfixModifyWithIndecies extends PostfixOperation {
    constructor(sinfo, isElvis, updates) {
        super(sinfo, isElvis, PostfixOpTag.PostfixModifyWithIndecies);
        this.updates = updates;
    }
}
exports.PostfixModifyWithIndecies = PostfixModifyWithIndecies;
class PostfixModifyWithNames extends PostfixOperation {
    constructor(sinfo, isElvis, updates) {
        super(sinfo, isElvis, PostfixOpTag.PostfixModifyWithNames);
        this.updates = updates;
    }
}
exports.PostfixModifyWithNames = PostfixModifyWithNames;
class PostfixStructuredExtend extends PostfixOperation {
    constructor(sinfo, isElvis, extension) {
        super(sinfo, isElvis, PostfixOpTag.PostfixStructuredExtend);
        this.extension = extension;
    }
}
exports.PostfixStructuredExtend = PostfixStructuredExtend;
class PostfixInvoke extends PostfixOperation {
    constructor(sinfo, isElvis, specificResolve, name, terms, pragmas, args) {
        super(sinfo, isElvis, PostfixOpTag.PostfixInvoke);
        this.specificResolve = specificResolve;
        this.name = name;
        this.pragmas = pragmas;
        this.terms = terms;
        this.args = args;
    }
}
exports.PostfixInvoke = PostfixInvoke;
class PrefixOp extends Expression {
    constructor(sinfo, op, exp) {
        super(ExpressionTag.PrefixOpExpression, sinfo);
        this.op = op;
        this.exp = exp;
    }
}
exports.PrefixOp = PrefixOp;
class BinOpExpression extends Expression {
    constructor(sinfo, lhs, op, rhs) {
        super(ExpressionTag.BinOpExpression, sinfo);
        this.lhs = lhs;
        this.op = op;
        this.rhs = rhs;
    }
}
exports.BinOpExpression = BinOpExpression;
class BinEqExpression extends Expression {
    constructor(sinfo, lhs, op, rhs) {
        super(ExpressionTag.BinEqExpression, sinfo);
        this.lhs = lhs;
        this.op = op;
        this.rhs = rhs;
    }
}
exports.BinEqExpression = BinEqExpression;
class BinCmpExpression extends Expression {
    constructor(sinfo, lhs, op, rhs) {
        super(ExpressionTag.BinCmpExpression, sinfo);
        this.lhs = lhs;
        this.op = op;
        this.rhs = rhs;
    }
}
exports.BinCmpExpression = BinCmpExpression;
class BinLogicExpression extends Expression {
    constructor(sinfo, lhs, op, rhs) {
        super(ExpressionTag.BinLogicExpression, sinfo);
        this.lhs = lhs;
        this.op = op;
        this.rhs = rhs;
    }
}
exports.BinLogicExpression = BinLogicExpression;
class NonecheckExpression extends Expression {
    constructor(sinfo, lhs, rhs) {
        super(ExpressionTag.NonecheckExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}
exports.NonecheckExpression = NonecheckExpression;
class CoalesceExpression extends Expression {
    constructor(sinfo, lhs, rhs) {
        super(ExpressionTag.CoalesceExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}
exports.CoalesceExpression = CoalesceExpression;
class SelectExpression extends Expression {
    constructor(sinfo, test, option1, option2) {
        super(ExpressionTag.SelectExpression, sinfo);
        this.test = test;
        this.option1 = option1;
        this.option2 = option2;
    }
}
exports.SelectExpression = SelectExpression;
class ExpOrExpression extends Expression {
    constructor(sinfo, exp, action, result, cond) {
        super(ExpressionTag.ExpOrExpression, sinfo);
        this.exp = exp;
        this.action = action;
        this.result = result;
        this.cond = cond;
    }
}
exports.ExpOrExpression = ExpOrExpression;
class BlockStatementExpression extends Expression {
    constructor(sinfo, ops) {
        super(ExpressionTag.BlockStatementExpression, sinfo);
        this.ops = ops;
    }
}
exports.BlockStatementExpression = BlockStatementExpression;
class IfExpression extends Expression {
    constructor(sinfo, flow) {
        super(ExpressionTag.IfExpression, sinfo);
        this.flow = flow;
    }
}
exports.IfExpression = IfExpression;
class MatchExpression extends Expression {
    constructor(sinfo, sval, flow) {
        super(ExpressionTag.MatchExpression, sinfo);
        this.sval = sval;
        this.flow = flow;
    }
}
exports.MatchExpression = MatchExpression;
var StatementTag;
(function (StatementTag) {
    StatementTag["Clear"] = "[CLEAR]";
    StatementTag["InvalidStatement"] = "[INVALID]";
    StatementTag["EmptyStatement"] = "EmptyStatement";
    StatementTag["VariableDeclarationStatement"] = "VariableDeclarationStatement";
    StatementTag["VariablePackDeclarationStatement"] = "VariablePackDeclarationStatement";
    StatementTag["VariableAssignmentStatement"] = "VariableAssignmentStatement";
    StatementTag["VariablePackAssignmentStatement"] = "VariablePackAssignmentStatement";
    StatementTag["StructuredVariableAssignmentStatement"] = "StructuredVariableAssignmentStatement";
    StatementTag["ReturnStatement"] = "ReturnStatement";
    StatementTag["YieldStatement"] = "YieldStatement";
    StatementTag["IfElseStatement"] = "IfElseStatement";
    StatementTag["MatchStatement"] = "MatchStatement";
    StatementTag["AbortStatement"] = "AbortStatement";
    StatementTag["AssertStatement"] = "AssertStatement";
    StatementTag["CheckStatement"] = "CheckStatement";
    StatementTag["ValidateStatement"] = "ValidateStatement";
    StatementTag["DebugStatement"] = "DebugStatement";
    StatementTag["NakedCallStatement"] = "NakedCallStatement";
    StatementTag["BlockStatement"] = "BlockStatement";
})(StatementTag || (StatementTag = {}));
exports.StatementTag = StatementTag;
class Statement {
    constructor(tag, sinfo) {
        this.tag = tag;
        this.sinfo = sinfo;
    }
}
exports.Statement = Statement;
class InvalidStatement extends Statement {
    constructor(sinfo) {
        super(StatementTag.InvalidStatement, sinfo);
    }
}
exports.InvalidStatement = InvalidStatement;
class EmptyStatement extends Statement {
    constructor(sinfo) {
        super(StatementTag.EmptyStatement, sinfo);
    }
}
exports.EmptyStatement = EmptyStatement;
class VariableDeclarationStatement extends Statement {
    constructor(sinfo, name, isConst, vtype, exp) {
        super(StatementTag.VariableDeclarationStatement, sinfo);
        this.name = name;
        this.isConst = isConst;
        this.vtype = vtype;
        this.exp = exp;
    }
}
exports.VariableDeclarationStatement = VariableDeclarationStatement;
class VariablePackDeclarationStatement extends Statement {
    constructor(sinfo, isConst, vars, exp) {
        super(StatementTag.VariablePackDeclarationStatement, sinfo);
        this.isConst = isConst;
        this.vars = vars;
        this.exp = exp;
    }
}
exports.VariablePackDeclarationStatement = VariablePackDeclarationStatement;
class VariableAssignmentStatement extends Statement {
    constructor(sinfo, name, exp) {
        super(StatementTag.VariableAssignmentStatement, sinfo);
        this.name = name;
        this.exp = exp;
    }
}
exports.VariableAssignmentStatement = VariableAssignmentStatement;
class VariablePackAssignmentStatement extends Statement {
    constructor(sinfo, names, exp) {
        super(StatementTag.VariablePackAssignmentStatement, sinfo);
        this.names = names;
        this.exp = exp;
    }
}
exports.VariablePackAssignmentStatement = VariablePackAssignmentStatement;
class StructuredAssignment {
}
exports.StructuredAssignment = StructuredAssignment;
class IgnoreTermStructuredAssignment extends StructuredAssignment {
    constructor(isOptional, termType) {
        super();
        this.isOptional = isOptional;
        this.termType = termType;
    }
}
exports.IgnoreTermStructuredAssignment = IgnoreTermStructuredAssignment;
class ConstValueStructuredAssignment extends StructuredAssignment {
    constructor(constValue) {
        super();
        this.constValue = constValue;
    }
}
exports.ConstValueStructuredAssignment = ConstValueStructuredAssignment;
class VariableDeclarationStructuredAssignment extends StructuredAssignment {
    constructor(isOptional, vname, isConst, vtype) {
        super();
        this.isOptional = isOptional;
        this.vname = vname;
        this.isConst = isConst;
        this.vtype = vtype;
    }
}
exports.VariableDeclarationStructuredAssignment = VariableDeclarationStructuredAssignment;
class VariableAssignmentStructuredAssignment extends StructuredAssignment {
    constructor(isOptional, vname) {
        super();
        this.isOptional = isOptional;
        this.vname = vname;
    }
}
exports.VariableAssignmentStructuredAssignment = VariableAssignmentStructuredAssignment;
class TupleStructuredAssignment extends StructuredAssignment {
    constructor(assigns) {
        super();
        this.assigns = assigns;
    }
}
exports.TupleStructuredAssignment = TupleStructuredAssignment;
class RecordStructuredAssignment extends StructuredAssignment {
    constructor(assigns) {
        super();
        this.assigns = assigns;
    }
}
exports.RecordStructuredAssignment = RecordStructuredAssignment;
class NominalStructuredAssignment extends StructuredAssignment {
    constructor(atype, isValue, assigns) {
        super();
        this.atype = atype;
        this.isValue = isValue;
        this.assigns = assigns;
    }
}
exports.NominalStructuredAssignment = NominalStructuredAssignment;
class ValueListStructuredAssignment extends StructuredAssignment {
    constructor(assigns) {
        super();
        this.assigns = assigns;
    }
}
exports.ValueListStructuredAssignment = ValueListStructuredAssignment;
class StructuredVariableAssignmentStatement extends Statement {
    constructor(sinfo, assign, exp) {
        super(StatementTag.StructuredVariableAssignmentStatement, sinfo);
        this.assign = assign;
        this.exp = exp;
    }
}
exports.StructuredVariableAssignmentStatement = StructuredVariableAssignmentStatement;
class ReturnStatement extends Statement {
    constructor(sinfo, values) {
        super(StatementTag.ReturnStatement, sinfo);
        this.values = values;
    }
}
exports.ReturnStatement = ReturnStatement;
class YieldStatement extends Statement {
    constructor(sinfo, values) {
        super(StatementTag.YieldStatement, sinfo);
        this.values = values;
    }
}
exports.YieldStatement = YieldStatement;
class IfElseStatement extends Statement {
    constructor(sinfo, flow) {
        super(StatementTag.IfElseStatement, sinfo);
        this.flow = flow;
    }
}
exports.IfElseStatement = IfElseStatement;
class MatchStatement extends Statement {
    constructor(sinfo, sval, flow) {
        super(StatementTag.MatchStatement, sinfo);
        this.sval = sval;
        this.flow = flow;
    }
}
exports.MatchStatement = MatchStatement;
class AbortStatement extends Statement {
    constructor(sinfo) {
        super(StatementTag.AbortStatement, sinfo);
    }
}
exports.AbortStatement = AbortStatement;
class AssertStatement extends Statement {
    constructor(sinfo, cond, level) {
        super(StatementTag.AssertStatement, sinfo);
        this.cond = cond;
        this.level = level;
    }
}
exports.AssertStatement = AssertStatement;
class CheckStatement extends Statement {
    constructor(sinfo, cond) {
        super(StatementTag.CheckStatement, sinfo);
        this.cond = cond;
    }
}
exports.CheckStatement = CheckStatement;
class ValidateStatement extends Statement {
    constructor(sinfo, cond, err) {
        super(StatementTag.ValidateStatement, sinfo);
        this.cond = cond;
        this.err = err;
    }
}
exports.ValidateStatement = ValidateStatement;
class DebugStatement extends Statement {
    constructor(sinfo, value) {
        super(StatementTag.DebugStatement, sinfo);
        this.value = value;
    }
}
exports.DebugStatement = DebugStatement;
class NakedCallStatement extends Statement {
    constructor(sinfo, call) {
        super(StatementTag.NakedCallStatement, sinfo);
        this.call = call;
    }
}
exports.NakedCallStatement = NakedCallStatement;
class BlockStatement extends Statement {
    constructor(sinfo, statements) {
        super(StatementTag.BlockStatement, sinfo);
        this.statements = statements;
    }
}
exports.BlockStatement = BlockStatement;
class BodyImplementation {
    constructor(bodyid, file, body) {
        this.id = bodyid;
        this.file = file;
        this.body = body;
    }
}
exports.BodyImplementation = BodyImplementation;
//# sourceMappingURL=body.js.map