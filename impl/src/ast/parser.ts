//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ParserEnvironment, FunctionScope } from "./parser_env";
import { FunctionParameter, TypeSignature, NominalTypeSignature, TemplateTypeSignature, ParseErrorTypeSignature, TupleTypeSignature, RecordTypeSignature, FunctionTypeSignature, UnionTypeSignature, AutoTypeSignature, ProjectTypeSignature, EphemeralListTypeSignature, PlusTypeSignature, AndTypeSignature, LiteralTypeSignature } from "./type_signature";
import { Arguments, TemplateArguments, NamedArgument, PositionalArgument, InvalidExpression, Expression, LiteralNoneExpression, LiteralBoolExpression, LiteralStringExpression, LiteralTypedStringExpression, AccessVariableExpression, AccessNamespaceConstantExpression, LiteralTypedStringConstructorExpression, CallNamespaceFunctionOrOperatorExpression, AccessStaticFieldExpression, ConstructorTupleExpression, ConstructorRecordExpression, ConstructorPrimaryExpression, ConstructorPrimaryWithFactoryExpression, PostfixOperation, PostfixAccessFromIndex, PostfixAccessFromName, PostfixProjectFromIndecies, PostfixProjectFromNames, PostfixModifyWithIndecies, PostfixModifyWithNames, PostfixInvoke, PostfixOp, PrefixNotOp, BinLogicExpression, NonecheckExpression, CoalesceExpression, SelectExpression, BlockStatement, Statement, BodyImplementation, EmptyStatement, InvalidStatement, VariableDeclarationStatement, VariableAssignmentStatement, ReturnStatement, YieldStatement, CondBranchEntry, IfElse, IfElseStatement, InvokeArgument, CallStaticFunctionOrOperatorExpression, AssertStatement, CheckStatement, DebugStatement, StructuredAssignment, TupleStructuredAssignment, RecordStructuredAssignment, VariableDeclarationStructuredAssignment, IgnoreTermStructuredAssignment, VariableAssignmentStructuredAssignment, ConstValueStructuredAssignment, StructuredVariableAssignmentStatement, MatchStatement, MatchEntry, MatchGuard, WildcardMatchGuard, StructureMatchGuard, AbortStatement, BlockStatementExpression, IfExpression, MatchExpression, RecursiveAnnotation, ConstructorPCodeExpression, PCodeInvokeExpression, ExpOrExpression, LiteralRegexExpression, ValidateStatement, NakedCallStatement, ValueListStructuredAssignment, NominalStructuredAssignment, VariablePackDeclarationStatement, VariablePackAssignmentStatement, ConstructorEphemeralValueList, MapEntryConstructorExpression, LiteralParamerterValueExpression, SpecialConstructorExpression, TypeMatchGuard, PostfixIs, LiteralTypedNumericConstructorExpression, PostfixHasIndex, PostfixHasProperty, PostfixAs, LiteralExpressionValue, LiteralIntegralExpression, LiteralFloatPointExpression, LiteralRationalExpression, OfTypeConvertExpression, PostfixGetIndexOrNone, PostfixGetIndexTry, PostfixGetPropertyOrNone, PostfixGetPropertyTry, ConstantExpressionValue, LiteralNumberinoExpression, BinKeyExpression, VerifierAssumeStatement } from "./body";
import { Assembly, NamespaceUsing, NamespaceDeclaration, NamespaceTypedef, StaticMemberDecl, StaticFunctionDecl, MemberFieldDecl, MemberMethodDecl, ConceptTypeDecl, EntityTypeDecl, NamespaceConstDecl, NamespaceFunctionDecl, InvokeDecl, TemplateTermDecl, PreConditionDecl, PostConditionDecl, BuildLevel, TypeConditionRestriction, InvariantDecl, TemplateTypeRestriction, SpecialTypeCategory, StaticOperatorDecl, NamespaceOperatorDecl, OOPTypeDecl, TemplateTermSpecialRestriction } from "./assembly";
import { BSQRegex } from "./bsqregex";

const KeywordStrings = [
    "recursive?",
    "recursive",
    
    "_assume",
    "_debug",
    "abort",
    "assert",
    "case",
    "check",
    "concept",
    "const",
    "elif",
    "else",
    "empty",
    "enum",
    "entity",
    "ensures",
    "err",
    "literal",
    "false",
    "field",
    "fn",
    "function",
    "grounded",
    "if",
    "invariant",
    "let",
    "method",
    "namespace",
    "none",
    "of",
    "ok",
    "operator",
    "private",
    "provides",
    "ref",
    "out",
    "out?",
    "release",
    "return",
    "requires",
    "switch",
    "test",
    "true",
    "type",
    "typedef",
    "typedecl",
    "unique",
    "numericdef",
    "validate",
    "var",
    "when",
    "where",
    "yield"
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : a.localeCompare(b); });

const SymbolStrings = [
    "[",
    "(",
    "{",
    "]",
    ")",
    "}",
    "(|",
    "|)",
    "{|",
    "|}",

    "#",
    "&",
    "&&",
    "@",
    "!",
    "!=",
    "!==",
    ":",
    "::",
    ",",
    ".",
    "...",
    "=",
    "==",
    "===",
    "=>",
    "==>",
    ";",
    "|",
    "||",
    "+",
    "?",
    "<",
    "<=",
    ">",
    ">=",
    "-",
    "->",
    "*",
    "/"
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : a.localeCompare(b); });

const RegexFollows = new Set<string>([
    "_assume",
    "_debug",
    "abort",
    "assert",
    "check",
    "else",
    "ensures",
    "invariant",
    "release",
    "return",
    "requires",
    "test",
    "validate",
    "when",
    "yield",
    "[",
    "(",
    "(|",
    "{|",
    "&&",
    "!",
    "!=",
    ",",
    "=",
    "==",
    "=>",
    "==>",
    "?",
    "||",
    "+",
    "<",
    "<=",
    ">",
    ">=",
    "-",
    "*",
    "/"
]);

const LeftScanParens = ["[", "(", "{", "(|", "{|"];
const RightScanParens = ["]", ")", "}", "|)", "|}"];

const AttributeStrings = [
    "entrypoint",
    "struct",
    "hidden",
    "private",
    "factory",
    "virtual",
    "abstract",
    "override",
    "recursive?",
    "recursive",
    "parsable",
    "validator",
    "derived",
    "lazy",
    "memoized",
    "interned",
    "inline",
    "prefix",
    "infix",
    "numeric",
    "dynamic",

    "__safe",
    "__assume_safe"
];

const UnsafeFieldNames = ["is", "as", "isNone", "isSome", "asTry", "asOrNone", "hasProperty", "getPropertyOrNone", "getPropertyTry"]

const TokenStrings = {
    Clear: "[CLEAR]",
    Error: "[ERROR]",

    Numberino: "[LITERAL_NUMBERINO]",
    Int: "[LITERAL_INT]",
    Nat: "[LITERAL_NAT]",
    Float: "[LITERAL_FLOAT]",
    Decimal: "[LITERAL_DECIMAL]",
    BigInt: "[LITERAL_BIGINT]",
    BigNat: "[LITERAL_BIGNAT]",
    Rational: "[LITERAL_RATIONAL]",
    String: "[LITERAL_STRING]",
    Regex: "[LITERAL_REGEX]",
    TypedString: "[LITERAL_TYPED_STRING]",

    //Names
    Namespace: "[NAMESPACE]",
    Type: "[TYPE]",
    Template: "[TEMPLATE]",
    Identifier: "[IDENTIFIER]",
    Operator: "[OPERATOR]",

    EndOfStream: "[EOS]"
};

class Token {
    readonly line: number;
    readonly column: number;
    readonly pos: number;
    readonly span: number;

    readonly kind: string;
    readonly data: string | undefined;

    constructor(line: number, column: number, cpos: number, span: number, kind: string, data?: string) {
        this.line = line;
        this.column = column;
        this.pos = cpos;
        this.span = span;

        this.kind = kind;
        this.data = data;
    }
}

class SourceInfo {
    readonly line: number;
    readonly column: number;
    readonly pos: number;
    readonly span: number;

    constructor(line: number, column: number, cpos: number, span: number) {
        this.line = line;
        this.column = column;
        this.pos = cpos;
        this.span = span;
    }
}

function unescapeLiteralString(str: string): string {
    let rs = str
        .replace(/\\0/ug, "\0")
        .replace(/\\'/ug, "'")
        .replace(/\\"/ug, "\"")
        .replace(/\\n/ug, "\n")
        .replace(/\\r/ug, "\r")
        .replace(/\\t/ug, "\t");

    let mm = rs.match(/\\u\{([0-9A-Fa-f])+\}/u);
    while(mm !== null) {
        const ccode = Number.parseInt(mm[1], 16);
        const charstr = String.fromCodePoint(ccode);
        rs = rs.slice(0, mm.index as number) + charstr + rs.slice(mm.index as number + mm[0].length);
    }

    return rs.replace(/\\\\/ug, "\\");
}

class Lexer {
    private static findSymbolString(str: string): string | undefined {
        if(str.startsWith("$") && !/^([$][_\p{L}])/.test(str)) {
            return "$";
        }

        return SymbolStrings.find((value) => str.startsWith(value));
    }

    private static findKeywordString(str: string): string | undefined {
        let imin = 0;
        let imax = KeywordStrings.length;

        while (imin < imax) {
            const imid = Math.floor((imin + imax) / 2);

            const scmpval = (str.length !== KeywordStrings[imid].length) ? (KeywordStrings[imid].length - str.length) : str.localeCompare(KeywordStrings[imid]);
            if (scmpval === 0) {
                return KeywordStrings[imid];
            }
            else if (scmpval < 0) {
                imax = imid;
            }
            else {
                imin = imid + 1;
            }
        }
        return undefined;
    }

    private m_input: string;
    private m_internTable: Map<string, string>;
    private m_cline: number;
    private m_linestart: number;
    private m_cpos: number;
    private m_tokens: Token[];

    constructor(input: string) {
        this.m_input = input;
        this.m_internTable = new Map<string, string>();
        this.m_cline = 1;
        this.m_linestart = 0;
        this.m_cpos = 0;
        this.m_tokens = [];
    }

    ////
    //Helpers
    private static isNamespaceName(str: string) {
        return /^NS/.test(str);
    }

    private static isTypenameName(str: string) {
        return str.length > 1 && !/^NS/.test(str) && /^[A-Z]/.test(str);
    }

    private static isTemplateName(str: string) {
        return str.length === 1 && /^[A-Z])$/.test(str);
    }

    //TODO: we need to make sure that someone doesn't name a local variable "_"
    private static isIdentifierName(str: string) {
        return /^([$]?([_\p{L}][_\p{L}\p{Nd}]*))$/u.test(str);
    }

    private recordLexToken(epos: number, kind: string) {
        this.m_tokens.push(new Token(this.m_cline, this.m_cpos - this.m_linestart, this.m_cpos, epos - this.m_cpos, kind, kind)); //set data to kind string
        this.m_cpos = epos;
    }

    private recordLexTokenWData(epos: number, kind: string, data: string) {
        const rdata = this.m_internTable.get(data) || this.m_internTable.set(data, data).get(data);
        this.m_tokens.push(new Token(this.m_cline, this.m_cpos - this.m_linestart, this.m_cpos, epos - this.m_cpos, kind, rdata));
        this.m_cpos = epos;
    }

    private static readonly _s_whitespaceRe = /\p{Z}+/uy;
    private tryLexWS(): boolean {
        Lexer._s_whitespaceRe.lastIndex = this.m_cpos;
        const m = Lexer._s_whitespaceRe.exec(this.m_input);
        if (m === null) {
            return false;
        }

        for (let i = 0; i < m[0].length; ++i) {
            if (m[0][i] === "\n") {
                this.m_cline++;
                this.m_linestart = this.m_cpos + i + 1;
            }
        }

        this.m_cpos += m[0].length;
        return true;
    }

    private static readonly _s_commentRe = /(\/\/.*)|(\/\*[\p{L}\p{M}\p{N}\p{S}\p{Z}]*?\*\/)/uy;
    private tryLexComment(): boolean {
        Lexer._s_commentRe.lastIndex = this.m_cpos;
        const m = Lexer._s_commentRe.exec(this.m_input);
        if (m === null) {
            return false;
        }

        for (let i = 0; i < m[0].length; ++i) {
            if (m[0][i] === "\n") {
                this.m_cline++;
                this.m_linestart = this.m_cpos + i + 1;
            }
        }

        this.m_cpos += m[0].length;
        return true;
    }

    private static readonly _s_numberinoRe = /(0|[1-9][0-9]*)|([0-9]+\.[0-9]+)([eE][-+]?[0-9]+)?/y;

    private static readonly _s_intRe = /(0|[1-9][0-9]*)i/y;
    private static readonly _s_natRe = /(0|[1-9][0-9]*)n/y;

    private static readonly _s_floatRe = /([0-9]+\.[0-9]+)([eE][-+]?[0-9]+)?f/y;
    private static readonly _s_decimalRe = /([0-9]+\.[0-9]+)([eE][-+]?[0-9]+)?d/y;

    private static readonly _s_bigintRe = /(0|[1-9][0-9]*)I/y;
    private static readonly _s_bignatRe = /(0|[1-9][0-9]*)N/y;
    private static readonly _s_rationalRe = /(0|[1-9][0-9]*)|(0|[1-9][0-9]*)\/(0|[1-9][0-9]*)R/y;

    private tryLexNumber(): boolean {
        Lexer._s_rationalRe.lastIndex = this.m_cpos;
        const mr = Lexer._s_rationalRe.exec(this.m_input);
        if (mr !== null) {
            this.recordLexTokenWData(this.m_cpos + mr[0].length, TokenStrings.Rational, mr[0]);
            return true;
        }

        Lexer._s_bignatRe.lastIndex = this.m_cpos;
        const mbn = Lexer._s_bignatRe.exec(this.m_input);
        if (mbn !== null) {
            this.recordLexTokenWData(this.m_cpos + mbn[0].length, TokenStrings.BigNat, mbn[0]);
            return true;
        }

        Lexer._s_bigintRe.lastIndex = this.m_cpos;
        const mbi = Lexer._s_bigintRe.exec(this.m_input);
        if (mbi !== null) {
            this.recordLexTokenWData(this.m_cpos + mbi[0].length, TokenStrings.BigInt, mbi[0]);
            return true;
        }

        Lexer._s_decimalRe.lastIndex = this.m_cpos;
        const md = Lexer._s_decimalRe.exec(this.m_input);
        if (md !== null) {
            this.recordLexTokenWData(this.m_cpos + md[0].length, TokenStrings.Decimal, md[0]);
            return true;
        }

        Lexer._s_floatRe.lastIndex = this.m_cpos;
        const mf = Lexer._s_floatRe.exec(this.m_input);
        if (mf !== null) {
            this.recordLexTokenWData(this.m_cpos + mf[0].length, TokenStrings.Float, mf[0]);
            return true;
        }

        Lexer._s_natRe.lastIndex = this.m_cpos;
        const mn = Lexer._s_natRe.exec(this.m_input);
        if (mn !== null) {
            this.recordLexTokenWData(this.m_cpos + mn[0].length, TokenStrings.Nat, mn[0]);
            return true;
        }

        Lexer._s_intRe.lastIndex = this.m_cpos;
        const mi = Lexer._s_intRe.exec(this.m_input);
        if (mi !== null) {
            this.recordLexTokenWData(this.m_cpos + mi[0].length, TokenStrings.Int, mi[0]);
            return true;
        }

        Lexer._s_numberinoRe.lastIndex = this.m_cpos;
        const mnio = Lexer._s_intRe.exec(this.m_input);
        if (mnio !== null) {
            this.recordLexTokenWData(this.m_cpos + mnio[0].length, TokenStrings.Numberino, mnio[0]);
            return true;
        }

        return false;
    }

    private static readonly _s_stringRe = /"[^"\\\r\n]*(\\(.|\r?\n)[^"\\\r\n]*)*"/uy;
    private static readonly _s_typedStringRe = /'[^'\\\r\n]*(\\(.|\r?\n)[^'\\\r\n]*)*'/uy;
    private tryLexString() {
        Lexer._s_stringRe.lastIndex = this.m_cpos;
        const ms = Lexer._s_stringRe.exec(this.m_input);
        if (ms !== null) {
            this.recordLexTokenWData(this.m_cpos + ms[0].length, TokenStrings.String, ms[0]);
            return true;
        }

        Lexer._s_typedStringRe.lastIndex = this.m_cpos;
        const mts = Lexer._s_typedStringRe.exec(this.m_input);
        if (mts !== null) {
            this.recordLexTokenWData(this.m_cpos + mts[0].length, TokenStrings.TypedString, mts[0]);
            return true;
        }

        return false;
    }

    private static readonly _s_regexRe = /\/[^"\\\r\n]*(\\(.)[^"\\\r\n]*)*\//uy;
    private tryLexRegex() {
        Lexer._s_regexRe.lastIndex = this.m_cpos;
        const ms = Lexer._s_regexRe.exec(this.m_input);
        if (ms !== null && RegexFollows.has(this.m_tokens[this.m_tokens.length - 1].kind)) {
            this.recordLexTokenWData(this.m_cpos + ms[0].length, TokenStrings.Regex, ms[0]);
            return true;
        }

        return false;
    }

    private static readonly _s_symbolRe = /[\W]+/y;
    private static readonly _s_operatorRe = /[\p{Sm}\p{So}]/uy;
    private tryLexSymbol() {
        Lexer._s_symbolRe.lastIndex = this.m_cpos;
        const ms = Lexer._s_symbolRe.exec(this.m_input);
        if (ms === null) {
            return false;
        }

        const sym = Lexer.findSymbolString(ms[0]);
        if (sym !== undefined) {
            this.recordLexToken(this.m_cpos + sym.length, sym);
            return true;
        }

        Lexer._s_operatorRe.lastIndex = this.m_cpos;
        const mo = Lexer._s_operatorRe.exec(this.m_input);
        if (mo !== null) {
            const oper = mo[0];
            this.recordLexTokenWData(this.m_cpos + oper.length, TokenStrings.Operator, oper);
            return true;
        }

        return false;
    }

    private static readonly _s_nameRe = /([$]?[_\p{L}][_\p{L}\p{Nd}]+)|(recursive\?)|(ref!)|(ref\?)/uy;
    private tryLexName(): boolean {
        Lexer._s_nameRe.lastIndex = this.m_cpos;
        const m = Lexer._s_nameRe.exec(this.m_input);
        if (m === null) {
            return false;
        }

        const name = m[0];

        const kwmatch = Lexer.findKeywordString(name);
        if (kwmatch) {
            this.recordLexToken(this.m_cpos + name.length, kwmatch);
            return true;
        }
        else if (Lexer.isNamespaceName(name)) {
            this.recordLexTokenWData(this.m_cpos + name.length, TokenStrings.Namespace, name);
            return true;
        }
        else if (Lexer.isTypenameName(name)) {
            this.recordLexTokenWData(this.m_cpos + name.length, TokenStrings.Type, name);
            return true;
        }
        else if (Lexer.isTemplateName(name)) {
            this.recordLexTokenWData(this.m_cpos + name.length, TokenStrings.Template, name);
            return true;
        }
        else if (Lexer.isIdentifierName(name)) {
            this.recordLexTokenWData(this.m_cpos + name.length, TokenStrings.Identifier, name);
            return true;
        }
        else {
            this.recordLexToken(this.m_cpos + name.length, TokenStrings.Error);
            return false;
        }
    }

    static isAttributeKW(str: string) {
        return AttributeStrings.indexOf(str) !== -1;
    }

    lex(): Token[] {
        if (this.m_tokens.length !== 0) {
            return this.m_tokens;
        }

        this.m_tokens = [];
        while (this.m_cpos < this.m_input.length) {
            if (this.tryLexWS() || this.tryLexComment()) {
                //continue
            }
            else if (this.tryLexNumber() || this.tryLexString() || this.tryLexRegex() || this.tryLexSymbol() || this.tryLexName()) {
                //continue
            }
            else {
                this.recordLexToken(this.m_cpos + 1, TokenStrings.Error);
            }
        }

        this.recordLexToken(this.m_input.length, TokenStrings.EndOfStream);
        return this.m_tokens;
    }
}

class ParseError extends Error {
    constructor(line: number, message?: string) {
        super(`Parse failure on line ${line} -- ${message}`);
        Object.setPrototypeOf(this, new.target.prototype);
    }
}

enum InvokableKind {
    Basic,
    Member,
    PCode,
    StaticOperator,
    DynamicOperator
}

class Parser {
    private m_tokens: Token[];
    private m_cpos: number;
    private m_epos: number;

    private m_penv: ParserEnvironment;

    private m_errors: [string, number, string][];
    private m_recoverStack: number[];

    constructor(assembly: Assembly) {
        this.m_tokens = [];
        this.m_cpos = 0;
        this.m_epos = 0;

        this.m_penv = new ParserEnvironment(assembly);
        this.m_errors = [];
        this.m_recoverStack = [];
    }

    private initialize(toks: Token[]) {
        this.m_tokens = toks;
        this.m_cpos = 0;
        this.m_epos = toks.length;
    }

    ////
    //Helpers

    private static attributeSetContains(attr: string, attribs: string[]): boolean {
        return attribs.indexOf(attr) !== -1;
    }

    private getCurrentLine(): number {
        return this.m_tokens[this.m_cpos].line;
    }

    private getCurrentSrcInfo(): SourceInfo {
        const tk = this.m_tokens[this.m_cpos];
        return new SourceInfo(tk.line, 0, tk.pos, tk.span);
    }

    private setRecover(pos: number) {
        this.m_recoverStack.push(pos);
    }

    private clearRecover(pos?: number) {
        this.m_recoverStack.pop();
    }

    private processRecover() {
        this.m_cpos = this.m_recoverStack.pop() as number;
    }

    private raiseError(line: number, msg: string) {
        this.m_errors.push([this.m_penv.getCurrentFile(), line, msg]);
        throw new ParseError(line, msg);
    }

    private scanMatchingParens(lp: string, rp: string, sindex?: number): number {
        let pscount = 1;
        for (let pos = this.m_cpos + (sindex || 0) + 1; pos < this.m_epos; ++pos) {
            const tok = this.m_tokens[pos];
            if (tok.kind === lp) {
                pscount++;
            }
            else if (tok.kind === rp) {
                pscount--;
            }
            else {
                //nop
            }

            if (pscount === 0) {
                return pos + 1;
            }
        }

        return this.m_epos;
    }

    private scanCodeParens(): number {
        let pscount = 1;
        for (let pos = this.m_cpos + 1; pos < this.m_epos; ++pos) {
            const tok = this.m_tokens[pos];
            if (LeftScanParens.indexOf(tok.kind) !== -1) {
                pscount++;
            }
            else if (RightScanParens.indexOf(tok.kind) !== -1) {
                pscount--;
            }
            else {
                //nop
            }

            if (pscount === 0) {
                return pos + 1;
            }
        }

        return this.m_epos;
    }

    private setNamespaceAndFile(ns: string, file: string) {
        this.m_penv.setNamespaceAndFile(ns, file);
    }

    private peekToken(pos?: number): string {
        return this.m_tokens[this.m_cpos + (pos || 0)].kind;
    }

    private peekTokenData(pos?: number): string {
        return this.m_tokens[this.m_cpos + (pos || 0)].data as string;
    }

    private testToken(kind: string): boolean {
        return (this.m_cpos !== this.m_epos) && this.m_tokens[this.m_cpos].kind === kind;
    }

    private testFollows(...kinds: string[]): boolean {
        for (let i = 0; i < kinds.length; ++i) {
            if (this.m_cpos + i === this.m_epos || this.m_tokens[this.m_cpos + i].kind !== kinds[i]) {
                return false;
            }
        }

        return true;
    }

    private testElvisFollows(ftoken: string): boolean {
        if(this.testFollows("?", ftoken)) {
            return true;
        }

        if(!this.testFollows("?", "(")) {
            return false;
        }
        else {
            const eepos = this.scanMatchingParens("(", ")", 1);
            if(eepos === this.m_epos) {
                return false;
            }

            return this.m_tokens[eepos].kind === ftoken;
        }
    }

    private consumeToken() {
        this.m_cpos++;
    }

    private consumeTokenIf(kind: string) {
        if (this.testToken(kind)) {
            this.consumeToken();
        }
    }

    private testAndConsumeTokenIf(kind: string): boolean {
        const test = this.testToken(kind);
        if (test) {
            this.consumeToken();
        }
        return test;
    }

    private consumeTokenAndGetValue(): string {
        const td = this.m_tokens[this.m_cpos].data;
        this.consumeToken();
        return td as string;
    }

    private ensureToken(kind: string) {
        if (!this.testToken(kind)) {
            const found = this.m_tokens[this.m_cpos].data || this.m_tokens[this.m_cpos].kind;
            this.raiseError(this.m_tokens[this.m_cpos].line, `Expected "${kind}" but found "${found}"`);
        }
    }

    private ensureAndConsumeToken(kind: string) {
        this.ensureToken(kind);
        this.consumeToken();
    }

    private ensureNotToken(kind: string) {
        if (this.testToken(kind)) {
            this.raiseError(this.m_tokens[this.m_cpos].line, `Token "${kind}" is not allowed`);
        }
    }

    private scanToken(tok: string): number {
        let pos = this.m_cpos;

        while (pos !== this.m_epos) {
            if (this.m_tokens[pos].kind === tok) {
                return pos;
            }
            pos++;
        }
        return this.m_epos;
    }

    private scanTokenOptions(...toks: string[]): number {
        let pos = this.m_cpos;

        while (pos !== this.m_epos) {
            if (toks.indexOf(this.m_tokens[pos].kind) !== -1) {
                return pos;
            }
            pos++;
        }
        return this.m_epos;
    }

    private parseListOf<T>(start: string, end: string, sep: string, fn: () => T, specialToken?: string): [T[], boolean] {
        let specialFound = false;
        let result: T[] = [];

        this.ensureAndConsumeToken(start);
        while (!this.testAndConsumeTokenIf(end)) {
            if (specialToken !== undefined && this.testAndConsumeTokenIf(specialToken)) {
                specialFound = true;
                this.ensureToken(end);
            }
            else {
                result.push(fn());
            }

            if (this.testAndConsumeTokenIf(sep)) {
                this.ensureNotToken(end);
            }
            else {
                this.ensureToken(end);
            }
        }

        return [result, specialFound];
    }

    private parseEphemeralListOf<T>(fn: () => T): T[] {
        let result: T[] = [];

        while (true) {
            result.push(fn());

            if(!this.testAndConsumeTokenIf(",")) {
                break;
            }
        }

        return result;
    }

    parseBuildInfo(cb: BuildLevel): BuildLevel {
        if(this.testToken("debug") || this.testToken("test") || this.testToken("release")) {
            return this.consumeTokenAndGetValue() as "debug" | "test" | "release";
        }
        else {
            return cb;
        }
    }

    ////
    //Misc parsing

    private parseInvokableCommon(ikind: InvokableKind, noBody: boolean, attributes: string[], isrecursive: "yes" | "no" | "cond", terms: TemplateTermDecl[], termRestrictions: TypeConditionRestriction | undefined, optSelfRef?: "ref" | "out" | "out?" | undefined, optSelfType?: TypeSignature): InvokeDecl {
        const sinfo = this.getCurrentSrcInfo();
        const srcFile = this.m_penv.getCurrentFile();
        const line = this.getCurrentLine();

        let fparams: FunctionParameter[] = [];
        if (ikind === InvokableKind.Member) {
            fparams.push(new FunctionParameter("this", optSelfType as TypeSignature, false, optSelfRef, undefined, undefined));
        }

        let restName: string | undefined = undefined;
        let restType: TypeSignature | undefined = undefined;
        let resultInfo = this.m_penv.SpecialAutoSignature;

        const params = this.parseListOf<[string, TypeSignature, boolean, boolean, "ref" | "out" | "out?" | undefined, ConstantExpressionValue | undefined, LiteralExpressionValue | undefined]>("(", ")", ",", () => {
            const isrest = this.testAndConsumeTokenIf("...");

            let rref: "ref" | "out" | "out?" | undefined = undefined;
            if(this.testToken("ref") || this.testToken("out") || this.testToken("out?")) {
                rref = this.consumeTokenAndGetValue() as "ref" | "out" | "out?";
            }

            this.ensureToken(TokenStrings.Identifier);
            const pname = this.consumeTokenAndGetValue();
            const isopt = this.testAndConsumeTokenIf("?");
            let argtype = this.m_penv.SpecialAutoSignature;

            if (this.testAndConsumeTokenIf(":")) {
                argtype = this.parseTypeSignature(ikind === InvokableKind.StaticOperator || ikind === InvokableKind.DynamicOperator);
            }
            else {
                if (ikind !== InvokableKind.PCode) {
                    this.raiseError(line, "Auto typing is not supported for this");
                }
            }

            if (rref !== undefined && (isopt || isrest)) {
                this.raiseError(line, "Cannot use ref parameters here");
            }

            let defaultexp: ConstantExpressionValue | undefined = undefined;
            if(isopt && this.testAndConsumeTokenIf("=")) {
                defaultexp = this.parseConstExpression(true);
            }

            let litexp: LiteralExpressionValue | undefined = undefined;
            if(this.testAndConsumeTokenIf("==")) {
                if(ikind !== InvokableKind.DynamicOperator) {
                    this.raiseError(line, "Literal parameters are only allowed on dynamic operator definitions");
                }

                litexp = this.parseConstExpression(false);
            }

            if(ikind === InvokableKind.DynamicOperator || ikind === InvokableKind.StaticOperator) {
                if(isopt || isrest) {
                    this.raiseError(line, "Cannot use opt or rest parameters in operators");
                }
            }

            return [pname, argtype, isopt, isrest, rref, defaultexp, litexp];
        })[0];

        for (let i = 0; i < params.length; i++) {
            if (!params[i][3]) {
                fparams.push(new FunctionParameter(params[i][0], params[i][1], params[i][2], params[i][4], params[i][5], params[i][6]));
            }
            else {
                if (i + 1 !== params.length) {
                    this.raiseError(line, "Rest parameter must be last in parameter list");
                }

                restName = params[i][0];
                restType = params[i][1];
            }
        }

        if (restName !== undefined && params.some((p) => p[2])) {
            this.raiseError(line, "Cannot have optional and rest parameters in a function");
        }

        if (this.testAndConsumeTokenIf(":")) {
            resultInfo = this.parseResultType(false);
        }
        else {
            if (ikind !== InvokableKind.PCode) {
                if(!params.some((p) => p[4])) {
                    this.raiseError(line, "Cannot have void return unless one of the params is by-ref");
                }
                resultInfo = this.m_penv.SpecialNoneSignature; //void conversion
            }
        }

        const argNames = new Set<string>([...(restName ? [restName] : []), ...fparams.map((param) => param.name)]);
        let preconds: PreConditionDecl[] = [];
        let postconds: PostConditionDecl[] = [];
        let body: BodyImplementation | undefined = undefined;
        let captured = new Set<string>();
        if (noBody) {
            this.ensureAndConsumeToken(";");
        }
        else {
            if (ikind == InvokableKind.PCode) {
                this.ensureAndConsumeToken("=>");
            }
            else {
                [preconds, postconds] = this.parsePreAndPostConditions(sinfo, argNames, resultInfo);
            }

            const bodyid = `${srcFile}::${sinfo.pos}`;
            try {
                this.m_penv.pushFunctionScope(new FunctionScope(argNames, resultInfo, ikind === InvokableKind.PCode));
                body = this.parseBody(bodyid, srcFile);
                captured = this.m_penv.getCurrentFunctionScope().getCaptureVars();
                this.m_penv.popFunctionScope();
            }
            catch (ex) {
                this.m_penv.popFunctionScope();
                throw ex;
            }
        }

        if (ikind === InvokableKind.PCode) {
            return InvokeDecl.createPCodeInvokeDecl(sinfo, srcFile, attributes, isrecursive, fparams, restName, restType, resultInfo, captured, body as BodyImplementation);
        }
        else {
            return InvokeDecl.createStandardInvokeDecl(sinfo, srcFile, attributes, isrecursive, terms, termRestrictions, fparams, restName, restType, resultInfo, preconds, postconds, body);
        }
    }

    parseElvisCheck(sinfo: SourceInfo): Expression | undefined {
        let customCheck: Expression | undefined = undefined;
        if (this.testToken("(")) {
            this.consumeToken();
            try {
                this.m_penv.getCurrentFunctionScope().pushLocalScope();
                this.m_penv.getCurrentFunctionScope().defineLocalVar("$chkval", `$chkval_#${sinfo.pos}`, true);

                customCheck = this.parseExpression();
            }
            finally {
                this.m_penv.getCurrentFunctionScope().popLocalScope();
            }
            this.ensureAndConsumeToken(")");
        }

        return customCheck;
    }

    ////
    //Type parsing

    private parseResultType(parensreq: boolean): TypeSignature {
        if (this.testAndConsumeTokenIf("(|")) {
            const decls = this.parseEphemeralListOf(() => {
                const tdecl = this.parseTypeSignature(false);
                return tdecl;
            });

            this.ensureAndConsumeToken("|)");
            return new EphemeralListTypeSignature(decls);
        }
        else {
            if(parensreq) {
                return this.parseTypeSignature(false);
            }
            else {
                const decls = this.parseEphemeralListOf(() => {
                    const tdecl = this.parseTypeSignature(false);
                    return tdecl;
                });
    
                return decls.length === 1 ? decls[0] : new EphemeralListTypeSignature(decls);
            }
        }
    } 

    private parseTypeSignature(literalTypeOk: boolean): TypeSignature {
        return this.parseOrCombinatorType(literalTypeOk);
    }

    private parseOrCombinatorType(literalTypeOk: boolean): TypeSignature {
        const ltype = this.parsePostfixTypeReference(literalTypeOk);
        if (!this.testToken("|")) {
            return ltype;
        }
        else {
            this.consumeToken();
            return Parser.orOfTypeSignatures(ltype, this.parseOrCombinatorType(false));
        }
    }

    private parsePostfixTypeReference(literalTypeOk: boolean): TypeSignature {
        let roottype = this.parseCombineCombinatorType(literalTypeOk);
        while (this.testToken("?")) {
            if(roottype instanceof LiteralTypeSignature) {
                this.raiseError(this.getCurrentLine(), "Cannot have nonable literal type");
            }

            roottype = this.parseNoneableType(roottype);
        }
        return roottype;
    }

    private parseNoneableType(basetype: TypeSignature): TypeSignature {
        this.ensureAndConsumeToken("?");
        return Parser.orOfTypeSignatures(basetype, this.m_penv.SpecialNoneSignature);
    }

    private parseCombineCombinatorType(literalTypeOk: boolean): TypeSignature {
        const ltype = this.parseProjectType(literalTypeOk);
        if (!this.testToken("&") && !this.testToken("+")) {
            return ltype;
        }
        else {
            if(this.testToken("&")) {
                this.consumeToken();
                return this.andOfTypeSignatures(ltype, this.parseCombineCombinatorType(false));
            }
            else {
                this.consumeToken();
                return this.plusOfTypeSignatures(ltype, this.parseCombineCombinatorType(false));
            }
        }
    }

    private parseProjectType(literalTypeOk: boolean): TypeSignature {
        const ltype = this.parseBaseTypeReference(literalTypeOk);
        if (!this.testToken("!")) {
            return ltype;
        }
        else {
            this.consumeToken();
            const ptype = this.parseNominalType();
            
            return new ProjectTypeSignature(ltype, ptype);
        }
    }

    private parseBaseTypeReference(literalTypeOk: boolean): TypeSignature {
        switch (this.peekToken()) {
            case TokenStrings.Template:
                return this.parseTemplateTypeReference();
            case TokenStrings.Namespace:
            case TokenStrings.Type:
                return this.parseNominalType();
            case "@":
            case "#": { 
                const isvalue = this.testToken("#");
                this.consumeToken();
                if(this.testToken("[")) {
                    return this.parseTupleType(isvalue);
                }
                else {
                    return this.parseRecordType(isvalue);
                }
            }
            case "fn":
            case "recursive?":
            case "recursive":
                return this.parsePCodeType();
            case "(": {
                this.ensureAndConsumeToken("(");
                const ptype = this.parseTypeSignature(literalTypeOk);
                this.ensureAndConsumeToken(")");

                return ptype;
            }
            default: {
                if(!literalTypeOk) {
                    this.raiseError(this.getCurrentLine(), "Unknown type option");
                }

                return this.parseLiteralType();
            }
        }
    }

    private parseTemplateTypeReference(): TypeSignature {
        return new TemplateTypeSignature(this.consumeTokenAndGetValue());
    }

    private parseTermList(): TypeSignature[] {
        let terms: TypeSignature[] = [];
        if (this.testToken("<")) {
            try {
                this.setRecover(this.scanMatchingParens("<", ">"));
                terms = this.parseListOf<TypeSignature>("<", ">", ",", () => {
                    return this.parseTypeSignature(true);
                })[0];

                this.clearRecover();
            }
            catch (ex) {
                this.processRecover();
            }
        }
        return terms;
    }

    private parseNominalType(): TypeSignature {
        const line = this.getCurrentLine();

        let ns: string | undefined = undefined;
        if (this.testToken(TokenStrings.Namespace)) {
            ns = this.consumeTokenAndGetValue();
            this.ensureAndConsumeToken("::");
        }

        const tname = this.consumeTokenAndGetValue();
        ns = this.m_penv.tryResolveNamespace(ns, tname);
        if (ns === undefined) {
            this.raiseError(line, "Could not resolve namespace");
        }

        let tnames: string[] = [tname];
        let terms: TypeSignature[] = this.parseTermList();

        while (!this.testFollows("::", TokenStrings.Type)) {
            this.ensureToken(TokenStrings.Type);
            const stname = this.consumeTokenAndGetValue();
            tnames.push(stname);

            const sterms = this.parseTermList();
            terms = [...terms, ...sterms];
        }

        return new NominalTypeSignature(ns as string, tnames, terms);
    }

    private parseLiteralType(): TypeSignature {
        this.ensureAndConsumeToken("type");
        this.ensureAndConsumeToken("(");
        const vv = this.parseLiteralExpression();
        this.ensureAndConsumeToken(")");

        return new LiteralTypeSignature(vv);
    }

    private parseTupleType(isvalue: boolean): TypeSignature {
        const line = this.getCurrentLine();
        let entries: [TypeSignature, boolean][] = [];

        try {
            this.setRecover(this.scanMatchingParens("[", "]"));
            entries = this.parseListOf<[TypeSignature, boolean]>("[", "]", ",", () => {
                const isopt = this.testAndConsumeTokenIf("?");
                if (isopt) {
                    this.ensureAndConsumeToken(":");
                }

                const rtype = this.parseTypeSignature(false);

                return [rtype, isopt];
            })[0];

            const firstOpt = entries.findIndex((entry) => entry[1]);
            if (entries.slice(firstOpt).findIndex((entry) => !entry[0]) !== -1) {
                this.raiseError(line, "Optional entries must all come at end of tuple");
            }

            this.clearRecover();
            return new TupleTypeSignature(isvalue, entries);
        }
        catch (ex) {
            this.processRecover();
            return new ParseErrorTypeSignature();
        }
    }

    private parseRecordType(isvalue: boolean): TypeSignature {
        let entries: [string, TypeSignature, boolean][] = [];

        try {
            this.setRecover(this.scanMatchingParens("{", "}"));

            let pnames = new Set<string>();
            entries = this.parseListOf<[string, TypeSignature, boolean]>("{", "}", ",", () => {
                this.ensureToken(TokenStrings.Identifier);

                const name = this.consumeTokenAndGetValue();
                if(UnsafeFieldNames.includes(name)) {
                    this.raiseError(this.getCurrentLine(), `Property name "${name}" is ambigious with the methods that Record may provide`);
                }

                if(pnames.has(name)) {
                    this.raiseError(this.getCurrentLine(), `Duplicate property name "${name}" in record declaration`);
                }
                pnames.add(name);

                const isopt = this.testAndConsumeTokenIf("?");
                this.ensureAndConsumeToken(":");
                const rtype = this.parseTypeSignature(false);

                return [name, rtype, isopt];
            })[0];

            this.clearRecover();
            return new RecordTypeSignature(isvalue, entries);
        }
        catch (ex) {
            this.processRecover();
            return new ParseErrorTypeSignature();
        }
    }

    private parsePCodeType(): TypeSignature {
        let recursive: "yes" | "no" | "cond" = "no";
        if (this.testAndConsumeTokenIf("recursive?")) {
            recursive = "cond";
        }
        if (this.testAndConsumeTokenIf("recursive")) {
            recursive = "yes";
        }

        this.ensureAndConsumeToken("fn");

        try {
            this.setRecover(this.scanMatchingParens("(", ")"));

            let fparams: FunctionParameter[] = [];
            let restName: string | undefined = undefined;
            let restType: TypeSignature | undefined = undefined;

            const params = this.parseListOf<[string, TypeSignature, boolean, boolean, "ref" | "out" | "out?" | undefined]>("(", ")", ",", () => {
                const isrest = this.testAndConsumeTokenIf("...");
                
                let rref: "ref" | "out" | "out?" | undefined = undefined;
                if(this.testToken("ref") || this.testToken("out") || this.testToken("out?")) {
                    rref = this.consumeTokenAndGetValue() as "ref" | "out" | "out?";
                }

                this.ensureToken(TokenStrings.Identifier);
                const pname = this.consumeTokenAndGetValue();
                const isopt = this.testAndConsumeTokenIf("?");
               
                this.ensureAndConsumeToken(":");
                const argtype = this.parseTypeSignature(false);

                if (rref !== undefined && (isopt || isrest)) {
                    this.raiseError(this.getCurrentLine(), "Cannot use ref/borrow parameters here");
                }

                return [pname, argtype, isopt, isrest, rref];
            })[0];

            for (let i = 0; i < params.length; i++) {
                if (!params[i][3]) {
                    fparams.push(new FunctionParameter(params[i][0], params[i][1], params[i][2], params[i][4], undefined, undefined));
                }
                else {
                    if (i + 1 !== params.length) {
                        this.raiseError(this.getCurrentLine(), "Rest parameter must be last in parameter list");
                    }

                    restName = params[i][0];
                    restType = params[i][1];
                }
            }

            if (restName !== undefined && params.some((p) => p[2])) {
                this.raiseError(this.getCurrentLine(), "Cannot have optional and rest parameters in a function type");
            }

            this.ensureAndConsumeToken("->");
            const resultInfo = this.parseResultType(true);

            this.clearRecover();
            return new FunctionTypeSignature(recursive, fparams, restName, restType, resultInfo);
        }
        catch (ex) {
            this.processRecover();
            return new ParseErrorTypeSignature();
        }
    }

    private static orOfTypeSignatures(t1: TypeSignature, t2: TypeSignature): TypeSignature {
        const types = [
            ...((t1 instanceof UnionTypeSignature) ? t1.types : [t1]),
            ...((t2 instanceof UnionTypeSignature) ? t2.types : [t2]),
        ];

        return new UnionTypeSignature(types);
    }

    private andOfTypeSignatures(t1: TypeSignature, t2: TypeSignature): TypeSignature {
        if(t1 instanceof PlusTypeSignature || t2 instanceof PlusTypeSignature) {
            this.raiseError(this.getCurrentLine(), "Cannot mix & and + type combiners");
        }

        const types = [
            ...((t1 instanceof AndTypeSignature) ? t1.types : [t1]),
            ...((t2 instanceof AndTypeSignature) ? t2.types : [t2]),
        ];

        return new AndTypeSignature(types);
    }

    private plusOfTypeSignatures(t1: TypeSignature, t2: TypeSignature): TypeSignature {
        if(t1 instanceof AndTypeSignature || t2 instanceof AndTypeSignature) {
            this.raiseError(this.getCurrentLine(), "Cannot mix & and + type combiners");
        }

        const types = [
            ...((t1 instanceof PlusTypeSignature) ? t1.types : [t1]),
            ...((t2 instanceof PlusTypeSignature) ? t2.types : [t2]),
        ];

        return new PlusTypeSignature(types);
    }

    ////
    //Expression parsing
    private parseArguments(lparen: string, rparen: string): Arguments {
        const argSrcInfo = this.getCurrentSrcInfo();

        let seenNames = new Set<string>();
        let args: InvokeArgument[] = [];

        try {
            this.setRecover(this.scanMatchingParens(lparen, rparen));

            this.ensureAndConsumeToken(lparen);
            while (!this.testAndConsumeTokenIf(rparen)) {
                const line = this.getCurrentLine();

                let rref: "ref" | "out" | "out?" | undefined = undefined;
                if(this.testToken("ref") || this.testToken("out") || this.testToken("out?")) {
                    rref = this.consumeTokenAndGetValue() as "ref" | "out" | "out?";
                }

                if (this.testFollows(TokenStrings.Identifier, "=")) {
                    const name = this.consumeTokenAndGetValue();
                    this.ensureAndConsumeToken("=");
                    let exp = this.parseOfExpression();

                    if (seenNames.has(name)) {
                        this.raiseError(line, "Cannot have duplicate named argument name");
                    }

                    if (name === "_") {
                        this.raiseError(line, `"_" is not a valid named parameter name`);
                    }
                    seenNames.add(name);

                    args.push(new NamedArgument(rref, name, exp));
                }
                else {
                    const isSpread = this.testAndConsumeTokenIf("...");
                    let exp = this.parseOfExpression();

                    args.push(new PositionalArgument(rref, isSpread, exp));
                }

                if (this.testAndConsumeTokenIf(",")) {
                    this.ensureNotToken(rparen);
                }
                else {
                    this.ensureToken(rparen);
                }
            }

            this.clearRecover();
            return new Arguments(args);
        }
        catch (ex) {
            this.processRecover();
            return new Arguments([new PositionalArgument(undefined, false, new InvalidExpression(argSrcInfo))]);
        }
    }

    private parseTemplateArguments(): TemplateArguments {
        try {
            this.setRecover(this.scanMatchingParens("<", ">"));
            let targs: TypeSignature[] = [];

            this.ensureAndConsumeToken("<");
            while (!this.testAndConsumeTokenIf(">")) {
                targs.push(this.parseTypeSignature(true));

                if (this.testAndConsumeTokenIf(",")) {
                    this.ensureNotToken(">");
                }
                else {
                    this.ensureToken(">");
                }
            }

            this.clearRecover();
            return new TemplateArguments(targs);
        }
        catch (ex) {
            this.processRecover();
            return new TemplateArguments([]);
        }
    }

    private parseRecursiveAnnotation(): RecursiveAnnotation {
        try {
            this.setRecover(this.scanMatchingParens("[", "]"));

            let recursive: "yes" | "no" | "cond" = "no";
            this.ensureAndConsumeToken("[");
            while (!this.testAndConsumeTokenIf("]")) {
                if (!this.testToken("recursive") && !this.testToken("recursive?")) {
                    this.raiseError(this.getCurrentLine(), "Expected recursive annotation");
                }

                if (recursive !== "no") {
                    this.raiseError(this.getCurrentLine(), "Multiple recursive annotations on call");
                }

                recursive = this.testToken("recursive") ? "yes" : "cond";
                this.consumeToken();

                if (this.testAndConsumeTokenIf(",")) {
                    this.ensureNotToken("]");
                }
                else {
                    this.ensureToken("]");
                }
            }

            this.clearRecover();
            return recursive;
        }
        catch (ex) {
            this.processRecover();
            return "no";
        }
    }

    private parseConstructorPrimary(otype: TypeSignature): Expression {
        const sinfo = this.getCurrentSrcInfo();

        if(!this.testToken("@") && !this.testToken("#")) {
            this.raiseError(sinfo.line, "Expected either @ or #");
        }

        const isvalue = this.testToken("#");
        this.consumeToken();

        const args = this.parseArguments("{", "}");

        return new ConstructorPrimaryExpression(sinfo, isvalue, otype, args);
    }

    private parseConstructorPrimaryWithFactory(otype: TypeSignature): Expression {
        const sinfo = this.getCurrentSrcInfo();

        if(!this.testToken("@") && !this.testToken("#")) {
            this.raiseError(sinfo.line, "Expected either @ or #");
        }

        const isvalue = this.testToken("#");
        this.consumeToken();
        this.ensureToken(TokenStrings.Identifier);

        const fname = this.consumeTokenAndGetValue();
        const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
        const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";
        const args = this.parseArguments("(", ")");

        return new ConstructorPrimaryWithFactoryExpression(sinfo, isvalue, otype, fname, rec, targs, args);
    }

    private parsePCodeTerm(): Expression {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();

        const isrecursive = this.testAndConsumeTokenIf("recursive");

        this.ensureAndConsumeToken("fn");
        const sig = this.parseInvokableCommon(InvokableKind.PCode, false, [], isrecursive ? "yes" : "no", [], undefined);
        const someAuto = sig.params.some((param) => param.type instanceof AutoTypeSignature) || (sig.optRestType !== undefined && sig.optRestType instanceof AutoTypeSignature) || (sig.resultType instanceof AutoTypeSignature);
        const allAuto = sig.params.every((param) => param.type instanceof AutoTypeSignature) && (sig.optRestType === undefined || sig.optRestType instanceof AutoTypeSignature) && (sig.resultType instanceof AutoTypeSignature);
        if (someAuto && !allAuto) {
            this.raiseError(line, "Cannot have mixed of auto propagated and explicit types on lambda arguments/return");
        }

        sig.captureSet.forEach((v) => {
            this.m_penv.useLocalVar(v);
        });

        return new ConstructorPCodeExpression(sinfo, allAuto, sig);
    }

    private parseFollowTypeTag(): TypeSignature {
        this.ensureAndConsumeToken("_");

        if (this.testToken(TokenStrings.Template)) {
            return this.parseTemplateTypeReference();
        }
        else {
            const line = this.getCurrentLine();

            let ns: string | undefined = undefined;
            if (this.testToken(TokenStrings.Namespace)) {
                ns = this.consumeTokenAndGetValue();
                this.ensureAndConsumeToken("::");
            }

            const tname = this.consumeTokenAndGetValue();
            ns = this.m_penv.tryResolveNamespace(ns, tname);
            if (ns === undefined) {
                this.raiseError(line, "Could not resolve namespace");
            }

            let tnames: string[] = [tname];
            let terms: TypeSignature[] = [];

            //
            //TODO: follow types -- used for stringof, datastring, and unit types cannot be template types
            //      maybe this is ok but we might want to allow it (at least for stringof/datastring)
            //

            return new NominalTypeSignature(ns as string, tnames, terms);
        }
    }

    private parseFollowTypeConstructor(): ["@" | "#" | undefined, TypeSignature] {
        let constype: "@" | "#" | undefined = undefined;
        if (this.testToken("@") || this.testToken("#")) {
            constype = this.consumeTokenAndGetValue() as "@" | "#";
        }

        this.ensureAndConsumeToken("(");

        if (this.testToken(TokenStrings.Template)) {
            this.ensureAndConsumeToken(")");
            return [constype, this.parseTemplateTypeReference()];
        }
        else {
            const line = this.getCurrentLine();

            let ns: string | undefined = undefined;
            if (this.testToken(TokenStrings.Namespace)) {
                ns = this.consumeTokenAndGetValue();
                this.ensureAndConsumeToken("::");
            }

            const tname = this.consumeTokenAndGetValue();
            ns = this.m_penv.tryResolveNamespace(ns, tname);
            if (ns === undefined) {
                this.raiseError(line, "Could not resolve namespace");
            }

            let tnames: string[] = [tname];
            let terms: TypeSignature[] = [];

            //
            //TODO: follow types -- used for stringof, datastring, and unit types cannot be template types
            //      maybe this is ok but we might want to allow it (at least for stringof/datastring)
            //

            this.ensureAndConsumeToken(")");
            return [constype, new NominalTypeSignature(ns as string, tnames, terms)];
        }
    }

    private processPrefixOnLiteralExpressionsIfNeeded(exp: Expression, op: "!" | "+" | "-"): [boolean, Expression] {
        if(op === "!") {
            if(exp instanceof LiteralBoolExpression) {
                return [true, new LiteralBoolExpression(exp.sinfo, !exp.value)];
            }
            else {
                return [false, exp];
            }
        }
        else {
            if(op === "+") {
                if(exp instanceof LiteralIntegralExpression) {
                    return [true, exp];
                }
                else if(exp instanceof LiteralRationalExpression) {
                    return [true, exp];
                }
                else if(exp instanceof LiteralFloatPointExpression) {
                    return [true, exp];
                }
                else {
                    return [false, exp];
                }
            }
            else {
                if(exp instanceof LiteralIntegralExpression) {
                    return [true, new LiteralIntegralExpression(exp.sinfo, exp.value.startsWith("-") ? exp.value.slice(1) : ("-" + exp.value), exp.itype)];
                }
                else if(exp instanceof LiteralRationalExpression) {
                    return [true, new LiteralRationalExpression(exp.sinfo, exp.value.startsWith("-") ? exp.value.slice(1) : ("-" + exp.value), exp.rtype)];
                }
                else if(exp instanceof LiteralFloatPointExpression) {
                    return [true, new LiteralFloatPointExpression(exp.sinfo, exp.value.startsWith("-") ? exp.value.slice(1) : ("-" + exp.value), exp.fptype)];
                }
                else {
                    return [false, exp];
                }
            }
        }
    }

    private parseLiteralExpressionPrimary(): Expression {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();

        const tk = this.peekToken();
        if (tk === "true" || tk === "false") {
            this.consumeToken();
            return new LiteralBoolExpression(sinfo, tk === "true");
        }
        else if(tk === TokenStrings.Numberino) {
            const niostr = this.consumeTokenAndGetValue();
            return new LiteralNumberinoExpression(sinfo, niostr);
        }
        else if (tk === TokenStrings.Int) {
            const istr = this.consumeTokenAndGetValue();
            return new LiteralIntegralExpression(sinfo, istr, this.m_penv.SpecialIntSignature);
        }
        else if (tk === TokenStrings.Nat) {
            const istr = this.consumeTokenAndGetValue();
            return new LiteralIntegralExpression(sinfo, istr.slice(0, istr.length - 1), this.m_penv.SpecialNatSignature);
        }
        else if (tk === "(") {
            try {
                this.setRecover(this.scanMatchingParens("(", ")"));

                this.consumeToken();
                const lexp = this.parseLiteralExpression();
                this.ensureAndConsumeToken(")");

                this.clearRecover();
                return lexp.exp;
            }
            catch (ex) {
                this.processRecover();
                return new InvalidExpression(sinfo);
            }
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Identifier)) {
            //it is a namespace access of some type
            const ns = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            if (this.testToken("<") || this.testToken("[") || this.testToken("(")) {
                this.raiseError(line, "Expected an namespace constant");
            }
            
            return new AccessNamespaceConstantExpression(sinfo, ns, name);
        }
        else {
            const ttype = this.parseTypeSignature(false);
            if (this.testFollows("::", TokenStrings.Identifier)) {
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                
                if (this.testToken("<") || this.testToken("[") || this.testToken("(")) {
                    this.raiseError(line, "Expected an namespace constant");
                }

                return new AccessStaticFieldExpression(sinfo, ttype, name);
            }
            else {
                this.raiseError(line, "Unknown token sequence in parsing expression");
                return new InvalidExpression(sinfo);
            }
        }
    }

    private parseLiteralExpressionPrefix(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        if (this.testAndConsumeTokenIf("!")) {
            const ee = this.parseLiteralExpressionPrefix();
            const [done, exp] = this.processPrefixOnLiteralExpressionsIfNeeded(ee, "!");
            if(!done) {
                return exp;
            }
            else {
                return new PrefixNotOp(sinfo, exp);
            }
        }
        else if(this.testToken("+") || this.testToken("-")) {
            const op = this.consumeTokenAndGetValue();
            const ee = this.parseLiteralExpressionPrefix();
            const [done, exp] = this.processPrefixOnLiteralExpressionsIfNeeded(ee, op as "+" | "-");
            
            if (done) {
                return exp;
            }
            else {
                const ons = this.m_penv.tryResolveAsPrefixUnaryOperator(op, 1);
                if (ons === undefined) {
                    this.raiseError(sinfo.line, "Could not resolve operator");
                }

                const arg = new PositionalArgument(undefined, false, exp);
                return new CallNamespaceFunctionOrOperatorExpression(sinfo, ons as string, op, new TemplateArguments([]), "no", new Arguments([arg]), "prefix");
            }
        }
        else {
            return this.parseLiteralExpressionPrimary();
        }
    }

    private parseLiteralTypedExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        const exp = this.parseLiteralExpressionPrefix();
        if (this.testToken("_")) {
            const ttype = this.parseFollowTypeTag();

            if (exp instanceof LiteralIntegralExpression) {
                return new LiteralTypedNumericConstructorExpression(sinfo, exp.value, exp.itype, ttype);
            }
            else if (exp instanceof LiteralFloatPointExpression) {
                return new LiteralTypedNumericConstructorExpression(sinfo, exp.value, exp.fptype, ttype);
            }
            else {
                if (!(exp instanceof LiteralRationalExpression)) {
                    this.raiseError(sinfo.line, "Expected literal value -- int, float, or rational");
                }

                const rexp = exp as LiteralRationalExpression;
                return new LiteralTypedNumericConstructorExpression(sinfo, rexp.value, rexp.rtype, ttype);
            }
        }
        else {
            return exp;
        }
    }

    private parseLiteralExpression(): LiteralExpressionValue {
        return new LiteralExpressionValue(this.parseLiteralTypedExpression());
    }

    private parseConstExpression(capturesok: boolean): ConstantExpressionValue {
        const sinfo = this.getCurrentSrcInfo();

        try {
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(), this.m_penv.SpecialAutoSignature, true));
            const exp = this.parseSelectExpression();
            const captured = this.m_penv.getCurrentFunctionScope().getCaptureVars();

            if(!capturesok && captured.size !== 0) {
                this.raiseError(sinfo.line, "Cannot reference local variables in constant expression");
            }

            this.m_penv.popFunctionScope();

            return new ConstantExpressionValue(exp, captured);
        }
        catch (ex) {
            this.m_penv.popFunctionScope();
            throw ex;
        }
    }

    private parsePrimaryExpression(): Expression {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();

        const tk = this.peekToken();
        if (tk === "none") {
            this.consumeToken();
            return new LiteralNoneExpression(sinfo);
        }
        else if (tk === "true" || tk === "false") {
            this.consumeToken();
            return new LiteralBoolExpression(sinfo, tk === "true");
        }
        else if (tk === "literal") {
            this.consumeToken();
            this.ensureAndConsumeToken("(")
            const ttype = this.parseTemplateTypeReference() as TemplateTypeSignature;
            this.ensureAndConsumeToken(")");
            return new LiteralParamerterValueExpression(sinfo, ttype);
        }
        else if(tk === TokenStrings.Numberino) {
            const niostr = this.consumeTokenAndGetValue();
            return new LiteralNumberinoExpression(sinfo, niostr);
        }
        else if (tk === TokenStrings.Int) {
            const istr = this.consumeTokenAndGetValue();
            return new LiteralIntegralExpression(sinfo, istr, this.m_penv.SpecialIntSignature);
        }
        else if (tk === TokenStrings.Nat) {
            const istr = this.consumeTokenAndGetValue();
            return new LiteralIntegralExpression(sinfo, istr, this.m_penv.SpecialNatSignature);
        }
        else if (tk === TokenStrings.Float) {
            const fstr = this.consumeTokenAndGetValue();
            return new LiteralFloatPointExpression(sinfo, fstr, this.m_penv.SpecialFloatSignature);
        }
        else if (tk === TokenStrings.Decimal) {
            const fstr = this.consumeTokenAndGetValue();
            return new LiteralFloatPointExpression(sinfo, fstr, this.m_penv.SpecialDecimalSignature);
        }
        else if (tk === TokenStrings.BigInt) {
            const istr = this.consumeTokenAndGetValue();
            return new LiteralIntegralExpression(sinfo, istr, this.m_penv.SpecialBigIntSignature);
        }
        else if (tk === TokenStrings.BigNat) {
            const istr = this.consumeTokenAndGetValue();
            return new LiteralIntegralExpression(sinfo, istr, this.m_penv.SpecialBigNatSignature);
        }
        else if (tk === TokenStrings.Rational) {
            const istr = this.consumeTokenAndGetValue();
            return new LiteralRationalExpression(sinfo, istr, this.m_penv.SpecialRationalSignature);
        }
        else if (tk === TokenStrings.String) {
            const sstr = this.consumeTokenAndGetValue(); //keep in escaped format
            return new LiteralStringExpression(sinfo, sstr);
        }
        else if (tk === TokenStrings.Regex) {
            const restr = this.consumeTokenAndGetValue(); //keep in escaped format
            const re = BSQRegex.parse(restr);
            if(typeof(re) === "string") {
                this.raiseError(line, re);
            }

            this.m_penv.assembly.addLiteralRegex(re as BSQRegex);
            return new LiteralRegexExpression(sinfo, re as BSQRegex);
        }
        else if (tk === "ok" || tk === "err") {
            this.consumeToken();
            this.ensureAndConsumeToken("(");
            const arg = this.parseOfExpression();
            this.ensureAndConsumeToken(")");

            return new SpecialConstructorExpression(sinfo, this.m_penv.getCurrentFunctionScope().getReturnType(), tk, arg);
        }
        else if (tk === TokenStrings.Identifier) {
            let namestr = this.consumeTokenAndGetValue();

            const isvar = this.m_penv.isVarDefinedInAnyScope(namestr) || namestr.startsWith("$");
            if (isvar) {
                const istr = this.m_penv.useLocalVar(namestr);

                if (this.testToken("[")) {
                    const rec = this.parseRecursiveAnnotation();
                    const args = this.parseArguments("(", ")");
                    return new PCodeInvokeExpression(sinfo, istr, rec, args);
                }
                else if (this.testToken("(")) {
                    const args = this.parseArguments("(", ")");
                    return new PCodeInvokeExpression(sinfo, istr, "no", args);
                }
                else {
                    return new AccessVariableExpression(sinfo, istr);
                }
            }
            else {
                const ns = this.m_penv.tryResolveNamespace(undefined, namestr);
                if (ns === undefined) {
                    this.raiseError(line, `Cannot resolve namespace for "${namestr}"`);
                }

                const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
                const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";
                const args = this.parseArguments("(", ")");

                return new CallNamespaceFunctionOrOperatorExpression(sinfo, ns as string, namestr, targs, rec, args, "std");
            }
        }
        else if (tk === TokenStrings.Operator) {
            const istr = this.consumeTokenAndGetValue();
            const ns = this.m_penv.tryResolveNamespace(undefined, istr);
            if (ns === undefined) {
                this.raiseError(line, "Cannot resolve namespace for invoke");
            }

            const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";
            const args = this.parseArguments("(", ")");

            return new CallNamespaceFunctionOrOperatorExpression(sinfo, ns as string, istr, new TemplateArguments([]), rec, args, "std");
        }
        else if (tk === "fn" || this.testFollows("recursive", "fn")) {
            return this.parsePCodeTerm();
        }
        else if (tk === "(") {
            try {
                this.setRecover(this.scanMatchingParens("(", ")"));

                this.consumeToken();
                const exp = this.parseExpression();
                this.ensureAndConsumeToken(")");

                this.clearRecover();
                return exp;
            }
            catch (ex) {
                this.processRecover();
                return new InvalidExpression(sinfo);
            }
        }
        else if (this.testToken("#") || this.testToken("@")) {
            const isvalue = this.testToken("#");
            this.consumeToken();

            if (this.testToken("[")) {
                const args = this.parseArguments("[", "]");
                return new ConstructorTupleExpression(sinfo, isvalue, args);
            }
            else {
                const args = this.parseArguments("{", "}");
                return new ConstructorRecordExpression(sinfo, isvalue, args);
            }
        }
        else if (this.testToken("(|")) {
            const args = this.parseArguments("(|", "|)");
            return new ConstructorEphemeralValueList(sinfo, args);
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Identifier)) {
            //it is a namespace access of some type
            const ns = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            if (!this.testToken("<") && !this.testToken("[") && !this.testToken("(")) {
                //just a constant access
                return new AccessNamespaceConstantExpression(sinfo, ns, name);
            }
            else {
                const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
                const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";
                const args = this.parseArguments("(", ")");

                return new CallNamespaceFunctionOrOperatorExpression(sinfo, ns, name, targs, rec, args, "std");
            }
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Operator)) {
            //it is a namespace access of some type
            const ns = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";
            const args = this.parseArguments("(", ")");

            return new CallNamespaceFunctionOrOperatorExpression(sinfo, ns, name, new TemplateArguments([]), rec, args, "std");
        }
        else {
            const ttype = this.parseTypeSignature(false);
            if (this.testFollows("::", TokenStrings.Identifier)) {
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                if (!this.testToken("<") && !this.testToken("[") && !this.testToken("(")) {
                    //just a static access
                    return new AccessStaticFieldExpression(sinfo, ttype, name);
                }
                else {
                    const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
                    const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";
                    const args = this.parseArguments("(", ")");

                    return new CallStaticFunctionOrOperatorExpression(sinfo, ttype, name, targs, rec, args, "std");
                }
            }
            else if (this.testFollows("@", TokenStrings.Identifier) || this.testFollows("#", TokenStrings.Identifier)) {
                return this.parseConstructorPrimaryWithFactory(ttype);
            }
            else if (this.testFollows("@", "{") || this.testFollows("#", "{")) {
                return this.parseConstructorPrimary(ttype);
            }
            else {
                this.raiseError(line, "Unknown token sequence in parsing expression");
                return new InvalidExpression(sinfo);
            }
        }
    }
    
    private literalPrefixStackAndTypedConstructorHandler(ops: ("!" | "+" | "-")[]): [Expression, ("!" | "+" | "-")[]] {
        const sinfo = this.getCurrentSrcInfo();

        if (this.testToken(TokenStrings.TypedString)) {
            const tstring = this.consumeTokenAndGetValue();
            const [cinfo, ttype] = this.parseFollowTypeConstructor();

            if (cinfo === undefined) {
                return [new LiteralTypedStringExpression(sinfo, tstring, ttype), ops];
            }
            else {
                return [new LiteralTypedStringConstructorExpression(sinfo, cinfo === "#", tstring, ttype), ops];
            }
        }
        else {
            let exp = this.parsePrimaryExpression();

            let cpos = 0;
            while(cpos < ops.length) {
                const op = ops[cpos];

                let done = false;
                [done, exp] = this.processPrefixOnLiteralExpressionsIfNeeded(exp, op);
                if (done) {
                    break;
                }

                cpos++;
            }
            
            const rops = ops.slice(cpos);
            if (this.testToken("_")) {
                const ttype = this.parseFollowTypeTag();

                if(exp instanceof LiteralIntegralExpression) {
                    return [new LiteralTypedNumericConstructorExpression(sinfo, exp.value, exp.itype, ttype), rops];
                }
                else if(exp instanceof LiteralFloatPointExpression) {
                    return [new LiteralTypedNumericConstructorExpression(sinfo, exp.value, exp.fptype, ttype), rops];
                }
                else {
                    if(!(exp instanceof LiteralRationalExpression)) {
                        this.raiseError(sinfo.line, "Expected literal value -- int, float, or rational");
                    }

                    const rexp = exp as LiteralRationalExpression;
                    return [new LiteralTypedNumericConstructorExpression(sinfo, rexp.value, rexp.rtype, ttype), rops];
                }
            }
            else {
                return [exp, rops];
            }
        }
    }

    private parseTupleIndex(): number {
        if(this.testToken(TokenStrings.Numberino)) {
            const niov = this.consumeTokenAndGetValue();
            return Number.parseInt(niov);
        }
        else if(this.testToken(TokenStrings.Int)) {
            const iv = this.consumeTokenAndGetValue();
            return Number.parseInt(iv.substr(0, iv.length - 1));
        }
        else if(this.testToken(TokenStrings.Nat)) {
            const nv = this.consumeTokenAndGetValue();
            return Number.parseInt(nv.substr(0, nv.length - 1));
        }
        else {
            this.raiseError(this.getCurrentSrcInfo().line, "Expected an Int or a Nat literal");
            return -1;
        }
    }

    private handleSpecialCaseMethods(sinfo: SourceInfo, isElvis: boolean, customCheck: Expression | undefined, specificResolve: TypeSignature | undefined, name: string): PostfixOperation {
        if (specificResolve !== undefined) {
            this.raiseError(this.getCurrentLine(), "Cannot use specific resolve on special methods");
        }

        const line = sinfo.line;
        if (name === "is") {
            this.ensureAndConsumeToken("<");
            const istype = this.parseTypeSignature(true);
            this.ensureAndConsumeToken(">");
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");

            return new PostfixIs(sinfo, isElvis, customCheck, istype);
        }
        else if (name === "isSome") {
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");

            return new PostfixIs(sinfo, isElvis, customCheck, this.m_penv.SpecialSomeSignature);
        }
        else if (name === "isNone") {
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");

            return new PostfixIs(sinfo, isElvis, customCheck, this.m_penv.SpecialNoneSignature);
        }
        else if (name === "as") {
            this.ensureAndConsumeToken("<");
            const astype = this.parseTypeSignature(true);
            this.ensureAndConsumeToken(">");
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");

            return new PostfixAs(sinfo, isElvis, customCheck, astype);
        }
        else if (name === "hasIndex") {
            this.ensureAndConsumeToken("<");
            const idx = this.parseTupleIndex();
            this.ensureAndConsumeToken(">");
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");
            return new PostfixHasIndex(sinfo, isElvis, customCheck, idx);
        }
        else if (name === "hasProperty") {
            this.ensureAndConsumeToken("<");
            this.ensureToken(TokenStrings.Identifier);
            const pname = this.consumeTokenAndGetValue(); 
            this.ensureAndConsumeToken(">");
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");
            return new PostfixHasProperty(sinfo, isElvis, customCheck, pname);
        }
        else if (name === "getIndexOrNone") {
            this.ensureAndConsumeToken("<");
            const idx = this.parseTupleIndex();
            this.ensureAndConsumeToken(">");
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");
            return new PostfixGetIndexOrNone(sinfo, isElvis, customCheck, idx);
        }
        else if (name === "getIndexTry") {
            this.ensureAndConsumeToken("<");
            const idx = this.parseTupleIndex();
            this.ensureAndConsumeToken(">");
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken("out?");
            this.ensureToken(TokenStrings.Identifier);
            const exp = this.consumeTokenAndGetValue();
            this.ensureAndConsumeToken(")");
            return new PostfixGetIndexTry(sinfo, isElvis, customCheck, idx, exp);
        }
        else if (name === "getPropertyOrNone") {
            this.ensureAndConsumeToken("<");
            this.ensureToken(TokenStrings.Identifier);
            const pname = this.consumeTokenAndGetValue(); 
            this.ensureAndConsumeToken(">");
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");
            return new PostfixGetPropertyOrNone(sinfo, isElvis, customCheck, pname);
        }
        else if (name === "getPropertyTry") {
            this.ensureAndConsumeToken("<");
            this.ensureToken(TokenStrings.Identifier);
            const pname = this.consumeTokenAndGetValue(); 
            this.ensureAndConsumeToken(">");
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken("out?");
            this.ensureToken(TokenStrings.Identifier);
            const exp = this.consumeTokenAndGetValue();
            this.ensureAndConsumeToken(")");
            return new PostfixGetPropertyTry(sinfo, isElvis, customCheck, pname, exp);
        }
        else {
            this.raiseError(line, "unknown special operation");
            return (undefined as unknown) as PostfixOperation;
        }
    }

    private parsePostfixExpression(pfxops: ("!" | "+" | "-")[]): [Expression, ("!" | "+" | "-")[]] {
        const rootinfo = this.getCurrentSrcInfo();
        let [rootexp, remainingops] = this.literalPrefixStackAndTypedConstructorHandler(pfxops);

        let ops: PostfixOperation[] = [];
        while (true) {
            const sinfo = this.getCurrentSrcInfo();

            if (this.testFollows(".") || this.testElvisFollows(".")) {
                const isElvis = this.testAndConsumeTokenIf("?");
                const customCheck = isElvis ? this.parseElvisCheck(sinfo) : undefined;

                this.ensureAndConsumeToken(".");
                const isBinder = this.testAndConsumeTokenIf("$");

                if (this.testToken(TokenStrings.Numberino) || this.testToken(TokenStrings.Int) || this.testToken(TokenStrings.Nat)) {
                    if(isBinder) {
                        this.raiseError(sinfo.line, "Cannot use binder in this position");
                    }

                    const index = this.parseTupleIndex();
                    ops.push(new PostfixAccessFromIndex(sinfo, isElvis, customCheck, index));
                }
                else if (this.testFollows("#", "[") || this.testFollows("@", "[")) {
                    const isvalue = this.testToken("#");
                    this.consumeToken();

                    if (this.testFollows(TokenStrings.Numberino, "=") ||this.testFollows(TokenStrings.Int, "=") || this.testFollows(TokenStrings.Nat, "=")) {
                        const updates = this.parseListOf<{ index: number, value: Expression }>("(", ")", ",", () => {
                            const idx = this.parseTupleIndex();
                            this.ensureAndConsumeToken("=");

                            try {
                                this.m_penv.getCurrentFunctionScope().pushLocalScope();
                                this.m_penv.getCurrentFunctionScope().defineLocalVar(`$${idx}`, `$${idx}_#${sinfo.pos}`, true);
                                
                                if (isBinder) {    
                                    this.m_penv.getCurrentFunctionScope().defineLocalVar(`$this`, `$this_#${sinfo.pos}`, true);
                                }

                                const value = this.parseOfExpression();
                                return { index: idx, value: value };
                            }
                            finally {
                                this.m_penv.getCurrentFunctionScope().popLocalScope();
                            }
                        })[0].sort((a, b) => a.index - b.index);

                        ops.push(new PostfixModifyWithIndecies(sinfo, isElvis, customCheck, isBinder, updates));
                    }
                    else {
                        if (isBinder) {
                            this.raiseError(sinfo.line, "Cannot use binder in this position");
                        }

                        const indecies = this.parseListOf<{ index: number, reqtype: TypeSignature | undefined }>("[", "]", ",", () => {
                            const idx = this.parseTupleIndex();

                            if (!this.testAndConsumeTokenIf(":")) {
                                return { index: idx, reqtype: undefined };
                            }
                            else {
                                return { index: idx, reqtype: this.parseTypeSignature(false) };
                            }
                        })[0];

                        if (indecies.length === 0) {
                            this.raiseError(sinfo.line, "You must have at least one index when projecting");
                        }

                        ops.push(new PostfixProjectFromIndecies(sinfo, isElvis, undefined, isvalue, false, indecies));
                    }
                }
                else if (this.testFollows("#", "{") || this.testFollows("@", "{")) {
                    const isvalue = this.testToken("#");
                    this.consumeToken();

                    if (this.testFollows(TokenStrings.Identifier, "=")) {
                        const updates = this.parseListOf<{ name: string, value: Expression }>("(", ")", ",", () => {
                            this.ensureToken(TokenStrings.Identifier);
                            const uname = this.consumeTokenAndGetValue();
                            this.ensureAndConsumeToken("=");

                            try {
                                this.m_penv.getCurrentFunctionScope().pushLocalScope();
                                this.m_penv.getCurrentFunctionScope().defineLocalVar(`$${uname}`, `$${uname}_#${sinfo.pos}`, true);

                                if (isBinder) {    
                                    this.m_penv.getCurrentFunctionScope().defineLocalVar(`$this`, `$this_#${sinfo.pos}`, true);
                                }

                                const value = this.parseOfExpression();
                                return { name: uname, value: value };
                            }
                            finally {
                                if (isBinder) {
                                    this.m_penv.getCurrentFunctionScope().popLocalScope();
                                }
                            }
                        })[0].sort((a, b) => a.name.localeCompare(b.name));

                        ops.push(new PostfixModifyWithNames(sinfo, isElvis, customCheck, isBinder, updates));
                    }
                    else {
                        if (isBinder) {
                            this.raiseError(sinfo.line, "Cannot use binder in this position");
                        }

                        const names = this.parseListOf<{ name: string, reqtype: TypeSignature | undefined }>("{", "}", ",", () => {
                            this.ensureToken(TokenStrings.Identifier);
                            const nn = this.consumeTokenAndGetValue();

                            if (!this.testAndConsumeTokenIf(":")) {
                                return { name: nn, reqtype: undefined };
                            }
                            else {
                                return { name: nn, reqtype: this.parseTypeSignature(false) };
                            }
                        })[0];

                        if (names.length === 0) {
                            this.raiseError(sinfo.line, "You must have at least one name when projecting");
                        }

                        ops.push(new PostfixProjectFromNames(sinfo, isElvis, customCheck, isvalue, false, names));
                    }
                }
                else if(this.testToken("(|")) {
                    if (isBinder) {
                        this.raiseError(sinfo.line, "Cannot use binder in this position");
                    }

                    if (this.testFollows("(|", TokenStrings.Numberino) || this.testFollows("(|", TokenStrings.Int) || this.testFollows("(|", TokenStrings.Nat)) {
                        const indecies = this.parseListOf<{ index: number, reqtype: TypeSignature | undefined }>("(|", "|)", ",", () => {
                            const idx = this.parseTupleIndex();
                            
                            if (!this.testAndConsumeTokenIf(":")) {
                                return { index: idx, reqtype: undefined};
                            }
                            else {
                                return { index: idx, reqtype: this.parseTypeSignature(false) };
                            }
                        })[0];

                        if (indecies.length <= 1) {
                            this.raiseError(sinfo.line, "You must have at least two indecies when projecting out a Ephemeral value pack (otherwise just access the index directly)");
                        }

                        ops.push(new PostfixProjectFromIndecies(sinfo, isElvis, customCheck, false, true, indecies));
                    }
                    else {
                        const names = this.parseListOf<{ name: string, isopt: boolean, reqtype: TypeSignature | undefined }>("(|", "|)", ",", () => {
                            this.ensureToken(TokenStrings.Identifier);
                            const nn = this.consumeTokenAndGetValue();
                            if(this.testAndConsumeTokenIf("?")) {
                                this.raiseError(sinfo.line, "Cannot have optional part in Ephemeral List projection");
                            }

                            if (!this.testAndConsumeTokenIf(":")) {
                                return { name: nn, isopt: false, reqtype: undefined };
                            }
                            else {
                                return { name: nn, isopt: false, reqtype: this.parseTypeSignature(false) };
                            }
                        })[0];

                        if (names.length <= 1) {
                            this.raiseError(sinfo.line, "You must have at least two names when projecting out a Ephemeral value pack (otherwise just access the property/field directly)");
                        }

                        ops.push(new PostfixProjectFromNames(sinfo, isElvis, customCheck, false, true, names));
                    }
                }
                else {
                    let specificResolve: TypeSignature | undefined = undefined;
                    if (this.testToken(TokenStrings.Namespace) || this.testToken(TokenStrings.Type) || this.testToken(TokenStrings.Template)) {
                        specificResolve = this.parseTypeSignature(false);
                        this.ensureAndConsumeToken("::");
                    }

                    this.ensureToken(TokenStrings.Identifier);
                    const name = this.consumeTokenAndGetValue();

                    if (name === "as" || name === "is" || name === "isSome" || name === "isNone" 
                        || name === "hasIndex" || "getIndexOrNone" || "getIndexTry" 
                        || name === "hasProperty" || "getPropertyOrNone" || "getPropertyTry") {
                        ops.push(this.handleSpecialCaseMethods(sinfo, isElvis, customCheck, specificResolve, name));
                    }
                    else if (!(this.testToken("<") || this.testToken("[") || this.testToken("("))) {
                        if (isBinder) {
                            this.raiseError(sinfo.line, "Cannot use binder in this position");
                        }

                        if (specificResolve !== undefined) {
                            this.raiseError(this.getCurrentLine(), "Encountered named access but given type resolver (only valid on method calls)");
                        }

                        ops.push(new PostfixAccessFromName(sinfo, isElvis, customCheck, name));
                    }
                    else {
                        //ugly ambiguity with < -- the follows should be a NS, Type, or T token
                        //    this.f.g < (1 + 2) and this.f.g<(Int)>() don't know with bounded lookahead :(
                        //
                        //TODO: in theory it could also be a "(" and we need to do a tryParseType thing OR just disallow () in this position
                        //
                        if (this.testToken("<")) {
                            if (this.testFollows("<", TokenStrings.Namespace) || this.testFollows("<", TokenStrings.Type) || this.testFollows("<", TokenStrings.Template)) {
                                const terms = this.parseTemplateArguments();
                                const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";

                                try {
                                    if (isBinder) {
                                        this.m_penv.getCurrentFunctionScope().pushLocalScope();
                                        this.m_penv.getCurrentFunctionScope().defineLocalVar(`$this`, `$this_#${sinfo.pos}`, true);
                                    }

                                    const args = this.parseArguments("(", ")");
                                    ops.push(new PostfixInvoke(sinfo, isElvis, customCheck, isBinder, specificResolve, name, terms, rec, args));
                                }
                                finally {
                                    if (isBinder) {
                                        this.m_penv.getCurrentFunctionScope().popLocalScope();
                                    }
                                }
                            }
                            else {
                                if (isBinder) {
                                    this.raiseError(sinfo.line, "Cannot use binder in this position");
                                }

                                if (specificResolve !== undefined) {
                                    this.raiseError(this.getCurrentLine(), "Encountered named access but given type resolver (only valid on method calls)");
                                }

                                ops.push(new PostfixAccessFromName(sinfo, isElvis, customCheck, name));
                            }
                        }
                        else {
                            const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";

                            try {
                                if (isBinder) {
                                    this.m_penv.getCurrentFunctionScope().pushLocalScope();
                                    this.m_penv.getCurrentFunctionScope().defineLocalVar(`$this`, `$this_#${sinfo.pos}`, true);
                                }

                                const args = this.parseArguments("(", ")");
                                ops.push(new PostfixInvoke(sinfo, isElvis, customCheck, isBinder, specificResolve, name, new TemplateArguments([]), rec, args));
                            }
                            finally {
                                if (isBinder) {
                                    this.m_penv.getCurrentFunctionScope().popLocalScope();
                                }
                            }
                        }
                    }
                }
            }
            else {
                if (ops.length === 0) {
                    return [rootexp, remainingops];
                }
                else {
                    return [new PostfixOp(rootinfo, rootexp, ops), remainingops];
                }
            }
        }
    }

    private parseStatementExpression(ops: ("!" | "+" | "-")[]): [Expression, ("!" | "+" | "-")[]] {
        if (this.testToken("{|")) {
            return [this.parseBlockStatementExpression(), ops];
        }
        else if (this.testToken("if")) {
            return [this.parseIfExpression(), ops];
        }
        else if (this.testToken("switch")) {
            return [this.parseMatchExpression(), ops];
        }
        else {
            return this.parsePostfixExpression(ops);
        }
    }

    private prefixStackApplicationHandler(sinfo: SourceInfo, ops: ("!" | "+" | "-")[]): Expression {
        let [exp, remainingops] = this.parseStatementExpression(ops);
        
        for (let i = 0; i < remainingops.length; ++i) {
            const op = remainingops[i];

            if (op === "!") {
                exp = new PrefixNotOp(sinfo, exp);
            }
            else {
                const ons = this.m_penv.tryResolveAsPrefixUnaryOperator(op, 1);
                if (ons === undefined) {
                    this.raiseError(sinfo.line, "Could not resolve operator");
                }

                const arg = new PositionalArgument(undefined, false, exp);
                return new CallNamespaceFunctionOrOperatorExpression(sinfo, ons as string, op, new TemplateArguments([]), "no", new Arguments([arg]), "prefix");
            }
        }

        return exp;
    }

    private parsePrefixExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        let ops:  ("!" | "+" | "-")[] = [];
        while(this.testToken("!") || this.testToken("+") || this.testToken("-")) {
            ops.push(this.consumeTokenAndGetValue() as "!" | "+" | "-");
        }

        return this.prefixStackApplicationHandler(sinfo, ops);
    }

    private parseMultiplicativeExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parsePrefixExpression();

        if(this.testToken("*") || this.testToken("/") || this.testToken(TokenStrings.Operator)) {
            const ons = this.m_penv.tryResolveAsInfixBinaryOperator(this.peekTokenData(), 2);
            if(ons === undefined) {
                this.raiseError(sinfo.line, "Could not resolve operator");
            }

            const op = this.consumeTokenAndGetValue();
            const lhs = new PositionalArgument(undefined, false, exp);
            const rhs = new PositionalArgument(undefined, false, this.parseMultiplicativeExpression());
            return new CallNamespaceFunctionOrOperatorExpression(sinfo, ons as string, op, new TemplateArguments([]), "no", new Arguments([lhs, rhs]), "infix");
        }
        else {
            return exp;
        }
    }

    private parseAdditiveExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseMultiplicativeExpression();

        if(this.testToken("+") || this.testToken("-") || this.testToken(TokenStrings.Operator)) {
            const ons = this.m_penv.tryResolveAsInfixBinaryOperator(this.peekTokenData(), 3);
            if (ons === undefined) {
                this.raiseError(sinfo.line, "Could not resolve operator");
            }

            const op = this.consumeTokenAndGetValue();
            const lhs = new PositionalArgument(undefined, false, exp);
            const rhs = new PositionalArgument(undefined, false, this.parseAdditiveExpression());
            return new CallNamespaceFunctionOrOperatorExpression(sinfo, ons as string, op, new TemplateArguments([]), "no", new Arguments([lhs, rhs]), "infix");
        }
        else {
            return exp;
        }
    }

    private parseRelationalExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseAdditiveExpression();

        if (this.testToken("===") || this.testToken("!==")) {
            const op = this.consumeTokenAndGetValue();
            return new BinKeyExpression(sinfo, exp, op, this.parseRelationalExpression());
        }
        else if(this.testToken("==") || this.testToken("!=")
            || this.testToken("<") || this.testToken(">") || this.testToken("<=") || this.testToken(">=")
            || this.testToken(TokenStrings.Operator)) {
            const ons = this.m_penv.tryResolveAsInfixBinaryOperator(this.peekTokenData(), 4);
            if (ons === undefined) {
                this.raiseError(sinfo.line, "Could not resolve operator");
            }

            const op = this.consumeTokenAndGetValue();
            const lhs = new PositionalArgument(undefined, false, exp);
            const rhs = new PositionalArgument(undefined, false, this.parseRelationalExpression());
            return new CallNamespaceFunctionOrOperatorExpression(sinfo, ons as string, op, new TemplateArguments([]), "no", new Arguments([lhs, rhs]), "infix");
        }
        else {
            return exp;
        }
    }

    private parseNonecheckExpression(): Expression {
        const exp = this.parseRelationalExpression();

        if (this.testElvisFollows("&")) {
            const sinfo = this.getCurrentSrcInfo();
            this.consumeToken();
            const customCheck = this.parseElvisCheck(sinfo);
            this.consumeToken();
            return new NonecheckExpression(sinfo, exp, customCheck, this.parseNonecheckExpression());
        }
        else {
            return exp;
        }
    }

    private parseCoalesceExpression(): Expression {
        const exp = this.parseNonecheckExpression();

        if (this.testElvisFollows("|")) {
            const sinfo = this.getCurrentSrcInfo();
            this.consumeToken();
            const customCheck = this.parseElvisCheck(sinfo);
            this.consumeToken();
            return new CoalesceExpression(sinfo, exp, customCheck, this.parseCoalesceExpression());
        }
        else {
            return exp;
        }
    }

    private parseImpliesExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseCoalesceExpression();

        if (this.testAndConsumeTokenIf("==>")) {
            return new BinLogicExpression(sinfo, exp, "==>", this.parseImpliesExpression());
        }
        else {
            return exp;
        }
    }

    private parseAndExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseImpliesExpression();

        if (this.testAndConsumeTokenIf("&&")) {
            return new BinLogicExpression(sinfo, exp, "&&", this.parseAndExpression());
        }
        else {
            return exp;
        }
    }

    private parseOrExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseAndExpression();

        if (this.testAndConsumeTokenIf("||")) {
            return new BinLogicExpression(sinfo, exp, "||", this.parseOrExpression());
        }
        else {
            return exp;
        }
    }

    private parseMapEntryConstructorExpression(disallowMapEntry?: boolean): Expression {
        const sinfo = this.getCurrentSrcInfo();

        if(disallowMapEntry) {
            return this.parseOrExpression();
        }
        else {
            let lexp = this.testToken("(") ? this.parseOfExpression() : this.parseOrExpression();
            let leftof: TypeSignature | undefined = undefined;
            if(this.testToken("of")) {
                leftof = this.parseTypeSignature(true);

                if(lexp instanceof OfTypeConvertExpression) {
                    this.raiseError(sinfo.line, "Nested 'of' expression here");
                }
            }
            
            if(this.testAndConsumeTokenIf("=>")) {
                let rexp = this.testToken("(") ? this.parseOfExpression() : this.parseOrExpression();
                let rightof: TypeSignature | undefined = undefined;
                if (this.testToken("of")) {
                    rightof = this.parseTypeSignature(true);

                    if(rexp instanceof OfTypeConvertExpression) {
                        this.raiseError(sinfo.line, "Nested 'of' expression here");
                    }
                }

                return new MapEntryConstructorExpression(sinfo, leftof !== undefined ? new OfTypeConvertExpression(lexp.sinfo, lexp, leftof) : lexp, rightof !== undefined ? new OfTypeConvertExpression(rexp.sinfo, rexp, rightof) : rexp);
            }
            else {
                if(leftof !== undefined) {
                    this.raiseError(sinfo.line, "Cannot use expression 'of' in this position");
                }

                return lexp;
            }
        }
    }

    private parseSelectExpression(disallowMapEntry?: boolean): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const texp = this.parseMapEntryConstructorExpression(disallowMapEntry);

        if (this.testAndConsumeTokenIf("?")) {
            const exp1 = this.parseMapEntryConstructorExpression(disallowMapEntry);
            this.ensureAndConsumeToken(":");
            const exp2 = this.parseSelectExpression(disallowMapEntry);

            return new SelectExpression(sinfo, texp, exp1, exp2);
        }
        else {
            return texp;
        }
    }

    private parseExpOrExpression(): Expression {
        const texp = this.parseSelectExpression();

        if (this.testFollows("?", "none", "?") || this.testFollows("?", "err", "?") || this.testElvisFollows("?")) {
            const ffsinfo = this.getCurrentSrcInfo();
            this.consumeToken();

            try {
                this.m_penv.getCurrentFunctionScope().pushLocalScope();
                this.m_penv.getCurrentFunctionScope().defineLocalVar("$value", `$value_#${ffsinfo.pos}`, true);

                let cond: Expression | "none" | "err" = "none";
                let action: "return" | "yield" = "return";
                if (this.testAndConsumeTokenIf("none")) {
                    cond = "none";
                }
                else if (this.testAndConsumeTokenIf("err")) {
                    cond = "err";
                }
                else {
                    cond = this.parseElvisCheck(ffsinfo) as Expression;
                }
                this.consumeToken();

                if (this.testToken("return") || this.testToken("yield")) {
                    action = this.consumeTokenAndGetValue() as "return" | "yield";
                }

                let value: Expression[] | undefined = undefined;
                if (!this.testToken(";")) {
                    value = this.parseEphemeralListOf(() => this.parseExpression());
                }

                return new ExpOrExpression(ffsinfo, texp, action, value, cond);
            }
            finally {
                this.m_penv.popFunctionScope();
            }
        }
        else {
            return texp;
        }
    }

    private parseBlockStatementExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        this.m_penv.getCurrentFunctionScope().pushLocalScope();
        let stmts: Statement[] = [];
        try {
            this.setRecover(this.scanMatchingParens("{|", "|}"));

            this.consumeToken();
            while (!this.testAndConsumeTokenIf("|}")) {
                stmts.push(this.parseStatement());
            }

            this.m_penv.getCurrentFunctionScope().popLocalScope();

            this.clearRecover();
            return new BlockStatementExpression(sinfo, stmts);
        }
        catch (ex) {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
            this.processRecover();
            return new BlockStatementExpression(sinfo, [new InvalidStatement(sinfo)]);
        }
    }

    private parseIfExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        let conds: CondBranchEntry<Expression>[] = [];

        this.ensureAndConsumeToken("if");
        this.ensureAndConsumeToken("(");
        const iftest = this.parseExpression();
        this.ensureAndConsumeToken(")");

        const ifbody = this.parseExpression();
        conds.push(new CondBranchEntry<Expression>(iftest, ifbody));

        while (this.testAndConsumeTokenIf("elif")) {
            this.ensureAndConsumeToken("(");
            const eliftest = this.parseExpression();
            this.ensureAndConsumeToken(")");
            const elifbody = this.parseExpression();

            conds.push(new CondBranchEntry<Expression>(eliftest, elifbody));
        }

        this.ensureAndConsumeToken("else");
        const elsebody = this.parseExpression();

        return new IfExpression(sinfo, new IfElse<Expression>(conds, elsebody));
    }

    private parseMatchExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        this.ensureAndConsumeToken("switch");

        this.ensureAndConsumeToken("(");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(")");

        try {
            this.m_penv.getCurrentFunctionScope().pushLocalScope();
            this.m_penv.getCurrentFunctionScope().defineLocalVar("$match", `$match_#${sinfo.pos}`, true);
            
            let entries: MatchEntry<Expression>[] = [];
            this.ensureAndConsumeToken("{");
            while (this.testToken("type") || this.testToken("case") || (this.testToken(TokenStrings.Identifier) && this.peekTokenData() === "_")) {
                if (this.testToken("type")) {
                    entries.push(this.parseMatchEntry<Expression>(this.getCurrentSrcInfo(), true, "type", () => this.parseExpression()));
                }
                else {
                    entries.push(this.parseMatchEntry<Expression>(this.getCurrentSrcInfo(), true, "case", () => this.parseExpression()));
                }
            }
            this.ensureAndConsumeToken("}");

            return new MatchExpression(sinfo, mexp, entries);
        }
        finally {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
        }
    }

    private parseExpression(): Expression {
        return this.parseExpOrExpression();
    }

    private parseOfExpression(): Expression {
        //either E | E of T or (E of T)
        if (this.testToken("(")) {
            const epos = this.scanMatchingParens("(", ")");
            if (epos !== this.m_epos && this.peekToken(epos + 1) === "of") {
                //(E) of T
                let exp = this.parseSelectExpression();
                this.ensureAndConsumeToken("of");

                const sinfo = this.getCurrentSrcInfo();
                const oftype = this.parseTypeSignature(true);
                return new OfTypeConvertExpression(sinfo, exp, oftype);
            }
            else {
                //(E [of T]?)
                this.ensureAndConsumeToken("(");
                let exp = this.parseSelectExpression();

                if (this.testAndConsumeTokenIf("of")) {
                    const sinfo = this.getCurrentSrcInfo();
                    const oftype = this.parseTypeSignature(true);
                    exp = new OfTypeConvertExpression(sinfo, exp, oftype);
                }
                this.ensureAndConsumeToken(")");

                return exp;
            }
        }
        else {
            let exp = this.parseSelectExpression();

            if (this.testAndConsumeTokenIf("of")) {
                const sinfo = this.getCurrentSrcInfo();
                const oftype = this.parseTypeSignature(true);
                exp = new OfTypeConvertExpression(sinfo, exp, oftype);
            }

            return exp;
        }
    }

    ////
    //Statement parsing

    parseSimpleStructuredAssignment(sinfo: SourceInfo, vars: "let" | "var" | undefined, decls: Set<string>): StructuredAssignment {
        if (!this.testToken(TokenStrings.Identifier)) {
            const expr = this.parseConstExpression(false);
            return new ConstValueStructuredAssignment(expr);
        }
        else {
            this.ensureToken(TokenStrings.Identifier);
            const name = this.consumeTokenAndGetValue();

            if (name === "_") {
                const isopt = this.testAndConsumeTokenIf("?");

                let itype = this.m_penv.SpecialAnySignature;
                if (this.testAndConsumeTokenIf(":")) {
                    itype = this.parseTypeSignature(false);
                }

                return new IgnoreTermStructuredAssignment(isopt, itype);
            }
            else {
                let itype = this.m_penv.SpecialAutoSignature;
                if (this.testAndConsumeTokenIf(":")) {
                    itype = this.parseTypeSignature(false);
                }

                if (vars !== undefined) {
                    if (decls.has(name)) {
                        this.raiseError(sinfo.line, "Variable is already defined in scope");
                    }
                    decls.add(name);

                    return new VariableDeclarationStructuredAssignment(name, itype);
                }
                else {
                    if (!this.m_penv.getCurrentFunctionScope().isVarNameDefined(name)) {
                        this.raiseError(sinfo.line, "Variable is not defined in scope");
                    }

                    if (!(itype instanceof AutoTypeSignature)) {
                        this.raiseError(sinfo.line, "Cannot redeclare type of variable on assignment");
                    }

                    return new VariableAssignmentStructuredAssignment(name);
                }
            }
        }
    }

    parseStructuredAssignment(sinfo: SourceInfo, vars: "let" | "var" | undefined, decls: Set<string>): StructuredAssignment {
        if (this.testToken("#") || this.testToken("@")) {
            const isvalue = this.testToken("#");
            this.consumeToken();

            if (this.testToken("[")) {
                const assigns = this.parseListOf<StructuredAssignment>("[", "]", ",", () => {
                    return this.parseSimpleStructuredAssignment(this.getCurrentSrcInfo(), vars, decls);
                })[0];

                return new TupleStructuredAssignment(isvalue, assigns);
            }
            else {
                const assigns = this.parseListOf<[string, StructuredAssignment]>("{", "}", ",", () => {
                    this.ensureToken(TokenStrings.Identifier);
                    const name = this.consumeTokenAndGetValue();

                    this.ensureAndConsumeToken("=");
                    const subg = this.parseSimpleStructuredAssignment(this.getCurrentSrcInfo(), vars, decls);

                    return [name, subg];
                })[0];

                return new RecordStructuredAssignment(isvalue, assigns);
            }
        }
        else if (this.testToken("(|")) {
            const assigns = this.parseListOf<StructuredAssignment>("(|", "|)", ",", () => {
                return this.parseSimpleStructuredAssignment(this.getCurrentSrcInfo(), vars, decls);
            })[0];

            return new ValueListStructuredAssignment(assigns);
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Type ) || this.testToken(TokenStrings.Type)) {
            const ttype = this.parseTypeSignature(true);
            if (this.testFollows("::", TokenStrings.Identifier)) {
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                if (this.testToken("<") || this.testToken("[") || this.testToken("(")) {
                    this.raiseError(sinfo.line, "Expected a static field expression");
                }

                return new ConstValueStructuredAssignment(new ConstantExpressionValue(new AccessStaticFieldExpression(sinfo, ttype, name), new Set<string>()));
            }
            else {
                const isvalue = this.testToken("#");
                this.consumeToken();

                const assigns = this.parseListOf<[string, StructuredAssignment]>("{", "}", ",", () => {
                    this.ensureToken(TokenStrings.Identifier);
                    const name = this.consumeTokenAndGetValue();
    
                    this.ensureAndConsumeToken("=");
                    const subg = this.parseSimpleStructuredAssignment(this.getCurrentSrcInfo(), vars, decls);
    
                    return [name, subg];
                })[0];

                return new NominalStructuredAssignment(isvalue, ttype, assigns);
            }
        }
        else {
            return this.parseSimpleStructuredAssignment(sinfo, vars, decls);
        }
    }

    private parseLineStatement(): Statement {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();

        const tk = this.peekToken();
        if (tk === ";") {
            this.consumeToken();
            return new EmptyStatement(sinfo);
        }
        else if (tk === "let" || tk === "var") {
            this.consumeToken();
            const isConst = tk === "let";

            if (this.testFollows("#", "[") || this.testFollows("#", "{") || this.testFollows("@", "[") || this.testFollows("@", "{")
                || this.testToken("(|")  || this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Type) || this.testToken(TokenStrings.Type)) {
                let decls = new Set<string>();
                const assign = this.parseStructuredAssignment(this.getCurrentSrcInfo(), isConst ? "let" : "var", decls);
                decls.forEach((dv) => {
                    if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(dv)) {
                        this.raiseError(line, "Variable name is already defined");
                    }
                    this.m_penv.getCurrentFunctionScope().defineLocalVar(dv, dv, false);
                });

                this.ensureAndConsumeToken("=");
                const exp = this.parseExpression();
                this.ensureAndConsumeToken(";");

                return new StructuredVariableAssignmentStatement(sinfo, isConst, assign, exp);
            }
            else {
                let decls = new Set<string>();
                const assigns = this.parseEphemeralListOf(() => {
                    return this.parseStructuredAssignment(this.getCurrentSrcInfo(), isConst ? "let" : "var", decls);
                });

                if(assigns.length === 0 || (assigns.length === 1 && !(assigns[0] instanceof VariableDeclarationStructuredAssignment))) {
                    this.raiseError(sinfo.line, "Vacuous variable declaration");
                }
                
                let vars: {name: string, vtype: TypeSignature}[] = [];
                for(let i = 0; i < assigns.length; ++i) {
                    if (assigns[i] instanceof IgnoreTermStructuredAssignment) {
                        vars.push({name: "_", vtype: (assigns[i] as IgnoreTermStructuredAssignment).termType});
                    }
                    else if(assigns[i] instanceof VariableDeclarationStructuredAssignment) {
                        const dv = assigns[i] as VariableDeclarationStructuredAssignment;

                        if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(dv.vname)) {
                            this.raiseError(line, "Variable name is already defined");
                        }
                        this.m_penv.getCurrentFunctionScope().defineLocalVar(dv.vname, dv.vname, false);

                        vars.push({name: dv.vname, vtype: dv.vtype});
                    }
                    else {
                        this.raiseError(sinfo.line, "Cannot have structured multi-decls");
                    }
                }

                let exp: Expression[] | undefined = undefined;
                if(this.testAndConsumeTokenIf("=")) {
                    exp = this.parseEphemeralListOf(() => {
                        return this.parseExpression();
                    });
                }

                if ((exp === undefined && isConst)) {
                    this.raiseError(line, "Const variable declaration must include an assignment to the variable");
                }

                this.ensureAndConsumeToken(";");

                if(vars.length === 1) {
                    if (exp !== undefined && exp.length !== 1) {
                        this.raiseError(line, "Mismatch between variables declared and values provided");
                    }

                    const sexp = exp !== undefined ? exp[0] : undefined;
                    return new VariableDeclarationStatement(sinfo, vars[0].name, isConst, vars[0].vtype, sexp); 
                }
                else {
                    return new VariablePackDeclarationStatement(sinfo, isConst, vars, exp);
                }
            }
        }
        else if (this.testFollows("#", "[") || this.testFollows("#", "{") || this.testFollows("@", "[") || this.testFollows("@", "{")
                || this.testToken("(|")) {
            let decls = new Set<string>();
            const assign = this.parseStructuredAssignment(this.getCurrentSrcInfo(), undefined, decls);
            
            this.ensureAndConsumeToken("=");
            const exp = this.parseExpression();
            this.ensureAndConsumeToken(";");

            return new StructuredVariableAssignmentStatement(sinfo, false, assign, exp);
        }
        else if (tk === TokenStrings.Identifier) {
            let decls = new Set<string>();
            const assigns = this.parseEphemeralListOf(() => {
                return this.parseStructuredAssignment(this.getCurrentSrcInfo(), undefined, decls);
            });

            if(assigns.length === 0 || (assigns.length === 1 && !(assigns[0] instanceof VariableAssignmentStructuredAssignment))) {
                this.raiseError(sinfo.line, "Vacuous variable assignment");
            }
            
            let vars: string[] = [];
            for(let i = 0; i < assigns.length; ++i) {
                if (assigns[i] instanceof IgnoreTermStructuredAssignment) {
                    vars.push("_");
                }
                else if(assigns[i] instanceof VariableAssignmentStructuredAssignment) {
                    const av = assigns[i] as VariableAssignmentStructuredAssignment;

                    if (!this.m_penv.getCurrentFunctionScope().isVarNameDefined(av.vname)) {
                        this.raiseError(line, "Variable name is not defined");
                    }

                    vars.push(av.vname);
                }
                else {
                    this.raiseError(sinfo.line, "Cannot have structured multi-assigns");
                }
            }

            this.ensureAndConsumeToken("=");

            let exps: Expression[] = this.parseEphemeralListOf(() => {
                return this.parseExpression();
            });
            this.ensureAndConsumeToken(";");

            if(vars.length === 1) {
                if (exps.length !== 1) {
                    this.raiseError(line, "Mismatch between variables assigned and values provided");
                }

                return new VariableAssignmentStatement(sinfo, vars[0], exps[0]); 
            }
            else {
                return new VariablePackAssignmentStatement(sinfo, vars, exps);
            }
        }
        else if (tk === "return") {
            this.consumeToken();

            if(this.testAndConsumeTokenIf(";")) {
                return new ReturnStatement(sinfo, [new LiteralNoneExpression(sinfo)]);
            }
            else {
                const exps = this.parseEphemeralListOf(() => this.parseExpression());

                this.ensureAndConsumeToken(";");
                return new ReturnStatement(sinfo, exps);
            }
        }
        else if (tk === "yield") {
            this.consumeToken();

            const exps = this.parseEphemeralListOf(() => this.parseExpression());

            this.ensureAndConsumeToken(";");
            return new YieldStatement(sinfo, exps);
        }
        else if (tk === "abort") {
            this.consumeToken();

            this.ensureAndConsumeToken(";");
            return new AbortStatement(sinfo);
        }
        else if (tk === "assert") {
            this.consumeToken();
            let level = "debug" as BuildLevel;
            level = this.parseBuildInfo(level);

            const exp = this.parseExpression();

            this.ensureAndConsumeToken(";");
            return new AssertStatement(sinfo, exp, level);
        }
        else if (tk === "check") {
            this.consumeToken();

            const exp = this.parseExpression();

            this.ensureAndConsumeToken(";");
            return new CheckStatement(sinfo, exp);
        }
        else if (tk === "validate") {
            this.consumeToken();

            const exp = this.parseSelectExpression();
            let err = new LiteralNoneExpression(sinfo);
            if (this.testFollows("else")) {
                err = this.parseExpression();
            }

            this.ensureAndConsumeToken(";");
            return new ValidateStatement(sinfo, exp, err);
        }
        else if (tk === "_assume") {
            this.consumeToken();
            const cond = this.parseExpression();

            this.ensureAndConsumeToken(";");
            return new VerifierAssumeStatement(sinfo, cond);
        }
        else if (tk === "_debug") {
            this.consumeToken();

            let value = undefined;
            if (this.testToken("(")) {
                this.consumeToken();
                value = this.parseExpression();
                this.ensureAndConsumeToken(")");
            }

            this.ensureAndConsumeToken(";");
            return new DebugStatement(sinfo, value);
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Identifier)) {
            //it is a namespace function call
            const ns = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
            const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";
            const args = this.parseArguments("(", ")");

            return new NakedCallStatement(sinfo, new CallNamespaceFunctionOrOperatorExpression(sinfo, ns, name, targs, rec, args, "std"));
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Operator)) {
            //it is a namespace function call
            const ns = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";
            const args = this.parseArguments("(", ")");

            return new NakedCallStatement(sinfo, new CallNamespaceFunctionOrOperatorExpression(sinfo, ns, name, new TemplateArguments([]), rec, args, "std"));
        }
        else {
            //we should find a type (nominal here) and it is a static invoke or a structured assign
            const ttype = this.parseTypeSignature(false);

            if (this.testFollows("@", "{") || this.testFollows("#", "{")) {
                const isvalue = this.testToken("#");
                this.consumeToken();

                let decls = new Set<string>();
                const assigns = this.parseListOf<[string, StructuredAssignment]>("{", "}", ",", () => {
                    this.ensureToken(TokenStrings.Identifier);
                    const name = this.consumeTokenAndGetValue();
    
                    this.ensureAndConsumeToken("=");
                    const subg = this.parseStructuredAssignment(this.getCurrentSrcInfo(), undefined, decls);
    
                    return [name, subg];
                })[0];

                const assign = new NominalStructuredAssignment(isvalue, ttype, assigns);
                decls.forEach((dv) => {
                    if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(dv)) {
                        this.raiseError(line, "Variable name is already defined");
                    }
                    this.m_penv.getCurrentFunctionScope().defineLocalVar(dv, dv, false);
                });

                this.ensureAndConsumeToken("=");
                const exp = this.parseExpression();
                this.ensureAndConsumeToken(";");

                return new StructuredVariableAssignmentStatement(sinfo, false, assign, exp);
            }
            else if(this.testFollows("::", TokenStrings.Identifier)) {
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
                const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";
                const args = this.parseArguments("(", ")");

                return new NakedCallStatement(sinfo, new CallStaticFunctionOrOperatorExpression(sinfo, ttype, name, targs, rec, args, "std"));
            }
            else if(this.testFollows("::", TokenStrings.Operator)) {
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";
                const args = this.parseArguments("(", ")");

                return new NakedCallStatement(sinfo, new CallStaticFunctionOrOperatorExpression(sinfo, ttype, name, new TemplateArguments([]), rec, args, "std"));
            }
            else {
                this.raiseError(line, "Unknown statement structure");

                return new InvalidStatement(sinfo);
            }
        }
    }

    private parseBlockStatement(): BlockStatement {
        const sinfo = this.getCurrentSrcInfo();

        this.m_penv.getCurrentFunctionScope().pushLocalScope();
        let stmts: Statement[] = [];
        try {
            this.setRecover(this.scanMatchingParens("{", "}"));

            this.consumeToken();
            while (!this.testAndConsumeTokenIf("}")) {
                stmts.push(this.parseStatement());
            }

            this.m_penv.getCurrentFunctionScope().popLocalScope();

            if (stmts.length === 0) {
                this.raiseError(this.getCurrentLine(), "No empty blocks -- requires at least ';'");
            }

            this.clearRecover();
            return new BlockStatement(sinfo, stmts);
        }
        catch (ex) {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
            this.processRecover();
            return new BlockStatement(sinfo, [new InvalidStatement(sinfo)]);
        }
    }

    private parseIfElseStatement(): Statement {
        const sinfo = this.getCurrentSrcInfo();

        let conds: CondBranchEntry<BlockStatement>[] = [];

        this.ensureAndConsumeToken("if");
        this.ensureAndConsumeToken("(");
        const iftest = this.parseExpression();
        this.ensureAndConsumeToken(")");
        const ifbody = this.parseBlockStatement();

        conds.push(new CondBranchEntry<BlockStatement>(iftest, ifbody));

        while (this.testAndConsumeTokenIf("elif")) {
            this.ensureAndConsumeToken("(");
            const eliftest = this.parseExpression();
            this.ensureAndConsumeToken(")");
            const elifbody = this.parseBlockStatement();

            conds.push(new CondBranchEntry<BlockStatement>(eliftest, elifbody));
        }

        const elsebody = this.testAndConsumeTokenIf("else") ? this.parseBlockStatement() : undefined;

        return new IfElseStatement(sinfo, new IfElse<BlockStatement>(conds, elsebody));
    }

    private parseMatchGuard(sinfo: SourceInfo, matchtype: "type" | "case"): MatchGuard {
        if (this.testToken(TokenStrings.Identifier)) {
            const tv = this.consumeTokenAndGetValue();
            if (tv !== "_") {
                this.raiseError(sinfo.line, "Expected wildcard match");
            }

            return new WildcardMatchGuard();
        }

        let typecheck: TypeSignature | undefined = undefined;
        let layoutcheck: StructuredAssignment | undefined = undefined;
        let decls = new Set<string>();
        if (matchtype !== "case") {
            typecheck = this.parseTypeSignature(true);
        }
        else {
            //always let bind the match variables
            layoutcheck = this.parseStructuredAssignment(sinfo, "let", decls);
        }

        let whencheck = undefined;
        if (this.testAndConsumeTokenIf("when")) {
            whencheck = this.parseSelectExpression(true);
        }

        if (matchtype === "type") {
            return new TypeMatchGuard(typecheck as TypeSignature, whencheck);
        }
        else {
            return new StructureMatchGuard(layoutcheck as StructuredAssignment, decls, whencheck);
        }
    }

    private parseMatchEntry<T>(sinfo: SourceInfo, expsemi: boolean, matchtype: "type" | "case", actionp: () => T): MatchEntry<T> {
        if(!this.testToken(TokenStrings.Identifier)) {
            this.consumeToken();
        }

        const guard = this.parseMatchGuard(sinfo, matchtype);
        this.ensureAndConsumeToken("=>");
        const action = actionp();
        if(expsemi) {
            this.ensureAndConsumeToken(";");
        }

        return new MatchEntry<T>(guard, action);
    }

    private parseMatchStatement(): Statement {
        const sinfo = this.getCurrentSrcInfo();

        this.ensureAndConsumeToken("switch");

        this.ensureAndConsumeToken("(");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(")");

        try {
            this.m_penv.getCurrentFunctionScope().pushLocalScope();
            this.m_penv.getCurrentFunctionScope().defineLocalVar("$match", `$match_#${sinfo.pos}`, true);

            let entries: MatchEntry<BlockStatement>[] = [];
            this.ensureAndConsumeToken("{");
            while (this.testToken("type") || this.testToken("case") || (this.testToken(TokenStrings.Identifier) && this.peekTokenData() === "_")) {
                if (this.testToken("type")) {
                    entries.push(this.parseMatchEntry<BlockStatement>(this.getCurrentSrcInfo(), false, "type", () => this.parseBlockStatement()));
                }
                else {
                    entries.push(this.parseMatchEntry<BlockStatement>(this.getCurrentSrcInfo(), false, "case", () => this.parseBlockStatement()));
                }
            }
            this.ensureAndConsumeToken("}");

            return new MatchStatement(sinfo, mexp, entries);
        }
        finally {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
        }
    }

    private parseStatement(): Statement {
        if (this.testToken("if")) {
            return this.parseIfElseStatement();
        }
        else if (this.testToken("switch")) {
            return this.parseMatchStatement();
        }
        else {
            return this.parseLineStatement();
        }
    }

    private parseBody(bodyid: string, file: string): BodyImplementation {
        if (this.testToken("#")) {
            this.consumeToken();
            this.ensureToken(TokenStrings.Identifier);
            return new BodyImplementation(bodyid, file, this.consumeTokenAndGetValue());
        }
        else if(this.testToken("=")) {
            this.consumeToken();
            const iname = this.consumeTokenAndGetValue();
            if(iname !== "default") {
                this.raiseError(this.getCurrentSrcInfo().line, "Only valid option is 'default'");
            }
            this.ensureAndConsumeToken(";")
            return new BodyImplementation(bodyid, file, "default");
        }
        else if (this.testToken("{")) {
            return new BodyImplementation(bodyid, file, this.parseBlockStatement());
        }
        else {
            return new BodyImplementation(bodyid, file, this.parseExpression());
        }
    }

    ////
    //Decl parsing

    private parseAttributes(): string[] {
        let attributes: string[] = [];
        while (Lexer.isAttributeKW(this.peekTokenData())) {
            attributes.push(this.consumeTokenAndGetValue());
        }
        return attributes;
    }

    private parseTemplateConstraint(hasconstraint: boolean): TypeSignature {
        if(!hasconstraint) {
            return this.m_penv.SpecialAnySignature;
        }
        else {
            return this.parseTypeSignature(false);
        }
    }

    private parseTermDeclarations(): TemplateTermDecl[] {
        let terms: TemplateTermDecl[] = [];
        if (this.testToken("<")) {
            terms = this.parseListOf<TemplateTermDecl>("<", ">", ",", () => {
                this.ensureToken(TokenStrings.Template);
                const templatename = this.consumeTokenAndGetValue();

                let isinfer = false;
                let defaulttype: TypeSignature | undefined = undefined;
                if (this.testAndConsumeTokenIf("=")) {
                    if (this.testAndConsumeTokenIf("?")) {
                        isinfer = true;
                    }
                    else {
                        //
                        //TODO: we want to mark this as a literal only term and check it later but right now just eat it
                        //
                        this.consumeTokenIf("literal");

                        defaulttype = this.parseTypeSignature(false);
                    }
                }

                const hasconstraint = this.testAndConsumeTokenIf("where");
                let specialConstraints = new Set<TemplateTermSpecialRestriction>();
                while (this.testToken("parsable") || this.testToken("validator") || this.testToken("struct") || this.testToken("entity")) {
                    if(this.testToken("parsable")) {
                        specialConstraints.add(TemplateTermSpecialRestriction.Parsable);
                    }
                    else if (this.testToken("validator")) {
                        specialConstraints.add(TemplateTermSpecialRestriction.Validator);
                    }
                    else if (this.testToken("struct")) {
                        specialConstraints.add(TemplateTermSpecialRestriction.Struct);
                    }
                    else {
                        if(!this.testToken("entity")) {
                            this.raiseError(this.getCurrentLine(), "Unknown template type constraint");
                        }

                        specialConstraints.add(TemplateTermSpecialRestriction.Entity);
                    } 
                }

                const tconstraint = this.parseTemplateConstraint(hasconstraint);
                return new TemplateTermDecl(templatename, specialConstraints, tconstraint, isinfer, defaulttype);
            })[0];
        }
        return terms;
    }

    private parseSingleTermRestriction(): TemplateTypeRestriction {
        this.ensureToken(TokenStrings.Template);
        const templatename = this.consumeTokenAndGetValue();
        const tconstraint = this.parseTemplateConstraint(true);

        return new TemplateTypeRestriction(new TemplateTypeSignature(templatename), tconstraint);
    }

    private parseTermRestrictionList(): TemplateTypeRestriction[] {
        const trl = this.parseSingleTermRestriction();
        if (this.testAndConsumeTokenIf("&&")) {
            const ands = this.parseTermRestrictionList();
            return [trl, ...ands];
        }
        else {
            return [trl];
        }
    }

    private parseTermRestriction(parencheck: boolean): TypeConditionRestriction | undefined {
        if(parencheck && !this.testToken("{")) {
            return undefined;
        }
        this.testAndConsumeTokenIf("{");

        if(parencheck) {
            this.testAndConsumeTokenIf("when");
        }
        
        const trl = this.parseTermRestrictionList();

        if(parencheck) {
            this.ensureAndConsumeToken("}");
        }

        return new TypeConditionRestriction(trl);
    }

    private parsePreAndPostConditions(sinfo: SourceInfo, argnames: Set<string>, rtype: TypeSignature): [PreConditionDecl[], PostConditionDecl[]] {
        let preconds: PreConditionDecl[] = [];
        try {
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(argnames), rtype, false));
            while (this.testToken("requires") || this.testToken("validate")) {
                const isvalidate = this.testToken("validate");
                this.consumeToken();
                
                let level: BuildLevel = isvalidate ? "release" : "debug";
                if (!isvalidate) {
                    level = this.parseBuildInfo(level);
                }

                const exp = this.parseSelectExpression();

                let err = new LiteralNoneExpression(sinfo);
                if (this.testFollows("else")) {
                    err = this.parseExpression();
                }

                preconds.push(new PreConditionDecl(sinfo, isvalidate, level, exp, err));

                this.ensureAndConsumeToken(";");
            }
        } finally {
            this.m_penv.popFunctionScope();
        }

        let postconds: PostConditionDecl[] = [];
        try {
            this.m_penv.pushFunctionScope(new FunctionScope(argnames, rtype, false));
            while (this.testToken("ensures")) {
                this.consumeToken();

                let level: BuildLevel = "debug";
                level = this.parseBuildInfo(level);

                const exp = this.parseExpression();
                postconds.push(new PostConditionDecl(sinfo, level, exp));

                this.ensureAndConsumeToken(";");
            }
        } finally {
            this.m_penv.popFunctionScope();
        }

        return [preconds, postconds];
    }

    private parseNamespaceUsing(currentDecl: NamespaceDeclaration) {
        //import NS {...} ;

        this.ensureAndConsumeToken("import");
        this.ensureToken(TokenStrings.Namespace);
        const fromns = this.consumeTokenAndGetValue();

        const names = this.parseListOf<string>("{", "}", ",", () => {
            return this.consumeTokenAndGetValue();
        })[0];

        this.ensureAndConsumeToken(";");

        if (currentDecl.checkUsingNameClash(names)) {
            this.raiseError(this.getCurrentLine(), "Collision between imported using names");
        }

        currentDecl.usings.push(new NamespaceUsing(fromns, names));
    }

    private parseNamespaceTypedef(currentDecl: NamespaceDeclaration) {
        //typedef NAME<T where C...> = TypeConstraint;

        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("typedef");
        this.ensureToken(TokenStrings.Type);
        const tyname = this.consumeTokenAndGetValue();

        if (currentDecl.checkDeclNameClash(currentDecl.ns, tyname)) {
            this.raiseError(this.getCurrentLine(), "Collision between typedef and other names");
        }

        const terms = this.parseTermDeclarations();

        this.ensureAndConsumeToken("=");
        const rpos = this.scanToken(";");
        if (rpos === this.m_epos) {
            this.raiseError(this.getCurrentLine(), "Missing ; on typedef");
        }

        if(this.testToken(TokenStrings.Regex)) {
            const vregex = this.consumeTokenAndGetValue();
            this.consumeToken();

            const re = BSQRegex.parse(vregex);
            if(typeof(re) === "string") {
                this.raiseError(this.getCurrentLine(), re);
            }

            const validator = new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), [], "vregex", new NominalTypeSignature("NSCore", ["Regex"]), new ConstantExpressionValue(new LiteralRegexExpression(sinfo, re as BSQRegex), new Set<string>()));
            const param = new FunctionParameter("arg", new NominalTypeSignature("NSCore", ["String"]), false, undefined, undefined, undefined);
            const acceptsbody = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "validator_accepts");
            const acceptsinvoke = new InvokeDecl(sinfo, this.m_penv.getCurrentFile(), ["validator_accepts", "__safe"], "no", [], undefined, [param], undefined, undefined, new NominalTypeSignature("NSCore", ["Bool"]), [], [], false, new Set<string>(), acceptsbody);
            const accepts = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), "accepts", acceptsinvoke);
            const provides = [[new NominalTypeSignature("NSCore", ["Validator"]), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
            const validatortype = new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), [], [SpecialTypeCategory.ValidatorTypeDecl], currentDecl.ns, tyname, [], provides, [], new Map<string, StaticMemberDecl>().set("vregex", validator), new Map<string, StaticFunctionDecl>().set("accepts", accepts), new Map<string, StaticOperatorDecl[]>(), new Map<string, MemberFieldDecl>(), new Map<string, MemberMethodDecl>(), new Map<string, EntityTypeDecl>());

            currentDecl.objects.set(tyname, validatortype);
            this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + tyname, currentDecl.objects.get(tyname) as EntityTypeDecl);
            this.m_penv.assembly.addValidatorRegex(currentDecl.ns + "::" + tyname, re as BSQRegex);
        }
        else {
            const btype = this.parseTypeSignature(true);
            this.consumeToken();

            currentDecl.typeDefs.set(currentDecl.ns + "::" + tyname, new NamespaceTypedef(currentDecl.ns, tyname, terms, btype));
        }
    }

    private parseProvides(iscorens: boolean): [TypeSignature, TypeConditionRestriction | undefined][] {
        let provides: [TypeSignature, TypeConditionRestriction | undefined][] = [];
        if (this.testToken("provides")) {
            this.consumeToken();

            while (!this.testToken("{")) {
                this.consumeTokenIf(",");

                const pv = this.parseTypeSignature(false);
                let res: TypeConditionRestriction | undefined = undefined;
                if(this.testAndConsumeTokenIf("when")) {
                    res = this.parseTermRestriction(false);
                }
                provides.push([pv, res]);
            }
        }
        
        if (!iscorens) {
            provides.push([new NominalTypeSignature("NSCore", ["Object"]), undefined]);
        }

        return provides;
    }

    private parseConstMember(staticMembers: Map<string, StaticMemberDecl>, allMemberNames: Set<string>, attributes: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] const NAME: T = exp;
        this.ensureAndConsumeToken("const");

        this.ensureToken(TokenStrings.Identifier);
        const sname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const stype = this.parseTypeSignature(false);

        this.ensureAndConsumeToken("=");
        const value = this.parseConstExpression(false);

        this.ensureAndConsumeToken(";");

        if (allMemberNames.has(sname)) {
            this.raiseError(this.getCurrentLine(), "Collision between const and other names");
        }

        allMemberNames.add(sname);
        staticMembers.set(sname, new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), attributes, sname, stype, value));
    }

    private parseStaticFunction(staticFunctions: Map<string, StaticFunctionDecl>, allMemberNames: Set<string>, attributes: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] function NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        this.ensureAndConsumeToken("function");
        const termRestrictions = this.parseTermRestriction(true);

        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        let recursive: "yes" | "no" | "cond" = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(InvokableKind.Basic, Parser.attributeSetContains("abstract", attributes), attributes, recursive, terms, termRestrictions);

        if (allMemberNames.has(fname)) {
            this.raiseError(this.getCurrentLine(), "Collision between static and other names");
        }
        allMemberNames.add(fname);

        staticFunctions.set(fname, new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), fname, sig));
    }

    private parseStaticOperator(staticOperators: Map<string, StaticOperatorDecl[]>, allMemberNames: Set<string>, attributes: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] operator NAME(params): type [requires...] [ensures...] { ... }
        this.ensureAndConsumeToken("operator");
        const termRestrictions = this.parseTermRestriction(true);

        if(!this.testToken(TokenStrings.Identifier) && !this.testToken(TokenStrings.Operator)) {
            this.raiseError(sinfo.line, "Expected valid name for operator");
        }

        const fname = this.consumeTokenAndGetValue();
        let recursive: "yes" | "no" | "cond" = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }

        const ikind = attributes.includes("dynamic") ? InvokableKind.DynamicOperator : InvokableKind.StaticOperator;
        const sig = this.parseInvokableCommon(ikind, Parser.attributeSetContains("abstract", attributes), attributes, recursive, [], termRestrictions);

        if (allMemberNames.has(fname)) {
            this.raiseError(this.getCurrentLine(), "Collision between static and other names");
        }
        allMemberNames.add(fname);

        if(!staticOperators.has(fname)) {
            staticOperators.set(fname, []);
        }
        (staticOperators.get(fname) as StaticOperatorDecl[]).push(new StaticOperatorDecl(sinfo, this.m_penv.getCurrentFile(), fname, sig));
    }

    private parseMemberField(memberFields: Map<string, MemberFieldDecl>, allMemberNames: Set<string>, attributes: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] field NAME: T = exp;
        this.ensureAndConsumeToken("field");

        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const stype = this.parseTypeSignature(false);
        let value: ConstantExpressionValue | undefined = undefined;

        if (this.testAndConsumeTokenIf("=")) {
            value = this.parseConstExpression(true);
        }

        this.ensureAndConsumeToken(";");

        if (allMemberNames.has(fname)) {
            this.raiseError(this.getCurrentLine(), "Collision between const and other names");
        }

        memberFields.set(fname, new MemberFieldDecl(sinfo, this.m_penv.getCurrentFile(), attributes, fname, stype, value));
    }

    private parseMemberMethod(thisRef: "ref" | undefined, thisType: TypeSignature, memberMethods: Map<string, MemberMethodDecl>, allMemberNames: Set<string>, attributes: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] [ref] method NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        const refrcvr = this.testAndConsumeTokenIf("ref");
        this.ensureAndConsumeToken("method");
        const termRestrictions = this.parseTermRestriction(true);

        this.ensureToken(TokenStrings.Identifier);
        const mname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        let recursive: "yes" | "no" | "cond" = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(InvokableKind.Member, Parser.attributeSetContains("abstract", attributes), attributes, recursive, terms, termRestrictions, thisRef, thisType);

        if (allMemberNames.has(mname)) {
            this.raiseError(this.getCurrentLine(), "Collision between static and other names");
        }
        allMemberNames.add(mname);

        memberMethods.set(mname, new MemberMethodDecl(sinfo, this.m_penv.getCurrentFile(), mname, refrcvr, sig));
    }

    private parseInvariantsInto(invs: InvariantDecl[]) {
        try {
            
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(), new NominalTypeSignature("NSCore", ["Bool"]), false));
            while (this.testToken("invariant")) {
                this.consumeToken();

                let level: BuildLevel = this.parseBuildInfo("debug");

                const sinfo = this.getCurrentSrcInfo();
                const exp = this.parseConstExpression(true);

                invs.push(new InvariantDecl(sinfo, level, exp));

                this.ensureAndConsumeToken(";");
            }
        } finally {
            this.m_penv.popFunctionScope();
        }
    }

    private parseOOPMembersCommon(thisType: TypeSignature, currentNamespace: NamespaceDeclaration, currentTypeNest: string[], currentTermNest: TemplateTermDecl[], 
        nestedEntities: Map<string, EntityTypeDecl>, invariants: InvariantDecl[], 
        staticMembers: Map<string, StaticMemberDecl>, staticFunctions: Map<string, StaticFunctionDecl>, staticOperators: Map<string, StaticOperatorDecl[]>, 
        memberFields: Map<string, MemberFieldDecl>, memberMethods: Map<string, MemberMethodDecl>) {
        let allMemberNames = new Set<string>();
        while (!this.testToken("}")) {
            const attributes = this.parseAttributes();

            if(this.testToken("entity")) {
                this.parseObject(currentNamespace, nestedEntities, currentTypeNest, currentTermNest);
            }
            else if (this.testToken("invariant")) {
                this.parseInvariantsInto(invariants);
            }
            else if (this.testToken("const")) {
                this.parseConstMember(staticMembers, allMemberNames, attributes);
            }
            else if (this.testToken("function")) {
                this.parseStaticFunction(staticFunctions, allMemberNames, attributes);
            }
            else if (this.testToken("operator")) {
                this.parseStaticOperator(staticOperators, allMemberNames, attributes);
            }
            else if (this.testToken("field")) {
                this.parseMemberField(memberFields, allMemberNames, attributes);
            }
            else {
                this.ensureToken("method");

                const thisRef = attributes.find((attr) => attr === "ref") as "ref" | undefined;
                this.parseMemberMethod(thisRef, thisType, memberMethods, allMemberNames, attributes);
            }
        }
    }

    private parseConcept(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();

        //[attr] concept NAME[T where C...] provides {...}
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("concept");
        this.ensureToken(TokenStrings.Type);

        const cname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        const provides = this.parseProvides(currentDecl.ns === "NSCore");

        try {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken("{");

            const thisType = new NominalTypeSignature(currentDecl.ns, [cname], terms.map((term) => new TemplateTypeSignature(term.name)));

            const invariants: InvariantDecl[] = [];
            const staticMembers = new Map<string, StaticMemberDecl>();
            const staticFunctions = new Map<string, StaticFunctionDecl>();
            const staticOperators = new Map<string, StaticOperatorDecl[]>();
            const memberFields = new Map<string, MemberFieldDecl>();
            const memberMethods = new Map<string, MemberMethodDecl>();
            const nestedEntities = new Map<string, EntityTypeDecl>();
            this.parseOOPMembersCommon(thisType, currentDecl, [cname], [...terms], nestedEntities, invariants, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods);

            this.ensureAndConsumeToken("}");

            if (currentDecl.checkDeclNameClash(currentDecl.ns, cname)) {
                this.raiseError(line, "Collision between concept and other names");
            }

            this.clearRecover();

            let tc: SpecialTypeCategory[] = [];
            if(OOPTypeDecl.attributeSetContains("parsable", attributes)) {
                tc.push(SpecialTypeCategory.ParsableTypeDecl);
            }

            if(currentDecl.ns === "NSCore") {
                if(cname === "Result") {
                    tc.push(SpecialTypeCategory.ResultDecl);
                }
            }


            const cdecl = new ConceptTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, tc, currentDecl.ns, cname, terms, provides, invariants, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, nestedEntities);
            currentDecl.concepts.set(cname, cdecl);
            this.m_penv.assembly.addConceptDecl(currentDecl.ns + "::" + cname, cdecl);
        }
        catch (ex) {
            this.processRecover();
        }
    }

    private parseObject(currentDecl: NamespaceDeclaration, enclosingMap: Map<string, EntityTypeDecl> | undefined, currentTypeNest: string[], currentTermNest: TemplateTermDecl[]) {
        const line = this.getCurrentLine();

        //[attr] object NAME[T where C...] provides {...}
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("entity");
        this.ensureToken(TokenStrings.Type);

        const ename = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        const provides = this.parseProvides(currentDecl.ns === "NSCore");

        try {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken("{");

            const thisType = new NominalTypeSignature(currentDecl.ns, [...currentTypeNest, ename], [...terms, ...currentTermNest].map((term) => new TemplateTypeSignature(term.name)));

            const invariants: InvariantDecl[] = [];
            const staticMembers = new Map<string, StaticMemberDecl>();
            const staticFunctions = new Map<string, StaticFunctionDecl>();
            const staticOperators = new Map<string, StaticOperatorDecl[]>();
            const memberFields = new Map<string, MemberFieldDecl>();
            const memberMethods = new Map<string, MemberMethodDecl>();
            const nestedEntities = new Map<string, EntityTypeDecl>();
            this.parseOOPMembersCommon(thisType, currentDecl, [...currentTypeNest, ename], [...currentTermNest, ...terms], nestedEntities, invariants, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods);

            this.ensureAndConsumeToken("}");

            if (currentDecl.checkDeclNameClash(currentDecl.ns, [...currentTypeNest, ename].join("::"))) {
                this.raiseError(line, "Collision between object and other names");
            }

            let specialinfo: SpecialTypeCategory[] = [];
            if(OOPTypeDecl.attributeSetContains("parsable", attributes)) {
                specialinfo.push(SpecialTypeCategory.ParsableTypeDecl);
            }

            if(currentDecl.ns === "NSCore") {
                if(OOPTypeDecl.attributeSetContains("grounded", attributes)) {
                    specialinfo.push(SpecialTypeCategory.GroundedTypeDecl);
                }

                if(ename === "StringOf") {
                    specialinfo.push(SpecialTypeCategory.StringOfDecl);
                }
                else if(ename === "DataString") {
                    specialinfo.push(SpecialTypeCategory.DataStringDecl);
                }
                else if(ename === "Buffer") {
                    specialinfo.push(SpecialTypeCategory.BufferDecl);
                }
                else if(ename === "DataBuffer") {
                    specialinfo.push(SpecialTypeCategory.DataBufferDecl);
                }
                else if(ename === "Ok") {
                    specialinfo.push(SpecialTypeCategory.ResultOkDecl);
                }
                else if(ename === "Err") {
                    specialinfo.push(SpecialTypeCategory.ResultErrDecl);
                }
                else if(ename === "Vector") {
                    specialinfo.push(SpecialTypeCategory.VectorTypeDecl);
                }
                else if(ename === "List") {
                    specialinfo.push(SpecialTypeCategory.ListTypeDecl);
                }
                else if(ename === "Stack") {
                    specialinfo.push(SpecialTypeCategory.StackTypeDecl);
                }
                else if(ename === "Queue") {
                    specialinfo.push(SpecialTypeCategory.QueueTypeDecl);
                }
                else if(ename === "Set") {
                    specialinfo.push(SpecialTypeCategory.SetTypeDecl);
                }
                else if(ename === "DynamicSet") {
                    specialinfo.push(SpecialTypeCategory.DynamicSetTypeDecl);
                }
                else if(ename === "Map") {
                    specialinfo.push(SpecialTypeCategory.MapTypeDecl);
                }
                else if(ename === "DynamicMap") {
                    specialinfo.push(SpecialTypeCategory.DynamicMapTypeDecl);
                }
                else {
                    //not special
                }
            }

            this.clearRecover();

            const fename = [...currentTypeNest, ename].join("::");
            const feterms = [...currentTermNest, ...terms];

            const edecl = new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, specialinfo, currentDecl.ns, fename, feterms, provides, invariants, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, nestedEntities);
            this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + fename, edecl);
            currentDecl.objects.set(ename, edecl);
            
            if(enclosingMap !== undefined) {
                enclosingMap.set(ename, edecl);
            }
        }
        catch (ex) {
            this.processRecover();
        }
    }

    private parseEnum(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();

        //[attr] enum NAME {...} [& {...}]
        const attributes = ["struct", ...this.parseAttributes()];

        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("enum");
        this.ensureToken(TokenStrings.Type);

        const ename = this.consumeTokenAndGetValue();
        const etype = new NominalTypeSignature(currentDecl.ns, [ename]);
        const simpleETypeResult = etype;
        
        if (currentDecl.checkDeclNameClash(currentDecl.ns, ename)) {
            this.raiseError(line, "Collision between object and other names");
        }

        try {
            this.setRecover(this.scanCodeParens());

            let oftype: TypeSignature | undefined = new NominalTypeSignature("NSCore", ["Nat"]);
            if(this.testAndConsumeTokenIf(":")) {
                oftype = this.parseTypeSignature(false);
            }

            const enums = this.parseListOf<[string, ConstantExpressionValue | undefined]>("{", "}", ";", () => {
                this.ensureToken(TokenStrings.Identifier);
                const ename = this.consumeTokenAndGetValue();
                let dvalue: ConstantExpressionValue | undefined = undefined;
                if (this.testAndConsumeTokenIf("=")) {
                    dvalue = this.parseConstExpression(false);
                }

                return [ename, dvalue];
            })[0];

            const cparam = new FunctionParameter("v", oftype, false, undefined, undefined, undefined);
            const cbody = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "enum_create");
            const createdecl = new InvokeDecl(sinfo, this.m_penv.getCurrentFile(), ["create_enum", "__safe"], "no", [], undefined, [cparam], undefined, undefined, simpleETypeResult, [], [], false, new Set<string>(), cbody);
            const create = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), "create", createdecl);

            const vbody = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "enum_value");
            const valuedecl = new InvokeDecl(sinfo, this.m_penv.getCurrentFile(), ["get_enum_value", "__safe"], "no", [], undefined, [], undefined, undefined, oftype, [], [], false, new Set<string>(), vbody);
            const value = new MemberMethodDecl(sinfo, this.m_penv.getCurrentFile(), "value", false, valuedecl);

            const provides = [
                [new NominalTypeSignature("NSCore", ["Some"]), undefined],
                [new NominalTypeSignature("NSCore", ["KeyType"]), undefined], 
                [new NominalTypeSignature("NSCore", ["APIType"]), undefined]
            ] as [TypeSignature, TypeConditionRestriction | undefined][];

            //
            //TODO: maybe want to make this parsable too!
            //

            const invariants: InvariantDecl[] = [];
            const staticMembers = new Map<string, StaticMemberDecl>();
            const staticFunctions = new Map<string, StaticFunctionDecl>().set("create", create);
            const staticOperators = new Map<string, StaticOperatorDecl[]>();
            const memberFields = new Map<string, MemberFieldDecl>();
            const memberMethods = new Map<string, MemberMethodDecl>().set("value", value);
    
            if(this.testAndConsumeTokenIf("&")) {
                this.setRecover(this.scanCodeParens());
                this.ensureAndConsumeToken("{");
    
                const thisType = new NominalTypeSignature(currentDecl.ns, [ename], []);
    
                const nestedEntities = new Map<string, EntityTypeDecl>();
                this.parseOOPMembersCommon(thisType, currentDecl, [ename], [], nestedEntities, invariants, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods);
    
                this.ensureAndConsumeToken("}");
    
                this.clearRecover();
            }

            if(staticMembers.size !== 0) {
                this.raiseError(line, "Cannot have explicit static fields on enum");
            }

            const explicitvalues = enums.some((env) => env[1] !== undefined);
            for(let i = 0; i < enums.length; ++i) {
                if(explicitvalues && enums[i][1] === undefined) {
                    this.raiseError(line, "When using explicit enum values they must all be provided for every entry");
                }

                const exp = enums[i][1] !== undefined ? (enums[i][1] as ConstantExpressionValue).exp : new LiteralIntegralExpression(sinfo, (i + 1).toString(), this.m_penv.SpecialNatSignature);
                const parg = new PositionalArgument(undefined, false, exp);

                const enminit = new CallStaticFunctionOrOperatorExpression(sinfo, etype, `@@create_${enums[i][0]}`, new TemplateArguments([]), "no", new Arguments([parg]), "std");
                const enm = new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), [], enums[i][0], etype, new ConstantExpressionValue(enminit, new Set<string>()));
                staticMembers.set(enums[i][0], enm);
            }
        
            if (currentDecl.checkDeclNameClash(currentDecl.ns, ename)) {
                this.raiseError(line, "Collision between object and other names");
            }

            this.clearRecover();
            currentDecl.objects.set(ename, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, [SpecialTypeCategory.EnumTypeDecl, SpecialTypeCategory.GroundedTypeDecl], currentDecl.ns, ename, [], provides, invariants, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, new Map<string, EntityTypeDecl>()));
            this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + ename, currentDecl.objects.get(ename) as EntityTypeDecl);
        }
        catch (ex) {
            this.processRecover();
        }
    }

    private parseTypeDecl(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();

        //[attr] typedecl NAME = Type (& {...} | ;)
        const attributes = ["struct", ...this.parseAttributes()];

        const sinfo = this.getCurrentSrcInfo();
       
        this.ensureAndConsumeToken("typedecl");

        this.ensureToken(TokenStrings.Type);
        const iname = this.consumeTokenAndGetValue();
        if (currentDecl.checkDeclNameClash(currentDecl.ns, iname)) {
            this.raiseError(line, "Collision between object and other names");
        }

        const itype = new NominalTypeSignature(currentDecl.ns, [iname]);

        this.ensureAndConsumeToken("=");
        const idval = this.parseTypeSignature(false);

        const cparam = new FunctionParameter("v", idval, false, undefined, undefined, undefined);
        const cbody = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "typedecl_create");
        const createdecl = new InvokeDecl(sinfo, this.m_penv.getCurrentFile(), ["create_typedecl", "__safe"], "no", [], undefined, [cparam], undefined, undefined, itype, [], [], false, new Set<string>(), cbody);
        const create = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), "create", createdecl);

        const vbody = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "typedecl_value");
        const valuedecl = new InvokeDecl(sinfo, this.m_penv.getCurrentFile(), ["get_typedecl_value", "__safe"], "no", [], undefined, [], undefined, undefined, idval, [], [], false, new Set<string>(), vbody);
        const value = new MemberMethodDecl(sinfo, this.m_penv.getCurrentFile(), "value", false, valuedecl);

        let provides = [[new NominalTypeSignature("NSCore", ["Some"]), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][]
        provides.push([new NominalTypeSignature("NSCore", ["KeyType"]), new TypeConditionRestriction([new TemplateTypeRestriction(idval, new NominalTypeSignature("NSCore", ["KeyType"]))])]);
        provides.push([new NominalTypeSignature("NSCore", ["APIType"]), new TypeConditionRestriction([new TemplateTypeRestriction(idval, new NominalTypeSignature("NSCore", ["APIType"]))])]);

        //
        //TODO: maybe want to make this parsable too!
        //

        const invariants: InvariantDecl[] = [];
        const staticMembers = new Map<string, StaticMemberDecl>();
        const staticFunctions = new Map<string, StaticFunctionDecl>().set("create", create);
        const staticOperators = new Map<string, StaticOperatorDecl[]>();
        const memberFields = new Map<string, MemberFieldDecl>();
        const memberMethods = new Map<string, MemberMethodDecl>().set("value", value);

        if(this.testAndConsumeTokenIf("&")) {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken("{");

            const thisType = new NominalTypeSignature(currentDecl.ns, [iname], []);

            const nestedEntities = new Map<string, EntityTypeDecl>();
            this.parseOOPMembersCommon(thisType, currentDecl, [iname], [], nestedEntities, invariants, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods);

            this.ensureAndConsumeToken("}");

            if (currentDecl.checkDeclNameClash(currentDecl.ns, iname)) {
                this.raiseError(line, "Collision between concept and other names");
            }

            this.clearRecover();
        }
        else {
            this.ensureAndConsumeToken(";");
        }

        let categories = [SpecialTypeCategory.TypeDeclDecl, SpecialTypeCategory.GroundedTypeDecl];
        if(OOPTypeDecl.attributeSetContains("numeric", attributes)) {
            categories.push(SpecialTypeCategory.TypeDeclNumeric);
        }

        currentDecl.objects.set(iname, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, categories, currentDecl.ns, iname, [], provides, invariants, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, new Map<string, EntityTypeDecl>()));
        this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + iname, currentDecl.objects.get(iname) as EntityTypeDecl);
    }

    private parseNamespaceConst(currentDecl: NamespaceDeclaration) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] const NAME = exp;
        const attributes = this.parseAttributes();

        this.ensureAndConsumeToken("const");
        this.ensureToken(TokenStrings.Identifier);
        const gname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const gtype = this.parseTypeSignature(false);

        this.ensureAndConsumeToken("=");
        const value = this.parseConstExpression(false);

        this.ensureAndConsumeToken(";");

        if (currentDecl.checkDeclNameClash(currentDecl.ns, gname)) {
            this.raiseError(this.getCurrentLine(), "Collision between global and other names");
        }

        currentDecl.consts.set(gname, new NamespaceConstDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, gname, gtype, value));
    }

    private parseNamespaceFunction(currentDecl: NamespaceDeclaration) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] function NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        const attributes = this.parseAttributes();

        this.ensureAndConsumeToken("function");
        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();

        const terms = this.parseTermDeclarations();
        let recursive: "yes" | "no" | "cond" = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(InvokableKind.Basic, false, attributes, recursive, terms, undefined);

        currentDecl.functions.set(fname, new NamespaceFunctionDecl(sinfo, this.m_penv.getCurrentFile(), currentDecl.ns, fname, sig));
    }

    private parseNamespaceOperator(currentDecl: NamespaceDeclaration) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] operator [NS ::] NAME(params): type [requires...] [ensures...] { ... }
        const attributes = this.parseAttributes();

        this.ensureAndConsumeToken("operator");
        if (this.testToken("+") || this.testToken("-") || this.testToken("*") || this.testToken("/") ||
            this.testToken("==") || this.testToken("!=") || this.testToken("<") || this.testToken(">") || this.testToken("<=") || this.testToken(">=")) {
            const fname = this.consumeTokenAndGetValue();

            let recursive: "yes" | "no" | "cond" = "no";
            if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
                recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
            }

            const ns = this.m_penv.assembly.getNamespace("NSMain");
            const sig = this.parseInvokableCommon(InvokableKind.StaticOperator, false, attributes, recursive, [], undefined);

            if (!currentDecl.operators.has(fname)) {
                currentDecl.operators.set(fname, []);
            }
            (ns.operators.get(fname) as NamespaceOperatorDecl[]).push(new NamespaceOperatorDecl(sinfo, this.m_penv.getCurrentFile(), "NSMain", fname, sig));
        }
        else {
            if(!this.testToken(TokenStrings.Identifier) && !this.testToken(TokenStrings.Operator)) {
                this.raiseError(sinfo.line, "Expected valid name for operator");
            }

            const fname = this.consumeTokenAndGetValue();

            let recursive: "yes" | "no" | "cond" = "no";
            if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
                recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
            }

            let ns = currentDecl;
            if(this.testToken(TokenStrings.Namespace)) {
                const nns = this.consumeTokenAndGetValue();
                this.ensureAndConsumeToken("::");

                ns = this.m_penv.assembly.getNamespace(nns);
            }

            const isabstract = OOPTypeDecl.attributeSetContains("abstract", attributes);
            const ikind = attributes.includes("dynamic") ? InvokableKind.DynamicOperator : InvokableKind.StaticOperator;
            const sig = this.parseInvokableCommon(ikind, isabstract, attributes, recursive, [], undefined);

            let level = -1;
            if(isabstract) {
                level = Number.parseInt(this.consumeTokenAndGetValue());
                this.ensureAndConsumeToken(";");
            }

            if (!ns.operators.has(fname)) {
                ns.operators.set(fname, []);
            }
            (ns.operators.get(fname) as NamespaceOperatorDecl[]).push(new NamespaceOperatorDecl(sinfo, this.m_penv.getCurrentFile(), ns.ns, fname, sig, level));
        }
    }

    private parseEndOfStream() {
        this.ensureAndConsumeToken(TokenStrings.EndOfStream);
    }

    ////
    //Public methods

    parseCompilationUnitPass1(file: string, contents: string): boolean {
        this.setNamespaceAndFile("[No Namespace]", file);

        const lexer = new Lexer(contents);
        this.initialize(lexer.lex());

        //namespace NS; ...
        this.ensureAndConsumeToken("namespace");
        this.ensureToken(TokenStrings.Namespace);
        const ns = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(";");

        this.setNamespaceAndFile(ns, file);
        const nsdecl = this.m_penv.assembly.ensureNamespace(ns);

        let parseok = true;
        while (this.m_cpos < this.m_epos) {
            try {
                this.m_cpos = this.scanTokenOptions("function", "operator", "const", "typedef", "concept", "entity", "enum", "typedecl");
                if (this.m_cpos === this.m_epos) {
                    const tokenIndexBeforeEOF = this.m_cpos - 2;
                    if (tokenIndexBeforeEOF >= 0 && tokenIndexBeforeEOF < this.m_tokens.length) {
                        const tokenBeforeEOF = this.m_tokens[tokenIndexBeforeEOF];
                        if (tokenBeforeEOF.kind === TokenStrings.Error) {
                            this.raiseError(tokenBeforeEOF.line, `Expected */ but found EOF`);
                        }
                    }
                    break;
                }

                if (this.testToken("function")  || this.testToken("const")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.Identifier);
                    const fname = this.consumeTokenAndGetValue();
                    if (nsdecl.declaredNames.has(fname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }

                    nsdecl.declaredNames.add(ns + "::" + fname);
                }
                else if (this.testToken("operator")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.Identifier);
                    const fname = this.consumeTokenAndGetValue();

                    if (!this.testToken("+") && !this.testToken("-") && !this.testToken("*") && !this.testToken("/") &&
                        !this.testToken("==") && !this.testToken("!=") && !this.testToken("<") && !this.testToken(">") && !this.testToken("<=") && !this.testToken(">=")) {
                        let nns = ns;
                        if (this.testToken(TokenStrings.Namespace)) {
                            nns = this.consumeTokenAndGetValue();
                        }

                        if (nns === ns) {
                            nsdecl.declaredNames.add(ns + "::" + fname);
                        }
                    }
                }
                else if (this.testToken("typedef")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.Type);
                    const tname = this.consumeTokenAndGetValue();
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }

                    nsdecl.declaredNames.add(ns + "::" + tname);
                }
                else if (this.testToken("typedecl")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.Type);
                    const tname = this.consumeTokenAndGetValue();
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }

                    this.ensureAndConsumeToken("=");
                    this.ensureAndConsumeToken(TokenStrings.Type);

                    nsdecl.declaredNames.add(ns + "::" + tname);

                    if (this.testToken("&")) {
                        this.ensureToken("{"); //we should be at the opening left paren 
                        this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                    }
                }
                else if (this.testToken("enum")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.Type);
                    const tname = this.consumeTokenAndGetValue();
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }

                    if(this.testAndConsumeTokenIf("=")) {
                        this.ensureAndConsumeToken(TokenStrings.Type);
                    }

                    this.ensureToken("{"); //we should be at the opening left paren 
                    this.m_cpos = this.scanCodeParens(); //scan to the closing paren

                    nsdecl.declaredNames.add(ns + "::" + tname);

                    if (this.testToken("&")) {
                        this.ensureToken("{"); //we should be at the opening left paren 
                        this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                    }
                }
                else if (this.testToken("concept") || this.testToken("entity")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.Type);
                    const tname = this.consumeTokenAndGetValue();
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }

                    nsdecl.declaredNames.add(ns + "::" + tname);

                    this.parseTermDeclarations();
                    this.parseProvides(ns === "NSCore");
            
                    this.ensureToken("{"); //we should be at the opening left paren 
                    this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                }
                else {
                    this.raiseError(this.getCurrentLine(), "Failed to parse top-level namespace declaration");
                }
            }
            catch (ex) {
                this.m_cpos++;
                parseok = false;
            }
        }

        return parseok;
    }

    parseCompilationUnitPass2(file: string, contents: string): boolean {
        this.setNamespaceAndFile("[No Namespace]", file);
        const lexer = new Lexer(contents);
        this.initialize(lexer.lex());

        //namespace NS; ...
        this.ensureAndConsumeToken("namespace");
        this.ensureToken(TokenStrings.Namespace);
        const ns = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(";");

        this.setNamespaceAndFile(ns, file);
        const nsdecl = this.m_penv.assembly.ensureNamespace(ns);

        let importok = true;
        let parseok = true;
        while (this.m_cpos < this.m_epos) {
            const rpos = this.scanTokenOptions("function", "operator", "import", "typedef", "concept", "entity", "enum", "typedecl", TokenStrings.EndOfStream);

            try {
                if (rpos === this.m_epos) {
                    break;
                }

                const tk = this.m_tokens[rpos].kind;
                importok = importok && tk === "import";
                if (tk === "import") {
                    if (!importok) {
                        this.raiseError(this.getCurrentLine(), "Using statements must come before other declarations");
                    }

                    this.parseNamespaceUsing(nsdecl);
                }
                else if (tk === "function") {
                    this.parseNamespaceFunction(nsdecl);
                }
                else if (tk === "operator") {
                    this.parseNamespaceOperator(nsdecl);
                }
                else if (tk === "global") {
                    this.parseNamespaceConst(nsdecl);
                }
                else if (tk === "typedef") {
                    this.parseNamespaceTypedef(nsdecl);
                }
                else if (tk === "concept") {
                    this.parseConcept(nsdecl);
                }
                else if (tk === "entity") {
                    this.parseObject(nsdecl, undefined, [], []);
                }
                else if (tk === "enum") {
                    this.parseEnum(nsdecl);
                }
                else if (tk === "typedecl") {
                    this.parseTypeDecl(nsdecl);
                }
                else if (tk === TokenStrings.EndOfStream) {
                    this.parseEndOfStream();
                }
                else {
                    this.raiseError(this.getCurrentLine(), "Invalid top-level definiton");
                }
            }
            catch (ex) {
                this.m_cpos = rpos + 1;
                parseok = false;
            }
        }

        return parseok;
    }

    getParseErrors(): [string, number, string][] | undefined {
        return this.m_errors.length !== 0 ? this.m_errors : undefined;
    }
}

export { 
    SourceInfo, ParseError, Parser,
    unescapeLiteralString
};
