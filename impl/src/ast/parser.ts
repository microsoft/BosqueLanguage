//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ParserEnvironment, FunctionScope } from "./parser_env";
import { FunctionParameter, TypeSignature, NominalTypeSignature, TemplateTypeSignature, ParseErrorTypeSignature, TupleTypeSignature, RecordTypeSignature, FunctionTypeSignature, UnionTypeSignature, AutoTypeSignature, ProjectTypeSignature, EphemeralListTypeSignature, PlusTypeSignature, AndTypeSignature } from "./type_signature";
import { Arguments, TemplateArguments, NamedArgument, PositionalArgument, InvalidExpression, Expression, LiteralNoneExpression, LiteralBoolExpression, LiteralStringExpression, LiteralTypedStringExpression, AccessVariableExpression, AccessNamespaceConstantExpression, LiteralTypedStringConstructorExpression, CallNamespaceFunctionOrOperatorExpression, AccessStaticFieldExpression, ConstructorTupleExpression, ConstructorRecordExpression, ConstructorPrimaryExpression, ConstructorPrimaryWithFactoryExpression, PostfixOperation, PostfixAccessFromIndex, PostfixAccessFromName, PostfixProjectFromIndecies, PostfixProjectFromNames, PostfixModifyWithIndecies, PostfixModifyWithNames, PostfixInvoke, PostfixOp, PrefixNotOp, BinLogicExpression, SelectExpression, BlockStatement, Statement, BodyImplementation, EmptyStatement, InvalidStatement, VariableDeclarationStatement, VariableAssignmentStatement, ReturnStatement, YieldStatement, CondBranchEntry, IfElse, IfElseStatement, InvokeArgument, CallStaticFunctionOrOperatorExpression, AssertStatement, DebugStatement, StructuredAssignment, TupleStructuredAssignment, RecordStructuredAssignment, VariableDeclarationStructuredAssignment, IgnoreTermStructuredAssignment, VariableAssignmentStructuredAssignment, StructuredVariableAssignmentStatement, MatchStatement, MatchEntry, MatchGuard, WildcardMatchGuard, StructureMatchGuard, AbortStatement, BlockStatementExpression, IfExpression, MatchExpression, RecursiveAnnotation, ConstructorPCodeExpression, PCodeInvokeExpression, ExpOrExpression, LiteralRegexExpression, ValidateStatement, NakedCallStatement, ValueListStructuredAssignment, NominalStructuredAssignment, VariablePackDeclarationStatement, VariablePackAssignmentStatement, ConstructorEphemeralValueList, MapEntryConstructorExpression, SpecialConstructorExpression, TypeMatchGuard, PostfixIs, PostfixHasIndex, PostfixHasProperty, PostfixAs, LiteralExpressionValue, LiteralIntegralExpression, LiteralFloatPointExpression, LiteralRationalExpression, IsTypeExpression, AsTypeExpression, PostfixGetIndexOrNone, PostfixGetIndexTry, PostfixGetPropertyOrNone, PostfixGetPropertyTry, ConstantExpressionValue, LiteralNumberinoExpression, BinKeyExpression, LiteralNothingExpression, LiteralTypedPrimitiveConstructorExpression, PostfixGetIndexOption, PostfixGetPropertyOption, SwitchEntry, SwitchExpression, StructuredAssignementPrimitive, SwitchStatement, SwitchGuard, WildcardSwitchGuard, LiteralSwitchGuard, LogicActionExpression } from "./body";
import { Assembly, NamespaceUsing, NamespaceDeclaration, NamespaceTypedef, StaticMemberDecl, StaticFunctionDecl, MemberFieldDecl, MemberMethodDecl, ConceptTypeDecl, EntityTypeDecl, NamespaceConstDecl, NamespaceFunctionDecl, InvokeDecl, TemplateTermDecl, PreConditionDecl, PostConditionDecl, BuildLevel, TypeConditionRestriction, InvariantDecl, TemplateTypeRestriction, StaticOperatorDecl, NamespaceOperatorDecl, OOPTypeDecl, ValidateDecl } from "./assembly";
import { BSQRegex } from "./bsqregex";

const KeywordStrings = [
    "recursive?",
    "recursive",
    
    "_debug",
    "abort",
    "assert",
    "astype",
    "concept",
    "const",
    "elif",
    "else",
    "enum",
    "entity",
    "ensures",
    "err",
    "false",
    "field",
    "fn",
    "pred",
    "function",
    "if",
    "invariant",
    "istype",
    "let",
    "match",
    "method",
    "namespace",
    "none",
    "nothing",
    "of",
    "ok",
    "operator",
    "provides",
    "ref",
    "out",
    "out?",
    "release",
    "return",
    "requires",
    "something",
    "spec",
    "doc",
    "debug",
    "switch",
    "test",
    "true",
    "type",
    "typedef",
    "typedecl",
    "using",
    "validate",
    "var",
    "when",
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

    "&",
    "&&",
    "!",
    "!=",
    "!==",
    ":",
    "::",
    ",",
    ".",
    ".$",
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
    "/",
    "/\\",
    "\\/"
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : a.localeCompare(b); });

const RegexFollows = new Set<string>([
    "_debug",
    "ensures",
    "invariant",
    "return",
    "requires",
    "validate",
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
    "===",
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
    "algebraic",
    "orderable",
    "entrypoint",
    "private",
    "internal",
    "factory",
    "virtual",
    "abstract",
    "override",
    "recursive?",
    "recursive",
    "derived",
    "lazy",
    "memoized",
    "interned",
    "inline",
    "prefix",
    "infix",
    "dynamic",
    "sensitive",
    "chktest",
    "errtest",

    "__chktest",

    "__internal",
    "__typedeclable",
    "__constructable",
    "__primitive",
    "__safe",
    "__assume_safe",
    "__universal"
];

const UnsafeFieldNames = ["is", "as", "isNone", "isSome", "asTry", "asOrNone", "asOptional", "asResult", "hasProperty", "getPropertyOrNone", "getPropertyOption", "getPropertyTry"]

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
    ScopeName: "[SCOPE]",
    Template: "[TEMPLATE]",
    Identifier: "[IDENTIFIER]",
    Operator: "[OPERATOR]",
    FollowTypeSep: "[FOLLOWTYPE]",

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

    static createIgnoreSourceInfo(): SourceInfo
    {
        return new SourceInfo(-1, -1, -1, -1);
    }
}

type CodeFileInfo = { 
    srcpath: string, 
    filename: string, 
    contents: string
};

function unescapeLiteralString(str: string): string {
    let rs = str
        .replace(/\\0/g, "\0")
        .replace(/\\'/g, "'")
        .replace(/\\"/g, "\"")
        .replace(/\\n/g, "\n")
        .replace(/\\r/g, "\r")
        .replace(/\\t/g, "\t");

    return rs.replace(/\\\\/g, "\\");
}

class Lexer {
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

    private m_macrodefs: string[];
    private m_namespaceScopes: Set<String> | undefined;

    private m_input: string;
    private m_internTable: Map<string, string>;
    private m_cline: number;
    private m_linestart: number;
    private m_cpos: number;
    private m_tokens: Token[];

    constructor(input: string, macrodefs: string[], namespaceScopes: Set<String> | undefined) {
        this.m_macrodefs = macrodefs;
        this.m_namespaceScopes = namespaceScopes;

        this.m_input = input;
        this.m_internTable = new Map<string, string>();
        this.m_cline = 1;
        this.m_linestart = 0;
        this.m_cpos = 0;
        this.m_tokens = [];
    }

    ////
    //Helpers
    private isInScopeNameMode(): boolean {
        return this.m_namespaceScopes === undefined;
    }

    private static readonly _s_scopenameRe = /(([A-Z][_a-zA-Z0-9]+)::)*([A-Z][_a-zA-Z0-9]+)/y;
    private static readonly _s_typenameRe = /[A-Z][_a-zA-Z0-9]+/y;
    private static readonly _s_istypenameRe = /^[A-Z][_a-zA-Z0-9]+$/y;
    private tryExtractScopeName(): string | undefined {
        if(this.m_namespaceScopes !== undefined) {
            return undefined;
        }

        Lexer._s_scopenameRe.lastIndex = this.m_cpos;
        const m = Lexer._s_scopenameRe.exec(this.m_input);
        if(m === null) {
            return undefined;
        }
        else {
            return m[0];
        }
    }

    private tryExtractNamespaceName(): string | undefined {
        if(this.m_namespaceScopes === undefined) {
            return undefined;
        }

        Lexer._s_scopenameRe.lastIndex = this.m_cpos;
        const m = Lexer._s_scopenameRe.exec(this.m_input);
        if(m === null) {
            return undefined;
        }
        else {
            const fullscope = m[0];
            if(this.m_namespaceScopes.has(fullscope)) {
                return fullscope;
            }
            else {
                let ttrim = fullscope.lastIndexOf("::");
                let pscope = fullscope;
                while(ttrim !== -1) {
                    pscope = pscope.substring(0, ttrim);

                    if(this.m_namespaceScopes.has(pscope)) {
                        return pscope;
                    }
                   
                    ttrim = pscope.lastIndexOf("::");
                }
                return undefined;
            }
        }
    }

    private tryExtractTypenameName(): string | undefined {
        if(this.m_namespaceScopes === undefined) {
            return undefined;
        }

        Lexer._s_typenameRe.lastIndex = this.m_cpos;
        const m = Lexer._s_typenameRe.exec(this.m_input);
        if(m === null) {
            return undefined;
        }
        else {
            return m[0];
        }
    }

    public isDeclTypeName(str: string): boolean {
        Lexer._s_istypenameRe.lastIndex = 0;
        return Lexer._s_istypenameRe.test(str);
    }

    private isTemplateName(str: string): boolean {
        return str.length === 1 && /^[A-Z]$/.test(str);
    }

    //TODO: we need to make sure that someone doesn't name a local variable "_"
    private isIdentifierName(str: string): boolean {
        return /^([$]?([_a-z]|([_a-z][_a-zA-Z0-9]*[a-zA-Z0-9])))$/.test(str);
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

    private static readonly _s_whitespaceRe = /\s+/y;
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

    private static readonly _s_commentRe = /(\/\/.*)|(\/\*(.|\s)*?\*\/)/uy;
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
    private static readonly _s_rationalRe = /((0|[1-9][0-9]*)|(0|[1-9][0-9]*)\/([1-9][0-9]*))R/y;

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
        const mnio = Lexer._s_numberinoRe.exec(this.m_input);
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

    private static readonly _s_regexRe = /\/[^"\\\r\n]*(\\(.)[^"\\\r\n]*)*\//y;
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
    private static readonly _s_operatorRe = /_([\\a-zA-Z0-9]+)_/y;
    private tryLexSymbol() {
        Lexer._s_symbolRe.lastIndex = this.m_cpos;
        const ms = Lexer._s_symbolRe.exec(this.m_input);
        if (ms === null) {
            return false;
        }

        const sym = SymbolStrings.find((value) => ms[0].startsWith(value));
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

    private static readonly _s_nameRe = /(recursive\?)|(out\?)|([$]?\w+)/y;
    private tryLexName(): boolean {
        Lexer._s_nameRe.lastIndex = this.m_cpos;
        const m = Lexer._s_nameRe.exec(this.m_input);

        const kwmatch = (m !== null) ? Lexer.findKeywordString(m[0]) : undefined;
        if (kwmatch !== undefined && m !== null) {
            this.recordLexToken(this.m_cpos + m[0].length, kwmatch);
            return true;
        }
        else if (m !== null && this.isIdentifierName(m[0])) {
            const name = m[0];
            const isTypeThing = /^_[A-Z]/.test(name);
            if (isTypeThing) {
                this.recordLexToken(this.m_cpos + 1, TokenStrings.FollowTypeSep);
            }
            else {
                this.recordLexTokenWData(this.m_cpos + name.length, TokenStrings.Identifier, name);
            }
            return true;
        }
        else if (m !== null && this.isTemplateName(m[0])) {
            const name = m[0];
            this.recordLexTokenWData(this.m_cpos + name.length, TokenStrings.Template, name);
            return true;
        }
        else {
            if(this.isInScopeNameMode()) {
                const scopeopt = this.tryExtractScopeName();
                if(scopeopt !== undefined) {
                    this.recordLexTokenWData(this.m_cpos + scopeopt.length, TokenStrings.ScopeName, scopeopt);
                    return true;
                }
                else {
                    this.recordLexToken(this.m_cpos + 1, TokenStrings.Error);
                    return false;
                }
            }
            else {
                const nsopt = this.tryExtractNamespaceName();
                if(nsopt !== undefined) {
                    this.recordLexTokenWData(this.m_cpos + nsopt.length, TokenStrings.Namespace, nsopt);
                    return true;
                }
                else {
                    const topt = this.tryExtractTypenameName();
                    if(topt !== undefined) {
                        this.recordLexTokenWData(this.m_cpos + topt.length, TokenStrings.Type, topt);
                        return true;
                    }
                    else {
                        this.recordLexToken(this.m_cpos + 1, TokenStrings.Error);
                        return false;
                    }
                }
            }
        }
    }

    static isAttributeKW(str: string) {
        return AttributeStrings.indexOf(str) !== -1;
    }

    private static readonly _s_macroRe = /(#if[ ]+([A-Z][_A-Z0-9]*)|#else|#endif)/y;
    tryLexMacroOp(): [string, string | undefined] | undefined {
        Lexer._s_macroRe.lastIndex = this.m_cpos;
        const m = Lexer._s_macroRe.exec(this.m_input);
        if (m === null) {
            return undefined;
        }

        const name = m[0].trim();
        this.m_cpos += m[0].length;

        if(name.slice(0, "#if".length) === "#if") {
            return ["#if", name.slice("#if".length).trim()];
        }
        else {
            return [name, undefined]
        }
    }

    lex(): Token[] {
        if (this.m_tokens.length !== 0) {
            return this.m_tokens;
        }

        let mode: "scan" | "normal" = "normal";
        let macrostack: ("scan" | "normal")[] = []

        this.m_tokens = [];
        while (this.m_cpos < this.m_input.length) {
            if(mode === "scan") {
                const macro = this.tryLexMacroOp();
                if (macro !== undefined) {
                    if (macro[0] === "#if") {
                        macrostack.push("scan")
                    }
                    else if (macro[0] === "#else") {
                        mode = "normal";
                    }
                    else {
                        mode = macrostack.pop() as "scan" | "normal";
                    }
                }
                else {
                    const nexthash = this.m_input.indexOf("#", this.m_cpos + 1);
                    if(nexthash === -1) {
                        //ended in dangling macro
                        this.recordLexToken(this.m_input.length, TokenStrings.Error);
                        this.m_cpos = this.m_input.length;
                    }
                    else {
                        const skips = this.m_input.slice(this.m_cpos, nexthash);

                        for (let i = 0; i < skips.length; ++i) {
                            if (skips[i] === "\n") {
                                this.m_cline++;
                                this.m_linestart = this.m_cpos + i + 1;
                            }
                        }

                        this.m_cpos = nexthash;
                    }
                }
            }
            else {
                const macro = this.tryLexMacroOp();
                if(macro !== undefined) {
                    if(macro[0] === "#if") {
                        macrostack.push("normal")
                        if(this.m_macrodefs.includes(macro[1] as string)) {
                            mode = "normal";
                        }
                        else {
                            mode = "scan";
                        }
                    }
                    else if(macro[0] === "#else") {
                        mode = "scan";
                    }
                    else {
                        mode = macrostack.pop() as "scan" | "normal";
                    }
                }
                else {
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
    PCodeFn,
    PCodePred,
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

    readonly sortedSrcFiles: {fullname: string, shortname: string}[]; 

    constructor(assembly: Assembly, srcFileNames: {fullname: string, shortname: string}[]) {
        this.m_tokens = [];
        this.m_cpos = 0;
        this.m_epos = 0;

        this.m_penv = new ParserEnvironment(assembly);
        this.m_errors = [];
        this.m_recoverStack = [];

        this.sortedSrcFiles = srcFileNames.sort((a, b) => a.fullname.localeCompare(b.fullname));
    }

    private initialize(toks: Token[]) {
        this.m_tokens = toks;
        this.m_cpos = 0;
        this.m_epos = toks.length;
    }

    ////
    //Helpers

    private generateBodyID(sinfo: SourceInfo, srcFile: string, etag?: string): string {
        //Keep consistent with version in type checker!!!
        const sfpos = this.sortedSrcFiles.findIndex((entry) => entry.fullname === srcFile);

        return `${this.sortedSrcFiles[sfpos].shortname}#k${sfpos}${etag !== undefined ? ("_" + etag) : ""}::${sinfo.line}@${sinfo.pos}`;
    }

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
        if(this.testToken("doc") || this.testToken("spec") || this.testToken("debug") || this.testToken("test") || this.testToken("release")) {
            return this.consumeTokenAndGetValue() as "doc" | "spec" | "debug" | "test" | "release";
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

        const bodyid = this.generateBodyID(sinfo, srcFile);

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
                argtype = this.parseTypeSignature();
            }
            else {
                if (ikind !== InvokableKind.PCodeFn && ikind !== InvokableKind.PCodePred) {
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
                    this.raiseError(line, "Literal match parameters are only allowed on dynamic operator definitions");
                }

                litexp = this.parseLiteralExpression();
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

        const allTypedParams = params.every((param) => !(param[1] instanceof AutoTypeSignature));
        if (this.testAndConsumeTokenIf(":")) {
            resultInfo = this.parseResultType(false);
        }
        else {
            if (ikind === InvokableKind.PCodePred && allTypedParams) {
                resultInfo = new NominalTypeSignature("Core", ["Bool"]);
            }

            if (ikind !== InvokableKind.PCodeFn && ikind !== InvokableKind.PCodePred) {
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
            if (ikind === InvokableKind.PCodeFn || ikind === InvokableKind.PCodePred) {
                this.ensureAndConsumeToken("=>");
            }
            else {
                [preconds, postconds] = this.parsePreAndPostConditions(sinfo, argNames, resultInfo);
            }

            try {
                this.m_penv.pushFunctionScope(new FunctionScope(argNames, resultInfo, ikind === InvokableKind.PCodeFn || ikind === InvokableKind.PCodePred));
                body = this.parseBody(bodyid, srcFile);
                captured = this.m_penv.getCurrentFunctionScope().getCaptureVars();
                this.m_penv.popFunctionScope();
            }
            catch (ex) {
                this.m_penv.popFunctionScope();
                throw ex;
            }
        }

        if (ikind === InvokableKind.PCodeFn || ikind === InvokableKind.PCodePred) {
            const bbody = body as BodyImplementation;
            return InvokeDecl.createPCodeInvokeDecl(this.m_penv.getCurrentNamespace(), sinfo, this.getCurrentSrcInfo(), bodyid, srcFile, attributes, isrecursive, fparams, restName, restType, resultInfo, captured, bbody, ikind === InvokableKind.PCodeFn, ikind === InvokableKind.PCodePred);
        }
        else {
            if(body !== undefined) {
                return InvokeDecl.createStandardInvokeDecl(this.m_penv.getCurrentNamespace(), sinfo, this.getCurrentSrcInfo(), bodyid, srcFile, attributes, isrecursive, terms, termRestrictions, fparams, restName, restType, resultInfo, preconds, postconds, body);
            }
            else {
                return InvokeDecl.createStandardInvokeDecl(this.m_penv.getCurrentNamespace(), sinfo, this.getCurrentSrcInfo(), bodyid, srcFile, attributes, isrecursive, terms, termRestrictions, fparams, restName, restType, resultInfo, preconds, postconds, undefined);
            }
        }
    }

    ////
    //Type parsing

    private parseResultType(parensreq: boolean): TypeSignature {
        if (this.testAndConsumeTokenIf("(|")) {
            const decls = this.parseEphemeralListOf(() => {
                const tdecl = this.parseTypeSignature();
                return tdecl;
            });

            this.ensureAndConsumeToken("|)");
            return new EphemeralListTypeSignature(decls);
        }
        else {
            if(parensreq) {
                return this.parseTypeSignature();
            }
            else {
                const decls = this.parseEphemeralListOf(() => {
                    const tdecl = this.parseTypeSignature();
                    return tdecl;
                });
    
                return decls.length === 1 ? decls[0] : new EphemeralListTypeSignature(decls);
            }
        }
    } 

    private parseTypeSignature(): TypeSignature {
        return this.parseOrCombinatorType();
    }

    private parseOrCombinatorType(): TypeSignature {
        const ltype = this.parsePostfixTypeReference();
        if (!this.testToken("|")) {
            return ltype;
        }
        else {
            this.consumeToken();
            return Parser.orOfTypeSignatures(ltype, this.parseOrCombinatorType());
        }
    }

    private parsePostfixTypeReference(): TypeSignature {
        let roottype = this.parseCombineCombinatorType();
        while (this.testToken("?")) {
            roottype = this.parseNoneableType(roottype);
        }
        return roottype;
    }

    private parseNoneableType(basetype: TypeSignature): TypeSignature {
        this.ensureAndConsumeToken("?");
        return Parser.orOfTypeSignatures(basetype, this.m_penv.SpecialNoneSignature);
    }

    private parseCombineCombinatorType(): TypeSignature {
        const ltype = this.parseProjectType();
        if (!this.testToken("&") && !this.testToken("+")) {
            return ltype;
        }
        else {
            if(this.testToken("&")) {
                this.consumeToken();
                return this.andOfTypeSignatures(ltype, this.parseCombineCombinatorType());
            }
            else {
                this.consumeToken();
                return this.plusOfTypeSignatures(ltype, this.parseCombineCombinatorType());
            }
        }
    }

    private parseProjectType(): TypeSignature {
        const ltype = this.parseBaseTypeReference();
        if (!this.testToken("!")) {
            return ltype;
        }
        else {
            this.consumeToken();
            const ptype = this.parseNominalType();
            
            return new ProjectTypeSignature(ltype, ptype);
        }
    }

    private parseBaseTypeReference(): TypeSignature {
        switch (this.peekToken()) {
            case TokenStrings.Template:
                return this.parseTemplateTypeReference();
            case TokenStrings.Namespace:
            case TokenStrings.Type:
                return this.parseNominalType();
            case "[":
                return this.parseTupleType();
            case "{":
                return this.parseRecordType();
            case "fn":
            case "pred":
            case "recursive?":
            case "recursive":
                return this.parsePCodeType();
            case TokenStrings.ScopeName: {
                //TODO: This is a dummy case for the parse provides call in pass1 where we just need to scan and discard the type info -- we should actually write a better pass for this
                this.consumeToken();
                this.parseTermList();
                return new NominalTypeSignature("Core", ["DummySig"]);
            }
            default: {
                this.ensureAndConsumeToken("(");
                const ptype = this.parseTypeSignature();
                this.ensureAndConsumeToken(")");

                return ptype;
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
                    return this.parseTypeSignature();
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
        let ns: string | undefined = undefined;
        if (this.testToken(TokenStrings.Namespace)) {
            ns = this.consumeTokenAndGetValue();
            this.ensureAndConsumeToken("::");
        }

        const tname = this.consumeTokenAndGetValue();
        ns = this.m_penv.tryResolveNamespace(ns, tname);
        if (ns === undefined) {
            ns = "[Unresolved Error]";
        }

        let tnames: string[] = [tname];
        let terms: TypeSignature[] = this.parseTermList();

        while (this.testFollows("::", TokenStrings.Type)) {
            this.ensureAndConsumeToken("::");

            this.ensureToken(TokenStrings.Type);
            const stname = this.consumeTokenAndGetValue();
            tnames.push(stname);

            const sterms = this.parseTermList();
            terms = [...terms, ...sterms];
        }

        return new NominalTypeSignature(ns as string, tnames, terms);
    }

    private parseTupleType(): TypeSignature {
        let entries: TypeSignature[] = [];

        try {
            this.setRecover(this.scanMatchingParens("[", "]"));
            entries = this.parseListOf<TypeSignature>("[", "]", ",", () => {
                const rtype = this.parseTypeSignature();

                return rtype;
            })[0];

            this.clearRecover();
            return new TupleTypeSignature(entries);
        }
        catch (ex) {
            this.processRecover();
            return new ParseErrorTypeSignature();
        }
    }

    private parseRecordType(): TypeSignature {
        let entries: [string, TypeSignature][] = [];

        try {
            this.setRecover(this.scanMatchingParens("{", "}"));

            let pnames = new Set<string>();
            entries = this.parseListOf<[string, TypeSignature]>("{", "}", ",", () => {
                this.ensureToken(TokenStrings.Identifier);

                const name = this.consumeTokenAndGetValue();
                if(UnsafeFieldNames.includes(name)) {
                    this.raiseError(this.getCurrentLine(), `Property name "${name}" is ambigious with the methods that Record may provide`);
                }

                if(pnames.has(name)) {
                    this.raiseError(this.getCurrentLine(), `Duplicate property name "${name}" in record declaration`);
                }
                pnames.add(name);

                this.ensureAndConsumeToken(":");
                const rtype = this.parseTypeSignature();

                return [name, rtype];
            })[0];

            this.clearRecover();
            return new RecordTypeSignature(entries);
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

        const ispred = this.testToken("pred");
        this.consumeToken();

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
                const argtype = this.parseTypeSignature();

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
            return new FunctionTypeSignature(recursive, fparams, restName, restType, resultInfo, ispred);
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
                    let exp = this.parseExpression();

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
                    let exp = this.parseExpression();

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
                targs.push(this.parseTypeSignature());

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
        const args = this.parseArguments("{", "}");

        return new ConstructorPrimaryExpression(sinfo, otype, args);
    }

    private parseConstructorPrimaryWithFactory(otype: TypeSignature, fname: string, targs: TemplateArguments, rec: RecursiveAnnotation): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const args = this.parseArguments("{", "}");

        return new ConstructorPrimaryWithFactoryExpression(sinfo, otype, fname, rec, targs, args);
    }

    private parsePCodeTerm(): Expression {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();

        let isrecursive: "yes" | "no" | "cond" = "no";
        if(this.testAndConsumeTokenIf("recursive")) {
            isrecursive = "yes";
        }
        else if(this.testAndConsumeTokenIf("recursive?")) {
            isrecursive = "cond";
        }
        else {
            isrecursive = "no";
        }

        const ispred = this.testToken("pred");
        this.consumeToken();

        const sig = this.parseInvokableCommon(ispred ? InvokableKind.PCodePred : InvokableKind.PCodeFn, false, [], isrecursive, [], undefined);
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
        this.ensureAndConsumeToken(TokenStrings.FollowTypeSep);

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

            return new NominalTypeSignature(ns as string, [tname], []);
        }
    }

    private parseFollowTypeConstructor(): TypeSignature {
        if (this.testToken(TokenStrings.Template)) {
            return this.parseTemplateTypeReference();
        }
        else {
            const ostype = this.parseNominalType();

            return ostype;
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
                else if(exp instanceof LiteralNumberinoExpression) {
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
                else if(exp instanceof LiteralNumberinoExpression) {
                    return [true, new LiteralNumberinoExpression(exp.sinfo, exp.value.startsWith("-") ? exp.value.slice(1) : ("-" + exp.value))];
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

    private parseLiteralExpression(): LiteralExpressionValue {
        const sinfo = this.getCurrentSrcInfo();

        try {
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(), this.m_penv.SpecialAutoSignature, true));
            const exp = this.parsePrefixExpression();
            const captured = this.m_penv.getCurrentFunctionScope().getCaptureVars();

            if(captured.size !== 0) {
                this.raiseError(sinfo.line, "Cannot reference local variables in constant expression");
            }

            this.m_penv.popFunctionScope();

            return new LiteralExpressionValue(exp);
        }
        catch (ex) {
            this.m_penv.popFunctionScope();
            throw ex;
        }
    }

    private parseConstExpression(capturesok: boolean): ConstantExpressionValue {
        const sinfo = this.getCurrentSrcInfo();

        try {
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(), this.m_penv.SpecialAutoSignature, true));
            const exp = this.parseOfExpression();
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

    private checkTypeScopeBasedExpressionFollowsParens(): boolean {
        const lpos = this.scanMatchingParens("(", ")");
        const ptok = this.peekToken(lpos - this.m_cpos);

        return ptok === "::";
    }

    private parsePrimaryExpression(): Expression {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();

        const tk = this.peekToken();
        if (tk === "none") {
            this.consumeToken();
            return new LiteralNoneExpression(sinfo);
        }
        else if (tk === "nothing") {
            this.consumeToken();
            return new LiteralNothingExpression(sinfo);
        }
        else if (tk === "true" || tk === "false") {
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
            const re = BSQRegex.parse(this.m_penv.getCurrentNamespace(), restr);
            if(typeof(re) === "string") {
                this.raiseError(line, re);
            }

            this.m_penv.assembly.addLiteralRegex(re as BSQRegex);
            return new LiteralRegexExpression(sinfo, re as BSQRegex);
        }
        else if (tk === "ok" || tk === "err" || tk === "something") {
            this.consumeToken();
            this.ensureAndConsumeToken("(");
            let arg = new LiteralNoneExpression(this.getCurrentSrcInfo());
            if(tk === "ok" || tk === "something") {
                arg = this.parseExpression();
            }
            else {
                if(!this.testToken(")")) {
                    arg = this.parseExpression();
                }
            }
            this.ensureAndConsumeToken(")");

            return new SpecialConstructorExpression(sinfo, tk, arg);
        }
        else if (tk === TokenStrings.Identifier) {
            let namestr = this.consumeTokenAndGetValue();

            const tryfunctionns = this.m_penv.tryResolveNamespace(undefined, namestr);
            const isvar = this.m_penv.isVarDefinedInAnyScope(namestr) || tryfunctionns === undefined || namestr.startsWith("$");
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
                if (tryfunctionns === undefined) {
                    this.raiseError(line, `Cannot resolve namespace for "${namestr}"`);
                }

                const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
                const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";
                const args = this.parseArguments("(", ")");

                return new CallNamespaceFunctionOrOperatorExpression(sinfo, tryfunctionns as string, namestr, targs, rec, args, "std");
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
        else if (tk === "fn" || this.testFollows("recursive", "fn") || this.testFollows("recursive?", "fn") || tk === "pred" || this.testFollows("recursive", "pred") || this.testFollows("recursive?", "pred")) {
            return this.parsePCodeTerm();
        }
        else if (tk === "(" && !this.checkTypeScopeBasedExpressionFollowsParens()) {
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
        else if (this.testToken("[")) {
            const args = this.parseArguments("[", "]");
            return new ConstructorTupleExpression(sinfo, args);
        }
        else if  (this.testToken("{")) {
            const args = this.parseArguments("{", "}");
            return new ConstructorRecordExpression(sinfo, args);
        }
        else if (this.testToken("(|")) {
            const args = this.parseArguments("(|", "|)");
            return new ConstructorEphemeralValueList(sinfo, args);
        }
        else if (this.testToken("/\\") || this.testToken("\\/")) {
            const op = this.consumeTokenAndGetValue() as "/\\" | "\\/";
            const args = this.parseArguments("(", ")");
            return new LogicActionExpression(sinfo, op, args);
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Identifier)) {
            //it is a namespace access of some type
            let ns: string | undefined = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            ns = this.m_penv.tryResolveNamespace(ns, name);
            if (ns === undefined) {
                ns = "[Unresolved Error]";
            }

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
            let ns: string | undefined = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            ns = this.m_penv.tryResolveNamespace(ns, name);
            if (ns === undefined) {
                ns = "[Unresolved Error]";
            }

            const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";
            const args = this.parseArguments("(", ")");

            return new CallNamespaceFunctionOrOperatorExpression(sinfo, ns, name, new TemplateArguments([]), rec, args, "std");
        }
        else {
            const ttype = this.parseTypeSignature();
            if (this.testFollows("::", TokenStrings.Identifier)) {
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                if (!this.testToken("<") && !this.testToken("[") && !this.testToken("(") && !this.testToken("{")) {
                    //just a static access
                    return new AccessStaticFieldExpression(sinfo, ttype, name);
                }
                else {
                    const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
                    const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";
                    if(this.testToken("{")) {
                        return this.parseConstructorPrimaryWithFactory(ttype, name, targs, rec);
                    }
                    else {
                        const args = this.parseArguments("(", ")");
                        return new CallStaticFunctionOrOperatorExpression(sinfo, ttype, name, targs, rec, args, "std");
                    }
                }
            }
            else if (this.testFollows("{")) {
                if(this.testFollows("{", TokenStrings.TypedString)) {
                    this.ensureAndConsumeToken("{");
                    const tstring = this.consumeTokenAndGetValue();
                    this.ensureAndConsumeToken("}");

                    return new LiteralTypedStringConstructorExpression(sinfo, tstring, ttype)
                }
                else {
                    return this.parseConstructorPrimary(ttype);
                }
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
            this.ensureAndConsumeToken(TokenStrings.FollowTypeSep);
             
            const ttype = this.parseFollowTypeConstructor();
            return [new LiteralTypedStringExpression(sinfo, tstring, ttype), ops];
        }
        else {
            let exp = this.parsePrimaryExpression();

            let cpos = 0;
            while(cpos < ops.length) {
                const op = ops[cpos];

                let done = false;
                [done, exp] = this.processPrefixOnLiteralExpressionsIfNeeded(exp, op);
                if (!done) {
                    break;
                }

                cpos++;
            }
            
            const rops = ops.slice(cpos);
            if (this.testToken(TokenStrings.FollowTypeSep)) {
                const ttype = this.parseFollowTypeTag();

                if(exp instanceof LiteralIntegralExpression) {
                    return [new LiteralTypedPrimitiveConstructorExpression(sinfo, exp.value, exp.itype, ttype), rops];
                }
                else if(exp instanceof LiteralFloatPointExpression) {
                    return [new LiteralTypedPrimitiveConstructorExpression(sinfo, exp.value, exp.fptype, ttype), rops];
                }
                else if(exp instanceof LiteralRationalExpression) {
                    return [new LiteralTypedPrimitiveConstructorExpression(sinfo, exp.value, exp.rtype, ttype), rops];
                }
                else {
                    if(!(exp instanceof LiteralNumberinoExpression)) {
                        this.raiseError(sinfo.line, "Expected literal value -- int, float, rational, or numberino");
                    }

                    const rexp = exp as LiteralNumberinoExpression;
                    return [new LiteralTypedPrimitiveConstructorExpression(sinfo, rexp.value, undefined, ttype), rops];
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

    private handleSpecialCaseMethods(sinfo: SourceInfo, specificResolve: TypeSignature | undefined, name: string): PostfixOperation {
        if (specificResolve !== undefined) {
            this.raiseError(this.getCurrentLine(), "Cannot use specific resolve on special methods");
        }

        const line = sinfo.line;
        if (name === "is") {
            this.ensureAndConsumeToken("<");
            const istype = this.parseTypeSignature();
            this.ensureAndConsumeToken(">");
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");

            return new PostfixIs(sinfo, istype);
        }
        else if (name === "isSome") {
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");

            return new PostfixIs(sinfo, this.m_penv.SpecialSomeSignature);
        }
        else if (name === "isNone") {
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");

            return new PostfixIs(sinfo, this.m_penv.SpecialNoneSignature);
        }
        else if (name === "as") {
            this.ensureAndConsumeToken("<");
            const astype = this.parseTypeSignature();
            this.ensureAndConsumeToken(">");
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");

            return new PostfixAs(sinfo, astype);
        }
        else if (name === "hasIndex") {
            this.ensureAndConsumeToken("<");
            const idx = this.parseTupleIndex();
            this.ensureAndConsumeToken(">");
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");
            return new PostfixHasIndex(sinfo, idx);
        }
        else if (name === "hasProperty") {
            this.ensureAndConsumeToken("<");
            this.ensureToken(TokenStrings.Identifier);
            const pname = this.consumeTokenAndGetValue(); 
            this.ensureAndConsumeToken(">");
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");
            return new PostfixHasProperty(sinfo, pname);
        }
        else if (name === "getIndexOrNone") {
            this.ensureAndConsumeToken("<");
            const idx = this.parseTupleIndex();
            this.ensureAndConsumeToken(">");
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");
            return new PostfixGetIndexOrNone(sinfo, idx);
        }
        else if (name === "getIndexOption") {
            this.ensureAndConsumeToken("<");
            const idx = this.parseTupleIndex();
            this.ensureAndConsumeToken(">");
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");
            return new PostfixGetIndexOption(sinfo, idx);
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
            return new PostfixGetIndexTry(sinfo, idx, exp);
        }
        else if (name === "getPropertyOrNone") {
            this.ensureAndConsumeToken("<");
            this.ensureToken(TokenStrings.Identifier);
            const pname = this.consumeTokenAndGetValue(); 
            this.ensureAndConsumeToken(">");
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");
            return new PostfixGetPropertyOrNone(sinfo, pname);
        }
        else if (name === "getPropertyOption") {
            this.ensureAndConsumeToken("<");
            this.ensureToken(TokenStrings.Identifier);
            const pname = this.consumeTokenAndGetValue(); 
            this.ensureAndConsumeToken(">");
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");
            return new PostfixGetPropertyOption(sinfo, pname);
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
            return new PostfixGetPropertyTry(sinfo, pname, exp);
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

            if (this.testToken(".") || this.testToken(".$")) {
                const isBinder = this.testToken(".$");
                this.consumeToken();

                if (this.testToken(TokenStrings.Numberino) || this.testToken(TokenStrings.Int) || this.testToken(TokenStrings.Nat)) {
                    if(isBinder) {
                        this.raiseError(sinfo.line, "Cannot use binder in this position");
                    }

                    const index = this.parseTupleIndex();
                    ops.push(new PostfixAccessFromIndex(sinfo, index));
                }
                else if (this.testToken("[")) {
                    if (this.testFollows("[", TokenStrings.Numberino, "=") ||this.testFollows("[", TokenStrings.Int, "=") || this.testFollows("[", TokenStrings.Nat, "=")) {
                        const updates = this.parseListOf<{ index: number, value: Expression }>("[", "]", ",", () => {
                            const idx = this.parseTupleIndex();
                            this.ensureAndConsumeToken("=");

                            try {
                                this.m_penv.getCurrentFunctionScope().pushLocalScope();
                                this.m_penv.getCurrentFunctionScope().defineLocalVar(`$${idx}`, `$${idx}_@${sinfo.pos}`, true);
                                
                                if (isBinder) {    
                                    this.m_penv.getCurrentFunctionScope().defineLocalVar(`$this`, `$this_@${sinfo.pos}`, true);
                                }

                                const value = this.parseExpression();
                                return { index: idx, value: value };
                            }
                            finally {
                                this.m_penv.getCurrentFunctionScope().popLocalScope();
                            }
                        })[0].sort((a, b) => a.index - b.index);

                        ops.push(new PostfixModifyWithIndecies(sinfo, isBinder, updates));
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
                                return { index: idx, reqtype: this.parseTypeSignature() };
                            }
                        })[0];

                        if (indecies.length === 0) {
                            this.raiseError(sinfo.line, "You must have at least one index when projecting");
                        }

                        ops.push(new PostfixProjectFromIndecies(sinfo, false, indecies));
                    }
                }
                else if (this.testToken("{")) {
                    if (this.testFollows("{", TokenStrings.Identifier, "=")) {
                        const updates = this.parseListOf<{ name: string, value: Expression }>("{", "}", ",", () => {
                            this.ensureToken(TokenStrings.Identifier);
                            const uname = this.consumeTokenAndGetValue();
                            this.ensureAndConsumeToken("=");

                            try {
                                this.m_penv.getCurrentFunctionScope().pushLocalScope();
                                this.m_penv.getCurrentFunctionScope().defineLocalVar(`$${uname}`, `$${uname}_@${sinfo.pos}`, true);

                                if (isBinder) {    
                                    this.m_penv.getCurrentFunctionScope().defineLocalVar(`$this`, `$this_@${sinfo.pos}`, true);
                                }

                                const value = this.parseExpression();
                                return { name: uname, value: value };
                            }
                            finally {
                                if (isBinder) {
                                    this.m_penv.getCurrentFunctionScope().popLocalScope();
                                }
                            }
                        })[0].sort((a, b) => a.name.localeCompare(b.name));

                        ops.push(new PostfixModifyWithNames(sinfo, isBinder, updates));
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
                                return { name: nn, reqtype: this.parseTypeSignature() };
                            }
                        })[0];

                        if (names.length === 0) {
                            this.raiseError(sinfo.line, "You must have at least one name when projecting");
                        }

                        ops.push(new PostfixProjectFromNames(sinfo, false, names));
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
                                return { index: idx, reqtype: this.parseTypeSignature() };
                            }
                        })[0];

                        if (indecies.length <= 1) {
                            this.raiseError(sinfo.line, "You must have at least two indecies when projecting out a Ephemeral value pack (otherwise just access the index directly)");
                        }

                        ops.push(new PostfixProjectFromIndecies(sinfo, true, indecies));
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
                                return { name: nn, isopt: false, reqtype: this.parseTypeSignature() };
                            }
                        })[0];

                        if (names.length <= 1) {
                            this.raiseError(sinfo.line, "You must have at least two names when projecting out a Ephemeral value pack (otherwise just access the property/field directly)");
                        }

                        ops.push(new PostfixProjectFromNames(sinfo, true, names));
                    }
                }
                else {
                    let specificResolve: TypeSignature | undefined = undefined;
                    if (this.testToken(TokenStrings.Namespace) || this.testToken(TokenStrings.Type) || this.testToken(TokenStrings.Template)) {
                        specificResolve = this.parseTypeSignature();
                        this.ensureAndConsumeToken("::");
                    }

                    this.ensureToken(TokenStrings.Identifier);
                    const name = this.consumeTokenAndGetValue();

                    if (name === "as" || name === "is" || name === "isSome" || name === "isNone"
                        || name === "hasIndex" || name === "getIndexOrNone" || name === "getIndexOption" || name === "getIndexTry" 
                        || name === "hasProperty" || name === "getPropertyOrNone" || name === "getPropertyOption" || name === "getPropertyTry") {
                        ops.push(this.handleSpecialCaseMethods(sinfo, specificResolve, name));
                    }
                    else if (!(this.testToken("<") || this.testToken("[") || this.testToken("("))) {
                        if (isBinder) {
                            this.raiseError(sinfo.line, "Cannot use binder in this position");
                        }

                        if (specificResolve !== undefined) {
                            this.raiseError(this.getCurrentLine(), "Encountered named access but given type resolver (only valid on method calls)");
                        }

                        ops.push(new PostfixAccessFromName(sinfo, name));
                    }
                    else {
                        //ugly ambiguity with < -- the follows should be a NS, Type, or T token
                        //    this.f.g < (1 + 2) and this.f.g<(Int)>() don't know with bounded lookahead :(
                        //
                        //TODO: in theory it could also be a "(" and we need to do a tryParseType thing OR just disallow () in this position
                        //
                        if (this.testToken("<")) {
                            if (this.testFollows("<", TokenStrings.Namespace) || this.testFollows("<", TokenStrings.Type) || this.testFollows("<", TokenStrings.Template) || this.testFollows("<", "[") || this.testFollows("<", "{") || this.testFollows("<", "(|")) {
                                const terms = this.parseTemplateArguments();
                                const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";

                                try {
                                    if (isBinder) {
                                        this.m_penv.getCurrentFunctionScope().pushLocalScope();
                                        this.m_penv.getCurrentFunctionScope().defineLocalVar(`$this`, `$this_@${sinfo.pos}`, true);
                                    }

                                    const args = this.parseArguments("(", ")");
                                    ops.push(new PostfixInvoke(sinfo, isBinder, specificResolve, name, terms, rec, args));
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

                                ops.push(new PostfixAccessFromName(sinfo, name));
                            }
                        }
                        else {
                            const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";

                            try {
                                if (isBinder) {
                                    this.m_penv.getCurrentFunctionScope().pushLocalScope();
                                    this.m_penv.getCurrentFunctionScope().defineLocalVar(`$this`, `$this_@${sinfo.pos}`, true);
                                }

                                const args = this.parseArguments("(", ")");
                                ops.push(new PostfixInvoke(sinfo, isBinder, specificResolve, name, new TemplateArguments([]), rec, args));
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
            return [this.parseSwitchExpression(), ops];
        }
        else if (this.testToken("match")) {
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

        return this.prefixStackApplicationHandler(sinfo, ops.reverse());
    }

    private isMultiplicativeFollow(): boolean {
        if(this.testToken("*") || this.testToken("/")) {
            return true;
        }
        else if(this.testToken(TokenStrings.Operator) && this.m_penv.tryResolveAsInfixBinaryOperator(this.peekTokenData(), 2) !== undefined) {
            return true;
        }
        else {
            return false;
        }
    }

    private parseMultiplicativeExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parsePrefixExpression();

        if(!this.isMultiplicativeFollow()) {
            return exp;
        }
        else {
            let aexp: Expression = exp;
            while (this.isMultiplicativeFollow()) {
                if (this.testToken("*") || this.testToken("/")) {
                    const op = this.consumeTokenAndGetValue();
                    const ons = this.m_penv.tryResolveAsInfixBinaryOperator(op, 2);
                    if (ons === undefined) {
                        this.raiseError(sinfo.line, "Could not resolve operator");
                    }

                    const lhs = new PositionalArgument(undefined, false, aexp);
                    const rhs = new PositionalArgument(undefined, false, this.parsePrefixExpression());
                    aexp = new CallNamespaceFunctionOrOperatorExpression(sinfo, ons as string, op, new TemplateArguments([]), "no", new Arguments([lhs, rhs]), "infix");
                }
                else {
                    const ons = this.m_penv.tryResolveAsInfixBinaryOperator(this.peekTokenData(), 2) as string;

                    const op = this.consumeTokenAndGetValue();
                    const lhs = new PositionalArgument(undefined, false, aexp);
                    const rhs = new PositionalArgument(undefined, false, this.parsePrefixExpression());
                    aexp = new CallNamespaceFunctionOrOperatorExpression(sinfo, ons as string, op, new TemplateArguments([]), "no", new Arguments([lhs, rhs]), "infix");
                }
            }

            return aexp;
        }
    }

    private isAdditiveFollow(): boolean {
        if(this.testToken("+") || this.testToken("-")) {
            return true;
        }
        else if(this.testToken(TokenStrings.Operator) && this.m_penv.tryResolveAsInfixBinaryOperator(this.peekTokenData(), 3) !== undefined) {
            return true;
        }
        else {
            return false;
        }
    }

    private parseAdditiveExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseMultiplicativeExpression();

        if(!this.isAdditiveFollow()) {
            return exp;
        }
        else {
            let aexp: Expression = exp;
            while (this.isAdditiveFollow()) {
                if (this.testToken("+") || this.testToken("-")) {
                    const op = this.consumeTokenAndGetValue();
                    const ons = this.m_penv.tryResolveAsInfixBinaryOperator(op, 3);
                    if (ons === undefined) {
                        this.raiseError(sinfo.line, "Could not resolve operator");
                    }

                    const lhs = new PositionalArgument(undefined, false, aexp);
                    const rhs = new PositionalArgument(undefined, false, this.parseMultiplicativeExpression());
                    aexp = new CallNamespaceFunctionOrOperatorExpression(sinfo, ons as string, op, new TemplateArguments([]), "no", new Arguments([lhs, rhs]), "infix");
                }
                else {
                    const ons = this.m_penv.tryResolveAsInfixBinaryOperator(this.peekTokenData(), 3) as string;

                    const op = this.consumeTokenAndGetValue();
                    const lhs = new PositionalArgument(undefined, false, aexp);
                    const rhs = new PositionalArgument(undefined, false, this.parseMultiplicativeExpression());
                    aexp = new CallNamespaceFunctionOrOperatorExpression(sinfo, ons as string, op, new TemplateArguments([]), "no", new Arguments([lhs, rhs]), "infix");
                }
            }

            return aexp;
        }
    }

    private parseRelationalExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseAdditiveExpression();

        if (this.testToken("===") || this.testToken("!==")) {
            const op = this.consumeTokenAndGetValue();
            return new BinKeyExpression(sinfo, exp, op, this.parseRelationalExpression());
        }
        else if(this.testToken("==") || this.testToken("!=") || this.testToken("<") || this.testToken(">") || this.testToken("<=") || this.testToken(">=")) {
            const ons = this.m_penv.tryResolveAsInfixBinaryOperator(this.peekTokenData(), 4);
            if (ons === undefined) {
                this.raiseError(sinfo.line, "Could not resolve operator");
            }

            const op = this.consumeTokenAndGetValue();
            const lhs = new PositionalArgument(undefined, false, exp);
            const rhs = new PositionalArgument(undefined, false, this.parseRelationalExpression());
            return new CallNamespaceFunctionOrOperatorExpression(sinfo, ons as string, op, new TemplateArguments([]), "no", new Arguments([lhs, rhs]), "infix");
        }
        else if(this.testToken(TokenStrings.Operator) && this.m_penv.tryResolveAsInfixBinaryOperator(this.peekTokenData(), 4) !== undefined) {
            const ons = this.m_penv.tryResolveAsInfixBinaryOperator(this.peekTokenData(), 4) as string;

            const op = this.consumeTokenAndGetValue();
            const lhs = new PositionalArgument(undefined, false, exp);
            const rhs = new PositionalArgument(undefined, false, this.parseRelationalExpression());
            return new CallNamespaceFunctionOrOperatorExpression(sinfo, ons as string, op, new TemplateArguments([]), "no", new Arguments([lhs, rhs]), "infix");
        }
        else {
            return exp;
        }
    }

    private parseAndExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseRelationalExpression();

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

    private parseImpliesExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseOrExpression();

        if (this.testAndConsumeTokenIf("==>")) {
            return new BinLogicExpression(sinfo, exp, "==>", this.parseImpliesExpression());
        }
        else {
            return exp;
        }
    }

    private parseMapEntryConstructorExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        const lexp = this.parseImpliesExpression();   
        if(this.testAndConsumeTokenIf("=>")) {
            const rexp = this.parseImpliesExpression();
        
            return new MapEntryConstructorExpression(sinfo, lexp, rexp);
        }
        else {
            return lexp;
        }
    }

    private parseSelectExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const texp = this.parseMapEntryConstructorExpression();

        if (this.testAndConsumeTokenIf("?")) {
            const exp1 = this.parseMapEntryConstructorExpression();
            this.ensureAndConsumeToken(":");
            const exp2 = this.parseSelectExpression();

            return new SelectExpression(sinfo, texp, exp1, exp2);
        }
        else {
            return texp;
        }
    }

    private parseOfExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        //
        //TODO: This will have an ugly parse if we do -- x astype Int < 3
        //      It will try to parse as Int<3 ... as a type which fails
        //

        let exp = this.parseSelectExpression();
        if (this.testAndConsumeTokenIf("istype")) {
            const oftype = this.parseTypeSignature();

            return new IsTypeExpression(sinfo, exp, oftype);
        }
        else if(this.testAndConsumeTokenIf("astype")) {
            const oftype = this.parseTypeSignature();

            return new AsTypeExpression(sinfo, exp, oftype);
        }
        else {
            return exp;
        }
    }

    private parseExpOrExpression(): Expression {
        const texp = this.parseOfExpression();

        if (this.testFollows("?", "none", "?") || this.testFollows("?", "nothing", "?") || this.testFollows("?", "err", "?")) {
            const ffsinfo = this.getCurrentSrcInfo();
            this.consumeToken();

            let cond: "none" | "nothing" | "err" = this.consumeTokenAndGetValue() as "none" | "nothing" | "err";
            this.consumeToken();

            //TODO: eventually we want to allow arbitrary boolean expressions in the ?...? and an optional following expression as the result

            return new ExpOrExpression(ffsinfo, texp, cond);
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

    private parseSwitchExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        this.ensureAndConsumeToken("switch");

        this.ensureAndConsumeToken("(");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(")");

        try {
            this.m_penv.getCurrentFunctionScope().pushLocalScope();
            this.m_penv.getCurrentFunctionScope().defineLocalVar("$switch", `$switch_@${sinfo.pos}`, true);
            
            let entries: SwitchEntry<Expression>[] = [];
            this.ensureAndConsumeToken("{|");
            entries.push(this.parseSwitchEntry<Expression>(this.getCurrentSrcInfo(), "|}", () => this.parseExpression()));
            while (this.testToken("|")) {
                entries.push(this.parseSwitchEntry<Expression>(this.getCurrentSrcInfo(), "|}", () => this.parseExpression()));
            }
            this.ensureAndConsumeToken("|}");

            return new SwitchExpression(sinfo, mexp, entries);
        }
        finally {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
        }
    }

    private parseMatchExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        this.ensureAndConsumeToken("match");

        this.ensureAndConsumeToken("(");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(")");

        try {
            this.m_penv.getCurrentFunctionScope().pushLocalScope();
            this.m_penv.getCurrentFunctionScope().defineLocalVar("$match", `$match_@${sinfo.pos}`, true);
            
            let entries: MatchEntry<Expression>[] = [];
            this.ensureAndConsumeToken("{|");
            entries.push(this.parseMatchEntry<Expression>(this.getCurrentSrcInfo(), "|}", () => this.parseExpression()));
            while (this.testToken("|")) {
                entries.push(this.parseMatchEntry<Expression>(this.getCurrentSrcInfo(), "|}", () => this.parseExpression()));
            }
            this.ensureAndConsumeToken("|}");

            return new MatchExpression(sinfo, mexp, entries);
        }
        finally {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
        }
    }

    private parseExpression(): Expression {
        return this.parseExpOrExpression();
    }

    ////
    //Statement parsing

    parsePrimitiveStructuredAssignment(sinfo: SourceInfo, vars: "let" | "var" | undefined, decls: Set<string>): StructuredAssignementPrimitive {
        this.ensureToken(TokenStrings.Identifier);
        const name = this.consumeTokenAndGetValue();

        if (name === "_") {
            let itype = this.m_penv.SpecialAnySignature;
            if (this.testAndConsumeTokenIf(":")) {
                itype = this.parseTypeSignature();
            }

            return new IgnoreTermStructuredAssignment(itype);
        }
        else {
            let itype = this.m_penv.SpecialAutoSignature;
            if (this.testAndConsumeTokenIf(":")) {
                itype = this.parseTypeSignature();
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

    parseStructuredAssignment(sinfo: SourceInfo, vars: "let" | "var" | undefined, decls: Set<string>): StructuredAssignment {
        if (this.testToken("[")) {
            const assigns = this.parseListOf<StructuredAssignementPrimitive>("[", "]", ",", () => {
                return this.parsePrimitiveStructuredAssignment(this.getCurrentSrcInfo(), vars, decls);
            })[0];

            return new TupleStructuredAssignment(assigns);
        }
        else if (this.testToken("{")) {
            const assigns = this.parseListOf<[string, StructuredAssignementPrimitive]>("{", "}", ",", () => {
                this.ensureToken(TokenStrings.Identifier);
                const name = this.consumeTokenAndGetValue();

                this.ensureAndConsumeToken("=");
                const subg = this.parsePrimitiveStructuredAssignment(this.getCurrentSrcInfo(), vars, decls);

                return [name, subg];
            })[0];

            return new RecordStructuredAssignment(assigns);
        }
        else if (this.testToken("(|")) {
            const assigns = this.parseListOf<StructuredAssignementPrimitive>("(|", "|)", ",", () => {
                return this.parsePrimitiveStructuredAssignment(this.getCurrentSrcInfo(), vars, decls);
            })[0];

            return new ValueListStructuredAssignment(assigns);
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Type ) || this.testToken(TokenStrings.Type)) {
            const ttype = this.parseTypeSignature();
            const assigns = this.parseListOf<[string | undefined, StructuredAssignementPrimitive]>("{", "}", ",", () => {
                if (this.testFollows(TokenStrings.Identifier, "=")) {
                    this.ensureToken(TokenStrings.Identifier);
                    const name = this.consumeTokenAndGetValue();

                    this.ensureAndConsumeToken("=");
                    const subg = this.parsePrimitiveStructuredAssignment(this.getCurrentSrcInfo(), vars, decls);

                    return [name, subg];
                }
                else {
                    const subg = this.parsePrimitiveStructuredAssignment(this.getCurrentSrcInfo(), vars, decls);

                    return [undefined, subg];
                }
            })[0];

            return new NominalStructuredAssignment(ttype, assigns);
        }
        else {
            return this.parsePrimitiveStructuredAssignment(sinfo, vars, decls);
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

            if (this.testToken("[") || this.testToken("{") || this.testToken("(|") || this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Type) || this.testToken(TokenStrings.Type)) {
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
                        vars.push({name: "_", vtype: (assigns[i] as IgnoreTermStructuredAssignment).assigntype});
                    }
                    else if(assigns[i] instanceof VariableDeclarationStructuredAssignment) {
                        const dv = assigns[i] as VariableDeclarationStructuredAssignment;

                        if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(dv.vname)) {
                            this.raiseError(line, "Variable name is already defined");
                        }
                        this.m_penv.getCurrentFunctionScope().defineLocalVar(dv.vname, dv.vname, false);

                        vars.push({name: dv.vname, vtype: dv.assigntype});
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
        else if (this.testToken("[") || this.testToken("{") || this.testToken("(|")) {
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

            const level = this.parseBuildInfo("release");
            const exp = this.parseExpression();

            this.ensureAndConsumeToken(";");
            return new AssertStatement(sinfo, exp, level);
        }
        else if (tk === "validate") {
            this.consumeToken();

            const exp = this.parseOfExpression();
            let err = new LiteralNoneExpression(sinfo);
            if (this.testFollows("else")) {
                err = this.parseExpression();
            }

            this.ensureAndConsumeToken(";");
            return new ValidateStatement(sinfo, exp, err);
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
            let ns: string | undefined = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            ns = this.m_penv.tryResolveNamespace(ns, name);
            if (ns === undefined) {
                ns = "[Unresolved Error]";
            }

            const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
            const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";
            const args = this.parseArguments("(", ")");

            return new NakedCallStatement(sinfo, new CallNamespaceFunctionOrOperatorExpression(sinfo, ns, name, targs, rec, args, "std"));
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Operator)) {
            //it is a namespace function call
            let ns: string | undefined = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            ns = this.m_penv.tryResolveNamespace(ns, name);
            if (ns === undefined) {
                ns = "[Unresolved Error]";
            }

            const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";
            const args = this.parseArguments("(", ")");

            return new NakedCallStatement(sinfo, new CallNamespaceFunctionOrOperatorExpression(sinfo, ns, name, new TemplateArguments([]), rec, args, "std"));
        }
        else {
            //we should find a type (nominal here) and it is a static invoke or a structured assign
            const ttype = this.parseTypeSignature();

            if (this.testToken("{")) {
                let decls = new Set<string>();
                const assigns = this.parseListOf<[string | undefined, StructuredAssignementPrimitive]>("{", "}", ",", () => {
                    if (this.testFollows(TokenStrings.Identifier, "=")) {
                        this.ensureToken(TokenStrings.Identifier);
                        const name = this.consumeTokenAndGetValue();
    
                        this.ensureAndConsumeToken("=");
                        const subg = this.parsePrimitiveStructuredAssignment(this.getCurrentSrcInfo(), undefined, decls);
    
                        return [name, subg];
                    }
                    else {
                        const subg = this.parsePrimitiveStructuredAssignment(this.getCurrentSrcInfo(), undefined, decls);
    
                        return [undefined, subg];
                    }
                })[0];

                const assign = new NominalStructuredAssignment(ttype, assigns);
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

    private parseSwitchGuard(sinfo: SourceInfo): SwitchGuard {
        this.consumeTokenIf("|");
        
        if (this.testToken(TokenStrings.Identifier)) {
            const tv = this.consumeTokenAndGetValue();
            if (tv !== "_") {
                this.raiseError(sinfo.line, "Expected wildcard match");
            }

            return new WildcardSwitchGuard();
        }
        else {
            const lexp = this.parseLiteralExpression();
            return new LiteralSwitchGuard(lexp);
        }
    }

    private parseMatchGuard(sinfo: SourceInfo): [MatchGuard, Set<string>] {
        this.consumeTokenIf("|");
        
        if (this.testToken(TokenStrings.Identifier)) {
            const tv = this.consumeTokenAndGetValue();
            if (tv !== "_") {
                this.raiseError(sinfo.line, "Expected wildcard match");
            }

            return [new WildcardMatchGuard(), new Set<string>()];
        }
        else {
            if(this.testToken("[")) {
                let decls = new Set<string>();
                if (this.testFollows("[", TokenStrings.Identifier)) {
                    const assign = this.parseStructuredAssignment(this.getCurrentSrcInfo(), "let", decls);
                    return [new StructureMatchGuard(assign, decls), decls];
                }
                else {
                    const oftype = this.parseTupleType();
                    return [new TypeMatchGuard(oftype), decls];
                }
            }
            else if(this.testToken("{")) {
                let decls = new Set<string>();
                if (this.testFollows("{", TokenStrings.Identifier, "=")) {
                    const assign = this.parseStructuredAssignment(this.getCurrentSrcInfo(), "let", decls);
                    return [new StructureMatchGuard(assign, decls), decls];
                }
                else {
                    const oftype = this.parseRecordType();
                    return [new TypeMatchGuard(oftype), decls];
                }
            }
            else {
                let decls = new Set<string>();
                const oftype = this.parseTypeSignature();

                if (this.testToken("{")) {
                    const assigns = this.parseListOf<[string | undefined, StructuredAssignementPrimitive]>("{", "}", ",", () => {
                        if (this.testFollows(TokenStrings.Identifier, "=")) {
                            this.ensureToken(TokenStrings.Identifier);
                            const name = this.consumeTokenAndGetValue();

                            this.ensureAndConsumeToken("=");
                            const subg = this.parsePrimitiveStructuredAssignment(this.getCurrentSrcInfo(), "let", decls);

                            return [name, subg];
                        }
                        else {
                            const subg = this.parsePrimitiveStructuredAssignment(this.getCurrentSrcInfo(), "let", decls);

                            return [undefined, subg];
                        }
                    })[0];

                    const assign = new NominalStructuredAssignment(oftype, assigns);
                    return [new StructureMatchGuard(assign, decls), decls];
                }
                else {
                    return [new TypeMatchGuard(oftype), decls];
                }
            }
        }
    }

    private parseSwitchEntry<T>(sinfo: SourceInfo, tailToken: string, actionp: () => T): MatchEntry<T> {
        const guard = this.parseSwitchGuard(sinfo);
        this.ensureAndConsumeToken("=>");
        const action = actionp();

        const isokfollow = this.testToken(tailToken) || this.testToken("|");
        if(!isokfollow) {
            this.raiseError(this.getCurrentLine(), "Unknown token at end of match entry");
        }

        return new SwitchEntry<T>(guard, action);
    }

    private parseMatchEntry<T>(sinfo: SourceInfo, tailToken: string, actionp: () => T): MatchEntry<T> {
        const [guard, decls] = this.parseMatchGuard(sinfo);
        this.ensureAndConsumeToken("=>");

        if (decls.size !== 0) {
            this.m_penv.getCurrentFunctionScope().pushLocalScope();
            decls.forEach((dv) => {
                if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(dv)) {
                    this.raiseError(sinfo.line, "Variable name is already defined");
                }
                this.m_penv.getCurrentFunctionScope().defineLocalVar(dv, dv, false);
            });
        }

        const action = actionp();

        if(decls.size !== 0) {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
        }

        const isokfollow = this.testToken(tailToken) || this.testToken("|");
        if(!isokfollow) {
            this.raiseError(this.getCurrentLine(), "Unknown token at end of match entry");
        }

        return new MatchEntry<T>(guard, action);
    }

    private parseStatementActionInBlock(): BlockStatement {
        if(this.testToken("{")) {
            return this.parseBlockStatement();
        }
        else {
            return new BlockStatement(this.getCurrentSrcInfo(), [this.parseLineStatement()]);
        }
    }

    private parseSwitchStatement(): Statement {
        const sinfo = this.getCurrentSrcInfo();

        this.ensureAndConsumeToken("switch");

        this.ensureAndConsumeToken("(");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(")");

        try {
            this.m_penv.getCurrentFunctionScope().pushLocalScope();
            this.m_penv.getCurrentFunctionScope().defineLocalVar("$switch", `$switch_@${sinfo.pos}`, true);

            let entries: MatchEntry<BlockStatement>[] = [];
            this.ensureAndConsumeToken("{");
            entries.push(this.parseSwitchEntry<BlockStatement>(this.getCurrentSrcInfo(), "}", () => this.parseStatementActionInBlock()));
            while (this.testToken("|")) {
                entries.push(this.parseSwitchEntry<BlockStatement>(this.getCurrentSrcInfo(), "}", () => this.parseStatementActionInBlock()));
            }
            this.ensureAndConsumeToken("}");

            return new SwitchStatement(sinfo, mexp, entries);
        }
        finally {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
        }
    }

    private parseMatchStatement(): Statement {
        const sinfo = this.getCurrentSrcInfo();

        this.ensureAndConsumeToken("match");

        this.ensureAndConsumeToken("(");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(")");

        try {
            this.m_penv.getCurrentFunctionScope().pushLocalScope();
            this.m_penv.getCurrentFunctionScope().defineLocalVar("$match", `$match_@${sinfo.pos}`, true);

            let entries: MatchEntry<BlockStatement>[] = [];
            this.ensureAndConsumeToken("{");
            entries.push(this.parseMatchEntry<BlockStatement>(this.getCurrentSrcInfo(), "}", () => this.parseStatementActionInBlock()));
            while (this.testToken("|")) {
                entries.push(this.parseMatchEntry<BlockStatement>(this.getCurrentSrcInfo(), "}", () => this.parseStatementActionInBlock()));
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
            return this.parseSwitchStatement();
        }
        else if (this.testToken("match")) {
            return this.parseMatchStatement();
        }
        else {
            return this.parseLineStatement();
        }
    }

    private parseBody(bodyid: string, file: string): BodyImplementation {
        if(this.testToken("=")) {
            this.consumeToken();
            const iname = this.consumeTokenAndGetValue();
            this.ensureAndConsumeToken(";")
            
            return new BodyImplementation(bodyid, file, iname);
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
            return this.parseTypeSignature();
        }
    }

    private parseTermDeclarations(): TemplateTermDecl[] {
        let terms: TemplateTermDecl[] = [];
        if (this.testToken("<")) {
            terms = this.parseListOf<TemplateTermDecl>("<", ">", ",", () => {
                this.ensureToken(TokenStrings.Template);
                const templatename = this.consumeTokenAndGetValue();

                const isunique = this.testToken(TokenStrings.Identifier) && this.peekTokenData() === "unique";
                if(isunique) {
                    this.consumeToken();
                }

                const isgrounded = this.testToken(TokenStrings.Identifier) && this.peekTokenData() === "grounded";
                if(isgrounded) {
                    this.consumeToken();
                }

                const tconstraint = this.parseTemplateConstraint(!this.testToken(",") && !this.testToken(">") && !this.testToken("="));

                let isinfer = false;
                let defaulttype: TypeSignature | undefined = undefined;
                if (this.testAndConsumeTokenIf("=")) {
                    if (this.testAndConsumeTokenIf("?")) {
                        isinfer = true;
                    }
                    else {
                        defaulttype = this.parseTypeSignature();
                    }
                }

                return new TemplateTermDecl(templatename, isunique, isgrounded, tconstraint, isinfer, defaulttype);
            })[0];
        }
        return terms;
    }

    private parseSingleTermRestriction(): TemplateTypeRestriction {
        this.ensureToken(TokenStrings.Template);
        const templatename = this.consumeTokenAndGetValue();

        const isunique = this.testToken(TokenStrings.Identifier) && this.peekTokenData() === "unique";
        if(isunique) {
            this.consumeToken();
        }
        
        const isgrounded = this.testToken(TokenStrings.Identifier) && this.peekTokenData() === "grounded";
        if(isgrounded) {
            this.consumeToken();
        }

        const tconstraint = this.parseTemplateConstraint(true);

        return new TemplateTypeRestriction(new TemplateTypeSignature(templatename), isunique, isgrounded, tconstraint);
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
                
                let level: BuildLevel = "release";
                if (!isvalidate) {
                    level = this.parseBuildInfo(level);
                }

                const exp = this.parseOfExpression();

                let err = new LiteralNoneExpression(sinfo);
                if (this.testAndConsumeTokenIf("else")) {
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

                const level = this.parseBuildInfo("release");
                const exp = this.parseExpression();

                postconds.push(new PostConditionDecl(sinfo, level, exp));

                this.ensureAndConsumeToken(";");
            }
        } finally {
            this.m_penv.popFunctionScope();
        }

        return [preconds, postconds];
    }

    private parseNamespaceDep(): {fromns: string, asns: string} {
        //import NS;
        //import NS as NS;

        this.ensureAndConsumeToken("import");
        this.ensureToken(TokenStrings.ScopeName);
        const fromns = this.consumeTokenAndGetValue();

        let nsp = {fromns: fromns, asns: fromns}; //case of import NS;
        if(this.testToken(TokenStrings.Identifier)) {
            const nn = this.consumeTokenAndGetValue();
            if(nn !== "as") {
                this.raiseError(this.getCurrentLine(), "Expected keyword 'as'");
            }

            this.ensureToken(TokenStrings.ScopeName);
            const asns = this.consumeTokenAndGetValue();

            nsp = {fromns: fromns, asns: asns};
        }
        
        this.ensureAndConsumeToken(";");

        return nsp;
    }

    private parseNamespaceUsing(currentDecl: NamespaceDeclaration) {
        //import NS;
        //import NS as NS;

        this.ensureAndConsumeToken("import");
        this.ensureToken(TokenStrings.Namespace);
        const fromns = this.consumeTokenAndGetValue();

        let asns = fromns; //case of import NS;
        if(this.testToken(TokenStrings.Identifier)) {
            const nn = this.consumeTokenAndGetValue();
            if(nn !== "as") {
                this.raiseError(this.getCurrentLine(), "Expected keyword 'as'");
            }

            this.ensureToken(TokenStrings.Namespace);
            asns = this.consumeTokenAndGetValue();
        }
        
        this.ensureAndConsumeToken(";");

        const ffns = this.m_penv.assembly.getNamespace(fromns);
        const names = [...ffns.declaredNames].map((vv) => vv.slice(ffns.ns.length + 2));

        this.ensureAndConsumeToken(";");

        if (currentDecl.checkUsingNameClash(names)) {
            this.raiseError(this.getCurrentLine(), "Collision between imported using names");
        }

        //
        //TODO: Packaging!!!!
        //
        //Our versioning trick is going to be looking at the imported types and signatures (including transative dependencies). We will split up the 
        //package dependencies into "public" and "internal" -- internal dependencies can be resolved by finding a satisfying version OR cloning. The 
        //public dependences can be part of the exported signatures and must be resolved by finding satifying versions with other packages. 
        //
        //The full NS SHOULD include a part like packageVN, where N is the major version number of the root package. This will allow multiple 
        //coexisting major versions of a package to be used in an application. Versioning must specify a major number or MajorX+, the others 
        //can be *, X+, X-Y, or X-
        //Good design practice would be put the public API type decls in one package and the API sigs + impls in thier own -- this way changing 
        //an API sig only forces updates to that package and the types + impl can be shared with the older versions if needed.
        //

        currentDecl.usings.push(new NamespaceUsing(fromns, asns, names));
    }

    private parseNamespaceTypedef(currentDecl: NamespaceDeclaration) {
        //typedef NAME<T...> = TypeConstraint;

        const attributes = this.parseAttributes();

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

        const btype = this.parseTypeSignature();
        this.consumeToken();

        currentDecl.typeDefs.set((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + tyname, new NamespaceTypedef(attributes, currentDecl.ns, tyname, terms, btype));
    }

    private parseProvides(iscorens: boolean, endtoken: string[]): [TypeSignature, TypeConditionRestriction | undefined][] {
        let provides: [TypeSignature, TypeConditionRestriction | undefined][] = [];
        if (this.testAndConsumeTokenIf("provides")) {
            while (!endtoken.some((tok) => this.testToken(tok))) {
                this.consumeTokenIf(",");

                const pv = this.parseTypeSignature();
                let res: TypeConditionRestriction | undefined = undefined;
                if(this.testAndConsumeTokenIf("when")) {
                    res = this.parseTermRestriction(false);
                }
                provides.push([pv, res]);
            }
        }
        
        if (!iscorens) {
            provides.push([new NominalTypeSignature("Core", ["Object"]), undefined]);
        }

        return provides;
    }

    private parseConstMember(staticMembers: StaticMemberDecl[], allMemberNames: Set<string>, attributes: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] const NAME: T = exp;
        this.ensureAndConsumeToken("const");

        this.ensureToken(TokenStrings.Identifier);
        const sname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const stype = this.parseTypeSignature();

        this.ensureAndConsumeToken("=");
        const value = this.parseConstExpression(false);

        this.ensureAndConsumeToken(";");

        if (allMemberNames.has(sname)) {
            this.raiseError(this.getCurrentLine(), "Collision between const and other names");
        }

        allMemberNames.add(sname);
        staticMembers.push(new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), attributes, sname, stype, value));
    }

    private parseStaticFunction(staticFunctions: StaticFunctionDecl[], allMemberNames: Set<string>, attributes: string[]) {
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

        staticFunctions.push(new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), fname, sig));
    }

    private parseStaticOperator(staticOperators: StaticOperatorDecl[], allMemberNames: Set<string>, attributes: string[]) {
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

        staticOperators.push(new StaticOperatorDecl(sinfo, this.m_penv.getCurrentFile(), fname, sig));
    }

    private parseMemberField(memberFields: MemberFieldDecl[], allMemberNames: Set<string>, attributes: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] field NAME: T = exp;
        this.ensureAndConsumeToken("field");

        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const stype = this.parseTypeSignature();
        let value: ConstantExpressionValue | undefined = undefined;

        if (this.testAndConsumeTokenIf("=")) {
            value = this.parseConstExpression(true);
        }

        this.ensureAndConsumeToken(";");

        if (allMemberNames.has(fname)) {
            this.raiseError(this.getCurrentLine(), "Collision between const and other names");
        }

        memberFields.push(new MemberFieldDecl(sinfo, this.m_penv.getCurrentFile(), attributes, fname, stype, value));
    }

    private parseMemberMethod(thisRef: "ref" | undefined, thisType: TypeSignature, memberMethods: MemberMethodDecl[], allMemberNames: Set<string>, attributes: string[]) {
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

        allMemberNames.add(mname);

        memberMethods.push(new MemberMethodDecl(sinfo, this.m_penv.getCurrentFile(), mname, refrcvr, sig));
    }

    private parseInvariantsInto(invs: InvariantDecl[], vdates: ValidateDecl[]) {
        try {
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(), new NominalTypeSignature("Core", ["Bool"]), false));
            while (this.testToken("invariant") || this.testToken("validate")) {
                if(this.testToken("validate")) {
                    this.consumeToken();

                    const sinfo = this.getCurrentSrcInfo();
                    const exp = this.parseConstExpression(true);

                    vdates.push(new ValidateDecl(sinfo, exp));
                }
                else {
                    this.consumeToken();

                    const level = this.parseBuildInfo("release");
                    const sinfo = this.getCurrentSrcInfo();
                    const exp = this.parseConstExpression(true);

                    invs.push(new InvariantDecl(sinfo, level, exp));
                }

                this.ensureAndConsumeToken(";");
            }
        } finally {
            this.m_penv.popFunctionScope();
        }
    }

    private parseOOPMembersCommon(thisType: TypeSignature, currentNamespace: NamespaceDeclaration, currentTypeNest: string[], currentTermNest: TemplateTermDecl[], 
        nestedEntities: Map<string, EntityTypeDecl>, invariants: InvariantDecl[], validates: ValidateDecl[],
        staticMembers: StaticMemberDecl[], staticFunctions: StaticFunctionDecl[], staticOperators: StaticOperatorDecl[], 
        memberFields: MemberFieldDecl[], memberMethods: MemberMethodDecl[]) {
        let allMemberNames = new Set<string>();
        while (!this.testToken("}")) {
            const attributes = this.parseAttributes();

            if(this.testToken("entity")) {
                this.parseObject(currentNamespace, nestedEntities, currentTypeNest, currentTermNest);
            }
            else if (this.testToken("invariant") || this.testToken("validate")) {
                this.parseInvariantsInto(invariants, validates);
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
        const provides = this.parseProvides(currentDecl.ns === "Core", ["{"]);

        try {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken("{");

            const thisType = new NominalTypeSignature(currentDecl.ns, [cname], terms.map((term) => new TemplateTypeSignature(term.name)));

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            const staticOperators: StaticOperatorDecl[] = [];
            const memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];
            const nestedEntities = new Map<string, EntityTypeDecl>();
            this.parseOOPMembersCommon(thisType, currentDecl, [cname], [...terms], nestedEntities, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods);

            this.ensureAndConsumeToken("}");

            if (currentDecl.checkDeclNameClash(currentDecl.ns, cname)) {
                this.raiseError(line, "Collision between concept and other names");
            }

            this.clearRecover();

            if(currentDecl.ns === "Core") {
                if(cname === "Result") {
                    attributes.push("__result_type");
                }
                else if(cname === "Option") {
                    attributes.push("__option_type");
                }
                else {
                    //not special
                }
            }

            const cdecl = new ConceptTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, cname, terms, provides, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, nestedEntities);
            currentDecl.concepts.set(cname, cdecl);
            this.m_penv.assembly.addConceptDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + cname, cdecl);
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
        const provides = this.parseProvides(currentDecl.ns === "Core", ["{"]);

        try {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken("{");

            const thisType = new NominalTypeSignature(currentDecl.ns, [...currentTypeNest, ename], [...terms, ...currentTermNest].map((term) => new TemplateTypeSignature(term.name)));

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            const staticOperators: StaticOperatorDecl[] = [];
            const memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];
            const nestedEntities = new Map<string, EntityTypeDecl>();
            this.parseOOPMembersCommon(thisType, currentDecl, [...currentTypeNest, ename], [...currentTermNest, ...terms], nestedEntities, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods);

            this.ensureAndConsumeToken("}");

            if (currentDecl.checkDeclNameClash(currentDecl.ns, [...currentTypeNest, ename].join("::"))) {
                this.raiseError(line, "Collision between object and other names");
            }

            if(currentDecl.ns === "Core") {
                if(ename === "StringOf") {
                    attributes.push("__stringof_type");
                }
                else if(ename === "DataString") {
                    attributes.push("__datastring_type");
                }
                else if(ename === "DataBuffer") {
                    attributes.push("__databuffer_type");
                }
                else if(ename === "Ok") {
                    attributes.push("__ok_type");
                }
                else if(ename === "Err") {
                    attributes.push("__err_type");
                }
                else if(ename === "Something") {
                    attributes.push("__something_type");
                }
                else if(ename === "HavocSequence") {
                    attributes.push("__havoc_type");
                }
                else if(ename === "List") {
                    attributes.push("__list_type");
                }
                else if(ename === "Stack") {
                    attributes.push("__stack_type");
                }
                else if(ename === "Queue") {
                    attributes.push("__queue_type");
                }
                else if(ename === "Set") {
                    attributes.push("__set_type");
                }
                else if(ename === "Map") {
                    attributes.push("__map_type");
                }
                else if(ename === "PartialVector4") {
                    attributes.push("__partial_vector4_type");
                }
                else if(ename === "PartialVector8") {
                    attributes.push("__partial_vector8_type");
                }
                else if(ename === "ListTree") {
                    attributes.push("__list_tree_type");
                }
                else if(ename === "MapTree") {
                    attributes.push("__map_tree_type");
                }
                else if(ename === "Vector1") {
                    attributes.push("__vector1_type");
                }
                else if(ename === "Vector2") {
                    attributes.push("__vector2_type");
                }
                else if(ename === "Vector3") {
                    attributes.push("__vector3_type");
                }
                else if(ename === "LargeList") {
                    attributes.push("__largelist_type");
                }
                else if(ename === "RecMap") {
                    attributes.push("__recmap_type");
                }
                else {
                    //not special
                }
            }

            this.clearRecover();

            const fename = [...currentTypeNest, ename].join("::");
            const feterms = [...currentTermNest, ...terms];

            const edecl = new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, fename, feterms, provides, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, nestedEntities);
            this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + fename, edecl);
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
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();

        const sfpos = this.sortedSrcFiles.findIndex((entry) => entry.fullname === this.m_penv.getCurrentFile());
        if(sfpos === -1) {
            this.raiseError(sinfo.line, "Source name not registered");
        }   

        this.ensureAndConsumeToken("enum");
        this.ensureToken(TokenStrings.Type);

        const ename = this.consumeTokenAndGetValue();
        const etype = new NominalTypeSignature(currentDecl.ns, [ename]);
        
        if (currentDecl.checkDeclNameClash(currentDecl.ns, ename)) {
            this.raiseError(line, "Collision between object and other names");
        }

        try {
            this.setRecover(this.scanCodeParens());

            const enums = this.parseListOf<string>("{", "}", ",", () => {
                this.ensureToken(TokenStrings.Identifier);
                return this.consumeTokenAndGetValue();
            })[0];
            
            const provides = [
                [new NominalTypeSignature("Core", ["Some"]), undefined],
                [new NominalTypeSignature("Core", ["KeyType"]), undefined], 
                [new NominalTypeSignature("Core", ["APIType"]), undefined]
            ] as [TypeSignature, TypeConditionRestriction | undefined][];

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            const staticOperators: StaticOperatorDecl[] = [];
            const memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];
    
            for(let i = 0; i < enums.length; ++i) {
                const exp = new LiteralIntegralExpression(sinfo, i.toString() + "n", this.m_penv.SpecialNatSignature);
                const enminit = new ConstructorPrimaryExpression(sinfo, etype, new Arguments([new PositionalArgument(undefined, false, exp)]));
                const enm = new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), ["__enum"], enums[i], etype, new ConstantExpressionValue(enminit, new Set<string>()));
                staticMembers.push(enm);
            }

            if(this.testAndConsumeTokenIf("&")) {
                this.setRecover(this.scanCodeParens());
                this.ensureAndConsumeToken("{");
    
                const thisType = new NominalTypeSignature(currentDecl.ns, [ename], []);
    
                const nestedEntities = new Map<string, EntityTypeDecl>();
                this.parseOOPMembersCommon(thisType, currentDecl, [ename], [], nestedEntities, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods);
    
                this.ensureAndConsumeToken("}");
    
                this.clearRecover();
            }

            if (currentDecl.checkDeclNameClash(currentDecl.ns, ename)) {
                this.raiseError(line, "Collision between object and other names");
            }

            if(invariants.length !== 0) {
                this.raiseError(line, "Cannot have invariant function on Enum types");
            }

            attributes.push("__enum_type", "__constructable");

            this.clearRecover();
            currentDecl.objects.set(ename, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, ename, [], provides, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, new Map<string, EntityTypeDecl>()));
            this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + ename, currentDecl.objects.get(ename) as EntityTypeDecl);
        }
        catch (ex) {
            this.processRecover();
        }
    }

    private parseTypeDecl(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();
       
        this.ensureAndConsumeToken("typedecl");

        const iname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        if (currentDecl.checkDeclNameClash(currentDecl.ns, iname)) {
            this.raiseError(line, "Collision between object and other names");
        }

        const isassigntype = this.testAndConsumeTokenIf("=");
        const sfpos = this.sortedSrcFiles.findIndex((entry) => entry.fullname === this.m_penv.getCurrentFile());
        if(sfpos === -1) {
            this.raiseError(sinfo.line, "Source name not registered");
        }
        
        const bodyid = `k${sfpos}#${this.sortedSrcFiles[sfpos].shortname}::${sinfo.line}@${sinfo.pos}`;

        if (isassigntype) {
            if (this.testToken(TokenStrings.Regex)) {
                //[attr] typedecl NAME = regex;
                if (terms.length !== 0) {
                    this.raiseError(line, "Cannot have template terms on Validator type");
                }

                const vregex = this.consumeTokenAndGetValue();
                this.consumeToken();

                const re = BSQRegex.parse(this.m_penv.getCurrentNamespace(), vregex);
                if (typeof (re) === "string") {
                    this.raiseError(this.getCurrentLine(), re);
                }

                const validator = new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), [], "vregex", new NominalTypeSignature("Core", ["Regex"]), new ConstantExpressionValue(new LiteralRegexExpression(sinfo, re as BSQRegex), new Set<string>()));
                const param = new FunctionParameter("arg", new NominalTypeSignature("Core", ["String"]), false, undefined, undefined, undefined);
                
                const acceptsid = this.generateBodyID(sinfo, this.m_penv.getCurrentFile(), "accepts");
                const acceptsbody = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "validator_accepts");
                const acceptsinvoke = new InvokeDecl("Core", sinfo, sinfo, acceptsid, this.m_penv.getCurrentFile(), ["__safe"], "no", [], undefined, [param], undefined, undefined, new NominalTypeSignature("Core", ["Bool"]), [], [], false, false, new Set<string>(), acceptsbody);
                const accepts = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), "accepts", acceptsinvoke);
                const provides = [[new NominalTypeSignature("Core", ["Some"]), undefined], [new NominalTypeSignature("Core", ["Validator"]), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
                const validatortype = new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), ["__validator_type", ...attributes], currentDecl.ns, iname, [], provides, [], [], [validator], [accepts], [], [], [], new Map<string, EntityTypeDecl>());

                currentDecl.objects.set(iname, validatortype);
                this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + iname, currentDecl.objects.get(iname) as EntityTypeDecl);
                this.m_penv.assembly.addValidatorRegex((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + iname, re as BSQRegex);
            }
            else {
                //[attr] typedecl NAME = PRIMITIVE [& {...}];

                if (terms.length !== 0) {
                    this.raiseError(line, "Cannot have template terms on Typed Primitive type");
                }
                const idval = this.parseNominalType();

                let provides = [[new NominalTypeSignature("Core", ["Some"]), undefined], [new NominalTypeSignature("Core", ["APIType"]), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
                provides.push([new NominalTypeSignature("Core", ["KeyType"]), new TypeConditionRestriction([new TemplateTypeRestriction(idval, false, false, new NominalTypeSignature("Core", ["KeyType"]))])]);
                
                let implicitops = [["t", "==", "t", "Bool"], ["t", "!=", "t", "Bool"]];

                if(attributes.includes("orderable")) {
                    provides.push([new NominalTypeSignature("Core", ["Orderable"]), undefined]);

                    implicitops = [...implicitops, ["t", "<", "t", "Bool"], ["t", ">", "t", "Bool"], ["t", "<=", "t", "Bool"], ["t", ">=", "t", "Bool"]];
                }

                if(attributes.includes("algebraic")) {
                    provides.push([new NominalTypeSignature("Core", ["Algebraic"]), undefined]);

                    implicitops = [...implicitops, ["+", "t", "t"], ["t", "+", "t", "t"], ["-", "t", "t"], ["t", "-", "t", "t"], ["t", "*", "u", "t"], ["u", "*", "t", "t"], ["t", "/", "t", "u"]];
                }

                implicitops.forEach((op) => {
                    const ns = this.m_penv.assembly.getNamespace("Core");

                    const isprefix = op[0] !== "t" && op[0] !== "u";
                    const opstr = isprefix ? op[0] : op[1];

                    const ttype = new NominalTypeSignature(currentDecl.ns, [iname], []);

                    let params: FunctionParameter[] = [];
                    let bexp: Expression = new LiteralNoneExpression(sinfo);

                    if(isprefix) {
                        const ptype = op[1] === "t" ? ttype : idval;
                        params = [new FunctionParameter("l", ptype, false, undefined, undefined, undefined)];
                        const laccess = new AccessVariableExpression(sinfo, "l");
                        const aexp = (op[1] === "t") ? 
                            new PostfixOp(sinfo, laccess, [new PostfixInvoke(sinfo, false, undefined, "value", new TemplateArguments([]), "no", new Arguments([]))])
                            : laccess;

                        bexp = new CallNamespaceFunctionOrOperatorExpression(sinfo, "Core", op[0], new TemplateArguments([]), "no", new Arguments([new PositionalArgument(undefined, false, aexp)]), "prefix");
                    }
                    else {
                        const lptype = op[0] === "t" ? ttype : idval;
                        const rptype = op[2] === "t" ? ttype : idval;
                        params = [new FunctionParameter("l", lptype, false, undefined, undefined, undefined), new FunctionParameter("r", rptype, false, undefined, undefined, undefined)];
                        
                        const laccess = new AccessVariableExpression(sinfo, "l");
                        const lexp = (op[0] === "t") ? 
                            new PostfixOp(sinfo, laccess, [new PostfixInvoke(sinfo, false, undefined, "value", new TemplateArguments([]), "no", new Arguments([]))])
                            : laccess;

                        const raccess = new AccessVariableExpression(sinfo, "r");
                        const rexp = (op[2] === "t") ? 
                            new PostfixOp(sinfo, raccess, [new PostfixInvoke(sinfo, false, undefined, "value", new TemplateArguments([]), "no", new Arguments([]))])
                            : raccess;

                        bexp = new CallNamespaceFunctionOrOperatorExpression(sinfo, "Core", op[1], new TemplateArguments([]), "no", new Arguments([new PositionalArgument(undefined, false, lexp), new PositionalArgument(undefined, false, rexp)]), "infix");
                    }

                    let resultType: TypeSignature = new NominalTypeSignature("Core", ["Bool"]);
                    const resstr = op[op.length - 1];
                    if(resstr === "t") {
                        resultType = ttype;
                    }
                    else if(resstr === "u") {
                        resultType = idval;
                    }
                    else {
                        //already set to bool
                    }
                    
                    if(resstr === "t") {
                        bexp = new ConstructorPrimaryExpression(sinfo, ttype, new Arguments([new PositionalArgument(undefined, false, bexp)]));
                    }

                    const bodyid = this.generateBodyID(sinfo, this.m_penv.getCurrentFile(), opstr);
                    const body = new BodyImplementation(bodyid, this.m_penv.getCurrentFile(), new BlockStatement(sinfo, [new ReturnStatement(sinfo, [bexp])]));
                    const sig = InvokeDecl.createStandardInvokeDecl("Core", sinfo, sinfo, bodyid, this.m_penv.getCurrentFile(), [isprefix ? "prefix" : "infix"], "no", [], undefined, params, undefined, undefined, resultType, [], [], body);

                    let level = -1;
                    if (opstr === "+" || opstr === "-") {
                        level = isprefix ? 1 : 3;
                    }
                    else if (opstr === "*" || opstr === "/") {
                        level = 2;
                    }
                    else {
                        level = 4;
                    }

                    if (!ns.operators.has(opstr)) {
                        ns.operators.set(opstr, []);
                    }
                    (ns.operators.get(opstr) as NamespaceOperatorDecl[]).push(new NamespaceOperatorDecl(sinfo, this.m_penv.getCurrentFile(), "Core", opstr, sig, level));
                });

                const invariants: InvariantDecl[] = [];
                const validates: ValidateDecl[] = [];
                const staticMembers: StaticMemberDecl[] = [];
                const staticFunctions: StaticFunctionDecl[] = [];
                const staticOperators: StaticOperatorDecl[] = [];
                const memberFields: MemberFieldDecl[] = [];
                const memberMethods: MemberMethodDecl[] = [];

                ["zero", "one"].forEach((sf) => {
                    const ttype = new NominalTypeSignature(currentDecl.ns, [iname], []);

                    const cexp = new ConstructorPrimaryExpression(sinfo, ttype, new Arguments([ new PositionalArgument(undefined, false, new AccessStaticFieldExpression(sinfo, idval, sf))]));
                    const sfdecl = new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), [], sf, ttype, new ConstantExpressionValue(cexp, new Set<string>())); 

                    staticMembers.push(sfdecl);
                });

                if(attributes.includes("algebraic")) {
                    const ttype = new NominalTypeSignature("Core", ["AlgebraicOpStability"], []);

                    const cexp = new AccessStaticFieldExpression(sinfo, idval, "stability")
                    const sfdecl = new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), [], "stability", ttype, new ConstantExpressionValue(cexp, new Set<string>())); 

                    staticMembers.push(sfdecl);
                }

                if (this.testAndConsumeTokenIf("&")) {
                    this.setRecover(this.scanCodeParens());
                    this.ensureAndConsumeToken("{");

                    const thisType = new NominalTypeSignature(currentDecl.ns, [iname], []);

                    const nestedEntities = new Map<string, EntityTypeDecl>();
                    this.parseOOPMembersCommon(thisType, currentDecl, [iname], [], nestedEntities, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods);

                    this.ensureAndConsumeToken("}");

                    if (currentDecl.checkDeclNameClash(currentDecl.ns, iname)) {
                        this.raiseError(line, "Collision between concept and other names");
                    }

                    this.clearRecover();
                }
                else {
                    this.ensureAndConsumeToken(";");
                }

                const vparam = new FunctionParameter("v", idval, false, undefined, undefined, undefined);

                const valueid = this.generateBodyID(sinfo, this.m_penv.getCurrentFile(), "value");
                const valuebody = new BodyImplementation(`${bodyid}_value`, this.m_penv.getCurrentFile(), "special_extract");
                const valuedecl = new InvokeDecl("Core", sinfo, sinfo, valueid, this.m_penv.getCurrentFile(), ["__safe"], "no", [], undefined, [vparam], undefined, undefined, idval, [], [], false, false, new Set<string>(), valuebody);
                const value = new MemberMethodDecl(sinfo, this.m_penv.getCurrentFile(), "value", false, valuedecl);

                memberMethods.push(value);

                attributes.push("__typedprimitive", "__constructable");

                currentDecl.objects.set(iname, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, iname, [], provides, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, new Map<string, EntityTypeDecl>()));
                this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + iname, currentDecl.objects.get(iname) as EntityTypeDecl);
            }
        }
        else {
            //[attr] typedecl NAME<...> [provides ... ] [using {...}] of
            // Foo {...}
            // | ...
            // [& {...}] | ;

            const concepttype = new NominalTypeSignature(currentDecl.ns, [iname], terms);

            const provides = this.parseProvides(currentDecl.ns === "Core", ["of", "using"]);

            let complexheader = false;
            const cinvariants: InvariantDecl[] = [];
            const cvalidates: ValidateDecl[] = [];
            const cstaticMembers: StaticMemberDecl[] = [];
            const cstaticFunctions: StaticFunctionDecl[] = [];
            const cstaticOperators: StaticOperatorDecl[] = [];
            let cusing: MemberFieldDecl[] = [];
            const cmemberMethods: MemberMethodDecl[] = [];
            if(this.testAndConsumeTokenIf("using")) {
                if (this.testFollows("{", TokenStrings.Identifier) && !Lexer.isAttributeKW(this.peekTokenData(1))) {
                cusing = this.parseListOf<MemberFieldDecl>("{", "}", ",", () => {
                    const mfinfo = this.getCurrentSrcInfo();

                    this.ensureToken(TokenStrings.Identifier);
                    const name = this.consumeTokenAndGetValue();
                    this.ensureAndConsumeToken(":");

                    const ttype = this.parseTypeSignature();
            
                    let dvalue: ConstantExpressionValue | undefined = undefined;
                    if (this.testAndConsumeTokenIf("=")) {
                        dvalue = this.parseConstExpression(false);
                    }
    
                    return new MemberFieldDecl(mfinfo, this.m_penv.getCurrentFile(), [], name, ttype, dvalue);
                })[0];
                }
                else {
                    complexheader = true;
                    const thisType = new NominalTypeSignature(currentDecl.ns, [iname], []);

                    const nestedEntities = new Map<string, EntityTypeDecl>();
                    this.parseOOPMembersCommon(thisType, currentDecl, [iname], [], nestedEntities, cinvariants, cvalidates, cstaticMembers, cstaticFunctions, cstaticOperators, cusing, cmemberMethods);
                }
            }

            this.ensureAndConsumeToken("of");

            const edecls: EntityTypeDecl[] = [];
            while(!this.testToken(";") && !this.testToken("&")) {
                if(this.testToken("|")) {
                    this.consumeToken();
                }
                let esinfo = this.getCurrentSrcInfo();

                this.ensureToken(TokenStrings.Type);
                const ename = this.consumeTokenAndGetValue();
                if (currentDecl.checkDeclNameClash(currentDecl.ns, ename)) {
                    this.raiseError(line, "Collision between object and other names");
                }

                const invariants: InvariantDecl[] = [];
                const validates: ValidateDecl[] = [];
                const staticMembers: StaticMemberDecl[] = [];
                const staticFunctions: StaticFunctionDecl[] = [];
                const staticOperators: StaticOperatorDecl[] = [];
                let memberFields: MemberFieldDecl[] = [];
                const memberMethods: MemberMethodDecl[] = [];
                if (this.testToken("{")) {
                    if (this.testFollows("{", TokenStrings.Identifier) && !Lexer.isAttributeKW(this.peekTokenData(1))) {
                        memberFields = this.parseListOf<MemberFieldDecl>("{", "}", ",", () => {
                            const mfinfo = this.getCurrentSrcInfo();

                            this.ensureToken(TokenStrings.Identifier);
                            const name = this.consumeTokenAndGetValue();
                            this.ensureAndConsumeToken(":");

                            const ttype = this.parseTypeSignature();

                            let dvalue: ConstantExpressionValue | undefined = undefined;
                            if (this.testAndConsumeTokenIf("=")) {
                                dvalue = this.parseConstExpression(false);
                            }

                            return new MemberFieldDecl(mfinfo, this.m_penv.getCurrentFile(), [], name, ttype, dvalue);
                        })[0];
                    }
                    else {
                        const thisType = new NominalTypeSignature(currentDecl.ns, [ename], []);

                        const nestedEntities = new Map<string, EntityTypeDecl>();
                        this.parseOOPMembersCommon(thisType, currentDecl, [ename], [], nestedEntities, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods);
                    }
                }

                const eprovides = [[concepttype, undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
                const edecl = new EntityTypeDecl(esinfo, this.m_penv.getCurrentFile(), ["__adt_entity_type"], currentDecl.ns, ename, terms, eprovides, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, new Map<string, EntityTypeDecl>());
                
                edecls.push(edecl);
                currentDecl.objects.set(ename, edecl);
                this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + ename, currentDecl.objects.get(ename) as EntityTypeDecl);
            }

            if (this.testAndConsumeTokenIf("&")) {
                this.setRecover(this.scanCodeParens());
                this.ensureAndConsumeToken("{");

                if(complexheader) {
                    this.raiseError(this.getCurrentLine(), "Cannot define complex ADT++ concept in multiple parts");
                }

                const thisType = new NominalTypeSignature(currentDecl.ns, [iname], []);

                const nestedEntities = new Map<string, EntityTypeDecl>();
                const memberFields: MemberFieldDecl[] = [];
                this.parseOOPMembersCommon(thisType, currentDecl, [iname], [], nestedEntities, cinvariants, cvalidates, cstaticMembers, cstaticFunctions, cstaticOperators, memberFields, cmemberMethods);

                if(cusing.length !== 0 && memberFields.length !== 0) {
                    this.raiseError(this.getCurrentLine(), "Cannot define fields in multiple places in ADT++ decl");
                }
                cusing = [...cusing, ...memberFields];

                this.ensureAndConsumeToken("}");

                if (currentDecl.checkDeclNameClash(currentDecl.ns, iname)) {
                    this.raiseError(line, "Collision between concept and other names");
                }

                this.clearRecover();
            }
            else {
                this.ensureAndConsumeToken(";");
            }

            const cdecl = new ConceptTypeDecl(sinfo, this.m_penv.getCurrentFile(), ["__adt_concept_type"], currentDecl.ns, iname, terms, provides, cinvariants, cvalidates, cstaticMembers, cstaticFunctions, cstaticOperators, cusing, cmemberMethods, new Map<string, EntityTypeDecl>());
            currentDecl.concepts.set(iname, cdecl);
            this.m_penv.assembly.addConceptDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + iname, cdecl);
        }
    }

    private parseNamespaceConst(currentDecl: NamespaceDeclaration) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] const NAME = exp;
        const attributes = this.parseAttributes();

        this.ensureAndConsumeToken("const");
        this.ensureToken(TokenStrings.Identifier);
        const gname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const gtype = this.parseTypeSignature();

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

            const ns = this.m_penv.assembly.getNamespace("Core");
            const sig = this.parseInvokableCommon(InvokableKind.StaticOperator, attributes.includes("abstract"), attributes, recursive, [], undefined);

            let level = -1;
            if(fname === "+" || fname === "-") {
                level = attributes.includes("prefix") ? 1 : 3 ;
            }
            else if(fname === "*" || fname === "/") {
                level = 2;
            }
            else {
                level = 4;
            }

            if (!ns.operators.has(fname)) {
                ns.operators.set(fname, []);
            }
            (ns.operators.get(fname) as NamespaceOperatorDecl[]).push(new NamespaceOperatorDecl(sinfo, this.m_penv.getCurrentFile(), "Core", fname, sig, level));
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
                let nns: string | undefined = this.consumeTokenAndGetValue();
                this.ensureAndConsumeToken("::");

                nns = this.m_penv.tryResolveNamespace(nns, fname);
                if (nns === undefined) {
                    nns = "[Unresolved Error]";
                }

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
    parseCompilationUnitGetNamespaceDeps(file: string, contents: string, macrodefs: string[]): {ns: string, deps: string[], remap: Map<string, string>} | undefined {
        this.setNamespaceAndFile("[No Namespace]", file);

        const lexer = new Lexer(contents, macrodefs, undefined);
        this.initialize(lexer.lex());

        //namespace NS; ...
        this.ensureAndConsumeToken("namespace");
        this.ensureToken(TokenStrings.ScopeName);
        const ns = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(";");

        this.setNamespaceAndFile(ns, file);

        let deps: string[] = [];
        let remap = new Map<string, string>();
        while (this.m_cpos < this.m_epos) {
            try {
                this.m_cpos = this.scanTokenOptions("import");
                if (this.m_cpos === this.m_epos) {
                    break;
                }

                const dep = this.parseNamespaceDep();
                deps.push(dep.fromns);
                remap.set(dep.asns, dep.fromns);
            }
            catch(ex) {
                return undefined;
            }
        }

        return {ns: ns, deps: deps, remap: remap};
    }

    parseCompilationUnitPass1(file: string, contents: string, macrodefs: string[]): boolean {
        this.setNamespaceAndFile("[No Namespace]", file);

        const lexer = new Lexer(contents, macrodefs, undefined);
        this.initialize(lexer.lex());

        //namespace NS; ...
        this.ensureAndConsumeToken("namespace");
        this.ensureToken(TokenStrings.ScopeName);
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

                    nsdecl.declaredNames.add(fname);
                }
                else if (this.testToken("operator")) {
                    this.consumeToken();
                    if (this.testToken("+") || this.testToken("-") || this.testToken("*") || this.testToken("/")
                        || this.testToken("==") || this.testToken("!=") || this.testToken("<") || this.testToken(">") || this.testToken("<=") || this.testToken(">=")) {
                        const fname = this.consumeTokenAndGetValue();
                        
                        const nscore = this.m_penv.assembly.getNamespace("Core");
                        nscore.declaredNames.add(fname);
                    }
                    else {
                        let nns = ns;
                        if (this.testToken(TokenStrings.ScopeName)) {
                            nns = this.consumeTokenAndGetValue();
                            this.ensureAndConsumeToken("::");
                        }

                        const fname = this.consumeTokenAndGetValue();
                        
                        if (nns === ns) {
                            nsdecl.declaredNames.add(fname);
                        }
                    }
                }
                else if (this.testToken("typedef")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.ScopeName);
                    const tname = this.consumeTokenAndGetValue();

                    if (!lexer.isDeclTypeName(tname)) {
                        this.raiseError(this.getCurrentLine(), "Not a valid type name to define");
                    }
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }
                    nsdecl.declaredNames.add(tname);
                }
                else if (this.testToken("typedecl")) {            
                    this.consumeToken();

                    this.ensureToken(TokenStrings.ScopeName);
                    const tname = this.consumeTokenAndGetValue();

                    if (!lexer.isDeclTypeName(tname)) {
                        this.raiseError(this.getCurrentLine(), "Not a valid type name to define");
                    }
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }
                    nsdecl.declaredNames.add(tname);

                    const isassigntype = this.testAndConsumeTokenIf("=");
                    if (isassigntype) {
                        if (this.testToken(TokenStrings.Regex)) {
                            this.consumeToken();
                            this.ensureAndConsumeToken(";");
                        }
                        else {
                            if (this.testAndConsumeTokenIf("&")) {
                                this.ensureToken("{"); //we should be at the opening left paren 
                                this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                            }
                        }
                    }
                    else {
                        //[attr] typedecl NAME<...> [provides ... ] [using {...}] of
                        // Foo {...}
                        // | ...
                        // [& {...}] | ;

                        this.parseProvides(false /*Doesn't matter since we arejust scanning*/, ["of", "using"]);

                        if (this.testAndConsumeTokenIf("using")) {
                            this.ensureToken("{"); //we should be at the opening left paren 
                            this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                        }

                        this.ensureAndConsumeToken("of");

                        while (!this.testToken(";") && !this.testToken("&")) {
                            if (this.testToken("|")) {
                                this.consumeToken();
                            }

                            this.ensureToken(TokenStrings.ScopeName);
                            const ename = this.consumeTokenAndGetValue();

                            if (!lexer.isDeclTypeName(ename)) {
                                this.raiseError(this.getCurrentLine(), "Not a valid type name to define");
                            }
                            if (nsdecl.declaredNames.has(ename)) {
                                this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                            }
                            nsdecl.declaredNames.add(ename);

                            if (this.testToken("{")) {
                                this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                            }
                        }

                        if (this.testAndConsumeTokenIf("&")) {
                            this.ensureToken("{"); //we should be at the opening left paren 
                            this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                        }
                        else {
                            this.ensureAndConsumeToken(";");
                        }
                    }
                }
                else if (this.testToken("enum")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.ScopeName);
                    const tname = this.consumeTokenAndGetValue();

                    if (!lexer.isDeclTypeName(tname)) {
                        this.raiseError(this.getCurrentLine(), "Not a valid type name to define");
                    }
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }
                    nsdecl.declaredNames.add(tname);

                    this.ensureToken("{"); //we should be at the opening left paren 
                    this.m_cpos = this.scanCodeParens(); //scan to the closing paren

                    if (this.testToken("&")) {
                        this.ensureToken("{"); //we should be at the opening left paren 
                        this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                    }
                }
                else if (this.testToken("concept") || this.testToken("entity")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.ScopeName);
                    const tname = this.consumeTokenAndGetValue();

                    if (!lexer.isDeclTypeName(tname)) {
                        this.raiseError(this.getCurrentLine(), "Not a valid type name to define");
                    }
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }
                    nsdecl.declaredNames.add(tname);

                    this.parseTermDeclarations();
                    this.parseProvides(ns === "Core", ["{"]);
            
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

    parseCompilationUnitPass2(file: string, contents: string, macrodefs: string[], namespacestrings: Set<string>): boolean {
        this.setNamespaceAndFile("[No Namespace]", file);
        const lexer = new Lexer(contents, macrodefs, namespacestrings);
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
            const rpos = this.scanTokenOptions("function", "operator", "const", "import", "typedef", "concept", "entity", "enum", "typedecl", TokenStrings.EndOfStream);

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
                else if (tk === "const") {
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

function cleanCommentsStringsFromFileContents(str: string): string {
    const commentRe = /(\/\/.*)|(\/\*(.|\s)*?\*\/)/ug;
    const stringRe = /"[^"\\\r\n]*(\\(.|\r?\n)[^"\\\r\n]*)*"/ug;
    const typedStringRe = /'[^'\\\r\n]*(\\(.|\r?\n)[^'\\\r\n]*)*'/ug;

    return str
        .replace(commentRe, "")
        .replace(stringRe, "\"\"")
        .replace(typedStringRe, "''");
}

export { 
    CodeFileInfo, SourceInfo, ParseError, Parser,
    unescapeLiteralString,
    cleanCommentsStringsFromFileContents
};
