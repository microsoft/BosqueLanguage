//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ParserEnvironment, FunctionScope } from "./parser_env";
import { FunctionParameter, TypeSignature, NominalTypeSignature, TemplateTypeSignature, ParseErrorTypeSignature, TupleTypeSignature, RecordTypeSignature, FunctionTypeSignature, UnionTypeSignature, IntersectionTypeSignature, AutoTypeSignature } from "./type_signature";
import { Arguments, TemplateArguments, NamedArgument, PositionalArgument, InvalidExpression, Expression, LiteralNoneExpression, LiteralBoolExpression, LiteralIntegerExpression, LiteralStringExpression, LiteralTypedStringExpression, AccessVariableExpression, AccessNamespaceConstantExpression, LiteralTypedStringConstructorExpression, CallNamespaceFunctionExpression, AccessStaticFieldExpression, ConstructorTupleExpression, ConstructorRecordExpression, ConstructorPrimaryExpression, ConstructorPrimaryWithFactoryExpression, ConstructorLambdaExpression, PostfixOperation, PostfixAccessFromIndex, PostfixAccessFromName, PostfixProjectFromIndecies, PostfixProjectFromNames, PostfixProjectFromType, PostfixModifyWithIndecies, PostfixModifyWithNames, PostfixStructuredExtend, PostfixInvoke, PostfixCallLambda, PostfixOp, PrefixOp, BinOpExpression, BinEqExpression, BinCmpExpression, BinLogicExpression, NonecheckExpression, CoalesceExpression, SelectExpression, BlockStatement, Statement, BodyImplementation, EmptyStatement, InvalidStatement, VariableDeclarationStatement, VariableAssignmentStatement, ReturnStatement, YieldStatement, CondBranchEntry, IfElse, IfElseStatement, InvokeArgument, CallStaticFunctionExpression, AssertStatement, CheckStatement, DebugStatement, StructuredAssignment, TupleStructuredAssignment, RecordStructuredAssignment, VariableDeclarationStructuredAssignment, IgnoreTermStructuredAssignment, VariableAssignmentStructuredAssignment, ConstValueStructuredAssignment, StructuredVariableAssignmentStatement, MatchStatement, MatchEntry, MatchGuard, WildcardMatchGuard, TypeMatchGuard, StructureMatchGuard, AbortStatement, BlockStatementExpression, IfExpression, MatchExpression } from "./body";
import { Assembly, NamespaceUsing, NamespaceDeclaration, NamespaceTypedef, StaticMemberDecl, StaticFunctionDecl, MemberFieldDecl, MemberMethodDecl, ConceptTypeDecl, EntityTypeDecl, NamespaceConstDecl, NamespaceFunctionDecl, InvokeDecl, TemplateTermDecl, TemplateTermRestriction } from "./assembly";

const KeywordStrings = [
    "hidden",
    "factory",
    "virtual",
    "abstract",
    "override",
    "entrypoint",

    "_debug",
    "abort",
    "assert",
    "case",
    "check",
    "concept",
    "const",
    "elif",
    "else",
    "enum",
    "entity",
    "ensures",
    "false",
    "field",
    "fn",
    "from",
    "function",
    "global",
    "identifier",
    "if",
    "invariant",
    "method",
    "namespace",
    "none",
    "provides",
    "return",
    "requires",
    "static",
    "switch",
    "true",
    "type",
    "typedef",
    "unique",
    "using",
    "var",
    "when",
    "where",
    "yield",
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : a.localeCompare(b); });

const SymbolStrings = [
    "[",
    "(",
    "{",
    "]",
    ")",
    "}",
    "@[",
    "@{",
    "?[",
    "?(",
    "?@[",
    "?@{",
    "{|",
    "|}",

    "#",
    "&",
    "&&",
    "@",
    "@#",
    "!",
    "!=",
    ":",
    "::",
    ",",
    ".",
    "...",
    "=",
    "==",
    "=>",
    "==>",
    "#",
    "~",
    ";",
    "|",
    "||",
    "+",
    "*",
    "/",
    "%",
    "?",
    "?&",
    "?|",
    "?.",
    "?@#",
    "?<~",
    "?<+",
    "<",
    "<=",
    "<~",
    "<+",
    ">",
    ">=",
    "-",
    "->",
    "?->"
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : a.localeCompare(b); });

const LeftScanParens = ["[", "(", "{", "@[", "@{", "?[", "?(", "?@[", "?@{", "{|"];
const RightScanParens = ["]", ")", "}", "|}"];

const AttributeStrings = ["hidden", "factory", "virtual", "abstract", "override", "entrypoint"];

const TokenStrings = {
    Clear: "[CLEAR]",
    Error: "[ERROR]",

    Int: "[LITERAL_INT]",
    String: "[LITERAL_STRING]",
    TypedString: "[LITERAL_TYPED_STRING]",

    //Names
    Namespace: "[NAMESPACE]",
    Type: "[TYPE]",
    Template: "[TEMPLATE]",
    Identifier: "[IDENTIFIER]",

    EndOfStream: "[EOS]"
};

class Token {
    readonly line: number;
    readonly pos: number;
    readonly span: number;

    readonly kind: string;
    readonly data: string | undefined;

    constructor(line: number, cpos: number, span: number, kind: string, data?: string) {
        this.line = line;
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

class Lexer {
    private static findSymbolString(str: string): string | undefined {
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
    private m_cpos: number;
    private m_tokens: Token[];

    constructor(input: string) {
        this.m_input = input;
        this.m_internTable = new Map<string, string>();
        this.m_cline = 1;
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
        return str.length === 1 && /^[A-Z]$/.test(str);
    }

    private static isIdentifierName(str: string) {
        return /^[a-z_]/.test(str);
    }

    private recordLexToken(epos: number, kind: string) {
        this.m_tokens.push(new Token(this.m_cline, this.m_cpos, epos - this.m_cpos, kind, kind)); //set data to kind string
        this.m_cpos = epos;
    }

    private recordLexTokenWData(epos: number, kind: string, data: string) {
        const rdata = this.m_internTable.get(data) || this.m_internTable.set(data, data).get(data);
        this.m_tokens.push(new Token(this.m_cline, this.m_cpos, epos - this.m_cpos, kind, rdata));
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
            }
        }

        this.m_cpos += m[0].length;
        return true;
    }

    private static readonly _s_commentRe = /\/(?:\/[^\n\r]*|\*(?<multiline>[^\*]*\**)+?(?<multilineEndChar>\/|$))/y;
    private tryLexComment(): boolean {
        Lexer._s_commentRe.lastIndex = this.m_cpos;
        const m = Lexer._s_commentRe.exec(this.m_input);
        if (m === null) {
            return false;
        }

        if (m.groups) {
            const groups = m.groups;
            if (groups.multiline !== undefined) {
                for (const char of groups.multiline) {
                    if (char === "\n") {
                        this.m_cline++;
                    }
                }
            }
            if (groups.multilineEndChar !== undefined && groups.multilineEndChar !== "/")
            {
                this.recordLexToken(this.m_cpos, TokenStrings.Error);
            }
        }

        this.m_cpos += m[0].length;
        return true;
    }

    private static readonly _s_numberRe = /[0-9]+/y;
    private tryLexNumber(): boolean {
        Lexer._s_numberRe.lastIndex = this.m_cpos;
        const m = Lexer._s_numberRe.exec(this.m_input);
        if (m === null) {
            return false;
        }

        this.recordLexTokenWData(this.m_cpos + m[0].length, TokenStrings.Int, m[0]);
        return true;
    }

    private static readonly _s_stringRe = /"[^"]*"/y;
    private static readonly _s_typedStringRe = /'[^']*'/y;
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

    private static readonly _s_symbolRe = /\W+/y;
    private tryLexSymbol() {
        Lexer._s_symbolRe.lastIndex = this.m_cpos;
        const m = Lexer._s_symbolRe.exec(this.m_input);
        if (m === null) {
            return false;
        }

        const sym = Lexer.findSymbolString(m[0]);
        if (sym === undefined) {
            return false;
        }
        else {
            this.recordLexToken(this.m_cpos + sym.length, sym);
            return true;
        }
    }

    private static readonly _s_nameRe = /\w+/y;
    private tryLexName() {
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
            else if (this.tryLexNumber() || this.tryLexString() || this.tryLexSymbol() || this.tryLexName()) {
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

class Parser {
    private m_tokens: Token[];
    private m_cpos: number;
    private m_epos: number;

    private m_penv: ParserEnvironment;

    private m_errors: [number, string][];
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
        this.m_errors.push([line, msg]);
        throw new ParseError(line, msg);
    }

    private scanParens(): number {
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

    private peekToken(): string {
        return this.m_tokens[this.m_cpos].kind;
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

    ////
    //Misc parsing
    private parseInvokableCommon(isLambda: boolean, isMember: boolean, noBody: boolean, terms: TemplateTermDecl[], termRestrictions: TemplateTermRestriction[], optSelfType?: TypeSignature): InvokeDecl {
        const sinfo = this.getCurrentSrcInfo();
        const srcFile = this.m_penv.getCurrentFile();
        const line = this.getCurrentLine();

        let fparams: FunctionParameter[] = [];
        if (isMember) {
            fparams.push(new FunctionParameter("this", optSelfType as TypeSignature, false));
        }

        let restName = undefined;
        let restType = undefined;
        let resultType = this.m_penv.SpecialAutoSignature;

        const params = this.parseListOf<[string, TypeSignature, boolean, boolean]>("(", ")", ",", () => {
            const isrest = this.testAndConsumeTokenIf("...");

            this.ensureToken(TokenStrings.Identifier);
            const pname = this.consumeTokenAndGetValue();
            const isopt = this.testAndConsumeTokenIf("?");
            let argtype = this.m_penv.SpecialAutoSignature;

            if (this.testAndConsumeTokenIf(":")) {
                argtype = this.parseTypeSignature();
            }
            else {
                if (!isLambda) {
                    this.raiseError(line, "Auto typing is not supported for this");
                }
            }

            return [pname, argtype, isopt, isrest];
        })[0];

        for (let i = 0; i < params.length; i++) {
            if (!params[i][3]) {
                fparams.push(new FunctionParameter(params[i][0], params[i][1], params[i][2]));
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
            resultType = this.parseTypeSignature();
        }
        else {
            if (!isLambda) {
                this.raiseError(line, "Auto typing is not supported for this");
            }
        }

        const argNames = new Set<string>([...(restName ? [restName] : []), ...fparams.map((param) => param.name)]);
        let preconds: Expression[] = [];
        let postconds: Expression[] = [];
        let body: BodyImplementation | undefined = undefined;
        let captured = new Set<string>();
        if (noBody) {
            this.ensureAndConsumeToken(";");
        }
        else {
            if (isLambda) {
                this.ensureAndConsumeToken("=>");
            }
            else {
                [preconds, postconds] = this.parsePreAndPostConditions(argNames);
            }

            const bodyid = `${srcFile}::${sinfo.pos}`;
            try {
                this.m_penv.pushFunctionScope(new FunctionScope(argNames));
                body = this.parseBody(bodyid, srcFile);
                captured = this.m_penv.getCurrentFunctionScope().getCaptureVars();
                this.m_penv.popFunctionScope();
            }
            catch (ex) {
                this.m_penv.popFunctionScope();
                throw ex;
            }
        }

        if (isLambda) {
            return InvokeDecl.createLambdaInvokeDecl(sinfo, srcFile, fparams, restName, restType, resultType, captured, body as BodyImplementation);
        }
        else if (isMember) {
            return InvokeDecl.createMemberInvokeDecl(sinfo, srcFile, terms, termRestrictions, fparams, restName, restType, resultType, preconds, postconds, body);
        }
        else {
            return InvokeDecl.createStaticInvokeDecl(sinfo, srcFile, terms, termRestrictions, fparams, restName, restType, resultType, preconds, postconds, body);
        }
    }

    ////
    //Type parsing

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
        let roottype = this.parseAndCombinatorType();
        while (this.testToken("?")) {
            roottype = this.parseNoneableType(roottype);
        }
        return roottype;
    }

    private parseNoneableType(basetype: TypeSignature): TypeSignature {
        this.ensureAndConsumeToken("?");
        return Parser.orOfTypeSignatures(basetype, this.m_penv.SpecialNoneSignature);
    }

    private parseAndCombinatorType(): TypeSignature {
        const line = this.getCurrentLine();

        const ltype = this.parseBaseTypeReference();
        if (!this.testToken("+")) {
            return ltype;
        }
        else {
            this.consumeToken();
            const rtype = this.parseAndCombinatorType();

            if (!(ltype instanceof NominalTypeSignature || ltype instanceof TemplateTypeSignature)) {
                this.raiseError(line, "Only nominal types can be used in a joined type");
            }

            if (!(rtype instanceof NominalTypeSignature || rtype instanceof TemplateTypeSignature)) {
                this.raiseError(line, "Only nominal types can be used in a joined type");
            }

            return Parser.andOfTypeSignatures(ltype, rtype);
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
                return this.parseFunctionType();
            default:
                {
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

        if (!this.testToken("[")) {
            return new NominalTypeSignature(ns as string, tname);
        }
        else {
            let terms: TypeSignature[] = [];
            try {
                this.setRecover(this.scanParens());
                terms = this.parseListOf<TypeSignature>("[", "]", ",", () => {
                    return this.parseTypeSignature();
                })[0];

                this.clearRecover();
                return new NominalTypeSignature(ns as string, tname, terms);
            }
            catch (ex) {
                this.processRecover();
                return new ParseErrorTypeSignature();
            }
        }
    }

    private parseTupleType(): TypeSignature {
        const line = this.getCurrentLine();
        let entries: [TypeSignature, boolean][] = [];
        let isOpen = false;

        try {
            this.setRecover(this.scanParens());
            [entries, isOpen] = this.parseListOf<[TypeSignature, boolean]>("[", "]", ",", () => {
                const isopt = this.testAndConsumeTokenIf("?");
                if (isopt) {
                    this.ensureAndConsumeToken(":");
                }

                const rtype = this.parseTypeSignature();

                return [rtype, isopt];
            }, "...");

            const firstOpt = entries.findIndex((entry) => entry[1]);
            if (entries.slice(firstOpt).findIndex((entry) => !entry[0]) !== -1) {
                this.raiseError(line, "Optional entries must all come at end of tuple");
            }

            this.clearRecover();
            return new TupleTypeSignature(isOpen, entries);
        }
        catch (ex) {
            this.processRecover();
            return new ParseErrorTypeSignature();
        }
    }

    private parseRecordType(): TypeSignature {
        let entries: [string, TypeSignature, boolean][] = [];
        let isOpen = false;

        try {
            this.setRecover(this.scanParens());
            [entries, isOpen] = this.parseListOf<[string, TypeSignature, boolean]>("{", "}", ",", () => {
                this.ensureToken(TokenStrings.Identifier);

                const name = this.consumeTokenAndGetValue();
                const isopt = this.testAndConsumeTokenIf("?");
                this.ensureAndConsumeToken(":");
                const rtype = this.parseTypeSignature();

                return [name, rtype, isopt];
            }, "...");

            this.clearRecover();
            return new RecordTypeSignature(isOpen, entries);
        }
        catch (ex) {
            this.processRecover();
            return new ParseErrorTypeSignature();
        }
    }

    private parseFunctionType(): TypeSignature {
        this.ensureAndConsumeToken("fn");

        try {
            this.setRecover(this.scanParens());

            let fparams: FunctionParameter[] = [];
            let restName = undefined;
            let restType = undefined;

            const params = this.parseListOf<[string, TypeSignature, boolean, boolean]>("(", ")", ",", () => {
                const isrest = this.testAndConsumeTokenIf("...");

                this.ensureToken(TokenStrings.Identifier);
                const pname = this.consumeTokenAndGetValue();
                const isopt = this.testAndConsumeTokenIf("?");

                this.ensureAndConsumeToken(":");
                const argtype = this.parseTypeSignature();

                return [pname, argtype, isopt, isrest];
            })[0];

            for (let i = 0; i < params.length; i++) {
                if (!params[i][3]) {
                    fparams.push(new FunctionParameter(params[i][0], params[i][1], params[i][2]));
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
            const resultType = this.parseTypeSignature();

            this.clearRecover();
            return new FunctionTypeSignature(fparams, restName, restType, resultType);
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

    private static andOfTypeSignatures(t1: TypeSignature, t2: TypeSignature): TypeSignature {
        const types = [
            ...((t1 instanceof IntersectionTypeSignature) ? t1.types : [t1]),
            ...((t2 instanceof IntersectionTypeSignature) ? t2.types : [t2]),
        ];

        return new IntersectionTypeSignature(types);
    }

    ////
    //Expression parsing
    private parseArguments(lparen: string, rparen: string): Arguments {
        const argSrcInfo = this.getCurrentSrcInfo();

        let seenNames = new Set<string>();
        let args: InvokeArgument[] = [];

        try {
            this.setRecover(this.scanParens());

            this.ensureAndConsumeToken(lparen);
            while (!this.testAndConsumeTokenIf(rparen)) {
                const line = this.getCurrentLine();
                if (this.testFollows(TokenStrings.Identifier, "=")) {
                    const name = this.consumeTokenAndGetValue();
                    this.ensureAndConsumeToken("=");
                    const exp = this.parseExpression();

                    if (seenNames.has(name)) {
                        this.raiseError(line, "Cannot have duplicate named argument name");
                    }

                    if (name !== "_") {
                        seenNames.add(name);
                    }

                    args.push(new NamedArgument(name, exp));
                }
                else {
                    const isSpread = this.testAndConsumeTokenIf("...");
                    const exp = this.parseExpression();

                    args.push(new PositionalArgument(isSpread, exp));
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
            return new Arguments([new PositionalArgument(false, new InvalidExpression(argSrcInfo))]);
        }
    }

    private parseTemplateArguments(): TemplateArguments {
        try {
            this.setRecover(this.scanParens());
            let targs: TypeSignature[] = [];

            this.ensureAndConsumeToken("[");
            while (!this.testAndConsumeTokenIf("]")) {
                targs.push(this.parseTypeSignature());

                if (this.testAndConsumeTokenIf(",")) {
                    this.ensureNotToken("]");
                }
                else {
                    this.ensureToken("]");
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

    private parseConstructorPrimary(otype: TypeSignature): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const args = this.parseArguments("@{", "}");

        return new ConstructorPrimaryExpression(sinfo, otype, args);
    }

    private parseConstructorPrimaryWithFactory(otype: TypeSignature): Expression {
        const sinfo = this.getCurrentSrcInfo();

        this.ensureAndConsumeToken("@");
        this.ensureToken(TokenStrings.Identifier);

        const fname = this.consumeTokenAndGetValue();
        const targs = this.testToken("[") ? this.parseTemplateArguments() : new TemplateArguments([]);
        const args = this.parseArguments("(", ")");

        return new ConstructorPrimaryWithFactoryExpression(sinfo, otype, fname, targs, args);
    }

    private parseLambdaConstructor(): Expression {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();

        this.ensureAndConsumeToken("fn");
        const sig = this.parseInvokableCommon(true, false, false, [], []);
        const someAuto = sig.params.some((param) => param.type instanceof AutoTypeSignature) || (sig.optRestType !== undefined && sig.optRestType instanceof AutoTypeSignature) || sig.resultType instanceof AutoTypeSignature;
        const allAuto = sig.params.every((param) => param.type instanceof AutoTypeSignature) && (sig.optRestType === undefined || sig.optRestType instanceof AutoTypeSignature) && sig.resultType instanceof AutoTypeSignature;
        if (someAuto && !allAuto) {
            this.raiseError(line, "Cannot have mixed of auto propagated and explicit types on lambda arguments/return");
        }

        sig.captureSet.forEach((v) => {
            this.m_penv.getCurrentFunctionScope().useLocalVar(v);
        });

        return new ConstructorLambdaExpression(sinfo, allAuto, sig);
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
        else if (tk === TokenStrings.Int) {
            const istr = this.consumeTokenAndGetValue();
            return new LiteralIntegerExpression(sinfo, istr);
        }
        else if (tk === TokenStrings.String) {
            const sstr = this.consumeTokenAndGetValue(); //keep in escaped format
            return new LiteralStringExpression(sinfo, sstr);
        }
        else if (tk === TokenStrings.TypedString) {
            const sstr = this.consumeTokenAndGetValue(); //keep in escaped format

            if (this.testAndConsumeTokenIf("#")) {
                const tsig = this.parseTypeSignature();
                return new LiteralTypedStringExpression(sinfo, sstr, tsig);
            }
            else {
                this.ensureAndConsumeToken("@");
                const tsig = this.parseTypeSignature();
                return new LiteralTypedStringConstructorExpression(sinfo, sstr, tsig);
            }
        }
        else if (tk === TokenStrings.Identifier) {
            const istr = this.consumeTokenAndGetValue();

            const ns = this.m_penv.tryResolveNamespace(undefined, istr);
            if (ns === undefined) {
                //Ignore special postcondition _return_ variable but everything else should be processed
                if (istr !== "_return_") {
                    this.m_penv.getCurrentFunctionScope().useLocalVar(istr);
                }

                return new AccessVariableExpression(sinfo, istr);
            }
            else {
                const targs = this.testToken("[") ? this.parseTemplateArguments() : new TemplateArguments([]);
                const args = this.parseArguments("(", ")");

                return new CallNamespaceFunctionExpression(sinfo, ns, istr, targs, args);
            }
        }
        else if (tk === "fn") {
            return this.parseLambdaConstructor();
        }
        else if (tk === "(") {
            try {
                this.setRecover(this.scanParens());

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
        else if (this.testToken("@[")) {
            const args = this.parseArguments("@[", "]");
            return new ConstructorTupleExpression(sinfo, args);
        }
        else if (this.testToken("@{")) {
            const args = this.parseArguments("@{", "}");
            return new ConstructorRecordExpression(sinfo, args);
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Identifier)) {
            //it is a namespace access of some type
            const ns = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            if (!this.testToken("[") && !this.testToken("(")) {
                //just a constant access
                return new AccessNamespaceConstantExpression(sinfo, ns, name);
            }
            else {
                const targs = this.testToken("[") ? this.parseTemplateArguments() : new TemplateArguments([]);
                const args = this.parseArguments("(", ")");

                return new CallNamespaceFunctionExpression(sinfo, ns, name, targs, args);
            }
        }
        else {
            //we should find a type (nominal here) and it is either (1) a constructor (2) constructor with factory or (3) static invoke

            const ttype = this.parseTypeSignature();
            if (this.testFollows("::", TokenStrings.Identifier)) {
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                if (!this.testToken("[") && !this.testToken("(")) {
                    //just a static access
                    return new AccessStaticFieldExpression(sinfo, ttype, name);
                }
                else {
                    const targs = this.testToken("[") ? this.parseTemplateArguments() : new TemplateArguments([]);
                    const args = this.parseArguments("(", ")");

                    return new CallStaticFunctionExpression(sinfo, ttype, name, targs, args);
                }
            }
            else if (this.testFollows("@", TokenStrings.Identifier)) {
                return this.parseConstructorPrimaryWithFactory(ttype);
            }
            else if (this.testToken("@{")) {
                return this.parseConstructorPrimary(ttype);
            }
            else {
                this.raiseError(line, "Unknown token sequence in parsing expression");
                return new InvalidExpression(sinfo);
            }
        }
    }

    private parsePostfixExpression(): Expression {
        const rootinfo = this.getCurrentSrcInfo();
        let rootexp = this.parsePrimaryExpression();

        let ops: PostfixOperation[] = [];
        while (true) {
            const line = this.getCurrentLine();
            const sinfo = this.getCurrentSrcInfo();

            const tk = this.peekToken();
            if (tk === "[" || tk === "?[") {
                const isElvis = this.testToken("?[");
                this.consumeToken();

                const index = Number.parseInt(this.consumeTokenAndGetValue());
                this.ensureAndConsumeToken("]");

                ops.push(new PostfixAccessFromIndex(sinfo, isElvis, index));
            }
            else if (tk === "." || tk === "?.") {
                const isElvis = this.testToken("?.");
                this.consumeToken();

                this.ensureToken(TokenStrings.Identifier);
                const name = this.consumeTokenAndGetValue();

                ops.push(new PostfixAccessFromName(sinfo, isElvis, name));
            }
            else if (tk === "@[" || tk === "?@[") {
                const isElvis = this.testToken("?@[");
                const indecies = this.parseListOf<number>(tk, "]", ",", () => {
                    this.ensureToken(TokenStrings.Int);
                    return Number.parseInt(this.consumeTokenAndGetValue());
                })[0].sort();

                ops.push(new PostfixProjectFromIndecies(sinfo, isElvis, indecies));
            }
            else if (tk === "@{" || tk === "?@{") {
                const isElvis = this.testToken("?@{");
                const names = this.parseListOf<string>(tk, "}", ",", () => {
                    this.ensureToken(TokenStrings.Identifier);
                    return this.consumeTokenAndGetValue();
                })[0].sort();

                ops.push(new PostfixProjectFromNames(sinfo, isElvis, names));
            }
            else if (tk === "@#" || tk === "?@#") {
                const isElvis = this.testToken("?@#");
                this.consumeToken();

                const type = this.parseTypeSignature();
                if (!(type instanceof TemplateTypeSignature || type instanceof NominalTypeSignature || type instanceof RecordTypeSignature || type instanceof TupleTypeSignature)) {
                    this.raiseError(line, "Can only project over record, tuple, or concept contraints");
                }

                ops.push(new PostfixProjectFromType(sinfo, isElvis, type));
            }
            else if (tk === "<~" || tk === "?<~") {
                const isElvis = this.testToken("?<~");
                this.consumeToken();

                if (this.testFollows("(", TokenStrings.Int)) {
                    const updates = this.parseListOf<[number, Expression]>("(", ")", ",", () => {
                        this.ensureToken(TokenStrings.Int);
                        const idx = Number.parseInt(this.consumeTokenAndGetValue());
                        this.ensureAndConsumeToken("=");
                        const value = this.parseExpression();

                        return [idx, value];
                    })[0].sort((a, b) => a[0] - b[0]);

                    ops.push(new PostfixModifyWithIndecies(sinfo, isElvis, updates));
                }
                else if (this.testFollows("(", TokenStrings.Identifier)) {
                    const updates = this.parseListOf<[string, Expression]>("(", ")", ",", () => {
                        this.ensureToken(TokenStrings.Identifier);
                        const name = this.consumeTokenAndGetValue();
                        this.ensureAndConsumeToken("=");
                        const value = this.parseExpression();

                        return [name, value];
                    })[0].sort((a, b) => a[0].localeCompare(b[0]));

                    ops.push(new PostfixModifyWithNames(sinfo, isElvis, updates));
                }
                else {
                    this.raiseError(line, "Expected list of property/field or tuple updates");
                }
            }
            else if (tk === "<+" || tk === "?<+") {
                const isElvis = this.testToken("?<+");
                this.consumeToken();

                this.ensureAndConsumeToken("(");
                const update = this.parseExpression();
                this.ensureAndConsumeToken(")");

                ops.push(new PostfixStructuredExtend(sinfo, isElvis, update));
            }
            else if (tk === "->" || tk === "?->") {
                const isElvis = this.testToken("?->");
                this.consumeToken();

                let specificResolve: TypeSignature | undefined = undefined;
                if (this.testToken(TokenStrings.Namespace) || this.testToken(TokenStrings.Type) || this.testToken(TokenStrings.Template)) {
                    specificResolve = this.parseTypeSignature();
                    this.ensureAndConsumeToken("::");
                }

                this.ensureToken(TokenStrings.Identifier);
                const name = this.consumeTokenAndGetValue();

                const terms = this.testToken("[") ? this.parseTemplateArguments() : new TemplateArguments([]);
                const args = this.parseArguments("(", ")");

                ops.push(new PostfixInvoke(sinfo, isElvis, specificResolve, name, terms, args));
            }
            else if (tk === "(" || tk === "?(") {
                const isElvis = this.testToken("?(");
                const args = this.parseArguments(tk, ")");

                ops.push(new PostfixCallLambda(sinfo, isElvis, args));
            }
            else {
                if (ops.length === 0) {
                    return rootexp;
                }
                else {
                    return new PostfixOp(rootinfo, rootexp, ops);
                }
            }
        }
    }

    private parseStatementExpression(): Expression {
        if (this.testToken("{|")) {
            return this.parseBlockStatementExpression();
        }
        else if (this.testToken("if")) {
            return this.parseIfExpression();
        }
        else if (this.testToken("switch")) {
            return this.parseMatchExpression();
        }
        else {
            return this.parsePostfixExpression();
        }
    }

    private parsePrefixExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        if (this.testToken("+") || this.testToken("-") || this.testToken("!")) {
            const op = this.consumeTokenAndGetValue();
            return new PrefixOp(sinfo, op, this.parsePrefixExpression());
        }
        else {
            return this.parseStatementExpression();
        }
    }

    private parseMultiplicativeExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parsePrefixExpression();

        if (this.testToken("*") || this.testToken("/") || this.testToken("%")) {
            const op = this.consumeTokenAndGetValue();
            return new BinOpExpression(sinfo, exp, op, this.parseMultiplicativeExpression());
        }
        else {
            return exp;
        }
    }

    private parseAdditiveExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseMultiplicativeExpression();

        if (this.testToken("+") || this.testToken("-")) {
            const op = this.consumeTokenAndGetValue();
            return new BinOpExpression(sinfo, exp, op, this.parseAdditiveExpression());
        }
        else {
            return exp;
        }
    }

    private parseRelationalExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseAdditiveExpression();

        if (this.testToken("==") || this.testToken("!=")) {
            const op = this.consumeTokenAndGetValue();
            return new BinEqExpression(sinfo, exp, op, this.parseRelationalExpression());
        }
        else if (this.testToken("<") || this.testToken(">") || this.testToken("<=") || this.testToken(">=")) {
            const op = this.consumeTokenAndGetValue();
            return new BinCmpExpression(sinfo, exp, op, this.parseRelationalExpression());
        }
        else {
            return exp;
        }
    }

    private parseImpliesExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseRelationalExpression();

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

    private parseNonecheckExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseOrExpression();

        if (this.testAndConsumeTokenIf("?&")) {
            return new NonecheckExpression(sinfo, exp, this.parseNonecheckExpression());
        }
        else {
            return exp;
        }
    }

    private parseCoalesceExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseNonecheckExpression();

        if (this.testAndConsumeTokenIf("?|")) {
            return new CoalesceExpression(sinfo, exp, this.parseCoalesceExpression());
        }
        else {
            return exp;
        }
    }

    private parseSelectExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const texp = this.parseCoalesceExpression();

        if (this.testAndConsumeTokenIf("?")) {
            const exp1 = this.parseCoalesceExpression();
            this.ensureAndConsumeToken(":");
            const exp2 = this.parseSelectExpression();

            return new SelectExpression(sinfo, texp, exp1, exp2);
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
            this.setRecover(this.scanParens());

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

        let entries: MatchEntry<Expression>[] = [];
        this.ensureAndConsumeToken("{");
        while (this.testToken("type") || this.testToken("case")) {
            if (this.testToken("type")) {
                entries.push(this.parseMatchEntry<Expression>(sinfo, true, () => this.parseExpression()));
            }
            else {
                entries.push(this.parseMatchEntry<Expression>(sinfo, false, () => this.parseExpression()));
            }
        }
        this.ensureAndConsumeToken("}");

        return new MatchExpression(sinfo, mexp, entries);
    }

    private parseExpression(): Expression {
        return this.parseSelectExpression();
    }

    ////
    //Statement parsing

    parseStructuredAssignment(sinfo: SourceInfo, vars: "var" | "var!" | undefined, trequired: boolean, decls: Set<string>): StructuredAssignment {
        if (this.testToken("@[")) {
            const [assigns, isOpen] = this.parseListOf<StructuredAssignment>("@[", "]", ",", () => {
                return this.parseStructuredAssignment(this.getCurrentSrcInfo(), vars, trequired, decls);
            }, "...");

            return new TupleStructuredAssignment(assigns, isOpen);
        }
        else if (this.testToken("@{")) {
            const [assigns, isOpen] = this.parseListOf<[string, StructuredAssignment]>("@{", "}", ",", () => {
                this.ensureToken(TokenStrings.Identifier);
                const name = this.consumeTokenAndGetValue();

                this.ensureAndConsumeToken("=");
                const subg = this.parseStructuredAssignment(this.getCurrentSrcInfo(), vars, trequired, decls);

                return [name, subg];
            }, "...");

            return new RecordStructuredAssignment(assigns, isOpen);
        }
        else {
            if (this.testToken("var")) {
                if (vars !== undefined) {
                    this.raiseError(sinfo.line, "Cannot mix var decl before and inside structured assign");
                }

                this.consumeToken();
                const isConst = !this.testAndConsumeTokenIf("!");

                this.ensureToken(TokenStrings.Identifier);
                const name = this.consumeTokenAndGetValue();

                if (decls.has(name)) {
                    this.raiseError(sinfo.line, "Variable is already defined in scope");
                }
                decls.add(name);

                const isopt = this.testAndConsumeTokenIf("?");
                let itype = this.m_penv.SpecialAutoSignature;
                if (trequired) {
                    this.ensureAndConsumeToken(":");
                    itype = this.parseTypeSignature();
                }
                else {
                    if (this.testAndConsumeTokenIf(":")) {
                        itype = this.parseTypeSignature();
                    }
                }

                return new VariableDeclarationStructuredAssignment(isopt, name, isConst, itype);
            }
            else if (this.testToken(TokenStrings.Identifier)) {
                const name = this.consumeTokenAndGetValue();

                if (name === "_") {
                    const isopt = this.testAndConsumeTokenIf("?");

                    let itype = this.m_penv.SpecialAnySignature;
                    if (trequired) {
                        this.ensureAndConsumeToken(":");
                        itype = this.parseTypeSignature();
                    }
                    else {
                        if (this.testAndConsumeTokenIf(":")) {
                            itype = this.parseTypeSignature();
                        }
                    }

                    return new IgnoreTermStructuredAssignment(isopt, itype);
                }
                else {
                    const isopt = this.testAndConsumeTokenIf("?");

                    let itype = this.m_penv.SpecialAutoSignature;
                    if (trequired && vars !== undefined) {
                        this.ensureAndConsumeToken(":");
                        itype = this.parseTypeSignature();
                    }
                    else {
                        if (this.testAndConsumeTokenIf(":")) {
                            itype = this.parseTypeSignature();
                        }
                    }

                    if (vars !== undefined) {
                        if (decls.has(name)) {
                            this.raiseError(sinfo.line, "Variable is already defined in scope");
                        }
                        decls.add(name);

                        if (vars === "var") {
                            return new VariableDeclarationStructuredAssignment(isopt, name, true, itype);
                        }
                        else {
                            return new VariableDeclarationStructuredAssignment(isopt, name, false, itype);
                        }
                    }
                    else {
                        if (!this.m_penv.getCurrentFunctionScope().isVarNameDefined(name)) {
                            this.raiseError(sinfo.line, "Variable is not defined in scope");
                        }

                        return new VariableAssignmentStructuredAssignment(isopt, name);
                    }
                }
            }
            else {
                const cexp = this.parseExpression();
                return new ConstValueStructuredAssignment(cexp);
            }
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
        else if (tk === "var") {
            this.consumeToken();
            const isConst = !this.testAndConsumeTokenIf("!");

            if (this.testToken("@[") || this.testToken("@{")) {
                let decls = new Set<string>();
                const assign = this.parseStructuredAssignment(this.getCurrentSrcInfo(), isConst ? "var" : "var!", false, decls);
                decls.forEach((dv) => {
                    if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(dv)) {
                        this.raiseError(line, "Variable name is already defined");
                    }
                    this.m_penv.getCurrentFunctionScope().defineLocalVar(dv);
                });

                this.ensureAndConsumeToken("=");
                const exp = this.parseExpression();
                this.ensureAndConsumeToken(";");

                return new StructuredVariableAssignmentStatement(sinfo, assign, exp);
            }
            else {
                this.ensureToken(TokenStrings.Identifier);
                const name = this.consumeTokenAndGetValue();

                if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(name)) {
                    this.raiseError(line, "Variable is already defined in scope");
                }
                this.m_penv.getCurrentFunctionScope().defineLocalVar(name);

                const vtype = this.testAndConsumeTokenIf(":") ? this.parseTypeSignature() : this.m_penv.SpecialAutoSignature;
                const exp = this.testAndConsumeTokenIf("=") ? this.parseExpression() : undefined;

                if (exp === undefined && isConst) {
                    this.raiseError(line, "Const variable declaration must include an assignment to the variable");
                }

                this.ensureAndConsumeToken(";");
                return new VariableDeclarationStatement(sinfo, name, isConst, vtype, exp);
            }
        }
        else if (tk === TokenStrings.Identifier) {
            const name = this.consumeTokenAndGetValue();
            if (!this.m_penv.getCurrentFunctionScope().isVarNameDefined(name)) {
                this.raiseError(line, "Variable is not defined in scope");
            }

            this.ensureAndConsumeToken("=");
            const exp = this.parseExpression();

            this.ensureAndConsumeToken(";");
            return new VariableAssignmentStatement(sinfo, name, exp);
        }
        else if (tk === "@[" || tk === "@{") {
            let decls = new Set<string>();
            const assign = this.parseStructuredAssignment(this.getCurrentSrcInfo(), undefined, false, decls);
            decls.forEach((dv) => {
                if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(dv)) {
                    this.raiseError(line, "Variable name is already defined");
                }
                this.m_penv.getCurrentFunctionScope().defineLocalVar(dv);
            });

            this.ensureAndConsumeToken("=");
            const exp = this.parseExpression();
            this.ensureAndConsumeToken(";");

            return new StructuredVariableAssignmentStatement(sinfo, assign, exp);
        }
        else if (tk === "return") {
            this.consumeToken();

            const exp = this.parseExpression();

            this.ensureAndConsumeToken(";");
            return new ReturnStatement(sinfo, exp);
        }
        else if (tk === "yield") {
            this.consumeToken();

            const exp = this.parseExpression();

            this.ensureAndConsumeToken(";");
            return new YieldStatement(sinfo, exp);
        }
        else if (tk === "abort") {
            this.consumeToken();

            this.ensureAndConsumeToken(";");
            return new AbortStatement(sinfo);
        }
        else if (tk === "assert") {
            this.consumeToken();

            const exp = this.parseExpression();

            this.ensureAndConsumeToken(";");
            return new AssertStatement(sinfo, exp);
        }
        else if (tk === "check") {
            this.consumeToken();

            const exp = this.parseExpression();

            this.ensureAndConsumeToken(";");
            return new CheckStatement(sinfo, exp);
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
        else {
            this.m_cpos = this.scanToken(";");
            return new InvalidStatement(sinfo);
        }
    }

    private parseBlockStatement(): BlockStatement {
        const sinfo = this.getCurrentSrcInfo();

        this.m_penv.getCurrentFunctionScope().pushLocalScope();
        let stmts: Statement[] = [];
        try {
            this.setRecover(this.scanParens());

            this.consumeToken();
            while (!this.testAndConsumeTokenIf("}")) {
                stmts.push(this.parseStatement());
            }

            this.m_penv.getCurrentFunctionScope().popLocalScope();

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

    private parseMatchGuard(sinfo: SourceInfo, istypematch: boolean): MatchGuard {
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
        if (istypematch) {
            typecheck = this.parseTypeSignature();
        }
        else {
            let varinfo: "var" | "var!" | undefined = undefined;
            if (this.testAndConsumeTokenIf("var")) {
                varinfo = (this.testAndConsumeTokenIf("!") ? "var!" : "var");
            }
            layoutcheck = this.parseStructuredAssignment(sinfo, varinfo, true, decls);
        }

        let whencheck = undefined;
        if (this.testAndConsumeTokenIf("when")) {
            whencheck = this.parseExpression();
        }

        if (istypematch) {
            return new TypeMatchGuard(typecheck as TypeSignature, whencheck);
        }
        else {
            return new StructureMatchGuard(layoutcheck as StructuredAssignment, decls, whencheck);
        }
    }

    private parseMatchEntry<T>(sinfo: SourceInfo, istypematch: boolean, actionp: () => T): MatchEntry<T> {
        this.consumeToken();
        const guard = this.parseMatchGuard(sinfo, istypematch);
        this.ensureAndConsumeToken("=>");
        const action = actionp();

        return new MatchEntry<T>(guard, action);
    }

    private parseMatchStatement(): Statement {
        const sinfo = this.getCurrentSrcInfo();

        this.ensureAndConsumeToken("switch");

        this.ensureAndConsumeToken("(");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(")");

        let entries: MatchEntry<BlockStatement>[] = [];
        this.ensureAndConsumeToken("{");
        while (this.testToken("type") || this.testToken("case")) {
            if (this.testToken("type")) {
                entries.push(this.parseMatchEntry<BlockStatement>(sinfo, true, () => this.parseBlockStatement()));
            }
            else {
                entries.push(this.parseMatchEntry<BlockStatement>(sinfo, false, () => this.parseBlockStatement()));
            }
        }
        this.ensureAndConsumeToken("}");

        return new MatchStatement(sinfo, mexp, entries);
    }

    private parseStatement(): Statement {
        if (this.testToken("{")) {
            return this.parseBlockStatement();
        }
        else {
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
    }

    private parseBody(bodyid: string, file: string): BodyImplementation {
        if (this.testToken("#")) {
            this.consumeToken();
            this.ensureToken(TokenStrings.Identifier);
            return new BodyImplementation(bodyid, file, this.consumeTokenAndGetValue());
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
        while (Lexer.isAttributeKW(this.peekToken())) {
            attributes.push(this.consumeTokenAndGetValue());
        }
        return attributes;
    }

    private parseTermDeclarations(): TemplateTermDecl[] {
        let terms: TemplateTermDecl[] = [];
        if (this.testToken("[")) {
            terms = this.parseListOf<TemplateTermDecl>("[", "]", ",", () => {
                const isuniq = this.testAndConsumeTokenIf("unique");
                this.ensureToken(TokenStrings.Template);
                const templatename = this.consumeTokenAndGetValue();
                const tconstraint = this.testAndConsumeTokenIf("where") ? this.parseTypeSignature() : this.m_penv.SpecialAnySignature;

                return new TemplateTermDecl(isuniq, templatename, tconstraint);
            })[0];
        }
        return terms;
    }

    private parseTermRestrictions(): TemplateTermRestriction[] {
        let terms: TemplateTermRestriction[] = [];
        if (this.testToken("{")) {
            terms = this.parseListOf<TemplateTermRestriction>("{", "}", ",", () => {
                this.ensureAndConsumeToken("when");

                this.ensureToken(TokenStrings.Template);
                const templatename = this.consumeTokenAndGetValue();

                const tconstraint = this.parseTypeSignature();

                return new TemplateTermRestriction(templatename, tconstraint);
            })[0];
        }
        return terms;
    }

    private parsePreAndPostConditions(argnames: Set<string>): [Expression[], Expression[]] {
        let preconds: Expression[] = [];
        try {
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(argnames)));
            while (this.testAndConsumeTokenIf("requires")) {
                preconds.push(this.parseExpression());
                this.ensureAndConsumeToken(";");
            }
        } finally {
            this.m_penv.popFunctionScope();
        }

        let postconds: Expression[] = [];
        try {
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(argnames).add("_return_")));
            while (this.testAndConsumeTokenIf("ensures")) {
                postconds.push(this.parseExpression());
                this.ensureAndConsumeToken(";");
            }
        } finally {
            this.m_penv.popFunctionScope();
        }

        return [preconds, postconds];
    }

    private parseNamespaceUsing(currentDecl: NamespaceDeclaration) {
        //from NS using {...} ;

        this.ensureAndConsumeToken("from");
        this.ensureToken(TokenStrings.Namespace);
        const fromns = this.consumeTokenAndGetValue();

        this.ensureAndConsumeToken("using");
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

        this.ensureAndConsumeToken("typedef");
        this.ensureToken(TokenStrings.Type);
        const tyname = this.consumeTokenAndGetValue();

        const terms = this.parseTermDeclarations();

        this.ensureAndConsumeToken("=");
        const rpos = this.scanToken(";");
        if (rpos === this.m_epos) {
            this.raiseError(this.getCurrentLine(), "Missing ; on typedef");
        }

        const btype = this.parseTypeSignature();
        this.consumeToken();

        if (currentDecl.checkDeclNameClash(currentDecl.ns, tyname)) {
            this.raiseError(this.getCurrentLine(), "Collision between typedef and other names");
        }

        currentDecl.typeDefs.set(currentDecl.ns + "::" + tyname, new NamespaceTypedef(currentDecl.ns, tyname, terms, btype));
    }

    private parseProvides(iscorens: boolean): TypeSignature[] {
        let provides: TypeSignature[] = [];
        if (this.testToken("provides")) {
            this.consumeToken();

            while (!this.testToken("{") && !this.testToken(";")) {
                this.consumeTokenIf(",");
                provides.push(this.parseTypeSignature());
            }
        }
        else {
            if (!iscorens) {
                provides.push(new NominalTypeSignature("NSCore", "Object"));
            }
        }
        return provides;
    }

    private parseConstMember(staticMembers: Map<string, StaticMemberDecl>, allMemberNames: Set<string>, attributes: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] const NAME[: T] = exp;
        this.ensureAndConsumeToken("const");

        this.ensureToken(TokenStrings.Identifier);
        const sname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const stype = this.parseTypeSignature();
        let value: Expression | undefined = undefined;

        if (!Parser.attributeSetContains("abstract", attributes)) {
            this.ensureAndConsumeToken("=");
            value = this.parseExpression();
        }

        this.ensureAndConsumeToken(";");

        if (allMemberNames.has(sname)) {
            this.raiseError(this.getCurrentLine(), "Collision between const and other names");
        }

        allMemberNames.add(sname);
        staticMembers.set(sname, new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), attributes, this.m_penv.getCurrentNamespace(), sname, stype, value));
    }

    private parseStaticFunction(staticFunctions: Map<string, StaticFunctionDecl>, allMemberNames: Set<string>, attributes: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] static NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        this.ensureAndConsumeToken("static");
        const termRestrictions = this.parseTermRestrictions();

        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        const sig = this.parseInvokableCommon(false, false, Parser.attributeSetContains("abstract", attributes), terms, termRestrictions);

        if (allMemberNames.has(fname)) {
            this.raiseError(this.getCurrentLine(), "Collision between static and other names");
        }
        allMemberNames.add(fname);

        staticFunctions.set(fname, new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), attributes, fname, sig));
    }

    private parseMemberField(memberFields: Map<string, MemberFieldDecl>, allMemberNames: Set<string>, attributes: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] field NAME[: T] = exp;
        this.ensureAndConsumeToken("field");

        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const stype = this.parseTypeSignature();
        let value: Expression | undefined = undefined;

        if (this.testAndConsumeTokenIf("=")) {
            value = this.parseExpression();
        }

        this.ensureAndConsumeToken(";");

        if (allMemberNames.has(fname)) {
            this.raiseError(this.getCurrentLine(), "Collision between const and other names");
        }

        memberFields.set(fname, new MemberFieldDecl(sinfo, this.m_penv.getCurrentFile(), attributes, fname, stype, value));
    }

    private parseMemberMethod(thisType: TypeSignature, memberMethods: Map<string, MemberMethodDecl>, allMemberNames: Set<string>, attributes: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] method NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        this.ensureAndConsumeToken("method");
        const termRestrictions = this.parseTermRestrictions();

        this.ensureToken(TokenStrings.Identifier);
        const mname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        const sig = this.parseInvokableCommon(false, true, Parser.attributeSetContains("abstract", attributes), terms, termRestrictions, thisType);

        if (allMemberNames.has(mname)) {
            this.raiseError(this.getCurrentLine(), "Collision between static and other names");
        }
        allMemberNames.add(mname);

        memberMethods.set(mname, new MemberMethodDecl(sinfo, this.m_penv.getCurrentFile(), attributes, mname, sig));
    }

    private parseOOPMembersCommon(abstractOk: boolean, thisType: TypeSignature, invariants: Expression[], staticMembers: Map<string, StaticMemberDecl>, staticFunctions: Map<string, StaticFunctionDecl>, memberFields: Map<string, MemberFieldDecl>, memberMethods: Map<string, MemberMethodDecl>) {
        while (this.testAndConsumeTokenIf("invariant")) {
            invariants.push(this.parseExpression());
            this.ensureAndConsumeToken(";");
        }

        let allMemberNames = new Set<string>();
        while (!this.testToken("}")) {
            const attributes = this.parseAttributes();

            if (this.testToken("const")) {
                this.parseConstMember(staticMembers, allMemberNames, attributes);
            }
            else if (this.testToken("static")) {
                this.parseStaticFunction(staticFunctions, allMemberNames, attributes);
            }
            else if (this.testToken("field")) {
                this.parseMemberField(memberFields, allMemberNames, attributes);
            }
            else {
                this.ensureToken("method");

                this.parseMemberMethod(thisType, memberMethods, allMemberNames, attributes);
            }
        }
    }

    private parseConcept(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();

        //[attr] concept NAME[T where C...] provides {...}
        const attributes = this.parseAttributes();

        this.ensureAndConsumeToken("concept");
        this.ensureToken(TokenStrings.Type);

        const cname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        const provides = this.parseProvides(currentDecl.ns === "NSCore");

        try {
            this.setRecover(this.scanParens());
            this.ensureAndConsumeToken("{");

            const thisType = new NominalTypeSignature(currentDecl.ns, cname, terms.map((term) => term.ttype));

            const invariants: Expression[] = [];
            const staticMembers = new Map<string, StaticMemberDecl>();
            const staticFunctions = new Map<string, StaticFunctionDecl>();
            const memberFields = new Map<string, MemberFieldDecl>();
            const memberMethods = new Map<string, MemberMethodDecl>();
            this.parseOOPMembersCommon(true, thisType, invariants, staticMembers, staticFunctions, memberFields, memberMethods);

            this.ensureAndConsumeToken("}");

            if (currentDecl.checkDeclNameClash(currentDecl.ns, cname)) {
                this.raiseError(line, "Collision between concept and other names");
            }

            this.clearRecover();
            currentDecl.concepts.set(cname, new ConceptTypeDecl(this.m_penv.getCurrentFile(), attributes, currentDecl.ns, cname, terms, provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods));
            this.m_penv.assembly.addConceptDecl(currentDecl.ns + "::" + cname, currentDecl.concepts.get(cname) as ConceptTypeDecl);
        }
        catch (ex) {
            this.processRecover();
        }
    }

    private parseObject(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();

        //[attr] object NAME[T where C...] provides {...}
        const attributes = this.parseAttributes();

        this.ensureAndConsumeToken("entity");
        this.ensureToken(TokenStrings.Type);

        const cname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        const provides = this.parseProvides(currentDecl.ns === "NSCore");

        try {
            this.setRecover(this.scanParens());
            this.ensureAndConsumeToken("{");

            const thisType = new NominalTypeSignature(currentDecl.ns, cname, terms.map((term) => new TemplateTypeSignature(term.name)));

            const invariants: Expression[] = [];
            const staticMembers = new Map<string, StaticMemberDecl>();
            const staticFunctions = new Map<string, StaticFunctionDecl>();
            const memberFields = new Map<string, MemberFieldDecl>();
            const memberMethods = new Map<string, MemberMethodDecl>();
            this.parseOOPMembersCommon(true, thisType, invariants, staticMembers, staticFunctions, memberFields, memberMethods);

            this.ensureAndConsumeToken("}");

            if (currentDecl.checkDeclNameClash(currentDecl.ns, cname)) {
                this.raiseError(line, "Collision between object and other names");
            }

            this.clearRecover();
            currentDecl.concepts.set(cname, new EntityTypeDecl(this.m_penv.getCurrentFile(), attributes, currentDecl.ns, cname, terms, provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods, false, false));
            this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + cname, currentDecl.concepts.get(cname) as EntityTypeDecl);
        }
        catch (ex) {
            this.processRecover();
        }
    }

    private parseNamespaceConst(currentDecl: NamespaceDeclaration) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] const NAME[: T] = exp;
        const attributes = this.parseAttributes();

        this.ensureAndConsumeToken("global");
        this.ensureToken(TokenStrings.Identifier);
        const gname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const gtype = this.parseTypeSignature();

        this.ensureAndConsumeToken("=");
        const value = this.parseExpression();

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
        const sig = this.parseInvokableCommon(false, false, false, terms, []);

        currentDecl.functions.set(fname, new NamespaceFunctionDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, fname, sig));
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
                this.m_cpos = this.scanTokenOptions("function", "global", "typedef", "concept", "entity", "enum", "identifier");
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

                if (this.testToken("function") || this.testToken("global")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.Identifier);
                    const fname = this.consumeTokenAndGetValue();
                    if (nsdecl.declaredNames.has(fname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }

                    nsdecl.declaredNames.add(ns + "::" + fname);
                }
                else if (this.testToken("typedef") || this.testToken("concept") || this.testToken("entity") || this.testToken("enum") || this.testToken("identifier")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.Type);
                    const tname = this.consumeTokenAndGetValue();
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }

                    nsdecl.declaredNames.add(ns + "::" + tname);
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

        let usingok = true;
        let parseok = true;
        while (this.m_cpos < this.m_epos) {
            const rpos = this.scanTokenOptions("function", "global", "using", "typedef", "concept", "entity", "enum", "identifier", TokenStrings.EndOfStream);

            try {
                if (rpos === this.m_epos) {
                    break;
                }

                const tk = this.m_tokens[rpos].kind;
                usingok = usingok && tk === "using";
                if (tk === "using") {
                    if (!usingok) {
                        this.raiseError(this.getCurrentLine(), "Using statements must come before other declarations");
                    }

                    this.parseNamespaceUsing(nsdecl);
                }
                else if (tk === "function") {
                    this.parseNamespaceFunction(nsdecl);
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
                    this.parseObject(nsdecl);
                }
                else if (tk === TokenStrings.EndOfStream) {
                    this.parseEndOfStream();
                }
                else {
                    //enum or identifier
                    this.raiseError(this.getCurrentLine(), "enum and identifier not implemented yet");
                }
            }
            catch (ex) {
                this.m_cpos = rpos + 1;
                parseok = false;
            }
        }

        return parseok;
    }

    getParseErrors(): string[] | undefined {
        return this.m_errors.length !== 0 ? this.m_errors.map((err) => `${err[1]} on line ${err[0]}`) : undefined;
    }
}

export { SourceInfo, ParseError, Parser };
