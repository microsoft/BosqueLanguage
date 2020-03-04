//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ParserEnvironment, FunctionScope } from "./parser_env";
import { FunctionParameter, TypeSignature, NominalTypeSignature, TemplateTypeSignature, ParseErrorTypeSignature, TupleTypeSignature, RecordTypeSignature, FunctionTypeSignature, UnionTypeSignature, IntersectionTypeSignature, AutoTypeSignature, ProjectTypeSignature, EphemeralListTypeSignature } from "./type_signature";
import { Arguments, TemplateArguments, NamedArgument, PositionalArgument, InvalidExpression, Expression, LiteralNoneExpression, LiteralBoolExpression, LiteralIntegerExpression, LiteralStringExpression, LiteralTypedStringExpression, AccessVariableExpression, AccessNamespaceConstantExpression, LiteralTypedStringConstructorExpression, CallNamespaceFunctionExpression, AccessStaticFieldExpression, ConstructorTupleExpression, ConstructorRecordExpression, ConstructorPrimaryExpression, ConstructorPrimaryWithFactoryExpression, PostfixOperation, PostfixAccessFromIndex, PostfixAccessFromName, PostfixProjectFromIndecies, PostfixProjectFromNames, PostfixProjectFromType, PostfixModifyWithIndecies, PostfixModifyWithNames, PostfixStructuredExtend, PostfixInvoke, PostfixOp, PrefixOp, BinOpExpression, BinEqExpression, BinCmpExpression, BinLogicExpression, NonecheckExpression, CoalesceExpression, SelectExpression, BlockStatement, Statement, BodyImplementation, EmptyStatement, InvalidStatement, VariableDeclarationStatement, VariableAssignmentStatement, ReturnStatement, YieldStatement, CondBranchEntry, IfElse, IfElseStatement, InvokeArgument, CallStaticFunctionExpression, AssertStatement, CheckStatement, DebugStatement, StructuredAssignment, TupleStructuredAssignment, RecordStructuredAssignment, VariableDeclarationStructuredAssignment, IgnoreTermStructuredAssignment, VariableAssignmentStructuredAssignment, ConstValueStructuredAssignment, StructuredVariableAssignmentStatement, MatchStatement, MatchEntry, MatchGuard, WildcardMatchGuard, TypeMatchGuard, StructureMatchGuard, AbortStatement, BlockStatementExpression, IfExpression, MatchExpression, PragmaArguments, ConstructorPCodeExpression, PCodeInvokeExpression, ExpOrExpression, MapArgument, LiteralRegexExpression, ValidateStatement, NakedCallStatement, ValueListStructuredAssignment, NominalStructuredAssignment, VariablePackDeclarationStatement, VariablePackAssignmentStatement, ConstructorEphemeralValueList } from "./body";
import { Assembly, NamespaceUsing, NamespaceDeclaration, NamespaceTypedef, StaticMemberDecl, StaticFunctionDecl, MemberFieldDecl, MemberMethodDecl, ConceptTypeDecl, EntityTypeDecl, NamespaceConstDecl, NamespaceFunctionDecl, InvokeDecl, TemplateTermDecl, PreConditionDecl, PostConditionDecl, BuildLevel, TypeConditionRestriction, InvariantDecl, TemplateTypeRestriction } from "./assembly";

const KeywordStrings = [
    "pragma",

    "hidden",
    "factory",
    "virtual",
    "abstract",
    "override",
    "entrypoint",
    "recursive?",
    "recursive",

    "_debug",
    "abort",
    "assert",
    "case",
    "check",
    "clock",
    "composite",
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
    "grounded",
    "guid",
    "hash",
    "identifier",
    "if",
    "invariant",
    "method",
    "namespace",
    "none",
    "or",
    "private",
    "provides",
    "ref",
    "release",
    "return",
    "requires",
    "static",
    "switch",
    "test",
    "true",
    "type",
    "typedef",
    "using",
    "validate",
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
    ":",
    "::",
    ",",
    ".",
    "...",
    "=",
    "==",
    "=>",
    "==>",
    ";",
    "|",
    "||",
    "+",
    "?",
    "?&",
    "?|",
    "?.",
    "<",
    "<=",
    ">",
    ">=",
    "-",
    "->",
    "?->"
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : a.localeCompare(b); });

const LeftScanParens = ["[", "(", "{", "(|", "{|"];
const RightScanParens = ["]", ")", "}", "|)", "|}"];

const AttributeStrings = ["hidden", "private", "factory", "virtual", "abstract", "override", "entrypoint", "recursive", "recursive?"];

const SpecialInvokeNames = ["update", "merge", "project", "tryProject"];

const TokenStrings = {
    Clear: "[CLEAR]",
    Error: "[ERROR]",

    Int: "[LITERAL_INT]",
    String: "[LITERAL_STRING]",
    Regex: "[LITERAL_REGEX]",
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
        return str.length === 1 && /^[A-Z]$/.test(str);
    }

    private static isIdentifierName(str: string) {
        return /^[$a-z_]/.test(str);
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

    private static readonly _s_regexRe = /\/(~[\/] | (\\\/))*\//y;
    private tryLexRegex() {
        Lexer._s_regexRe.lastIndex = this.m_cpos;
        const ms = Lexer._s_regexRe.exec(this.m_input);
        if (ms !== null) {
            this.recordLexTokenWData(this.m_cpos + ms[0].length, TokenStrings.Regex, ms[0]);
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

    private static readonly _s_nameRe = /([$]?\w+)|(recursive\?)/y;
    private tryLexName() {
        if (this.m_input.startsWith("recursive?", this.m_cpos)) {
            this.recordLexToken(this.m_cpos + "recursive?".length, "recursive?");
            return true;
        }

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

    private scanMatchingParens(lp: string, rp: string): number {
        let pscount = 1;
        for (let pos = this.m_cpos + 1; pos < this.m_epos; ++pos) {
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

    testFollowsFrom(pos: number, ...kinds: string[]): boolean {
        for (let i = 0; i < kinds.length; ++i) {
            if (pos + i === this.m_epos || this.m_tokens[pos + i].kind !== kinds[i]) {
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
        if(this.testToken("debug") || this.testToken("test") || this.testToken("release")) {
            return this.consumeTokenAndGetValue() as "debug" | "test" | "release";
        }
        else {
            return cb;
        }
    }

    ////
    //Misc parsing

    private parseInvokableCommon(ispcode: boolean, isMember: boolean, noBody: boolean, attributes: string[], isrecursive: "yes" | "no" | "cond", pragmas: [TypeSignature, string][], terms: TemplateTermDecl[], termRestrictions: TypeConditionRestriction | undefined, optSelfType?: TypeSignature): InvokeDecl {
        const sinfo = this.getCurrentSrcInfo();
        const srcFile = this.m_penv.getCurrentFile();
        const line = this.getCurrentLine();

        let fparams: FunctionParameter[] = [];
        if (isMember) {
            fparams.push(new FunctionParameter("this", optSelfType as TypeSignature, false, false));
        }

        let restName: string | undefined = undefined;
        let restType: TypeSignature | undefined = undefined;
        let resultInfo = this.m_penv.SpecialAutoSignature;

        const params = this.parseListOf<[string, TypeSignature, boolean, boolean, boolean]>("(", ")", ",", () => {
            const isrest = this.testAndConsumeTokenIf("...");
            const isref = this.testAndConsumeTokenIf("ref");

            this.ensureToken(TokenStrings.Identifier);
            const pname = this.consumeTokenAndGetValue();
            const isopt = this.testAndConsumeTokenIf("?");
            let argtype = this.m_penv.SpecialAutoSignature;

            if (this.testAndConsumeTokenIf(":")) {
                argtype = this.parseTypeSignature();
            }
            else {
                if (!ispcode) {
                    this.raiseError(line, "Auto typing is not supported for this");
                }
            }

            if (isref && (isopt || isrest)) {
                this.raiseError(line, "Cannot use ref/borrow parameters here");
            }

            return [pname, argtype, isopt, isrest, isref];
        })[0];

        for (let i = 0; i < params.length; i++) {
            if (!params[i][3]) {
                fparams.push(new FunctionParameter(params[i][0], params[i][1], params[i][2], params[i][4]));
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
            if (!ispcode) {
                this.raiseError(line, "Auto typing is not supported for this");
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
            if (ispcode) {
                this.ensureAndConsumeToken("=>");
            }
            else {
                [preconds, postconds] = this.parsePreAndPostConditions(sinfo, argNames);
            }

            const bodyid = `${srcFile}::${sinfo.pos}`;
            try {
                this.m_penv.pushFunctionScope(new FunctionScope(argNames));
                body = this.parseBody(bodyid, srcFile, fparams.map((p) => p.name));
                captured = this.m_penv.getCurrentFunctionScope().getCaptureVars();
                this.m_penv.popFunctionScope();
            }
            catch (ex) {
                this.m_penv.popFunctionScope();
                throw ex;
            }
        }

        if (ispcode) {
            return InvokeDecl.createPCodeInvokeDecl(sinfo, srcFile, attributes, isrecursive, fparams, restName, restType, resultInfo, captured, body as BodyImplementation);
        }
        else if (isMember) {
            return InvokeDecl.createMemberInvokeDecl(sinfo, srcFile, attributes, isrecursive, pragmas, terms, termRestrictions, fparams, restName, restType, resultInfo, preconds, postconds, body);
        }
        else {
            return InvokeDecl.createStaticInvokeDecl(sinfo, srcFile, attributes, isrecursive, pragmas, terms, termRestrictions, fparams, restName, restType, resultInfo, preconds, postconds, body);
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
        let roottype = this.parseProjectType();
        while (this.testToken("?")) {
            roottype = this.parseNoneableType(roottype);
        }
        return roottype;
    }

    private parseNoneableType(basetype: TypeSignature): TypeSignature {
        this.ensureAndConsumeToken("?");
        return Parser.orOfTypeSignatures(basetype, this.m_penv.SpecialNoneSignature);
    }

    private parseProjectType(): TypeSignature {
        const ltype = this.parseAndCombinatorType();
        if (!this.testToken("!")) {
            return ltype;
        }
        else {
            this.consumeToken();
            return new ProjectTypeSignature(ltype, this.parseNominalType());
        }
    }

    private parseAndCombinatorType(): TypeSignature {
        const ltype = this.parseBaseTypeReference();
        if (!this.testToken("&")) {
            return ltype;
        }
        else {
            this.consumeToken();
            return Parser.andOfTypeSignatures(ltype, this.parseAndCombinatorType());
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
            case "recursive?":
            case "recursive":
                return this.parsePCodeType();
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

        if (!this.testToken("<")) {
            return new NominalTypeSignature(ns as string, tname);
        }
        else {
            let terms: TypeSignature[] = [];
            try {
                this.setRecover(this.scanMatchingParens("<", ">"));
                terms = this.parseListOf<TypeSignature>("<", ">", ",", () => {
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

        try {
            this.setRecover(this.scanMatchingParens("[", "]"));
            entries = this.parseListOf<[TypeSignature, boolean]>("[", "]", ",", () => {
                const isopt = this.testAndConsumeTokenIf("?");
                if (isopt) {
                    this.ensureAndConsumeToken(":");
                }

                const rtype = this.parseTypeSignature();

                return [rtype, isopt];
            })[0];

            const firstOpt = entries.findIndex((entry) => entry[1]);
            if (entries.slice(firstOpt).findIndex((entry) => !entry[0]) !== -1) {
                this.raiseError(line, "Optional entries must all come at end of tuple");
            }

            this.clearRecover();
            return new TupleTypeSignature(entries);
        }
        catch (ex) {
            this.processRecover();
            return new ParseErrorTypeSignature();
        }
    }

    private parseRecordType(): TypeSignature {
        let entries: [string, TypeSignature, boolean][] = [];

        try {
            this.setRecover(this.scanMatchingParens("{", "}"));
            entries = this.parseListOf<[string, TypeSignature, boolean]>("{", "}", ",", () => {
                this.ensureToken(TokenStrings.Identifier);

                const name = this.consumeTokenAndGetValue();
                const isopt = this.testAndConsumeTokenIf("?");
                this.ensureAndConsumeToken(":");
                const rtype = this.parseTypeSignature();

                return [name, rtype, isopt];
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

        this.ensureAndConsumeToken("fn");

        try {
            this.setRecover(this.scanMatchingParens("(", ")"));

            let fparams: FunctionParameter[] = [];
            let restName: string | undefined = undefined;
            let restType: TypeSignature | undefined = undefined;

            const params = this.parseListOf<[string, TypeSignature, boolean, boolean, boolean]>("(", ")", ",", () => {
                const isrest = this.testAndConsumeTokenIf("...");
                const isref = this.testAndConsumeTokenIf("ref");

                this.ensureToken(TokenStrings.Identifier);
                const pname = this.consumeTokenAndGetValue();
                const isopt = this.testAndConsumeTokenIf("?");
               
                this.ensureAndConsumeToken(":");
                const argtype = this.parseTypeSignature();

                if (isref && (isopt || isrest)) {
                    this.raiseError(this.getCurrentLine(), "Cannot use ref/borrow parameters here");
                }

                return [pname, argtype, isopt, isrest, isref];
            })[0];

            for (let i = 0; i < params.length; i++) {
                if (!params[i][3]) {
                    fparams.push(new FunctionParameter(params[i][0], params[i][1], params[i][2], params[i][4]));
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
            this.setRecover(this.scanMatchingParens(lparen, rparen));

            this.ensureAndConsumeToken(lparen);
            while (!this.testAndConsumeTokenIf(rparen)) {
                const line = this.getCurrentLine();
                const isref = this.testAndConsumeTokenIf("ref");

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

                    args.push(new NamedArgument(isref, name, exp));
                }
                else {
                    const isSpread = this.testAndConsumeTokenIf("...");
                    const exp = this.parseExpression();

                    if (!this.testToken("=>")) {
                        args.push(new PositionalArgument(isref, isSpread, exp));
                    }
                    else {
                        if(isSpread) {
                            this.raiseError(line, "Cannot use spread operator on map argument key");
                        }

                        this.ensureAndConsumeToken("=>");
                        const value = this.parseExpression();

                        args.push(new MapArgument(exp, value));
                    }
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
            return new Arguments([new PositionalArgument(false, false, new InvalidExpression(argSrcInfo))]);
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

    private parsePragmaArguments(): PragmaArguments {
        try {
            this.setRecover(this.scanMatchingParens("[", "]"));
            let pargs: [TypeSignature, string][] = [];

            let recursive: "yes" | "no" | "cond" = "no";
            this.ensureAndConsumeToken("[");
            while (!this.testAndConsumeTokenIf("]")) {
                if (this.testToken("recursive") || this.testToken("recursive?")) {
                    if (recursive !== "no") {
                        this.raiseError(this.getCurrentLine(), "Multiple recursive pragmas on call");
                    }

                    recursive = this.testToken("recursive") ? "yes" : "cond";
                    this.consumeToken();
                }
                else {
                    const ptype = this.parseTypeSignature();
                    this.ensureToken(TokenStrings.TypedString);
                    const pstr = this.consumeTokenAndGetValue();

                    pargs.push([ptype, pstr]);
                }

                if (this.testAndConsumeTokenIf(",")) {
                    this.ensureNotToken("]");
                }
                else {
                    this.ensureToken("]");
                }
            }

            this.clearRecover();
            return new PragmaArguments(recursive, pargs);
        }
        catch (ex) {
            this.processRecover();
            return new PragmaArguments("no", []);
        }
    }

    private parseConstructorPrimary(otype: TypeSignature): Expression {
        const sinfo = this.getCurrentSrcInfo();

        let asvalue = false;
        if(this.testToken("@")) {
            this.consumeToken();
        }
        else {
            this.ensureAndConsumeToken("#");
            asvalue = true;
        }
        const args = this.parseArguments("{", "}");

        return new ConstructorPrimaryExpression(sinfo, otype, asvalue, args);
    }

    private parseConstructorPrimaryWithFactory(otype: TypeSignature): Expression {
        const sinfo = this.getCurrentSrcInfo();

        let asvalue = false;
        if(this.testToken("@")) {
            this.consumeToken();
        }
        else {
            this.ensureAndConsumeToken("#");
            asvalue = true;
        }
        this.ensureToken(TokenStrings.Identifier);

        const fname = this.consumeTokenAndGetValue();
        const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
        const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new PragmaArguments("no", []);
        const args = this.parseArguments("(", ")");

        return new ConstructorPrimaryWithFactoryExpression(sinfo, otype, asvalue, fname, pragmas, targs, args);
    }

    private parsePCodeTerm(): Expression {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();

        const isrecursive = this.testAndConsumeTokenIf("recursive");

        this.ensureAndConsumeToken("fn");
        const sig = this.parseInvokableCommon(true, false, false, [], isrecursive ? "yes" : "no", [], [], undefined);
        const someAuto = sig.params.some((param) => param.type instanceof AutoTypeSignature) || (sig.optRestType !== undefined && sig.optRestType instanceof AutoTypeSignature) || (sig.resultType instanceof AutoTypeSignature);
        const allAuto = sig.params.every((param) => param.type instanceof AutoTypeSignature) && (sig.optRestType === undefined || sig.optRestType instanceof AutoTypeSignature) && (sig.resultType instanceof AutoTypeSignature);
        if (someAuto && !allAuto) {
            this.raiseError(line, "Cannot have mixed of auto propagated and explicit types on lambda arguments/return");
        }

        sig.captureSet.forEach((v) => {
            this.m_penv.getCurrentFunctionScope().useLocalVar(v);
        });

        return new ConstructorPCodeExpression(sinfo, allAuto, sig);
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
        else if (tk === TokenStrings.Regex) {
            const restr = this.consumeTokenAndGetValue(); //keep in escaped format
            return new LiteralRegexExpression(sinfo, restr);
        }
        else if (tk === TokenStrings.Identifier) {
            const istr = this.consumeTokenAndGetValue();

            const ns = this.m_penv.tryResolveNamespace(undefined, istr);
            if (ns === undefined) {
                //Ignore special postcondition $return variable but everything else should be processed
                if (istr !== "$return") {
                    this.m_penv.getCurrentFunctionScope().useLocalVar(istr);
                }

                if (this.testToken("[")) {
                    const pragmas = this.parsePragmaArguments();
                    const args = this.parseArguments("(", ")");
                    return new PCodeInvokeExpression(sinfo, istr, pragmas, args);
                }
                else if (this.testToken("(")) {
                    const args = this.parseArguments("(", ")");
                    return new PCodeInvokeExpression(sinfo, istr, new PragmaArguments("no", []), args);
                }
                else {
                    return new AccessVariableExpression(sinfo, istr);
                }
            }
            else {
                const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
                const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new PragmaArguments("no", []);
                const args = this.parseArguments("(", ")");

                return new CallNamespaceFunctionExpression(sinfo, ns, istr, targs, pragmas, args);
            }
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
        else if (this.testToken("[")) {
            const args = this.parseArguments("[", "]");
            return new ConstructorTupleExpression(sinfo, args);
        }
        else if (this.testToken("{")) {
            const args = this.parseArguments("{", "}");
            return new ConstructorRecordExpression(sinfo, args);
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
                const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new PragmaArguments("no", []);
                const args = this.parseArguments("(", ")");

                return new CallNamespaceFunctionExpression(sinfo, ns, name, targs, pragmas, args);
            }
        }
        else {
            //we should find a type (nominal here) and it is either (1) a constructor (2) constructor with factory or (3) static invoke

            const ttype = this.parseTypeSignature();
            if (this.testFollows("::", TokenStrings.Identifier)) {
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                if (!this.testToken("<") && !this.testToken("[") && !this.testToken("(")) {
                    //just a static access
                    return new AccessStaticFieldExpression(sinfo, ttype, name);
                }
                else {
                    const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
                    const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new PragmaArguments("no", []);
                    const args = this.parseArguments("(", ")");

                    return new CallStaticFunctionExpression(sinfo, ttype, name, targs, pragmas, args);
                }
            }
            else if (this.testToken(TokenStrings.TypedString) || this.testFollows("@", TokenStrings.TypedString) || this.testFollows("#", TokenStrings.TypedString)) {
                if (this.testAndConsumeTokenIf("@")) {
                    const sstr = this.consumeTokenAndGetValue(); //keep in escaped format
                    return new LiteralTypedStringConstructorExpression(sinfo, sstr, false, ttype);
                }
                else if (this.testAndConsumeTokenIf("#")) {
                    const sstr = this.consumeTokenAndGetValue(); //keep in escaped format
                    return new LiteralTypedStringConstructorExpression(sinfo, sstr, true, ttype);
                }
                else {
                    const sstr = this.consumeTokenAndGetValue(); //keep in escaped format
                    return new LiteralTypedStringExpression(sinfo, sstr, ttype);
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

    private handleSpecialCaseMethods(sinfo: SourceInfo, isElvis: boolean, specificResolve: TypeSignature | undefined, name: string): PostfixOperation {
        if (specificResolve !== undefined) {
            this.raiseError(this.getCurrentLine(), "Cannot use specific resolve on special methods");
        }

        const line = this.getCurrentLine();
        if (name === "project" || name === "tryProject") {
            this.ensureToken("<");
            const terms = this.parseTemplateArguments();
            if (terms.targs.length !== 1) {
                this.raiseError(line, "The project method expects a single template type argument");
            }

            const type = terms.targs[0];
            if (!(type instanceof TemplateTypeSignature || type instanceof NominalTypeSignature || type instanceof RecordTypeSignature || type instanceof TupleTypeSignature)) {
                this.raiseError(line, "Can only project over record, tuple, or concept contraints");
            }

            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");
            return new PostfixProjectFromType(sinfo, isElvis, name === "tryProject", type);
        }
        else if (name === "update") {
            if (this.testFollows("(", TokenStrings.Int)) {
                const updates = this.parseListOf<[number, Expression]>("(", ")", ",", () => {
                    this.ensureToken(TokenStrings.Int);
                    const idx = Number.parseInt(this.consumeTokenAndGetValue());
                    this.ensureAndConsumeToken("=");
                    const value = this.parseExpression();

                    return [idx, value];
                })[0].sort((a, b) => a[0] - b[0]);

                return new PostfixModifyWithIndecies(sinfo, isElvis, updates);
            }
            else if (this.testFollows("(", TokenStrings.Identifier)) {
                const updates = this.parseListOf<[string, Expression]>("(", ")", ",", () => {
                    this.ensureToken(TokenStrings.Identifier);
                    const uname = this.consumeTokenAndGetValue();
                    this.ensureAndConsumeToken("=");
                    const value = this.parseExpression();

                    return [uname, value];
                })[0].sort((a, b) => a[0].localeCompare(b[0]));

                return new PostfixModifyWithNames(sinfo, isElvis, updates);
            }
            else {
                this.raiseError(line, "Expected list of property/field or tuple updates");
                return (undefined as unknown) as PostfixOperation;
            }
        }
        else if (name === "merge") {
            this.ensureAndConsumeToken("(");
            const update = this.parseExpression();
            this.ensureAndConsumeToken(")");

            return new PostfixStructuredExtend(sinfo, isElvis, update);
        }
        else {
            this.raiseError(line, "unknown special operation");
            return (undefined as unknown) as PostfixOperation;
        }
    }

    private parsePostfixExpression(): Expression {
        const rootinfo = this.getCurrentSrcInfo();
        let rootexp = this.parsePrimaryExpression();

        let ops: PostfixOperation[] = [];
        while (true) {
            const sinfo = this.getCurrentSrcInfo();

            const tk = this.peekToken();
            if (tk === "." || tk === "?.") {
                const isElvis = this.testToken("?.");
                this.consumeToken();

                if (this.testToken(TokenStrings.Int)) {
                    const index = Number.parseInt(this.consumeTokenAndGetValue());

                    ops.push(new PostfixAccessFromIndex(sinfo, isElvis, index));
                }
                else if (this.testToken("[")) {
                    const indecies = this.parseListOf<number>("[", "]", ",", () => {
                        this.ensureToken(TokenStrings.Int);
                        return Number.parseInt(this.consumeTokenAndGetValue());
                    })[0];

                    if(indecies.length === 0) {
                        this.raiseError(sinfo.line, "You must have at least one index when projecting");
                    }

                    ops.push(new PostfixProjectFromIndecies(sinfo, isElvis, false, indecies));
                }
                else if (this.testToken(TokenStrings.Identifier)) {
                    const name = this.consumeTokenAndGetValue();

                    ops.push(new PostfixAccessFromName(sinfo, isElvis, name));
                }
                else if (this.testToken("{")) {
                    const names = this.parseListOf<string>("{", "}", ",", () => {
                        this.ensureToken(TokenStrings.Identifier);
                        return this.consumeTokenAndGetValue();
                    })[0].sort();

                    if(names.length === 0) {
                        this.raiseError(sinfo.line, "You must have at least one index when projecting");
                    }

                    ops.push(new PostfixProjectFromNames(sinfo, isElvis, false, names));
                }
                else {
                    this.ensureToken("(|");

                    if (this.testFollows("(|", TokenStrings.Int)) {
                        const indecies = this.parseListOf<number>("(|", "|)", ",", () => {
                            this.ensureToken(TokenStrings.Int);
                            return Number.parseInt(this.consumeTokenAndGetValue());
                        })[0];

                        if (indecies.length <= 1) {
                            this.raiseError(sinfo.line, "You must have at least two indecies when projecting out a Ephemeral value pack (otherwise just access the index directly)");
                        }

                        ops.push(new PostfixProjectFromIndecies(sinfo, isElvis, true, indecies));
                    }
                    else {
                        const names = this.parseListOf<string>("(|", "|)", ",", () => {
                            this.ensureToken(TokenStrings.Identifier);
                            return this.consumeTokenAndGetValue();
                        })[0].sort();

                        if (names.length <= 1) {
                            this.raiseError(sinfo.line, "You must have at least two names when projecting out a Ephemeral value pack (otherwise just access the property/field directly)");
                        }

                        ops.push(new PostfixProjectFromNames(sinfo, isElvis, true, names));
                    }
                }
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

                if (SpecialInvokeNames.includes(name)) {
                    ops.push(this.handleSpecialCaseMethods(sinfo, isElvis, specificResolve, name));
                }
                else {
                    const terms = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
                    const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new PragmaArguments("no", []);
                    const args = this.parseArguments("(", ")");

                    ops.push(new PostfixInvoke(sinfo, isElvis, specificResolve, name, terms, pragmas, args));
                }
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

    private parseAdditiveExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parsePrefixExpression();

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

    private parseExpOrExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const texp = this.parseSelectExpression();

        if (this.testAndConsumeTokenIf("or")) {
            if (!this.testToken("return") && !this.testToken("yield")) {
                this.raiseError(this.getCurrentLine(), "Expected 'return' or 'yield");
            }

            const action = this.consumeTokenAndGetValue();
            let value: undefined | Expression = undefined;
            let cond: undefined | Expression = undefined;

            if (!this.testToken(";")) {
                if (this.testToken("when")) {
                    this.consumeToken();
                    cond = this.parseExpression();
                }
                else {
                    value = this.parseExpression();
                    if (this.testToken("when")) {
                        this.consumeToken();
                        cond = this.parseExpression();
                    }
                }
            }

            return new ExpOrExpression(sinfo, texp, action, value, cond);
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
        return this.parseExpOrExpression();
    }

    ////
    //Statement parsing

    parseStructuredAssignment(sinfo: SourceInfo, vars: "var" | "var!" | undefined, trequired: boolean, decls: Set<string>): StructuredAssignment {
        if (this.testToken("[")) {
            const assigns = this.parseListOf<StructuredAssignment>("[", "]", ",", () => {
                return this.parseStructuredAssignment(this.getCurrentSrcInfo(), vars, trequired, decls);
            })[0];

            return new TupleStructuredAssignment(assigns);
        }
        else if (this.testToken("{")) {
            const assigns = this.parseListOf<[string, StructuredAssignment]>("{", "}", ",", () => {
                this.ensureToken(TokenStrings.Identifier);
                const name = this.consumeTokenAndGetValue();

                this.ensureAndConsumeToken("=");
                const subg = this.parseStructuredAssignment(this.getCurrentSrcInfo(), vars, trequired, decls);

                return [name, subg];
            })[0];

            return new RecordStructuredAssignment(assigns);
        }
        else if (this.testToken("(|")) {
            const assigns = this.parseListOf<StructuredAssignment>("(|", "|)", ",", () => {
                return this.parseStructuredAssignment(this.getCurrentSrcInfo(), vars, trequired, decls);
            })[0];

            return new ValueListStructuredAssignment(assigns);
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
                        
                        if(!(itype instanceof AutoTypeSignature)) {
                            this.raiseError(sinfo.line, "Cannot redeclare type of variable on assignment");
                        }

                        return new VariableAssignmentStructuredAssignment(isopt, name);
                    }
                }
            }
            else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Type ) || this.testToken(TokenStrings.Type)) {
                const ttype = this.parseTypeSignature();
                if (this.testFollows("::", TokenStrings.Identifier)) {
                    this.consumeToken();
                    const name = this.consumeTokenAndGetValue();
                    if (this.testToken("<") || !this.testToken("[") || !this.testToken("(")) {
                        this.raiseError(sinfo.line, "Expected a static field expression");
                    }

                    return new ConstValueStructuredAssignment(new AccessStaticFieldExpression(sinfo, ttype, name));
                }
                else if (this.testToken(TokenStrings.TypedString) || this.testFollows("@", TokenStrings.TypedString) || this.testFollows("#", TokenStrings.TypedString)) {
                    if (this.testAndConsumeTokenIf("@")) {
                        const sstr = this.consumeTokenAndGetValue(); //keep in escaped format
                        return new ConstValueStructuredAssignment(new LiteralTypedStringConstructorExpression(sinfo, sstr, false, ttype));
                    }
                    else if (this.testAndConsumeTokenIf("#")) {
                        const sstr = this.consumeTokenAndGetValue(); //keep in escaped format
                        return new ConstValueStructuredAssignment(new LiteralTypedStringConstructorExpression(sinfo, sstr, true, ttype));
                    }
                    else {
                        const sstr = this.consumeTokenAndGetValue(); //keep in escaped format
                        return new ConstValueStructuredAssignment(new LiteralTypedStringExpression(sinfo, sstr, ttype));
                    }
                }
                else if (this.testFollows("@", "{") || this.testFollows("#", "{")) {
                    let isvalue = false;
                    if(this.testAndConsumeTokenIf("#")) {
                        isvalue = true;
                    }
                    else {
                        this.ensureAndConsumeToken("@");
                    }

                    const assigns = this.parseListOf<[string, StructuredAssignment]>("{", "}", ",", () => {
                        this.ensureToken(TokenStrings.Identifier);
                        const name = this.consumeTokenAndGetValue();
        
                        this.ensureAndConsumeToken("=");
                        const subg = this.parseStructuredAssignment(this.getCurrentSrcInfo(), vars, trequired, decls);
        
                        return [name, subg];
                    })[0];

                    return new NominalStructuredAssignment(ttype, isvalue, assigns);
                }
                else {
                    this.raiseError(sinfo.line, "Unknown token sequence in parsing expression");
                    return new ConstValueStructuredAssignment(new InvalidExpression(sinfo));
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

            if (this.testToken("[") || this.testToken("{") || this.testToken("(|") || this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Type ) || this.testToken(TokenStrings.Type)) {
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
                let decls = new Set<string>();
                const assigns = this.parseEphemeralListOf(() => {
                    return this.parseStructuredAssignment(this.getCurrentSrcInfo(), isConst ? "var" : "var!", false, decls);
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
                        this.m_penv.getCurrentFunctionScope().defineLocalVar(dv.vname);

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
                    if (exp !== undefined && (exp.length !== 1 || exp.length !== vars.length)) {
                        this.raiseError(line, "Mismatch between variables declared and values provided");
                    }

                    return new VariablePackDeclarationStatement(sinfo, isConst, vars, exp);
                }
            }
        }
        else if (tk === "[" || tk === "{" || tk === "(|") {
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
        else if (tk === TokenStrings.Identifier) {
            let decls = new Set<string>();
            const assigns = this.parseEphemeralListOf(() => {
                return this.parseStructuredAssignment(this.getCurrentSrcInfo(), undefined, false, decls);
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
                if (exps.length !== 1 || exps.length !== vars.length) {
                    this.raiseError(line, "Mismatch between variables declared and values provided");
                }

                return new VariablePackAssignmentStatement(sinfo, vars, exps);
            }
        }
        else if (tk === "return") {
            this.consumeToken();

            const exps = this.parseEphemeralListOf(() => this.parseExpression());

            this.ensureAndConsumeToken(";");
            return new ReturnStatement(sinfo, exps);
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

            const exp = this.parseExpression();
            let err = new LiteralNoneExpression(sinfo);
            if (this.testAndConsumeTokenIf("or")) {
                this.ensureAndConsumeToken("return");
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
            const ns = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
            const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new PragmaArguments("no", []);
            const args = this.parseArguments("(", ")");

            return new NakedCallStatement(sinfo, new CallNamespaceFunctionExpression(sinfo, ns, name, targs, pragmas, args));
        }
        else {
            //we should find a type (nominal here) and it is a static invoke or a structured assign
            const ttype = this.parseTypeSignature();

            if (this.testFollows("@", "{") || this.testFollows("#", "{")) {
                let isvalue = false;
                if(this.testAndConsumeTokenIf("#")) {
                    isvalue = true;
                }
                else {
                    this.ensureAndConsumeToken("@");
                }

                let decls = new Set<string>();
                const assigns = this.parseListOf<[string, StructuredAssignment]>("{", "}", ",", () => {
                    this.ensureToken(TokenStrings.Identifier);
                    const name = this.consumeTokenAndGetValue();
    
                    this.ensureAndConsumeToken("=");
                    const subg = this.parseStructuredAssignment(this.getCurrentSrcInfo(), undefined, false, decls);
    
                    return [name, subg];
                })[0];

                const assign = new NominalStructuredAssignment(ttype, isvalue, assigns);
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
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
                const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new PragmaArguments("no", []);
                const args = this.parseArguments("(", ")");

                return new NakedCallStatement(sinfo, new CallStaticFunctionExpression(sinfo, ttype, name, targs, pragmas, args));
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
                this.raiseError(this.getCurrentLine(), "No empty blocks");
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

    private parseBody(bodyid: string, file: string, pnames: string[]): BodyImplementation {
        if (this.testToken("#")) {
            this.consumeToken();
            this.ensureToken(TokenStrings.Identifier);
            return new BodyImplementation(bodyid, file, this.consumeTokenAndGetValue());
        }
        else if (this.testToken("{")) {
            if (this.testFollows("{", TokenStrings.Identifier, "=") && !pnames.includes(this.peekTokenData(1))) {
                //This is ambigious with the record constructor {p=exp ...} and the statement block {x=exp; ...}
                //However it is illegal to set a variable before declaration -- only option is updating a ref parameter so we check that
                return new BodyImplementation(bodyid, file, this.parseExpression());
            }
            else {
                return new BodyImplementation(bodyid, file, this.parseBlockStatement());
            }
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

    private parseDeclPragmas(): [TypeSignature, string][] {
        let pragmas: [TypeSignature, string][] = [];
        while (this.testToken("pragma")) {
            const ts = this.parseTypeSignature();

            this.ensureToken(TokenStrings.TypedString);
            const sl = this.consumeTokenAndGetValue();

            pragmas.push([ts, sl]);
        }

        return pragmas;
    }

    private parseTermDeclarations(): TemplateTermDecl[] {
        let terms: TemplateTermDecl[] = [];
        if (this.testToken("<")) {
            terms = this.parseListOf<TemplateTermDecl>("<", ">", ",", () => {
                this.ensureToken(TokenStrings.Template);
                const templatename = this.consumeTokenAndGetValue();
                const hasconstraint = this.testAndConsumeTokenIf("where");
                const isgrounded = this.testAndConsumeTokenIf("grounded");
                const tconstraint = hasconstraint ? this.parseTypeSignature() : this.m_penv.SpecialAnySignature;

                return new TemplateTermDecl(templatename, isgrounded, tconstraint);
            })[0];
        }
        return terms;
    }

    private parseSingleTermRestriction(): TemplateTypeRestriction {
        this.ensureToken(TokenStrings.Template);
        const templatename = this.consumeTokenAndGetValue();
        const isgrounded = this.testAndConsumeTokenIf("grounded")
        const oftype = this.parseTypeSignature();

        return new TemplateTypeRestriction(new TemplateTypeSignature(templatename), isgrounded, oftype);
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

    private parsePreAndPostConditions(sinfo: SourceInfo, argnames: Set<string>): [PreConditionDecl[], PostConditionDecl[]] {
        let preconds: PreConditionDecl[] = [];
        try {
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(argnames)));
            while (this.testToken("requires") || this.testToken("validate")) {
                const isvalidate = this.testToken("validate");
                this.consumeToken();
                
                let level: BuildLevel = isvalidate ? "release" : "debug";
                if (!isvalidate) {
                    level = this.parseBuildInfo(level);
                }

                const exp = this.parseExpression();

                let err: Expression | undefined = undefined;
                if (isvalidate) {
                    err = new LiteralNoneExpression(sinfo);
                    if (this.testAndConsumeTokenIf("or")) {
                        this.ensureAndConsumeToken("reutrn");
                        err = this.parseExpression();
                    }
                }

                preconds.push(new PreConditionDecl(sinfo, isvalidate, level, exp, err));

                this.ensureAndConsumeToken(";");
            }
        } finally {
            this.m_penv.popFunctionScope();
        }

        let postconds: PostConditionDecl[] = [];
        try {
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(argnames).add("$return")));
            while (this.testToken("ensures")) {
                this.consumeToken();

                let level: BuildLevel = "debug";
                if (this.testAndConsumeTokenIf("#")) {
                    level = this.consumeTokenAndGetValue() as BuildLevel;
                }

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

        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("typedef");
        this.ensureToken(TokenStrings.Type);
        const tyname = this.consumeTokenAndGetValue();

        const terms = this.parseTermDeclarations();

        this.ensureAndConsumeToken("=");
        const rpos = this.scanToken(";");
        if (rpos === this.m_epos) {
            this.raiseError(this.getCurrentLine(), "Missing ; on typedef");
        }

        if(this.testToken(TokenStrings.Regex)) {
            const vregex = this.consumeTokenAndGetValue();
            this.consumeToken();

            const validator = new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), [], [], "vregex", new NominalTypeSignature("NSCore", "Regex"), new LiteralRegexExpression(sinfo, vregex));
            const provides = [[new NominalTypeSignature("NSCore", "Validator"), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
            const validatortype = new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), [], [], currentDecl.ns, tyname, [], provides, [], new Map<string, StaticMemberDecl>().set("vregex", validator), new Map<string, StaticFunctionDecl>(), new Map<string, MemberFieldDecl>(), new Map<string, MemberMethodDecl>());

            currentDecl.objects.set(tyname, validatortype);
            this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + tyname, 0, currentDecl.objects.get(tyname) as EntityTypeDecl);
        }
        else {
            const btype = this.parseTypeSignature();
            this.consumeToken();

            if (currentDecl.checkDeclNameClash(currentDecl.ns, tyname)) {
                this.raiseError(this.getCurrentLine(), "Collision between typedef and other names");
            }

            currentDecl.typeDefs.set(currentDecl.ns + "::" + tyname, new NamespaceTypedef(currentDecl.ns, tyname, terms, btype));
        }
    }

    private parseProvides(iscorens: boolean): [TypeSignature, TypeConditionRestriction | undefined][] {
        let provides: [TypeSignature, TypeConditionRestriction | undefined][] = [];
        if (this.testToken("provides")) {
            this.consumeToken();

            while (!this.testToken("{")) {
                this.consumeTokenIf(",");

                const pv = this.parseTypeSignature();
                let res: TypeConditionRestriction | undefined = undefined;
                if(this.testAndConsumeTokenIf("when")) {
                    res = this.parseTermRestriction(false);
                }
                provides.push([pv, res]);
            }
        }
        else {
            if (!iscorens) {
                provides.push([new NominalTypeSignature("NSCore", "Object"), undefined]);
            }
        }
        return provides;
    }

    private parseConstMember(staticMembers: Map<string, StaticMemberDecl>, allMemberNames: Set<string>, attributes: string[], pragmas: [TypeSignature, string][]) {
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
        staticMembers.set(sname, new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, sname, stype, value));
    }

    private parseStaticFunction(staticFunctions: Map<string, StaticFunctionDecl>, allMemberNames: Set<string>, attributes: string[], pragmas: [TypeSignature, string][]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] static NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        this.ensureAndConsumeToken("static");
        const termRestrictions = this.parseTermRestriction(true);

        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        let recursive: "yes" | "no" | "cond" = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(false, false, Parser.attributeSetContains("abstract", attributes), attributes, recursive, pragmas, terms, termRestrictions);

        if (allMemberNames.has(fname)) {
            this.raiseError(this.getCurrentLine(), "Collision between static and other names");
        }
        allMemberNames.add(fname);

        staticFunctions.set(fname, new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), attributes, fname, sig));
    }

    private parseMemberField(memberFields: Map<string, MemberFieldDecl>, allMemberNames: Set<string>, attributes: string[], pragmas: [TypeSignature, string][]) {
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

        memberFields.set(fname, new MemberFieldDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, fname, stype, value));
    }

    private parseMemberMethod(thisType: TypeSignature, memberMethods: Map<string, MemberMethodDecl>, allMemberNames: Set<string>, attributes: string[], pragmas: [TypeSignature, string][]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] method NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        this.ensureAndConsumeToken("method");
        const termRestrictions = this.parseTermRestriction(true);

        this.ensureToken(TokenStrings.Identifier);
        const mname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        let recursive: "yes" | "no" | "cond" = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(false, true, Parser.attributeSetContains("abstract", attributes), attributes, recursive, pragmas, terms, termRestrictions, thisType);

        if (allMemberNames.has(mname)) {
            this.raiseError(this.getCurrentLine(), "Collision between static and other names");
        }
        allMemberNames.add(mname);

        memberMethods.set(mname, new MemberMethodDecl(sinfo, this.m_penv.getCurrentFile(), attributes, mname, sig));
    }

    private parseInvariantsInto(invs: InvariantDecl[]) {
        try {
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(["this"])));
            while (this.testToken("invariant") || this.testToken("check")) {
                const ischeck = this.testAndConsumeTokenIf("check");
                this.consumeToken();

                let level: BuildLevel = ischeck ? "release" : "debug";
                if (!ischeck) {
                    level = this.parseBuildInfo(level);
                }

                const sinfo = this.getCurrentSrcInfo();
                const exp = this.parseExpression();

                invs.push(new InvariantDecl(sinfo, level, exp));

                this.ensureAndConsumeToken(";");
            }
        } finally {
            this.m_penv.popFunctionScope();
        }
    }

    private parseOOPMembersCommon(thisType: TypeSignature, invariants: InvariantDecl[], staticMembers: Map<string, StaticMemberDecl>, staticFunctions: Map<string, StaticFunctionDecl>, memberFields: Map<string, MemberFieldDecl>, memberMethods: Map<string, MemberMethodDecl>) {
        this.parseInvariantsInto(invariants);

        let allMemberNames = new Set<string>();
        while (!this.testToken("}")) {
            const pragmas = this.parseDeclPragmas();
            const attributes = this.parseAttributes();

            if (this.testToken("const")) {
                this.parseConstMember(staticMembers, allMemberNames, attributes, pragmas);
            }
            else if (this.testToken("static")) {
                this.parseStaticFunction(staticFunctions, allMemberNames, attributes, pragmas);
            }
            else if (this.testToken("field")) {
                this.parseMemberField(memberFields, allMemberNames, attributes, pragmas);
            }
            else {
                this.ensureToken("method");

                this.parseMemberMethod(thisType, memberMethods, allMemberNames, attributes, pragmas);
            }
        }
    }

    private parseConcept(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();

        //[attr] concept NAME[T where C...] provides {...}
        const pragmas = this.parseDeclPragmas();
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

            const thisType = new NominalTypeSignature(currentDecl.ns, cname, terms.map((term) => new TemplateTypeSignature(term.name)));

            const invariants: InvariantDecl[] = [];
            const staticMembers = new Map<string, StaticMemberDecl>();
            const staticFunctions = new Map<string, StaticFunctionDecl>();
            const memberFields = new Map<string, MemberFieldDecl>();
            const memberMethods = new Map<string, MemberMethodDecl>();
            this.parseOOPMembersCommon(thisType, invariants, staticMembers, staticFunctions, memberFields, memberMethods);

            this.ensureAndConsumeToken("}");

            if (currentDecl.checkDeclNameClash(currentDecl.ns, cname)) {
                this.raiseError(line, "Collision between concept and other names");
            }

            this.clearRecover();
            currentDecl.concepts.set(cname, new ConceptTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, currentDecl.ns, cname, terms, provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods));
            this.m_penv.assembly.addConceptDecl(currentDecl.ns + "::" + cname, terms.length, currentDecl.concepts.get(cname) as ConceptTypeDecl);
        }
        catch (ex) {
            this.processRecover();
        }
    }

    private parseObject(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();

        //[attr] object NAME[T where C...] provides {...}
        const pragmas = this.parseDeclPragmas();
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("entity");
        this.ensureToken(TokenStrings.Type);

        const cname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        const provides = this.parseProvides(currentDecl.ns === "NSCore");

        try {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken("{");

            const thisType = new NominalTypeSignature(currentDecl.ns, cname, terms.map((term) => new TemplateTypeSignature(term.name)));

            const invariants: InvariantDecl[] = [];
            const staticMembers = new Map<string, StaticMemberDecl>();
            const staticFunctions = new Map<string, StaticFunctionDecl>();
            const memberFields = new Map<string, MemberFieldDecl>();
            const memberMethods = new Map<string, MemberMethodDecl>();
            this.parseOOPMembersCommon(thisType, invariants, staticMembers, staticFunctions, memberFields, memberMethods);

            this.ensureAndConsumeToken("}");

            if (currentDecl.checkDeclNameClash(currentDecl.ns, cname)) {
                this.raiseError(line, "Collision between object and other names");
            }

            this.clearRecover();
            currentDecl.objects.set(cname, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, currentDecl.ns, cname, terms, provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods));
            this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + cname, terms.length, currentDecl.objects.get(cname) as EntityTypeDecl);
        }
        catch (ex) {
            this.processRecover();
        }
    }

    private parseEnum(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();

        //[attr] enum NAME {...}
        const pragmas = this.parseDeclPragmas();
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("enum");
        this.ensureToken(TokenStrings.Type);

        const ename = this.consumeTokenAndGetValue();
        const etype = new NominalTypeSignature(currentDecl.ns, ename);
        const simpleETypeResult = etype;

        try {
            this.setRecover(this.scanCodeParens());

            const enums = this.parseListOf("{", "}", ",", () => {
                this.ensureToken(TokenStrings.Identifier);
                return this.consumeTokenAndGetValue();
            })[0];

            const param = new FunctionParameter("value", new NominalTypeSignature("NSCore", "Int"), false, false);
            const body = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "enum_create");
            const createdecl = new InvokeDecl(sinfo, this.m_penv.getCurrentFile(), [], "no", [], [], undefined, [param], undefined, undefined, simpleETypeResult, [], [], false, new Set<string>(), body);
            const create = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), ["private"], "create", createdecl);

            const provides = [[new NominalTypeSignature("NSCore", "Enum"), undefined], [new NominalTypeSignature("NSCore", "APIType"), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
            const invariants: InvariantDecl[] = [];
            const staticMembers = new Map<string, StaticMemberDecl>();
            const staticFunctions = new Map<string, StaticFunctionDecl>().set("create", create);
            const memberFields = new Map<string, MemberFieldDecl>();
            const memberMethods = new Map<string, MemberMethodDecl>();

            for(let i = 0; i < enums.length; ++i) {
                const enminit = new CallStaticFunctionExpression(sinfo, etype, "create", new TemplateArguments([]), new PragmaArguments("no", []), new Arguments([new PositionalArgument(false, false, new LiteralIntegerExpression(sinfo, i.toString()))]));
                const enm = new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), [], [], enums[i], etype, enminit);
                staticMembers.set(enums[i], enm);
            }

            if (currentDecl.checkDeclNameClash(currentDecl.ns, ename)) {
                this.raiseError(line, "Collision between object and other names");
            }

            this.clearRecover();
            currentDecl.objects.set(ename, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, currentDecl.ns, ename, [], provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods));
            this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + ename, 0, currentDecl.objects.get(ename) as EntityTypeDecl);
        }
        catch (ex) {
            this.processRecover();
        }
    }

    private parseIdentifier(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();

        //[attr] (hash) identifier NAME = 
        const pragmas = this.parseDeclPragmas();
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();
        const ishash = this.testAndConsumeTokenIf("hash");
        const isguid = this.testAndConsumeTokenIf("guid");
        const isclock = this.testAndConsumeTokenIf("clock");
        const iscomposite = this.testAndConsumeTokenIf("composite");
        if ((ishash ? 1 : 0) + (isguid ? 1 : 0) + (isclock ? 1 : 0) + (iscomposite ? 1 : 0) <= 1) {
            this.raiseError(sinfo.line, "Cannot have multiple of hashkey, GIUD, composite, or clock identifier");
        }

        this.ensureAndConsumeToken("identifier");

        this.ensureToken(TokenStrings.Type);
        const iname = this.consumeTokenAndGetValue();
        if (currentDecl.checkDeclNameClash(currentDecl.ns, iname)) {
            this.raiseError(line, "Collision between object and other names");
        }

        const itype = new NominalTypeSignature(currentDecl.ns, iname);
        const simpleITypeResult = itype;

        if(iscomposite) {
            this.ensureAndConsumeToken("=");
            const components = this.parseListOf("{", "}", ";", () => {
                this.ensureToken(TokenStrings.Identifier);
                const cname = this.consumeTokenAndGetValue();
                
                this.ensureAndConsumeToken(":");
                const ctype = this.parseTypeSignature();

                return {cname: cname, ctype: ctype};
            })[0];

            const consparams = components.map((cmp) => new FunctionParameter(cmp.cname, cmp.ctype, false, false));
            const body = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "compositekey_create");
            const createdecl = new InvokeDecl(sinfo, this.m_penv.getCurrentFile(), [], "no", [], [], undefined, consparams, undefined, undefined, simpleITypeResult, [], [], false, new Set<string>(), body);
            const create = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), [], "create", createdecl);

            let provides = [[new NominalTypeSignature("NSCore", "IdKey"), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];

            const rstrs = components.map((cmp) => new TemplateTypeRestriction(cmp.ctype, true, new NominalTypeSignature("NSCore", "APIType")));
            provides.push([new NominalTypeSignature("NSCore", "APIType"), new TypeConditionRestriction(rstrs)]);
                    
            const invariants: InvariantDecl[] = [];
            const staticMembers = new Map<string, StaticMemberDecl>();
            const staticFunctions = new Map<string, StaticFunctionDecl>().set("create", create);
            const memberFields = new Map<string, MemberFieldDecl>();
            const memberMethods = new Map<string, MemberMethodDecl>();

            currentDecl.objects.set(iname, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, currentDecl.ns, iname, [], provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods));
            this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + iname, 0, currentDecl.objects.get(iname) as EntityTypeDecl);
        }
        else {
            if (isguid) {
                this.ensureAndConsumeToken(";");

                const param = new FunctionParameter("value", new NominalTypeSignature("NSCore", "GUID"), false, false);
                const body = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "gidkey_create");
                const createdecl = new InvokeDecl(sinfo, this.m_penv.getCurrentFile(), [], "no", [], [], undefined, [param], undefined, undefined, simpleITypeResult, [], [], false, new Set<string>(), body);
                const create = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), [], "create", createdecl);

                const provides = [[new NominalTypeSignature("NSCore", "GUIDIdKey"), undefined], [new NominalTypeSignature("NSCore", "APIType"), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
            
                const invariants: InvariantDecl[] = [];
                const staticMembers = new Map<string, StaticMemberDecl>();
                const staticFunctions = new Map<string, StaticFunctionDecl>().set("create", create);
                const memberFields = new Map<string, MemberFieldDecl>();
                const memberMethods = new Map<string, MemberMethodDecl>();

                currentDecl.objects.set(iname, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, currentDecl.ns, iname, [], provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods));
                this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + iname, 0, currentDecl.objects.get(iname) as EntityTypeDecl);
            }
            else if (isclock) {
                this.ensureAndConsumeToken(";");

                const zerobody = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "time_zero");
                const zerodecl = new InvokeDecl(sinfo, this.m_penv.getCurrentFile(), [], "no", [], [], undefined, [], undefined, undefined, simpleITypeResult, [], [], false, new Set<string>(), zerobody);
                const zero = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), [], "zero", zerodecl);

                const param = new FunctionParameter("tick", itype, false, false);
                const body = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "time_nexttick");
                const tickdecl = new InvokeDecl(sinfo, this.m_penv.getCurrentFile(), [], "no", [], [], undefined, [param], undefined, undefined, simpleITypeResult, [], [], false, new Set<string>(), body);
                const nexttick = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), [], "tick", tickdecl);

                const provides = [[new NominalTypeSignature("NSCore", "LogicalTimeIdKey"), undefined], [new NominalTypeSignature("NSCore", "APIType"), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
            
                const invariants: InvariantDecl[] = [];
                const staticMembers = new Map<string, StaticMemberDecl>();
                const staticFunctions = new Map<string, StaticFunctionDecl>().set("zero", zero).set("tick", nexttick);
                const memberFields = new Map<string, MemberFieldDecl>();
                const memberMethods = new Map<string, MemberMethodDecl>();

                currentDecl.objects.set(iname, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, currentDecl.ns, iname, [], provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods));
                this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + iname, 0, currentDecl.objects.get(iname) as EntityTypeDecl);
            }
            else {
                this.ensureAndConsumeToken("=");
                const idval = this.parseTypeSignature();
                this.ensureAndConsumeToken(";");

                if (ishash) {
                    const param = new FunctionParameter("value", idval, false, false);
                    const body = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "hashkey_crypto_create");
                    const createdecl = new InvokeDecl(sinfo, this.m_penv.getCurrentFile(), [], "no", [], [], undefined, [param], undefined, undefined, simpleITypeResult, [], [], false, new Set<string>(), body);
                    const create = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), [], "create", createdecl);

                    let provides = [[new NominalTypeSignature("NSCore", "ContentHashIdKey"), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
                    provides.push([new NominalTypeSignature("NSCore", "APIType"), new TypeConditionRestriction([new TemplateTypeRestriction(idval, true, new NominalTypeSignature("NSCore", "APIType"))])]);
                    
                    const invariants: InvariantDecl[] = [];
                    const staticMembers = new Map<string, StaticMemberDecl>();
                    const staticFunctions = new Map<string, StaticFunctionDecl>().set("create", create);
                    const memberFields = new Map<string, MemberFieldDecl>();
                    const memberMethods = new Map<string, MemberMethodDecl>();

                    currentDecl.objects.set(iname, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, currentDecl.ns, iname, [], provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods));
                    this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + iname, 0, currentDecl.objects.get(iname) as EntityTypeDecl);
                }
                else {
                    const param = new FunctionParameter("value", idval, false, false);
                    const body = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "idkey_create");
                    const createdecl = new InvokeDecl(sinfo, this.m_penv.getCurrentFile(), [], "no", [], [], undefined, [param], undefined, undefined, simpleITypeResult, [], [], false, new Set<string>(), body);
                    const create = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), [], "create", createdecl);

                    let provides = [[new NominalTypeSignature("NSCore", "IdKey"), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
                    provides.push([new NominalTypeSignature("NSCore", "APIType"), new TypeConditionRestriction([new TemplateTypeRestriction(idval, true, new NominalTypeSignature("NSCore", "APIType"))])]);
                    
                    const invariants: InvariantDecl[] = [];
                    const staticMembers = new Map<string, StaticMemberDecl>();
                    const staticFunctions = new Map<string, StaticFunctionDecl>().set("create", create);
                    const memberFields = new Map<string, MemberFieldDecl>();
                    const memberMethods = new Map<string, MemberMethodDecl>();

                    currentDecl.objects.set(iname, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, currentDecl.ns, iname, [], provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods));
                    this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + iname, 0, currentDecl.objects.get(iname) as EntityTypeDecl);
                }
            }
        }
    }

    private parseNamespaceConst(currentDecl: NamespaceDeclaration) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] const NAME[: T] = exp;
        const pragmas = this.parseDeclPragmas();
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

        currentDecl.consts.set(gname, new NamespaceConstDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, currentDecl.ns, gname, gtype, value));
    }

    private parseNamespaceFunction(currentDecl: NamespaceDeclaration) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] function NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        const pragmas = this.parseDeclPragmas();
        const attributes = this.parseAttributes();

        this.ensureAndConsumeToken("function");
        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();

        const terms = this.parseTermDeclarations();
        let recursive: "yes" | "no" | "cond" = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(false, false, false, attributes, recursive, pragmas, terms, undefined);

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
                this.m_cpos = this.scanTokenOptions("function", "global", "typedef", "concept", "entity", "clock", "enum", "hash", "guid", "composite", "identifier");
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
                else if (this.testToken("typedef") || this.testToken("concept") || this.testToken("entity") || this.testToken("clock") || this.testToken("enum") || this.testToken("hash") || this.testToken("guid") || this.testToken("composite") || this.testToken("identifier")) {
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
            const rpos = this.scanTokenOptions("function", "global", "using", "typedef", "concept", "entity", "clock", "enum", "hash", "guid", "composite", "identifier", TokenStrings.EndOfStream);

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
                else if (tk === "enum") {
                    this.parseEnum(nsdecl);
                }
                else if (tk === "hash" || tk === "guid" || tk === "composite" || tk === "identifier" || tk === "clock") {
                    this.parseIdentifier(nsdecl);
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

export { SourceInfo, ParseError, Parser };
