"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const parser_env_1 = require("./parser_env");
const type_signature_1 = require("./type_signature");
const body_1 = require("./body");
const assembly_1 = require("./assembly");
const KeywordStrings = [
    "pragma",
    "struct",
    "hidden",
    "private",
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
    "function",
    "global",
    "identifier",
    "if",
    "invariant",
    "method",
    "namespace",
    "none",
    "ok",
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
    "typeis",
    "typeas",
    "typetry",
    "typedef",
    "validate",
    "let",
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
    "?->",
    "*",
    "/"
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : a.localeCompare(b); });
const RegexFollows = new Set([
    "_debug",
    "abort",
    "assert",
    "check",
    "else",
    "ensures",
    "invariant",
    "or",
    "release",
    "return",
    "requires",
    "test",
    "validate",
    "when",
    "yield",
    "[",
    "(",
    "{",
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
    ";",
    "||",
    "+",
    "?&",
    "?|",
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
const AttributeStrings = ["struct", "hidden", "private", "factory", "virtual", "abstract", "override", "entrypoint", "recursive", "recursive?"];
const SpecialInvokeNames = ["update", "merge", "project", "tryProject"];
const TokenStrings = {
    Clear: "[CLEAR]",
    Error: "[ERROR]",
    Int: "[LITERAL_INT]",
    BigInt: "[LITERAL_BIGINT]",
    Float: "[LITERAL_FLOAT]",
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
    constructor(line, column, cpos, span, kind, data) {
        this.line = line;
        this.column = column;
        this.pos = cpos;
        this.span = span;
        this.kind = kind;
        this.data = data;
    }
}
class SourceInfo {
    constructor(line, column, cpos, span) {
        this.line = line;
        this.column = column;
        this.pos = cpos;
        this.span = span;
    }
}
exports.SourceInfo = SourceInfo;
class Lexer {
    constructor(input) {
        this.m_input = input;
        this.m_internTable = new Map();
        this.m_cline = 1;
        this.m_linestart = 0;
        this.m_cpos = 0;
        this.m_tokens = [];
    }
    static findSymbolString(str) {
        return SymbolStrings.find((value) => str.startsWith(value));
    }
    static findKeywordString(str) {
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
    ////
    //Helpers
    static isNamespaceName(str) {
        return /^NS/.test(str);
    }
    static isTypenameName(str) {
        return str.length > 1 && !/^NS/.test(str) && /^[A-Z]/.test(str);
    }
    static isTemplateName(str) {
        return str.length === 1 && /^[A-Z]$/.test(str);
    }
    //TODO: we need to make sure that someone doesn't name a local variable _ -- also want to reserve _X_ for custom operators
    static isIdentifierName(str) {
        return /^([$]?([a-z]|[a-z][_a-zA-Z0-9]*[a-zA-Z0-9]))|[_]$/.test(str);
    }
    recordLexToken(epos, kind) {
        this.m_tokens.push(new Token(this.m_cline, this.m_cpos - this.m_linestart, this.m_cpos, epos - this.m_cpos, kind, kind)); //set data to kind string
        this.m_cpos = epos;
    }
    recordLexTokenWData(epos, kind, data) {
        const rdata = this.m_internTable.get(data) || this.m_internTable.set(data, data).get(data);
        this.m_tokens.push(new Token(this.m_cline, this.m_cpos - this.m_linestart, this.m_cpos, epos - this.m_cpos, kind, rdata));
        this.m_cpos = epos;
    }
    tryLexWS() {
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
    tryLexComment() {
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
            if (groups.multilineEndChar !== undefined && groups.multilineEndChar !== "/") {
                this.recordLexToken(this.m_cpos, TokenStrings.Error);
            }
        }
        this.m_cpos += m[0].length;
        return true;
    }
    tryLexNumber() {
        Lexer._s_floatRe.lastIndex = this.m_cpos;
        const mf = Lexer._s_floatRe.exec(this.m_input);
        if (mf !== null) {
            this.recordLexTokenWData(this.m_cpos + mf[0].length, TokenStrings.Float, mf[0]);
            return true;
        }
        Lexer._s_bigintRe.lastIndex = this.m_cpos;
        const mb = Lexer._s_bigintRe.exec(this.m_input);
        if (mb !== null) {
            this.recordLexTokenWData(this.m_cpos + mb[0].length, TokenStrings.Int, mb[0]);
            return true;
        }
        Lexer._s_intRe.lastIndex = this.m_cpos;
        const mi = Lexer._s_intRe.exec(this.m_input);
        if (mi !== null) {
            this.recordLexTokenWData(this.m_cpos + mi[0].length, TokenStrings.Int, mi[0]);
            return true;
        }
        return false;
    }
    tryLexString() {
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
    tryLexRegex() {
        Lexer._s_regexRe.lastIndex = this.m_cpos;
        const ms = Lexer._s_regexRe.exec(this.m_input);
        if (ms !== null && RegexFollows.has(this.m_tokens[this.m_tokens.length - 1].kind)) {
            this.recordLexTokenWData(this.m_cpos + ms[0].length, TokenStrings.Regex, ms[0]);
            return true;
        }
        return false;
    }
    tryLexSymbol() {
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
    tryLexName() {
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
    static isAttributeKW(str) {
        return AttributeStrings.indexOf(str) !== -1;
    }
    lex() {
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
Lexer._s_whitespaceRe = /\s+/y;
Lexer._s_commentRe = /(\/\/.*)|(\/\*[\s\S]*?\*\/)/y;
Lexer._s_intRe = /(0|[1-9][0-9]*)/y;
Lexer._s_bigintRe = /(0|[1-9][0-9]*)n/y;
Lexer._s_floatRe = /[0-9]+\.[0-9]+f/y;
Lexer._s_stringRe = /"[^"\\\r\n]*(?:\\(?:.|\r?\n)[^"\\\r\n]*)*"/y;
Lexer._s_typedStringRe = /'[^'\\\r\n]*(?:\\(?:.|\r?\n)[^'\\\r\n]*)*'/y;
Lexer._s_regexRe = /\/[^"\\\r\n]*(?:\\(?:.)[^"\\\r\n]*)*\//y;
Lexer._s_symbolRe = /\W+/y;
Lexer._s_nameRe = /([$]?\w+)|(recursive\?)/y;
class ParseError extends Error {
    constructor(line, message) {
        super(`Parse failure on line ${line} -- ${message}`);
        Object.setPrototypeOf(this, new.target.prototype);
    }
}
exports.ParseError = ParseError;
class Parser {
    constructor(assembly) {
        this.m_tokens = [];
        this.m_cpos = 0;
        this.m_epos = 0;
        this.m_penv = new parser_env_1.ParserEnvironment(assembly);
        this.m_errors = [];
        this.m_recoverStack = [];
    }
    initialize(toks) {
        this.m_tokens = toks;
        this.m_cpos = 0;
        this.m_epos = toks.length;
    }
    ////
    //Helpers
    static attributeSetContains(attr, attribs) {
        return attribs.indexOf(attr) !== -1;
    }
    getCurrentLine() {
        return this.m_tokens[this.m_cpos].line;
    }
    getCurrentSrcInfo() {
        const tk = this.m_tokens[this.m_cpos];
        return new SourceInfo(tk.line, 0, tk.pos, tk.span);
    }
    setRecover(pos) {
        this.m_recoverStack.push(pos);
    }
    clearRecover(pos) {
        this.m_recoverStack.pop();
    }
    processRecover() {
        this.m_cpos = this.m_recoverStack.pop();
    }
    raiseError(line, msg) {
        this.m_errors.push([this.m_penv.getCurrentFile(), line, msg]);
        throw new ParseError(line, msg);
    }
    scanMatchingParens(lp, rp) {
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
    scanCodeParens() {
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
    setNamespaceAndFile(ns, file) {
        this.m_penv.setNamespaceAndFile(ns, file);
    }
    peekToken(pos) {
        return this.m_tokens[this.m_cpos + (pos || 0)].kind;
    }
    peekTokenData(pos) {
        return this.m_tokens[this.m_cpos + (pos || 0)].data;
    }
    testToken(kind) {
        return (this.m_cpos !== this.m_epos) && this.m_tokens[this.m_cpos].kind === kind;
    }
    testFollows(...kinds) {
        for (let i = 0; i < kinds.length; ++i) {
            if (this.m_cpos + i === this.m_epos || this.m_tokens[this.m_cpos + i].kind !== kinds[i]) {
                return false;
            }
        }
        return true;
    }
    testFollowsFrom(pos, ...kinds) {
        for (let i = 0; i < kinds.length; ++i) {
            if (pos + i === this.m_epos || this.m_tokens[pos + i].kind !== kinds[i]) {
                return false;
            }
        }
        return true;
    }
    consumeToken() {
        this.m_cpos++;
    }
    consumeTokenIf(kind) {
        if (this.testToken(kind)) {
            this.consumeToken();
        }
    }
    testAndConsumeTokenIf(kind) {
        const test = this.testToken(kind);
        if (test) {
            this.consumeToken();
        }
        return test;
    }
    consumeTokenAndGetValue() {
        const td = this.m_tokens[this.m_cpos].data;
        this.consumeToken();
        return td;
    }
    ensureToken(kind) {
        if (!this.testToken(kind)) {
            const found = this.m_tokens[this.m_cpos].data || this.m_tokens[this.m_cpos].kind;
            this.raiseError(this.m_tokens[this.m_cpos].line, `Expected "${kind}" but found "${found}"`);
        }
    }
    ensureAndConsumeToken(kind) {
        this.ensureToken(kind);
        this.consumeToken();
    }
    ensureNotToken(kind) {
        if (this.testToken(kind)) {
            this.raiseError(this.m_tokens[this.m_cpos].line, `Token "${kind}" is not allowed`);
        }
    }
    scanToken(tok) {
        let pos = this.m_cpos;
        while (pos !== this.m_epos) {
            if (this.m_tokens[pos].kind === tok) {
                return pos;
            }
            pos++;
        }
        return this.m_epos;
    }
    scanTokenOptions(...toks) {
        let pos = this.m_cpos;
        while (pos !== this.m_epos) {
            if (toks.indexOf(this.m_tokens[pos].kind) !== -1) {
                return pos;
            }
            pos++;
        }
        return this.m_epos;
    }
    parseListOf(start, end, sep, fn, specialToken) {
        let specialFound = false;
        let result = [];
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
    parseEphemeralListOf(fn) {
        let result = [];
        while (true) {
            result.push(fn());
            if (!this.testAndConsumeTokenIf(",")) {
                break;
            }
        }
        return result;
    }
    parseBuildInfo(cb) {
        if (this.testToken("debug") || this.testToken("test") || this.testToken("release")) {
            return this.consumeTokenAndGetValue();
        }
        else {
            return cb;
        }
    }
    ////
    //Misc parsing
    parseInvokableCommon(ispcode, isMember, noBody, attributes, isrecursive, pragmas, terms, termRestrictions, optSelfType) {
        const sinfo = this.getCurrentSrcInfo();
        const srcFile = this.m_penv.getCurrentFile();
        const line = this.getCurrentLine();
        let fparams = [];
        if (isMember) {
            fparams.push(new type_signature_1.FunctionParameter("this", optSelfType, false, false));
        }
        let restName = undefined;
        let restType = undefined;
        let resultInfo = this.m_penv.SpecialAutoSignature;
        const params = this.parseListOf("(", ")", ",", () => {
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
                fparams.push(new type_signature_1.FunctionParameter(params[i][0], params[i][1], params[i][2], params[i][4]));
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
                if (!params.some((p) => p[4])) {
                    this.raiseError(line, "Cannot have void return unless on of the params is by-ref");
                }
                resultInfo = this.m_penv.SpecialNoneSignature; //void conversion
            }
        }
        const argNames = new Set([...(restName ? [restName] : []), ...fparams.map((param) => param.name)]);
        let preconds = [];
        let postconds = [];
        let body = undefined;
        let captured = new Set();
        if (noBody) {
            this.ensureAndConsumeToken(";");
        }
        else {
            if (ispcode) {
                this.ensureAndConsumeToken("=>");
            }
            else {
                [preconds, postconds] = this.parsePreAndPostConditions(sinfo, argNames, resultInfo);
            }
            const bodyid = `${srcFile}::${sinfo.pos}`;
            try {
                this.m_penv.pushFunctionScope(new parser_env_1.FunctionScope(argNames, resultInfo));
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
            return assembly_1.InvokeDecl.createPCodeInvokeDecl(sinfo, srcFile, attributes, isrecursive, fparams, restName, restType, resultInfo, captured, body);
        }
        else if (isMember) {
            return assembly_1.InvokeDecl.createMemberInvokeDecl(sinfo, srcFile, attributes, isrecursive, pragmas, terms, termRestrictions, fparams, restName, restType, resultInfo, preconds, postconds, body);
        }
        else {
            return assembly_1.InvokeDecl.createStaticInvokeDecl(sinfo, srcFile, attributes, isrecursive, pragmas, terms, termRestrictions, fparams, restName, restType, resultInfo, preconds, postconds, body);
        }
    }
    ////
    //Type parsing
    parseResultType(parensreq) {
        if (this.testAndConsumeTokenIf("(|")) {
            const decls = this.parseEphemeralListOf(() => {
                const tdecl = this.parseTypeSignature();
                return tdecl;
            });
            this.ensureAndConsumeToken("|)");
            return new type_signature_1.EphemeralListTypeSignature(decls);
        }
        else {
            if (parensreq) {
                return this.parseTypeSignature();
            }
            else {
                const decls = this.parseEphemeralListOf(() => {
                    const tdecl = this.parseTypeSignature();
                    return tdecl;
                });
                return decls.length === 1 ? decls[0] : new type_signature_1.EphemeralListTypeSignature(decls);
            }
        }
    }
    parseTypeSignature() {
        return this.parseOrCombinatorType();
    }
    parseOrCombinatorType() {
        const ltype = this.parsePostfixTypeReference();
        if (!this.testToken("|")) {
            return ltype;
        }
        else {
            this.consumeToken();
            return Parser.orOfTypeSignatures(ltype, this.parseOrCombinatorType());
        }
    }
    parsePostfixTypeReference() {
        let roottype = this.parseProjectType();
        while (this.testToken("?")) {
            roottype = this.parseNoneableType(roottype);
        }
        return roottype;
    }
    parseNoneableType(basetype) {
        this.ensureAndConsumeToken("?");
        return Parser.orOfTypeSignatures(basetype, this.m_penv.SpecialNoneSignature);
    }
    parseProjectType() {
        const ltype = this.parseAndCombinatorType();
        if (!this.testToken("!")) {
            return ltype;
        }
        else {
            this.consumeToken();
            const ptype = this.parseNominalType();
            return new type_signature_1.ProjectTypeSignature(ltype, ptype);
        }
    }
    parseAndCombinatorType() {
        const ltype = this.parseBaseTypeReference();
        if (!this.testToken("&")) {
            return ltype;
        }
        else {
            this.consumeToken();
            return Parser.andOfTypeSignatures(ltype, this.parseAndCombinatorType());
        }
    }
    parseBaseTypeReference() {
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
    parseTemplateTypeReference() {
        return new type_signature_1.TemplateTypeSignature(this.consumeTokenAndGetValue());
    }
    parseNominalType() {
        const line = this.getCurrentLine();
        let ns = undefined;
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
            return new type_signature_1.NominalTypeSignature(ns, tname);
        }
        else {
            let terms = [];
            try {
                this.setRecover(this.scanMatchingParens("<", ">"));
                terms = this.parseListOf("<", ">", ",", () => {
                    return this.parseTypeSignature();
                })[0];
                this.clearRecover();
                return new type_signature_1.NominalTypeSignature(ns, tname, terms);
            }
            catch (ex) {
                this.processRecover();
                return new type_signature_1.ParseErrorTypeSignature();
            }
        }
    }
    parseTupleType() {
        const line = this.getCurrentLine();
        let entries = [];
        try {
            this.setRecover(this.scanMatchingParens("[", "]"));
            entries = this.parseListOf("[", "]", ",", () => {
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
            return new type_signature_1.TupleTypeSignature(entries);
        }
        catch (ex) {
            this.processRecover();
            return new type_signature_1.ParseErrorTypeSignature();
        }
    }
    parseRecordType() {
        let entries = [];
        try {
            this.setRecover(this.scanMatchingParens("{", "}"));
            entries = this.parseListOf("{", "}", ",", () => {
                this.ensureToken(TokenStrings.Identifier);
                const name = this.consumeTokenAndGetValue();
                const isopt = this.testAndConsumeTokenIf("?");
                this.ensureAndConsumeToken(":");
                const rtype = this.parseTypeSignature();
                return [name, rtype, isopt];
            })[0];
            this.clearRecover();
            return new type_signature_1.RecordTypeSignature(entries);
        }
        catch (ex) {
            this.processRecover();
            return new type_signature_1.ParseErrorTypeSignature();
        }
    }
    parsePCodeType() {
        let recursive = "no";
        if (this.testAndConsumeTokenIf("recursive?")) {
            recursive = "cond";
        }
        if (this.testAndConsumeTokenIf("recursive")) {
            recursive = "yes";
        }
        this.ensureAndConsumeToken("fn");
        try {
            this.setRecover(this.scanMatchingParens("(", ")"));
            let fparams = [];
            let restName = undefined;
            let restType = undefined;
            const params = this.parseListOf("(", ")", ",", () => {
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
                    fparams.push(new type_signature_1.FunctionParameter(params[i][0], params[i][1], params[i][2], params[i][4]));
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
            return new type_signature_1.FunctionTypeSignature(recursive, fparams, restName, restType, resultInfo);
        }
        catch (ex) {
            this.processRecover();
            return new type_signature_1.ParseErrorTypeSignature();
        }
    }
    static orOfTypeSignatures(t1, t2) {
        const types = [
            ...((t1 instanceof type_signature_1.UnionTypeSignature) ? t1.types : [t1]),
            ...((t2 instanceof type_signature_1.UnionTypeSignature) ? t2.types : [t2]),
        ];
        return new type_signature_1.UnionTypeSignature(types);
    }
    static andOfTypeSignatures(t1, t2) {
        const types = [
            ...((t1 instanceof type_signature_1.IntersectionTypeSignature) ? t1.types : [t1]),
            ...((t2 instanceof type_signature_1.IntersectionTypeSignature) ? t2.types : [t2]),
        ];
        return new type_signature_1.IntersectionTypeSignature(types);
    }
    ////
    //Expression parsing
    parseArguments(lparen, rparen) {
        const argSrcInfo = this.getCurrentSrcInfo();
        let seenNames = new Set();
        let args = [];
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
                    args.push(new body_1.NamedArgument(isref, name, exp));
                }
                else {
                    const isSpread = this.testAndConsumeTokenIf("...");
                    const exp = this.parseExpression();
                    args.push(new body_1.PositionalArgument(isref, isSpread, exp));
                }
                if (this.testAndConsumeTokenIf(",")) {
                    this.ensureNotToken(rparen);
                }
                else {
                    this.ensureToken(rparen);
                }
            }
            this.clearRecover();
            return new body_1.Arguments(args);
        }
        catch (ex) {
            this.processRecover();
            return new body_1.Arguments([new body_1.PositionalArgument(false, false, new body_1.InvalidExpression(argSrcInfo))]);
        }
    }
    parseTemplateArguments() {
        try {
            this.setRecover(this.scanMatchingParens("<", ">"));
            let targs = [];
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
            return new body_1.TemplateArguments(targs);
        }
        catch (ex) {
            this.processRecover();
            return new body_1.TemplateArguments([]);
        }
    }
    parsePragmaArguments() {
        try {
            this.setRecover(this.scanMatchingParens("[", "]"));
            let pargs = [];
            let recursive = "no";
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
            return new body_1.PragmaArguments(recursive, pargs);
        }
        catch (ex) {
            this.processRecover();
            return new body_1.PragmaArguments("no", []);
        }
    }
    parseConstructorPrimary(otype) {
        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("@");
        const args = this.parseArguments("{", "}");
        return new body_1.ConstructorPrimaryExpression(sinfo, otype, args);
    }
    parseConstructorPrimaryWithFactory(otype) {
        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("@");
        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();
        const targs = this.testToken("<") ? this.parseTemplateArguments() : new body_1.TemplateArguments([]);
        const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new body_1.PragmaArguments("no", []);
        const args = this.parseArguments("(", ")");
        return new body_1.ConstructorPrimaryWithFactoryExpression(sinfo, otype, fname, pragmas, targs, args);
    }
    parsePCodeTerm() {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();
        const isrecursive = this.testAndConsumeTokenIf("recursive");
        this.ensureAndConsumeToken("fn");
        const sig = this.parseInvokableCommon(true, false, false, [], isrecursive ? "yes" : "no", [], [], undefined);
        const someAuto = sig.params.some((param) => param.type instanceof type_signature_1.AutoTypeSignature) || (sig.optRestType !== undefined && sig.optRestType instanceof type_signature_1.AutoTypeSignature) || (sig.resultType instanceof type_signature_1.AutoTypeSignature);
        const allAuto = sig.params.every((param) => param.type instanceof type_signature_1.AutoTypeSignature) && (sig.optRestType === undefined || sig.optRestType instanceof type_signature_1.AutoTypeSignature) && (sig.resultType instanceof type_signature_1.AutoTypeSignature);
        if (someAuto && !allAuto) {
            this.raiseError(line, "Cannot have mixed of auto propagated and explicit types on lambda arguments/return");
        }
        sig.captureSet.forEach((v) => {
            this.m_penv.getCurrentFunctionScope().useLocalVar(v);
        });
        return new body_1.ConstructorPCodeExpression(sinfo, allAuto, sig);
    }
    parsePrimaryExpression() {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();
        const tk = this.peekToken();
        if (tk === "none") {
            this.consumeToken();
            return new body_1.LiteralNoneExpression(sinfo);
        }
        else if (tk === "true" || tk === "false") {
            this.consumeToken();
            return new body_1.LiteralBoolExpression(sinfo, tk === "true");
        }
        else if (tk === TokenStrings.Int) {
            const istr = this.consumeTokenAndGetValue();
            return new body_1.LiteralIntegerExpression(sinfo, istr);
        }
        else if (tk === TokenStrings.BigInt) {
            const istr = this.consumeTokenAndGetValue();
            return new body_1.LiteralBigIntegerExpression(sinfo, istr);
        }
        else if (tk === TokenStrings.Float) {
            const fstr = this.consumeTokenAndGetValue();
            return new body_1.LiteralFloatExpression(sinfo, fstr);
        }
        else if (tk === TokenStrings.String) {
            const sstr = this.consumeTokenAndGetValue(); //keep in escaped format
            return new body_1.LiteralStringExpression(sinfo, sstr);
        }
        else if (tk === TokenStrings.Regex) {
            const restr = this.consumeTokenAndGetValue(); //keep in escaped format
            this.m_penv.assembly.addLiteralRegex(restr);
            return new body_1.LiteralRegexExpression(sinfo, restr);
        }
        else if (tk === "err" || tk === "ok") {
            this.consumeToken();
            this.ensureAndConsumeToken("(");
            const arg = this.parseExpression();
            this.ensureAndConsumeToken(")");
            return new body_1.ResultExpression(sinfo, this.m_penv.getCurrentFunctionScope().getReturnType(), tk, arg);
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
                    return new body_1.PCodeInvokeExpression(sinfo, istr, pragmas, args);
                }
                else if (this.testToken("(")) {
                    const args = this.parseArguments("(", ")");
                    return new body_1.PCodeInvokeExpression(sinfo, istr, new body_1.PragmaArguments("no", []), args);
                }
                else {
                    return new body_1.AccessVariableExpression(sinfo, istr);
                }
            }
            else {
                const targs = this.testToken("<") ? this.parseTemplateArguments() : new body_1.TemplateArguments([]);
                const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new body_1.PragmaArguments("no", []);
                const args = this.parseArguments("(", ")");
                return new body_1.CallNamespaceFunctionExpression(sinfo, ns, istr, targs, pragmas, args);
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
                return new body_1.InvalidExpression(sinfo);
            }
        }
        else if (this.testToken("[")) {
            const args = this.parseArguments("[", "]");
            return new body_1.ConstructorTupleExpression(sinfo, args);
        }
        else if (this.testToken("{")) {
            const args = this.parseArguments("{", "}");
            return new body_1.ConstructorRecordExpression(sinfo, args);
        }
        else if (this.testToken("(|")) {
            const args = this.parseArguments("(|", "|)");
            return new body_1.ConstructorEphemeralValueList(sinfo, args);
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Identifier)) {
            //it is a namespace access of some type
            const ns = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();
            if (!this.testToken("<") && !this.testToken("[") && !this.testToken("(")) {
                //just a constant access
                return new body_1.AccessNamespaceConstantExpression(sinfo, ns, name);
            }
            else {
                const targs = this.testToken("<") ? this.parseTemplateArguments() : new body_1.TemplateArguments([]);
                const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new body_1.PragmaArguments("no", []);
                const args = this.parseArguments("(", ")");
                return new body_1.CallNamespaceFunctionExpression(sinfo, ns, name, targs, pragmas, args);
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
                    return new body_1.AccessStaticFieldExpression(sinfo, ttype, name);
                }
                else {
                    const targs = this.testToken("<") ? this.parseTemplateArguments() : new body_1.TemplateArguments([]);
                    const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new body_1.PragmaArguments("no", []);
                    const args = this.parseArguments("(", ")");
                    return new body_1.CallStaticFunctionExpression(sinfo, ttype, name, targs, pragmas, args);
                }
            }
            else if (this.testToken(TokenStrings.TypedString) || this.testFollows("@", TokenStrings.TypedString)) {
                if (this.testAndConsumeTokenIf("@")) {
                    const sstr = this.consumeTokenAndGetValue(); //keep in escaped format
                    return new body_1.LiteralTypedStringConstructorExpression(sinfo, sstr, ttype);
                }
                else {
                    const sstr = this.consumeTokenAndGetValue(); //keep in escaped format
                    return new body_1.LiteralTypedStringExpression(sinfo, sstr, ttype);
                }
            }
            else if (this.testFollows("@", TokenStrings.Identifier)) {
                return this.parseConstructorPrimaryWithFactory(ttype);
            }
            else if (this.testFollows("@", "{")) {
                return this.parseConstructorPrimary(ttype);
            }
            else {
                this.raiseError(line, "Unknown token sequence in parsing expression");
                return new body_1.InvalidExpression(sinfo);
            }
        }
    }
    handleSpecialCaseMethods(sinfo, isElvis, specificResolve, name) {
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
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");
            return new body_1.PostfixProjectFromType(sinfo, isElvis, name === "tryProject", type);
        }
        else if (name === "update") {
            if (this.testFollows("(", TokenStrings.Int)) {
                const updates = this.parseListOf("(", ")", ",", () => {
                    this.ensureToken(TokenStrings.Int);
                    const idx = Number.parseInt(this.consumeTokenAndGetValue());
                    this.ensureAndConsumeToken("=");
                    const value = this.parseExpression();
                    return [idx, value];
                })[0].sort((a, b) => a[0] - b[0]);
                return new body_1.PostfixModifyWithIndecies(sinfo, isElvis, updates);
            }
            else if (this.testFollows("(", TokenStrings.Identifier)) {
                const updates = this.parseListOf("(", ")", ",", () => {
                    this.ensureToken(TokenStrings.Identifier);
                    const uname = this.consumeTokenAndGetValue();
                    this.ensureAndConsumeToken("=");
                    const value = this.parseExpression();
                    return [uname, value];
                })[0].sort((a, b) => a[0].localeCompare(b[0]));
                return new body_1.PostfixModifyWithNames(sinfo, isElvis, updates);
            }
            else {
                this.raiseError(line, "Expected list of property/field or tuple updates");
                return undefined;
            }
        }
        else if (name === "merge") {
            this.ensureAndConsumeToken("(");
            const update = this.parseExpression();
            this.ensureAndConsumeToken(")");
            return new body_1.PostfixStructuredExtend(sinfo, isElvis, update);
        }
        else {
            this.raiseError(line, "unknown special operation");
            return undefined;
        }
    }
    parsePostfixExpression() {
        const rootinfo = this.getCurrentSrcInfo();
        let rootexp = this.parsePrimaryExpression();
        let ops = [];
        while (true) {
            const sinfo = this.getCurrentSrcInfo();
            const tk = this.peekToken();
            if (tk === "." || tk === "?.") {
                const isElvis = this.testToken("?.");
                this.consumeToken();
                if (this.testToken(TokenStrings.Int)) {
                    const index = Number.parseInt(this.consumeTokenAndGetValue());
                    ops.push(new body_1.PostfixAccessFromIndex(sinfo, isElvis, index));
                }
                else if (this.testToken("[")) {
                    const indecies = this.parseListOf("[", "]", ",", () => {
                        this.ensureToken(TokenStrings.Int);
                        return Number.parseInt(this.consumeTokenAndGetValue());
                    })[0];
                    if (indecies.length === 0) {
                        this.raiseError(sinfo.line, "You must have at least one index when projecting");
                    }
                    ops.push(new body_1.PostfixProjectFromIndecies(sinfo, isElvis, false, indecies));
                }
                else if (this.testToken(TokenStrings.Identifier)) {
                    const name = this.consumeTokenAndGetValue();
                    ops.push(new body_1.PostfixAccessFromName(sinfo, isElvis, name));
                }
                else if (this.testToken("{")) {
                    const names = this.parseListOf("{", "}", ",", () => {
                        this.ensureToken(TokenStrings.Identifier);
                        return this.consumeTokenAndGetValue();
                    })[0].sort();
                    if (names.length === 0) {
                        this.raiseError(sinfo.line, "You must have at least one index when projecting");
                    }
                    ops.push(new body_1.PostfixProjectFromNames(sinfo, isElvis, false, names));
                }
                else {
                    this.ensureToken("(|");
                    if (this.testFollows("(|", TokenStrings.Int)) {
                        const indecies = this.parseListOf("(|", "|)", ",", () => {
                            this.ensureToken(TokenStrings.Int);
                            return Number.parseInt(this.consumeTokenAndGetValue());
                        })[0];
                        if (indecies.length <= 1) {
                            this.raiseError(sinfo.line, "You must have at least two indecies when projecting out a Ephemeral value pack (otherwise just access the index directly)");
                        }
                        ops.push(new body_1.PostfixProjectFromIndecies(sinfo, isElvis, true, indecies));
                    }
                    else {
                        const names = this.parseListOf("(|", "|)", ",", () => {
                            this.ensureToken(TokenStrings.Identifier);
                            return this.consumeTokenAndGetValue();
                        })[0].sort();
                        if (names.length <= 1) {
                            this.raiseError(sinfo.line, "You must have at least two names when projecting out a Ephemeral value pack (otherwise just access the property/field directly)");
                        }
                        ops.push(new body_1.PostfixProjectFromNames(sinfo, isElvis, true, names));
                    }
                }
            }
            else if (tk === "->" || tk === "?->") {
                const isElvis = this.testToken("?->");
                this.consumeToken();
                let specificResolve = undefined;
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
                    const terms = this.testToken("<") ? this.parseTemplateArguments() : new body_1.TemplateArguments([]);
                    const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new body_1.PragmaArguments("no", []);
                    const args = this.parseArguments("(", ")");
                    ops.push(new body_1.PostfixInvoke(sinfo, isElvis, specificResolve, name, terms, pragmas, args));
                }
            }
            else {
                if (ops.length === 0) {
                    return rootexp;
                }
                else {
                    return new body_1.PostfixOp(rootinfo, rootexp, ops);
                }
            }
        }
    }
    parseStatementExpression() {
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
    parsePrefixExpression() {
        const sinfo = this.getCurrentSrcInfo();
        if (this.testToken("+") || this.testToken("-") || this.testToken("!")) {
            const op = this.consumeTokenAndGetValue();
            return new body_1.PrefixOp(sinfo, op, this.parsePrefixExpression());
        }
        else {
            return this.parseStatementExpression();
        }
    }
    parseTailTypeOp() {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parsePrefixExpression();
        if (this.testToken("typeis") || this.testToken("typeas") || this.testToken("typetry")) {
            const op = this.consumeTokenAndGetValue();
            const tt = this.parseTypeSignature();
            return new body_1.TailTypeExpression(sinfo, exp, op, tt);
        }
        else {
            return exp;
        }
    }
    parseMultiplicativeExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseTailTypeOp();
        if (this.testToken("*") || this.testToken("/")) {
            const op = this.consumeTokenAndGetValue();
            return new body_1.BinOpExpression(sinfo, exp, op, this.parseMultiplicativeExpression());
        }
        else {
            return exp;
        }
    }
    parseAdditiveExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseMultiplicativeExpression();
        if (this.testToken("+") || this.testToken("-")) {
            const op = this.consumeTokenAndGetValue();
            return new body_1.BinOpExpression(sinfo, exp, op, this.parseAdditiveExpression());
        }
        else {
            return exp;
        }
    }
    parseRelationalExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseAdditiveExpression();
        if (this.testToken("==") || this.testToken("!=")) {
            const op = this.consumeTokenAndGetValue();
            return new body_1.BinEqExpression(sinfo, exp, op, this.parseRelationalExpression());
        }
        else if (this.testToken("<") || this.testToken(">") || this.testToken("<=") || this.testToken(">=")) {
            const op = this.consumeTokenAndGetValue();
            return new body_1.BinCmpExpression(sinfo, exp, op, this.parseRelationalExpression());
        }
        else {
            return exp;
        }
    }
    parseNonecheckExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseRelationalExpression();
        if (this.testAndConsumeTokenIf("?&")) {
            return new body_1.NonecheckExpression(sinfo, exp, this.parseNonecheckExpression());
        }
        else {
            return exp;
        }
    }
    parseCoalesceExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseNonecheckExpression();
        if (this.testAndConsumeTokenIf("?|")) {
            return new body_1.CoalesceExpression(sinfo, exp, this.parseCoalesceExpression());
        }
        else {
            return exp;
        }
    }
    parseImpliesExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseCoalesceExpression();
        if (this.testAndConsumeTokenIf("==>")) {
            return new body_1.BinLogicExpression(sinfo, exp, "==>", this.parseImpliesExpression());
        }
        else {
            return exp;
        }
    }
    parseAndExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseImpliesExpression();
        if (this.testAndConsumeTokenIf("&&")) {
            return new body_1.BinLogicExpression(sinfo, exp, "&&", this.parseAndExpression());
        }
        else {
            return exp;
        }
    }
    parseOrExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseAndExpression();
        if (this.testAndConsumeTokenIf("||")) {
            return new body_1.BinLogicExpression(sinfo, exp, "||", this.parseOrExpression());
        }
        else {
            return exp;
        }
    }
    parseMapEntryConstructorExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseOrExpression();
        if (this.testAndConsumeTokenIf("=>")) {
            return new body_1.MapEntryConstructorExpression(sinfo, exp, this.parseMapEntryConstructorExpression());
        }
        else {
            return exp;
        }
    }
    parseSelectExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const texp = this.parseMapEntryConstructorExpression();
        if (this.testAndConsumeTokenIf("?")) {
            const exp1 = this.parseMapEntryConstructorExpression();
            this.ensureAndConsumeToken(":");
            const exp2 = this.parseSelectExpression();
            return new body_1.SelectExpression(sinfo, texp, exp1, exp2);
        }
        else {
            return texp;
        }
    }
    parseExpOrExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const texp = this.parseSelectExpression();
        if (this.testAndConsumeTokenIf("or")) {
            if (!this.testToken("return") && !this.testToken("yield")) {
                this.raiseError(this.getCurrentLine(), "Expected 'return' or 'yield");
            }
            const action = this.consumeTokenAndGetValue();
            let value = undefined;
            let cond = undefined;
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
            return new body_1.ExpOrExpression(sinfo, texp, action, value, cond);
        }
        else {
            return texp;
        }
    }
    parseBlockStatementExpression() {
        const sinfo = this.getCurrentSrcInfo();
        this.m_penv.getCurrentFunctionScope().pushLocalScope();
        let stmts = [];
        try {
            this.setRecover(this.scanMatchingParens("{|", "|}"));
            this.consumeToken();
            while (!this.testAndConsumeTokenIf("|}")) {
                stmts.push(this.parseStatement());
            }
            this.m_penv.getCurrentFunctionScope().popLocalScope();
            this.clearRecover();
            return new body_1.BlockStatementExpression(sinfo, stmts);
        }
        catch (ex) {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
            this.processRecover();
            return new body_1.BlockStatementExpression(sinfo, [new body_1.InvalidStatement(sinfo)]);
        }
    }
    parseIfExpression() {
        const sinfo = this.getCurrentSrcInfo();
        let conds = [];
        this.ensureAndConsumeToken("if");
        this.ensureAndConsumeToken("(");
        const iftest = this.parseExpression();
        this.ensureAndConsumeToken(")");
        const ifbody = this.parseExpression();
        conds.push(new body_1.CondBranchEntry(iftest, ifbody));
        while (this.testAndConsumeTokenIf("elif")) {
            this.ensureAndConsumeToken("(");
            const eliftest = this.parseExpression();
            this.ensureAndConsumeToken(")");
            const elifbody = this.parseExpression();
            conds.push(new body_1.CondBranchEntry(eliftest, elifbody));
        }
        this.ensureAndConsumeToken("else");
        const elsebody = this.parseExpression();
        return new body_1.IfExpression(sinfo, new body_1.IfElse(conds, elsebody));
    }
    parseMatchExpression() {
        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("switch");
        this.ensureAndConsumeToken("(");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(")");
        let entries = [];
        this.ensureAndConsumeToken("{");
        while (this.testToken("type") || this.testToken("case")) {
            if (this.testToken("type")) {
                entries.push(this.parseMatchEntry(sinfo, true, () => this.parseExpression()));
            }
            else {
                entries.push(this.parseMatchEntry(sinfo, false, () => this.parseExpression()));
            }
        }
        this.ensureAndConsumeToken("}");
        return new body_1.MatchExpression(sinfo, mexp, entries);
    }
    parseExpression() {
        return this.parseExpOrExpression();
    }
    ////
    //Statement parsing
    parseStructuredAssignment(sinfo, vars, trequired, literalok, decls) {
        if (this.testToken("[")) {
            const assigns = this.parseListOf("[", "]", ",", () => {
                return this.parseStructuredAssignment(this.getCurrentSrcInfo(), vars, trequired, literalok, decls);
            })[0];
            return new body_1.TupleStructuredAssignment(assigns);
        }
        else if (this.testToken("{")) {
            const assigns = this.parseListOf("{", "}", ",", () => {
                this.ensureToken(TokenStrings.Identifier);
                const name = this.consumeTokenAndGetValue();
                this.ensureAndConsumeToken("=");
                const subg = this.parseStructuredAssignment(this.getCurrentSrcInfo(), vars, trequired, literalok, decls);
                return [name, subg];
            })[0];
            return new body_1.RecordStructuredAssignment(assigns);
        }
        else if (this.testToken("(|")) {
            const assigns = this.parseListOf("(|", "|)", ",", () => {
                return this.parseStructuredAssignment(this.getCurrentSrcInfo(), vars, trequired, literalok, decls);
            })[0];
            return new body_1.ValueListStructuredAssignment(assigns);
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Type) || this.testToken(TokenStrings.Type)) {
            const ttype = this.parseTypeSignature();
            if (this.testFollows("::", TokenStrings.Identifier)) {
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                if (this.testToken("<") || !this.testToken("[") || !this.testToken("(")) {
                    this.raiseError(sinfo.line, "Expected a static field expression");
                }
                if (!literalok) {
                    this.raiseError(sinfo.line, "Literal match is not allowed");
                }
                return new body_1.ConstValueStructuredAssignment(new body_1.AccessStaticFieldExpression(sinfo, ttype, name));
            }
            else if (this.testToken(TokenStrings.TypedString) || this.testFollows("@", TokenStrings.TypedString)) {
                if (!literalok) {
                    this.raiseError(sinfo.line, "Literal match is not allowed");
                }
                if (this.testAndConsumeTokenIf("@")) {
                    const sstr = this.consumeTokenAndGetValue(); //keep in escaped format
                    return new body_1.ConstValueStructuredAssignment(new body_1.LiteralTypedStringConstructorExpression(sinfo, sstr, ttype));
                }
                else {
                    const sstr = this.consumeTokenAndGetValue(); //keep in escaped format
                    return new body_1.ConstValueStructuredAssignment(new body_1.LiteralTypedStringExpression(sinfo, sstr, ttype));
                }
            }
            else if (this.testFollows("@", "{")) {
                this.ensureAndConsumeToken("@");
                const assigns = this.parseListOf("{", "}", ",", () => {
                    this.ensureToken(TokenStrings.Identifier);
                    const name = this.consumeTokenAndGetValue();
                    this.ensureAndConsumeToken("=");
                    const subg = this.parseStructuredAssignment(this.getCurrentSrcInfo(), vars, trequired, literalok, decls);
                    return [name, subg];
                })[0];
                return new body_1.NominalStructuredAssignment(ttype, assigns);
            }
            else {
                this.raiseError(sinfo.line, "Unknown token sequence in parsing expression");
                return new body_1.ConstValueStructuredAssignment(new body_1.InvalidExpression(sinfo));
            }
        }
        else {
            if (this.testToken("let") || this.testToken("var")) {
                if (vars !== undefined) {
                    this.raiseError(sinfo.line, "Cannot mix var decl before and inside structured assign");
                }
                const isConst = this.testToken("let");
                this.consumeToken();
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
                return new body_1.VariableDeclarationStructuredAssignment(isopt, name, isConst, itype);
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
                    return new body_1.IgnoreTermStructuredAssignment(isopt, itype);
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
                        if (vars === "let") {
                            return new body_1.VariableDeclarationStructuredAssignment(isopt, name, true, itype);
                        }
                        else {
                            return new body_1.VariableDeclarationStructuredAssignment(isopt, name, false, itype);
                        }
                    }
                    else {
                        if (!this.m_penv.getCurrentFunctionScope().isVarNameDefined(name)) {
                            this.raiseError(sinfo.line, "Variable is not defined in scope");
                        }
                        if (!(itype instanceof type_signature_1.AutoTypeSignature)) {
                            this.raiseError(sinfo.line, "Cannot redeclare type of variable on assignment");
                        }
                        return new body_1.VariableAssignmentStructuredAssignment(isopt, name);
                    }
                }
            }
            else {
                if (!literalok) {
                    this.raiseError(sinfo.line, "Literal match is not allowed");
                }
                if (this.testToken("+") || this.testToken("-")) {
                    const op = this.consumeTokenAndGetValue();
                    return new body_1.ConstValueStructuredAssignment(new body_1.PrefixOp(sinfo, op, this.parsePrimaryExpression()));
                }
                else {
                    return new body_1.ConstValueStructuredAssignment(this.parsePrimaryExpression());
                }
            }
        }
    }
    parseLineStatement() {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();
        const tk = this.peekToken();
        if (tk === ";") {
            this.consumeToken();
            return new body_1.EmptyStatement(sinfo);
        }
        else if (tk === "let" || tk === "var") {
            this.consumeToken();
            const isConst = tk === "let";
            if (this.testToken("[") || this.testToken("{") || this.testToken("(|") || this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Type) || this.testToken(TokenStrings.Type)) {
                let decls = new Set();
                const assign = this.parseStructuredAssignment(this.getCurrentSrcInfo(), isConst ? "let" : "var", false, false, decls);
                decls.forEach((dv) => {
                    if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(dv)) {
                        this.raiseError(line, "Variable name is already defined");
                    }
                    this.m_penv.getCurrentFunctionScope().defineLocalVar(dv);
                });
                this.ensureAndConsumeToken("=");
                const exp = this.parseExpression();
                this.ensureAndConsumeToken(";");
                return new body_1.StructuredVariableAssignmentStatement(sinfo, assign, exp);
            }
            else {
                let decls = new Set();
                const assigns = this.parseEphemeralListOf(() => {
                    return this.parseStructuredAssignment(this.getCurrentSrcInfo(), isConst ? "let" : "var", false, false, decls);
                });
                if (assigns.length === 0 || (assigns.length === 1 && !(assigns[0] instanceof body_1.VariableDeclarationStructuredAssignment))) {
                    this.raiseError(sinfo.line, "Vacuous variable declaration");
                }
                let vars = [];
                for (let i = 0; i < assigns.length; ++i) {
                    if (assigns[i] instanceof body_1.IgnoreTermStructuredAssignment) {
                        vars.push({ name: "_", vtype: assigns[i].termType });
                    }
                    else if (assigns[i] instanceof body_1.VariableDeclarationStructuredAssignment) {
                        const dv = assigns[i];
                        if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(dv.vname)) {
                            this.raiseError(line, "Variable name is already defined");
                        }
                        this.m_penv.getCurrentFunctionScope().defineLocalVar(dv.vname);
                        vars.push({ name: dv.vname, vtype: dv.vtype });
                    }
                    else {
                        this.raiseError(sinfo.line, "Cannot have structured multi-decls");
                    }
                }
                let exp = undefined;
                if (this.testAndConsumeTokenIf("=")) {
                    exp = this.parseEphemeralListOf(() => {
                        return this.parseExpression();
                    });
                }
                if ((exp === undefined && isConst)) {
                    this.raiseError(line, "Const variable declaration must include an assignment to the variable");
                }
                this.ensureAndConsumeToken(";");
                if (vars.length === 1) {
                    if (exp !== undefined && exp.length !== 1) {
                        this.raiseError(line, "Mismatch between variables declared and values provided");
                    }
                    const sexp = exp !== undefined ? exp[0] : undefined;
                    return new body_1.VariableDeclarationStatement(sinfo, vars[0].name, isConst, vars[0].vtype, sexp);
                }
                else {
                    if (exp !== undefined && exp.length !== vars.length) {
                        this.raiseError(line, "Mismatch between variables declared and values provided");
                    }
                    return new body_1.VariablePackDeclarationStatement(sinfo, isConst, vars, exp);
                }
            }
        }
        else if (tk === "[" || tk === "{" || tk === "(|") {
            let decls = new Set();
            const assign = this.parseStructuredAssignment(this.getCurrentSrcInfo(), undefined, false, false, decls);
            decls.forEach((dv) => {
                if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(dv)) {
                    this.raiseError(line, "Variable name is already defined");
                }
                this.m_penv.getCurrentFunctionScope().defineLocalVar(dv);
            });
            this.ensureAndConsumeToken("=");
            const exp = this.parseExpression();
            this.ensureAndConsumeToken(";");
            return new body_1.StructuredVariableAssignmentStatement(sinfo, assign, exp);
        }
        else if (tk === TokenStrings.Identifier) {
            let decls = new Set();
            const assigns = this.parseEphemeralListOf(() => {
                return this.parseStructuredAssignment(this.getCurrentSrcInfo(), undefined, false, false, decls);
            });
            if (assigns.length === 0 || (assigns.length === 1 && !(assigns[0] instanceof body_1.VariableAssignmentStructuredAssignment))) {
                this.raiseError(sinfo.line, "Vacuous variable assignment");
            }
            let vars = [];
            for (let i = 0; i < assigns.length; ++i) {
                if (assigns[i] instanceof body_1.IgnoreTermStructuredAssignment) {
                    vars.push("_");
                }
                else if (assigns[i] instanceof body_1.VariableAssignmentStructuredAssignment) {
                    const av = assigns[i];
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
            let exps = this.parseEphemeralListOf(() => {
                return this.parseExpression();
            });
            this.ensureAndConsumeToken(";");
            if (vars.length === 1) {
                if (exps.length !== 1) {
                    this.raiseError(line, "Mismatch between variables assigned and values provided");
                }
                return new body_1.VariableAssignmentStatement(sinfo, vars[0], exps[0]);
            }
            else {
                if (exps.length !== 1 || exps.length !== vars.length) {
                    this.raiseError(line, "Mismatch between variables declared and values provided");
                }
                return new body_1.VariablePackAssignmentStatement(sinfo, vars, exps);
            }
        }
        else if (tk === "return") {
            this.consumeToken();
            if (this.testAndConsumeTokenIf(";")) {
                return new body_1.ReturnStatement(sinfo, [new body_1.LiteralNoneExpression(sinfo)]);
            }
            else {
                const exps = this.parseEphemeralListOf(() => this.parseExpression());
                this.ensureAndConsumeToken(";");
                return new body_1.ReturnStatement(sinfo, exps);
            }
        }
        else if (tk === "yield") {
            this.consumeToken();
            const exps = this.parseEphemeralListOf(() => this.parseExpression());
            this.ensureAndConsumeToken(";");
            return new body_1.YieldStatement(sinfo, exps);
        }
        else if (tk === "abort") {
            this.consumeToken();
            this.ensureAndConsumeToken(";");
            return new body_1.AbortStatement(sinfo);
        }
        else if (tk === "assert") {
            this.consumeToken();
            let level = "debug";
            level = this.parseBuildInfo(level);
            const exp = this.parseExpression();
            this.ensureAndConsumeToken(";");
            return new body_1.AssertStatement(sinfo, exp, level);
        }
        else if (tk === "check") {
            this.consumeToken();
            const exp = this.parseExpression();
            this.ensureAndConsumeToken(";");
            return new body_1.CheckStatement(sinfo, exp);
        }
        else if (tk === "validate") {
            this.consumeToken();
            const exp = this.parseExpression();
            let err = new body_1.LiteralNoneExpression(sinfo);
            if (this.testAndConsumeTokenIf("or")) {
                this.ensureAndConsumeToken("return");
                err = this.parseExpression();
            }
            this.ensureAndConsumeToken(";");
            return new body_1.ValidateStatement(sinfo, exp, err);
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
            return new body_1.DebugStatement(sinfo, value);
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Identifier)) {
            //it is a namespace function call
            const ns = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();
            const targs = this.testToken("<") ? this.parseTemplateArguments() : new body_1.TemplateArguments([]);
            const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new body_1.PragmaArguments("no", []);
            const args = this.parseArguments("(", ")");
            return new body_1.NakedCallStatement(sinfo, new body_1.CallNamespaceFunctionExpression(sinfo, ns, name, targs, pragmas, args));
        }
        else {
            //we should find a type (nominal here) and it is a static invoke or a structured assign
            const ttype = this.parseTypeSignature();
            if (this.testFollows("@", "{")) {
                this.ensureAndConsumeToken("@");
                let decls = new Set();
                const assigns = this.parseListOf("{", "}", ",", () => {
                    this.ensureToken(TokenStrings.Identifier);
                    const name = this.consumeTokenAndGetValue();
                    this.ensureAndConsumeToken("=");
                    const subg = this.parseStructuredAssignment(this.getCurrentSrcInfo(), undefined, false, false, decls);
                    return [name, subg];
                })[0];
                const assign = new body_1.NominalStructuredAssignment(ttype, assigns);
                decls.forEach((dv) => {
                    if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(dv)) {
                        this.raiseError(line, "Variable name is already defined");
                    }
                    this.m_penv.getCurrentFunctionScope().defineLocalVar(dv);
                });
                this.ensureAndConsumeToken("=");
                const exp = this.parseExpression();
                this.ensureAndConsumeToken(";");
                return new body_1.StructuredVariableAssignmentStatement(sinfo, assign, exp);
            }
            else {
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                const targs = this.testToken("<") ? this.parseTemplateArguments() : new body_1.TemplateArguments([]);
                const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new body_1.PragmaArguments("no", []);
                const args = this.parseArguments("(", ")");
                return new body_1.NakedCallStatement(sinfo, new body_1.CallStaticFunctionExpression(sinfo, ttype, name, targs, pragmas, args));
            }
        }
    }
    parseBlockStatement() {
        const sinfo = this.getCurrentSrcInfo();
        this.m_penv.getCurrentFunctionScope().pushLocalScope();
        let stmts = [];
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
            return new body_1.BlockStatement(sinfo, stmts);
        }
        catch (ex) {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
            this.processRecover();
            return new body_1.BlockStatement(sinfo, [new body_1.InvalidStatement(sinfo)]);
        }
    }
    parseIfElseStatement() {
        const sinfo = this.getCurrentSrcInfo();
        let conds = [];
        this.ensureAndConsumeToken("if");
        this.ensureAndConsumeToken("(");
        const iftest = this.parseExpression();
        this.ensureAndConsumeToken(")");
        const ifbody = this.parseBlockStatement();
        conds.push(new body_1.CondBranchEntry(iftest, ifbody));
        while (this.testAndConsumeTokenIf("elif")) {
            this.ensureAndConsumeToken("(");
            const eliftest = this.parseExpression();
            this.ensureAndConsumeToken(")");
            const elifbody = this.parseBlockStatement();
            conds.push(new body_1.CondBranchEntry(eliftest, elifbody));
        }
        const elsebody = this.testAndConsumeTokenIf("else") ? this.parseBlockStatement() : undefined;
        return new body_1.IfElseStatement(sinfo, new body_1.IfElse(conds, elsebody));
    }
    parseMatchGuard(sinfo, istypematch) {
        if (this.testToken(TokenStrings.Identifier)) {
            const tv = this.consumeTokenAndGetValue();
            if (tv !== "_") {
                this.raiseError(sinfo.line, "Expected wildcard match");
            }
            return new body_1.WildcardMatchGuard();
        }
        let typecheck = undefined;
        let layoutcheck = undefined;
        let decls = new Set();
        if (istypematch) {
            typecheck = this.parseTypeSignature();
        }
        else {
            let varinfo = undefined;
            if (this.testToken("var") || this.testToken("let")) {
                if (this.testToken("var")) {
                    varinfo = "var";
                }
                this.consumeToken();
            }
            layoutcheck = this.parseStructuredAssignment(sinfo, varinfo, true, true, decls);
        }
        let whencheck = undefined;
        if (this.testAndConsumeTokenIf("when")) {
            whencheck = this.parseExpression();
        }
        if (istypematch) {
            return new body_1.TypeMatchGuard(typecheck, whencheck);
        }
        else {
            return new body_1.StructureMatchGuard(layoutcheck, decls, whencheck);
        }
    }
    parseMatchEntry(sinfo, istypematch, actionp) {
        this.consumeToken();
        const guard = this.parseMatchGuard(sinfo, istypematch);
        this.ensureAndConsumeToken("=>");
        const action = actionp();
        return new body_1.MatchEntry(guard, action);
    }
    parseMatchStatement() {
        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("switch");
        this.ensureAndConsumeToken("(");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(")");
        let entries = [];
        this.ensureAndConsumeToken("{");
        while (this.testToken("type") || this.testToken("case")) {
            if (this.testToken("type")) {
                entries.push(this.parseMatchEntry(sinfo, true, () => this.parseBlockStatement()));
            }
            else {
                entries.push(this.parseMatchEntry(sinfo, false, () => this.parseBlockStatement()));
            }
        }
        this.ensureAndConsumeToken("}");
        return new body_1.MatchStatement(sinfo, mexp, entries);
    }
    parseStatement() {
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
    parseBody(bodyid, file, pnames) {
        if (this.testToken("#")) {
            this.consumeToken();
            this.ensureToken(TokenStrings.Identifier);
            return new body_1.BodyImplementation(bodyid, file, this.consumeTokenAndGetValue());
        }
        else if (this.testToken("{")) {
            if (this.testFollows("{", TokenStrings.Identifier, "=") && !pnames.includes(this.peekTokenData(1))) {
                //This is ambigious with the record constructor {p=exp ...} and the statement block {x=exp; ...}
                //However it is illegal to set a variable before declaration -- only option is updating a ref parameter so we check that
                return new body_1.BodyImplementation(bodyid, file, this.parseExpression());
            }
            else {
                return new body_1.BodyImplementation(bodyid, file, this.parseBlockStatement());
            }
        }
        else {
            return new body_1.BodyImplementation(bodyid, file, this.parseExpression());
        }
    }
    ////
    //Decl parsing
    parseAttributes() {
        let attributes = [];
        while (Lexer.isAttributeKW(this.peekToken())) {
            attributes.push(this.consumeTokenAndGetValue());
        }
        return attributes;
    }
    parseDeclPragmas() {
        let pragmas = [];
        while (this.testToken("pragma")) {
            const ts = this.parseTypeSignature();
            this.ensureToken(TokenStrings.TypedString);
            const sl = this.consumeTokenAndGetValue();
            pragmas.push([ts, sl]);
        }
        return pragmas;
    }
    parseTermDeclarations() {
        let terms = [];
        if (this.testToken("<")) {
            terms = this.parseListOf("<", ">", ",", () => {
                this.ensureToken(TokenStrings.Template);
                const templatename = this.consumeTokenAndGetValue();
                const hasconstraint = this.testAndConsumeTokenIf("where");
                const tconstraint = hasconstraint ? this.parseTypeSignature() : this.m_penv.SpecialAnySignature;
                let defaulttype = undefined;
                let isinfer = false;
                if (this.testAndConsumeTokenIf("=")) {
                    if (this.testToken("?")) {
                        isinfer = true;
                    }
                    else {
                        defaulttype = this.parseTypeSignature();
                    }
                }
                return new assembly_1.TemplateTermDecl(templatename, tconstraint, isinfer, defaulttype);
            })[0];
        }
        return terms;
    }
    parseSingleTermRestriction() {
        this.ensureToken(TokenStrings.Template);
        const templatename = this.consumeTokenAndGetValue();
        const oftype = this.parseTypeSignature();
        return new assembly_1.TemplateTypeRestriction(new type_signature_1.TemplateTypeSignature(templatename), oftype);
    }
    parseTermRestrictionList() {
        const trl = this.parseSingleTermRestriction();
        if (this.testAndConsumeTokenIf("&&")) {
            const ands = this.parseTermRestrictionList();
            return [trl, ...ands];
        }
        else {
            return [trl];
        }
    }
    parseTermRestriction(parencheck) {
        if (parencheck && !this.testToken("{")) {
            return undefined;
        }
        this.testAndConsumeTokenIf("{");
        if (parencheck) {
            this.testAndConsumeTokenIf("when");
        }
        const trl = this.parseTermRestrictionList();
        if (parencheck) {
            this.ensureAndConsumeToken("}");
        }
        return new assembly_1.TypeConditionRestriction(trl);
    }
    parsePreAndPostConditions(sinfo, argnames, rtype) {
        let preconds = [];
        try {
            this.m_penv.pushFunctionScope(new parser_env_1.FunctionScope(new Set(argnames), rtype));
            while (this.testToken("requires") || this.testToken("validate")) {
                const isvalidate = this.testToken("validate");
                this.consumeToken();
                let level = isvalidate ? "release" : "debug";
                if (!isvalidate) {
                    level = this.parseBuildInfo(level);
                }
                const exp = this.parseSelectExpression(); //don't want to get the ExpOrExpression
                let err = undefined;
                if (isvalidate) {
                    err = new body_1.LiteralNoneExpression(sinfo);
                    if (this.testAndConsumeTokenIf("or")) {
                        this.ensureAndConsumeToken("return");
                        err = this.parseExpression();
                    }
                }
                preconds.push(new assembly_1.PreConditionDecl(sinfo, isvalidate, level, exp, err));
                this.ensureAndConsumeToken(";");
            }
        }
        finally {
            this.m_penv.popFunctionScope();
        }
        let postconds = [];
        try {
            this.m_penv.pushFunctionScope(new parser_env_1.FunctionScope(new Set(argnames).add("$return"), rtype));
            while (this.testToken("ensures")) {
                this.consumeToken();
                let level = "debug";
                level = this.parseBuildInfo(level);
                const exp = this.parseExpression();
                postconds.push(new assembly_1.PostConditionDecl(sinfo, level, exp));
                this.ensureAndConsumeToken(";");
            }
        }
        finally {
            this.m_penv.popFunctionScope();
        }
        return [preconds, postconds];
    }
    parseNamespaceUsing(currentDecl) {
        //import NS {...} ;
        this.ensureAndConsumeToken("import");
        this.ensureToken(TokenStrings.Namespace);
        const fromns = this.consumeTokenAndGetValue();
        const names = this.parseListOf("{", "}", ",", () => {
            return this.consumeTokenAndGetValue();
        })[0];
        this.ensureAndConsumeToken(";");
        if (currentDecl.checkUsingNameClash(names)) {
            this.raiseError(this.getCurrentLine(), "Collision between imported using names");
        }
        currentDecl.usings.push(new assembly_1.NamespaceUsing(fromns, names));
    }
    parseNamespaceTypedef(currentDecl) {
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
        if (this.testToken(TokenStrings.Regex)) {
            const vregex = this.consumeTokenAndGetValue();
            this.consumeToken();
            const validator = new assembly_1.StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), [], [], "vregex", new type_signature_1.NominalTypeSignature("NSCore", "Regex"), new body_1.LiteralRegexExpression(sinfo, vregex));
            const param = new type_signature_1.FunctionParameter("arg", new type_signature_1.NominalTypeSignature("NSCore", "String"), false, false);
            const acceptsbody = new body_1.BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "validator_accepts");
            const acceptsinvoke = new assembly_1.InvokeDecl(sinfo, this.m_penv.getCurrentFile(), [], "no", [], [], undefined, [param], undefined, undefined, new type_signature_1.NominalTypeSignature("NSCore", "Bool"), [], [], false, new Set(), acceptsbody);
            const accepts = new assembly_1.StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), [], "accepts", acceptsinvoke);
            const provides = [[new type_signature_1.NominalTypeSignature("NSCore", "Validator"), undefined]];
            const validatortype = new assembly_1.EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), [], [], currentDecl.ns, tyname, [], provides, [], new Map().set("vregex", validator), new Map().set("accepts", accepts), new Map(), new Map());
            currentDecl.objects.set(tyname, validatortype);
            this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + tyname, currentDecl.objects.get(tyname));
            this.m_penv.assembly.addValidatorRegex(currentDecl.ns + "::" + tyname, vregex);
        }
        else {
            const btype = this.parseTypeSignature();
            this.consumeToken();
            if (currentDecl.checkDeclNameClash(currentDecl.ns, tyname)) {
                this.raiseError(this.getCurrentLine(), "Collision between typedef and other names");
            }
            currentDecl.typeDefs.set(currentDecl.ns + "::" + tyname, new assembly_1.NamespaceTypedef(currentDecl.ns, tyname, terms, btype));
        }
    }
    parseProvides(iscorens) {
        let provides = [];
        if (this.testToken("provides")) {
            this.consumeToken();
            while (!this.testToken("{")) {
                this.consumeTokenIf(",");
                const pv = this.parseTypeSignature();
                let res = undefined;
                if (this.testAndConsumeTokenIf("when")) {
                    res = this.parseTermRestriction(false);
                }
                provides.push([pv, res]);
            }
        }
        if (!iscorens) {
            provides.push([new type_signature_1.NominalTypeSignature("NSCore", "Object"), undefined]);
        }
        return provides;
    }
    parseConstMember(staticMembers, allMemberNames, attributes, pragmas) {
        const sinfo = this.getCurrentSrcInfo();
        //[attr] const NAME[: T] = exp;
        this.ensureAndConsumeToken("const");
        this.ensureToken(TokenStrings.Identifier);
        const sname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const stype = this.parseTypeSignature();
        let value = undefined;
        if (!Parser.attributeSetContains("abstract", attributes)) {
            this.ensureAndConsumeToken("=");
            value = this.parseExpression();
        }
        this.ensureAndConsumeToken(";");
        if (allMemberNames.has(sname)) {
            this.raiseError(this.getCurrentLine(), "Collision between const and other names");
        }
        allMemberNames.add(sname);
        staticMembers.set(sname, new assembly_1.StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, sname, stype, value));
    }
    parseStaticFunction(staticFunctions, allMemberNames, attributes, pragmas) {
        const sinfo = this.getCurrentSrcInfo();
        //[attr] static NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        this.ensureAndConsumeToken("static");
        const termRestrictions = this.parseTermRestriction(true);
        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        let recursive = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(false, false, Parser.attributeSetContains("abstract", attributes), attributes, recursive, pragmas, terms, termRestrictions);
        if (allMemberNames.has(fname)) {
            this.raiseError(this.getCurrentLine(), "Collision between static and other names");
        }
        allMemberNames.add(fname);
        staticFunctions.set(fname, new assembly_1.StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), attributes, fname, sig));
    }
    parseMemberField(memberFields, allMemberNames, attributes, pragmas) {
        const sinfo = this.getCurrentSrcInfo();
        //[attr] field NAME[: T] = exp;
        this.ensureAndConsumeToken("field");
        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const stype = this.parseTypeSignature();
        let value = undefined;
        if (this.testAndConsumeTokenIf("=")) {
            value = this.parseExpression();
        }
        this.ensureAndConsumeToken(";");
        if (allMemberNames.has(fname)) {
            this.raiseError(this.getCurrentLine(), "Collision between const and other names");
        }
        memberFields.set(fname, new assembly_1.MemberFieldDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, fname, stype, value));
    }
    parseMemberMethod(thisType, memberMethods, allMemberNames, attributes, pragmas) {
        const sinfo = this.getCurrentSrcInfo();
        //[attr] method NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        this.ensureAndConsumeToken("method");
        const termRestrictions = this.parseTermRestriction(true);
        this.ensureToken(TokenStrings.Identifier);
        const mname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        let recursive = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(false, true, Parser.attributeSetContains("abstract", attributes), attributes, recursive, pragmas, terms, termRestrictions, thisType);
        if (allMemberNames.has(mname)) {
            this.raiseError(this.getCurrentLine(), "Collision between static and other names");
        }
        allMemberNames.add(mname);
        memberMethods.set(mname, new assembly_1.MemberMethodDecl(sinfo, this.m_penv.getCurrentFile(), attributes, mname, sig));
    }
    parseInvariantsInto(invs) {
        try {
            this.m_penv.pushFunctionScope(new parser_env_1.FunctionScope(new Set(["this"]), new type_signature_1.NominalTypeSignature("NSCore", "Bool")));
            while (this.testToken("invariant") || this.testToken("check")) {
                const ischeck = this.testAndConsumeTokenIf("check");
                this.consumeToken();
                let level = ischeck ? "release" : "debug";
                if (!ischeck) {
                    level = this.parseBuildInfo(level);
                }
                const sinfo = this.getCurrentSrcInfo();
                const exp = this.parseExpression();
                invs.push(new assembly_1.InvariantDecl(sinfo, level, exp));
                this.ensureAndConsumeToken(";");
            }
        }
        finally {
            this.m_penv.popFunctionScope();
        }
    }
    parseOOPMembersCommon(thisType, invariants, staticMembers, staticFunctions, memberFields, memberMethods) {
        this.parseInvariantsInto(invariants);
        let allMemberNames = new Set();
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
    parseConcept(currentDecl) {
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
            const thisType = new type_signature_1.NominalTypeSignature(currentDecl.ns, cname, terms.map((term) => new type_signature_1.TemplateTypeSignature(term.name)));
            const invariants = [];
            const staticMembers = new Map();
            const staticFunctions = new Map();
            const memberFields = new Map();
            const memberMethods = new Map();
            this.parseOOPMembersCommon(thisType, invariants, staticMembers, staticFunctions, memberFields, memberMethods);
            this.ensureAndConsumeToken("}");
            if (currentDecl.checkDeclNameClash(currentDecl.ns, cname)) {
                this.raiseError(line, "Collision between concept and other names");
            }
            this.clearRecover();
            currentDecl.concepts.set(cname, new assembly_1.ConceptTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, currentDecl.ns, cname, terms, provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods));
            this.m_penv.assembly.addConceptDecl(currentDecl.ns + "::" + cname, currentDecl.concepts.get(cname));
        }
        catch (ex) {
            this.processRecover();
        }
    }
    parseObject(currentDecl) {
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
            const thisType = new type_signature_1.NominalTypeSignature(currentDecl.ns, cname, terms.map((term) => new type_signature_1.TemplateTypeSignature(term.name)));
            const invariants = [];
            const staticMembers = new Map();
            const staticFunctions = new Map();
            const memberFields = new Map();
            const memberMethods = new Map();
            this.parseOOPMembersCommon(thisType, invariants, staticMembers, staticFunctions, memberFields, memberMethods);
            this.ensureAndConsumeToken("}");
            if (currentDecl.checkDeclNameClash(currentDecl.ns, cname)) {
                this.raiseError(line, "Collision between object and other names");
            }
            this.clearRecover();
            currentDecl.objects.set(cname, new assembly_1.EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, currentDecl.ns, cname, terms, provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods));
            this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + cname, currentDecl.objects.get(cname));
        }
        catch (ex) {
            this.processRecover();
        }
    }
    parseEnum(currentDecl) {
        const line = this.getCurrentLine();
        //[attr] enum NAME {...}
        const pragmas = this.parseDeclPragmas();
        const attributes = ["struct", ...this.parseAttributes()];
        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("enum");
        this.ensureToken(TokenStrings.Type);
        const ename = this.consumeTokenAndGetValue();
        const etype = new type_signature_1.NominalTypeSignature(currentDecl.ns, ename);
        const simpleETypeResult = etype;
        const tryParseResult = new type_signature_1.NominalTypeSignature("NSCore", "Result", [simpleETypeResult, new type_signature_1.NominalTypeSignature("NSCore", "String")]);
        try {
            this.setRecover(this.scanCodeParens());
            const enums = this.parseListOf("{", "}", ",", () => {
                this.ensureToken(TokenStrings.Identifier);
                return this.consumeTokenAndGetValue();
            })[0];
            const cparam = new type_signature_1.FunctionParameter("value", new type_signature_1.NominalTypeSignature("NSCore", "Int"), false, false);
            const cbody = new body_1.BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "enum_create");
            const createdecl = new assembly_1.InvokeDecl(sinfo, this.m_penv.getCurrentFile(), [], "no", [], [], undefined, [cparam], undefined, undefined, simpleETypeResult, [], [], false, new Set(), cbody);
            const create = new assembly_1.StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), ["private"], "create", createdecl);
            const tpparam = new type_signature_1.FunctionParameter("str", new type_signature_1.NominalTypeSignature("NSCore", "String"), false, false);
            const tpbody = new body_1.BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "enum_tryparse");
            const tryparsedecl = new assembly_1.InvokeDecl(sinfo, this.m_penv.getCurrentFile(), [], "no", [], [], undefined, [tpparam], undefined, undefined, tryParseResult, [], [], false, new Set(), tpbody);
            const tryparse = new assembly_1.StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), ["private"], "create", tryparsedecl);
            const provides = [[new type_signature_1.NominalTypeSignature("NSCore", "Enum"), undefined], [new type_signature_1.NominalTypeSignature("NSCore", "Parsable"), undefined], [new type_signature_1.NominalTypeSignature("NSCore", "APIType"), undefined]];
            const invariants = [];
            const staticMembers = new Map();
            const staticFunctions = new Map().set("create", create).set("tryParse", tryparse);
            const memberFields = new Map();
            const memberMethods = new Map();
            for (let i = 0; i < enums.length; ++i) {
                const enminit = new body_1.CallStaticFunctionExpression(sinfo, etype, "create", new body_1.TemplateArguments([]), new body_1.PragmaArguments("no", []), new body_1.Arguments([new body_1.PositionalArgument(false, false, new body_1.LiteralIntegerExpression(sinfo, i.toString()))]));
                const enm = new assembly_1.StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), [], [], enums[i], etype, enminit);
                staticMembers.set(enums[i], enm);
            }
            if (currentDecl.checkDeclNameClash(currentDecl.ns, ename)) {
                this.raiseError(line, "Collision between object and other names");
            }
            this.clearRecover();
            currentDecl.objects.set(ename, new assembly_1.EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, currentDecl.ns, ename, [], provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods));
            this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + ename, currentDecl.objects.get(ename));
        }
        catch (ex) {
            this.processRecover();
        }
    }
    parseIdentifier(currentDecl) {
        const line = this.getCurrentLine();
        //[attr] (hash) identifier NAME = 
        const pragmas = this.parseDeclPragmas();
        const attributes = ["struct", ...this.parseAttributes()];
        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("identifier");
        this.ensureToken(TokenStrings.Type);
        const iname = this.consumeTokenAndGetValue();
        if (currentDecl.checkDeclNameClash(currentDecl.ns, iname)) {
            this.raiseError(line, "Collision between object and other names");
        }
        const itype = new type_signature_1.NominalTypeSignature(currentDecl.ns, iname);
        const simpleITypeResult = itype;
        this.ensureAndConsumeToken("=");
        const idval = this.parseTypeSignature();
        this.ensureAndConsumeToken(";");
        if (idval instanceof type_signature_1.TupleTypeSignature || idval instanceof type_signature_1.RecordTypeSignature) {
            let components = [];
            if (idval instanceof type_signature_1.TupleTypeSignature) {
                if (idval.entries.some((te) => te[1])) {
                    this.raiseError(line, "Composite key Tuple cannot have optional entries");
                }
                components = idval.entries.map((te, i) => { return { cname: `entry_${i}`, ctype: te[0] }; });
            }
            else {
                if (idval.entries.some((re) => re[2])) {
                    this.raiseError(line, "Composite key Tuple cannot have optional entries");
                }
                components = idval.entries.map((re, i) => { return { cname: re[0], ctype: re[1] }; });
            }
            const consparams = components.map((cmp) => new type_signature_1.FunctionParameter(cmp.cname, cmp.ctype, false, false));
            const body = new body_1.BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "idkey_from");
            const createdecl = new assembly_1.InvokeDecl(sinfo, this.m_penv.getCurrentFile(), [], "no", [], [], undefined, consparams, undefined, undefined, simpleITypeResult, [], [], false, new Set(), body);
            const create = new assembly_1.StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), [], "create", createdecl);
            let provides = [[new type_signature_1.NominalTypeSignature("NSCore", "IdKey"), undefined]];
            const rstrs = components.map((cmp) => new assembly_1.TemplateTypeRestriction(cmp.ctype, new type_signature_1.NominalTypeSignature("NSCore", "APIType")));
            provides.push([new type_signature_1.NominalTypeSignature("NSCore", "APIType"), new assembly_1.TypeConditionRestriction(rstrs)]);
            const invariants = [];
            const staticMembers = new Map();
            const staticFunctions = new Map().set("create", create);
            const memberFields = new Map();
            const memberMethods = new Map();
            currentDecl.objects.set(iname, new assembly_1.EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, currentDecl.ns, iname, [], provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods));
            this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + iname, currentDecl.objects.get(iname));
        }
        else {
            const param = new type_signature_1.FunctionParameter("value", idval, false, false);
            const body = new body_1.BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "idkey_from");
            const createdecl = new assembly_1.InvokeDecl(sinfo, this.m_penv.getCurrentFile(), [], "no", [], [], undefined, [param], undefined, undefined, simpleITypeResult, [], [], false, new Set(), body);
            const create = new assembly_1.StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), [], "create", createdecl);
            let provides = [[new type_signature_1.NominalTypeSignature("NSCore", "IdKey"), undefined]];
            provides.push([new type_signature_1.NominalTypeSignature("NSCore", "APIType"), new assembly_1.TypeConditionRestriction([new assembly_1.TemplateTypeRestriction(idval, new type_signature_1.NominalTypeSignature("NSCore", "APIType"))])]);
            const invariants = [];
            const staticMembers = new Map();
            const staticFunctions = new Map().set("create", create);
            const memberFields = new Map();
            const memberMethods = new Map();
            currentDecl.objects.set(iname, new assembly_1.EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, currentDecl.ns, iname, [], provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods));
            this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + iname, currentDecl.objects.get(iname));
        }
    }
    parseNamespaceConst(currentDecl) {
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
        currentDecl.consts.set(gname, new assembly_1.NamespaceConstDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, currentDecl.ns, gname, gtype, value));
    }
    parseNamespaceFunction(currentDecl) {
        const sinfo = this.getCurrentSrcInfo();
        //[attr] function NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        const pragmas = this.parseDeclPragmas();
        const attributes = this.parseAttributes();
        this.ensureAndConsumeToken("function");
        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        let recursive = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(false, false, false, attributes, recursive, pragmas, terms, undefined);
        currentDecl.functions.set(fname, new assembly_1.NamespaceFunctionDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, fname, sig));
    }
    parseEndOfStream() {
        this.ensureAndConsumeToken(TokenStrings.EndOfStream);
    }
    ////
    //Public methods
    parseCompilationUnitPass1(file, contents) {
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
    parseCompilationUnitPass2(file, contents) {
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
            const rpos = this.scanTokenOptions("function", "global", "import", "typedef", "concept", "entity", "enum", "identifier", TokenStrings.EndOfStream);
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
                else if (tk === "identifier") {
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
    getParseErrors() {
        return this.m_errors.length !== 0 ? this.m_errors : undefined;
    }
}
exports.Parser = Parser;
//# sourceMappingURL=parser.js.map