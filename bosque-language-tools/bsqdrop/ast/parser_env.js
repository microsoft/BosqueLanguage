"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const type_signature_1 = require("./type_signature");
class FunctionScope {
    constructor(args) {
        this.m_captured = new Set();
        this.m_args = args;
        this.m_locals = [];
    }
    pushLocalScope() {
        this.m_locals.push(new Set());
    }
    popLocalScope() {
        this.m_locals.pop();
    }
    isVarNameDefined(name) {
        if (this.m_locals.some((frame) => frame.has(name))) {
            return true;
        }
        return this.m_args.has(name) || this.m_captured.has(name);
    }
    defineLocalVar(name) {
        this.m_locals[this.m_locals.length - 1].add(name);
    }
    useLocalVar(name) {
        if (!this.isVarNameDefined(name)) {
            this.m_captured.add(name);
        }
    }
    getCaptureVars() {
        return this.m_captured;
    }
}
exports.FunctionScope = FunctionScope;
class ParserEnvironment {
    constructor(assembly) {
        this.m_currentFile = undefined;
        this.m_currentNamespace = undefined;
        this.assembly = assembly;
        this.m_functionScopes = [];
        this.SpecialAnySignature = new type_signature_1.NominalTypeSignature("NSCore", "Any", []);
        this.SpecialNoneSignature = new type_signature_1.NominalTypeSignature("NSCore", "None", []);
        this.SpecialAutoSignature = new type_signature_1.AutoTypeSignature();
    }
    getCurrentFunctionScope() {
        return this.m_functionScopes[this.m_functionScopes.length - 1];
    }
    pushFunctionScope(scope) {
        this.m_functionScopes.push(scope);
    }
    popFunctionScope() {
        return this.m_functionScopes.pop();
    }
    setNamespaceAndFile(ns, file) {
        this.m_currentFile = file;
        this.m_currentNamespace = ns;
    }
    getCurrentFile() {
        return this.m_currentFile;
    }
    getCurrentNamespace() {
        return this.m_currentNamespace;
    }
    tryResolveNamespace(ns, typename) {
        if (ns !== undefined) {
            return ns;
        }
        const coredecl = this.assembly.getNamespace("NSCore");
        if (coredecl.declaredNames.has("NSCore::" + typename)) {
            return "NSCore";
        }
        else {
            const nsdecl = this.assembly.getNamespace(this.m_currentNamespace);
            if (nsdecl.declaredNames.has(this.m_currentNamespace + "::" + typename)) {
                return this.m_currentNamespace;
            }
            else {
                const fromns = nsdecl.usings.find((nsuse) => nsuse.names.indexOf(typename) !== -1);
                return fromns !== undefined ? fromns.fromNamespace : undefined;
            }
        }
    }
}
exports.ParserEnvironment = ParserEnvironment;
//# sourceMappingURL=parser_env.js.map