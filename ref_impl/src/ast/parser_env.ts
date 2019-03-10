//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { Assembly } from "./assembly";
import { NominalTypeSignature, TypeSignature, AutoTypeSignature } from "./type_signature";

class FunctionScope {
    private m_captured: Set<string>;
    private readonly m_args: Set<string>;
    private m_locals: Set<string>[];

    constructor(args: Set<string>) {
        this.m_captured = new Set<string>();
        this.m_args = args;
        this.m_locals = [];
    }

    pushLocalScope() {
        this.m_locals.push(new Set<string>());
    }

    popLocalScope() {
        this.m_locals.pop();
    }

    isVarNameDefined(name: string): boolean {
        if (this.m_locals.some((frame) => frame.has(name))) {
            return true;
        }

        return this.m_args.has(name) || this.m_captured.has(name);
    }

    defineLocalVar(name: string) {
        this.m_locals[this.m_locals.length - 1].add(name);
    }

    useLocalVar(name: string) {
        if (!this.isVarNameDefined(name)) {
            this.m_captured.add(name);
        }
    }

    getCaptureVars(): Set<string> {
        return this.m_captured;
    }
}

class ParserEnvironment {
    private m_currentFile: string | undefined;
    private m_currentNamespace: string | undefined;

    private m_functionScopes: FunctionScope[];

    readonly assembly: Assembly;

    readonly SpecialAnySignature: TypeSignature;
    readonly SpecialNoneSignature: TypeSignature;
    readonly SpecialAutoSignature: TypeSignature;

    constructor(assembly: Assembly) {
        this.m_currentFile = undefined;
        this.m_currentNamespace = undefined;

        this.assembly = assembly;

        this.m_functionScopes = [];

        this.SpecialAnySignature = new NominalTypeSignature("NSCore", "Any", []);
        this.SpecialNoneSignature = new NominalTypeSignature("NSCore", "None", []);
        this.SpecialAutoSignature = new AutoTypeSignature();
    }

    getCurrentFunctionScope(): FunctionScope {
        return this.m_functionScopes[this.m_functionScopes.length - 1];
    }

    pushFunctionScope(scope: FunctionScope) {
        this.m_functionScopes.push(scope);
    }

    popFunctionScope(): FunctionScope {
        return this.m_functionScopes.pop() as FunctionScope;
    }

    setNamespaceAndFile(ns: string, file: string) {
        this.m_currentFile = file;
        this.m_currentNamespace = ns;
    }

    getCurrentFile(): string {
        return this.m_currentFile as string;
    }

    getCurrentNamespace(): string {
        return this.m_currentNamespace as string;
    }

    tryResolveNamespace(ns: string | undefined, typename: string): string | undefined {
        if (ns !== undefined) {
            return ns;
        }

        const coredecl = this.assembly.getNamespace("NSCore");
        if (coredecl.declaredNames.has("NSCore::" + typename)) {
            return "NSCore";
        }
        else {
            const nsdecl = this.assembly.getNamespace(this.m_currentNamespace as string);
            if (nsdecl.declaredNames.has(this.m_currentNamespace + "::" + typename)) {
                return this.m_currentNamespace as string;
            }
            else {
                const fromns = nsdecl.usings.find((nsuse) => nsuse.names.indexOf(typename) !== -1);
                return fromns !== undefined ? fromns.fromNamespace : undefined;
            }
        }
    }
}

export { FunctionScope, ParserEnvironment };
