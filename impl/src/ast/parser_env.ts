//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { Assembly, NamespaceOperatorDecl } from "./assembly";
import { NominalTypeSignature, TypeSignature, AutoTypeSignature } from "./type_signature";

class FunctionScope {
    private readonly m_rtype: TypeSignature;
    private m_captured: Set<string>;
    private readonly m_ispcode: boolean;
    private readonly m_args: Set<string>;
    private m_locals: { name: string, scopedname: string, isbinder: boolean }[][];

    constructor(args: Set<string>, rtype: TypeSignature, ispcode: boolean) {
        this.m_rtype = rtype;
        this.m_captured = new Set<string>();
        this.m_ispcode = ispcode;
        this.m_args = args;
        this.m_locals = [];
    }

    pushLocalScope() {
        this.m_locals.push([]);
    }

    popLocalScope() {
        this.m_locals.pop();
    }

    isPCodeEnv(): boolean {
        return this.m_ispcode;
    }

    isVarNameDefined(name: string): boolean {
        return this.m_args.has(name) || this.m_locals.some((frame) => frame.some((fr) => fr.name === name));
    }

    getScopedVarName(name: string): string {
        for (let i = this.m_locals.length - 1; i >= 0; --i) {
            const vinfo = this.m_locals[i].find((fr) => fr.name === name);
            if (vinfo !== undefined) {
                return vinfo.scopedname;
            }
        }

        return name;
    }

    defineLocalVar(name: string, scopedname: string, isbinder: boolean) {
        this.m_locals[this.m_locals.length - 1].push({ name: name, scopedname: scopedname, isbinder: isbinder });
    }

    getCaptureVars(): Set<string> {
        return this.m_captured;
    }

    getReturnType(): TypeSignature {
        return this.m_rtype;
    }
}

class ParserEnvironment {
    private m_currentFile: string | undefined;
    private m_currentNamespace: string | undefined;

    private m_functionScopes: FunctionScope[];

    readonly assembly: Assembly;

    readonly SpecialAnySignature: TypeSignature;
    readonly SpecialSomeSignature: TypeSignature;
    readonly SpecialNoneSignature: TypeSignature;
    readonly SpecialBoolSignature: TypeSignature;
    
    readonly SpecialIntSignature: TypeSignature;
    readonly SpecialNatSignature: TypeSignature;
    readonly SpecialFloatSignature: TypeSignature;
    readonly SpecialDecimalSignature: TypeSignature;
    readonly SpecialBigIntSignature: TypeSignature;
    readonly SpecialBigNatSignature: TypeSignature;
    readonly SpecialRationalSignature: TypeSignature;
    readonly SpecialStringSignature: TypeSignature;

    readonly SpecialAutoSignature: TypeSignature;

    constructor(assembly: Assembly) {
        this.m_currentFile = undefined;
        this.m_currentNamespace = undefined;

        this.assembly = assembly;

        this.m_functionScopes = [];

        this.SpecialAnySignature = new NominalTypeSignature("Core", ["Any"], []);
        this.SpecialSomeSignature = new NominalTypeSignature("Core", ["Some"], []);
        this.SpecialNoneSignature = new NominalTypeSignature("Core", ["None"], []);
        this.SpecialBoolSignature = new NominalTypeSignature("Core", ["Bool"], []);

        this.SpecialIntSignature = new NominalTypeSignature("Core", ["Int"], []);
        this.SpecialNatSignature = new NominalTypeSignature("Core", ["Nat"], []);
        this.SpecialFloatSignature = new NominalTypeSignature("Core", ["Float"], []);
        this.SpecialDecimalSignature = new NominalTypeSignature("Core", ["Decimal"], []);
        this.SpecialBigIntSignature = new NominalTypeSignature("Core", ["BigInt"], []);
        this.SpecialBigNatSignature = new NominalTypeSignature("Core", ["BigNat"], []);
        this.SpecialRationalSignature = new NominalTypeSignature("Core", ["Rational"], []);
        this.SpecialStringSignature = new NominalTypeSignature("Core", ["String"], []);
        
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

    isVarDefinedInAnyScope(name: string): boolean {
        return this.m_functionScopes.some((sc) => sc.isVarNameDefined(name));
    }

    useLocalVar(name: string): string {
        const cscope = this.getCurrentFunctionScope();

        if(name.startsWith("$")) {
            for(let i = this.m_functionScopes.length - 1; i >= 0; --i) {
                if(this.m_functionScopes[i].isVarNameDefined(name)) {
                    name = this.m_functionScopes[i].getScopedVarName(name);
                    break;
                }
            }
        }

        if (!cscope.isVarNameDefined(name) && cscope.isPCodeEnv()) {
            cscope.getCaptureVars().add(name);
        }
        
        return name;
    }

    tryResolveNamespace(ns: string | undefined, typename: string): string | undefined {
        if (ns !== undefined) {
            return ns;
        }

        const coredecl = this.assembly.getNamespace("Core");
        if (coredecl.declaredNames.has("Core::" + typename)) {
            return "Core";
        }
        else {
            const nsdecl = this.assembly.getNamespace(this.m_currentNamespace as string);
            if (nsdecl.declaredNames.has(this.m_currentNamespace + "::" + typename)) {
                return this.m_currentNamespace as string;
            }
            else {
                const fromns = nsdecl.usings.find((nsuse) => nsuse.names.indexOf(typename) !== -1);
                return fromns !== undefined ? fromns.fromns : undefined;
            }
        }
    }

    tryResolveAsPrefixUnaryOperator(opname: string, level: number): string | undefined {
        const nsdecl = this.assembly.getNamespace(this.m_currentNamespace as string);
        if (nsdecl.declaredNames.has(this.m_currentNamespace + "::" + opname) && nsdecl.operators.get(opname) !== undefined) {
            const opdecls = nsdecl.operators.get(opname) as NamespaceOperatorDecl[];
            return opdecls.some((opdecl) => (opdecl.isPrefix && opdecl.level === level)) ? this.m_currentNamespace as string : undefined;
        }

        const nsmaindecl = this.assembly.getNamespace("Core");
        if (nsmaindecl.declaredNames.has("Core::" + opname) && nsmaindecl.operators.get(opname) !== undefined) {
            const opdecls = nsmaindecl.operators.get(opname) as NamespaceOperatorDecl[];
            return opdecls.some((opdecl) => (opdecl.isPrefix && opdecl.level === level)) ? "Core" : undefined;
        }

        const fromns = nsdecl.usings.find((nsuse) => nsuse.names.indexOf(opname) !== -1);
        return fromns !== undefined ? fromns.fromns : undefined;
    }

    tryResolveAsInfixBinaryOperator(opname: string, level: number): string | undefined {
        const nsdecl = this.assembly.getNamespace(this.m_currentNamespace as string);
        if (nsdecl.declaredNames.has(this.m_currentNamespace + "::" + opname) && nsdecl.operators.get(opname) !== undefined) {
            const opdecls = nsdecl.operators.get(opname) as NamespaceOperatorDecl[];
            return opdecls.some((opdecl) => (opdecl.isInfix && opdecl.level === level)) ? this.m_currentNamespace as string : undefined;
        }

        const nsmaindecl = this.assembly.getNamespace("Core");
        if (nsmaindecl.declaredNames.has("Core::" + opname) && nsmaindecl.operators.get(opname) !== undefined) {
            const opdecls = nsmaindecl.operators.get(opname) as NamespaceOperatorDecl[];
            return opdecls.some((opdecl) => (opdecl.isInfix && opdecl.level === level)) ? "Core" : undefined;
        }
        
        const fromns = nsdecl.usings.find((nsuse) => nsuse.names.indexOf(opname) !== -1);
        return fromns !== undefined ? fromns.fromns : undefined;
    }
}

export { FunctionScope, ParserEnvironment };
