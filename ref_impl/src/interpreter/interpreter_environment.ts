//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { Value, ValueOps } from "./value";
import { MIRAssembly } from "../compiler/mir_assembly";
import { MIROp, MIRBody, MIRBasicBlock } from "../compiler/mir_ops";

class RuntimeError extends Error {
    constructor() {
        super("Runtime Error");
        Object.setPrototypeOf(this, new.target.prototype);
    }
}

class InvariantError extends Error {
    constructor(ontype: string) {
        super("Invariant Error on type: " + ontype);
        Object.setPrototypeOf(this, new.target.prototype);
    }
}

class PrePostError extends Error {
    constructor(isPre: boolean) {
        super(`${isPre ? "Pre" : "Post"}-Condition Error`);
        Object.setPrototypeOf(this, new.target.prototype);
    }
}

class NotImplementedRuntimeError extends Error {
    constructor(action: string) {
        super("Not Implemented: " + action);
        Object.setPrototypeOf(this, new.target.prototype);
    }
}

function raiseRuntimeError() {
    throw new RuntimeError();
}

function raiseRuntimeErrorIf(cond: boolean) {
    if (cond) {
        raiseRuntimeError();
    }
}

class FunctionScope {
    private readonly m_file: string;
    private m_line: number;

    private readonly m_flow: Map<string, MIRBasicBlock>;
    private m_activeblock: MIRBasicBlock;
    private m_activeops: MIROp[];

    private m_lastJumpBlock: string;

    private readonly m_captured: Map<string, Value>;
    private readonly m_args: Map<string, Value>;
    private readonly m_locals: Map<string, Value>;
    private readonly m_tmpRegs: Map<number, Value>;

    constructor(args: Map<string, Value>, captured: Map<string, Value>, flow: Map<string, MIRBasicBlock>, file: string) {
        this.m_file = file;
        this.m_line = -1;

        this.m_flow = flow;
        this.m_activeblock = this.m_flow.get("entry") as MIRBasicBlock;
        this.m_activeops = this.m_activeblock.ops;

        this.m_lastJumpBlock = "[NO JUMP]";

        this.m_args = args;
        this.m_captured = captured;
        this.m_locals = new Map<string, Value>();
        this.m_tmpRegs = new Map<number, Value>();
    }

    setCurrentLine(line: number) {
        this.m_line = line;
    }

    getCallFrameInfo(): { file: string, line: number } {
        return { file: this.m_file, line: this.m_line };
    }

    lookupVar(name: string): Value {
        if (this.m_locals.has(name)) {
            return this.m_locals.get(name);
        }
        else if (this.m_args.has(name)) {
            return this.m_args.get(name);
        }
        else {
            return this.m_captured.get(name);
        }
    }

    lookupTmpReg(id: number): Value {
        return this.m_tmpRegs.get(id);
    }

    assignTmpReg(id: number, value: Value) {
        this.m_tmpRegs.set(id, value);
    }

    declareVar(name: string, value: Value) {
        this.m_locals.set(name, value);
    }

    assignVar(name: string, value: Value) {
        this.m_locals.set(name, value);
    }

    clearVar(name: string) {
        this.m_locals.delete(name);
    }

    getActiveBlock(): MIRBasicBlock {
        return this.m_activeblock;
    }

    getActiveOps(): MIROp[] {
        return this.m_activeops;
    }

    setActiveBlock(label: string) {
        this.m_activeblock = this.m_flow.get(label) as MIRBasicBlock;
        this.m_activeops = this.m_activeblock.ops;
    }

    getLastJumpSource(): string {
        return this.m_lastJumpBlock;
    }

    setLastJumpSource() {
        this.m_lastJumpBlock = this.m_activeblock.label;
    }

    stringify(): string {
        let args: string[] = [];
        this.m_args.forEach((v, k) => args.push(`${k} = ${ValueOps.diagnosticPrintValue(v)}`));

        let captured: string[] = [];
        this.m_captured.forEach((v, k) => captured.push(`${k} = ${ValueOps.diagnosticPrintValue(v)}`));

        let locals: string[] = [];
        this.m_locals.forEach((v, k) => locals.push(`${k} = ${ValueOps.diagnosticPrintValue(v)}`));

        let tmps: string[] = [];
        this.m_tmpRegs.forEach((v, k) => tmps.push(`${k} = ${ValueOps.diagnosticPrintValue(v)}`));

        const frame = {
            file: this.m_file,
            line: this.m_line,
            args: args,
            captured: captured,
            locals: locals,
            tmps: tmps
        };

        return JSON.stringify(frame);
    }
}

class Environment {
    readonly assembly: MIRAssembly;
    private m_scopes: FunctionScope[];
    private m_activeScope: FunctionScope | undefined;

    constructor(assembly: MIRAssembly) {
        this.assembly = assembly;
        this.m_scopes = [];
        this.m_activeScope = undefined;
    }

    getActiveScope(): FunctionScope {
        return this.m_activeScope as FunctionScope;
    }

    pushCallFrame(args: Map<string, Value>, captured: Map<string, Value>, mirbody: MIRBody, file: string) {
        this.m_scopes.push(new FunctionScope(args, captured, mirbody.body as Map<string, MIRBasicBlock>, file));
        this.m_activeScope = this.m_scopes[this.m_scopes.length - 1];
    }

    popCallFrame() {
        this.m_scopes.pop();
        this.m_activeScope = this.m_scopes.length > 0 ? this.m_scopes[this.m_scopes.length - 1] : undefined;
    }

    stringify(): string {
        return JSON.stringify(this.m_scopes.map((frame) => frame.stringify()));
    }
}

export {
    FunctionScope, Environment,
    RuntimeError, InvariantError, PrePostError, NotImplementedRuntimeError,
    raiseRuntimeError, raiseRuntimeErrorIf
};
