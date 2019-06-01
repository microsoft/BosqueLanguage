//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import assert = require("assert");

import { Assembly } from "../ast/assembly";
import { ResolvedType } from "../ast/resolved_type";
import { MIRTempRegister } from "../compiler/mir_ops";

enum FlowTypeTruthValue {
    True = "True",
    False = "False",
    Unknown = "Unknown"
}

class FlowTypeTruthOps {
    static equal(e1: FlowTypeTruthValue, e2: FlowTypeTruthValue): boolean {
        return e1 === e2;
    }

    static subvalue(e1: FlowTypeTruthValue, e2: FlowTypeTruthValue): boolean {
        return e2 === FlowTypeTruthOps.join(e1, e2);
    }

    static join(...values: FlowTypeTruthValue[]): FlowTypeTruthValue {
        if (values.length === 0) {
            return FlowTypeTruthValue.Unknown;
        }

        const hasunknown = values.indexOf(FlowTypeTruthValue.Unknown) !== -1;
        const hastrue = values.indexOf(FlowTypeTruthValue.True) !== -1;
        const hasfalse = values.indexOf(FlowTypeTruthValue.False) !== -1;

        if (hasunknown || (hastrue && hasfalse)) {
            return FlowTypeTruthValue.Unknown;
        }
        else {
            return hastrue ? FlowTypeTruthValue.True : FlowTypeTruthValue.False;
        }
    }

    static maybeTrueValue(e: FlowTypeTruthValue): boolean {
        return (e === FlowTypeTruthValue.True || e === FlowTypeTruthValue.Unknown);
    }

    static maybeFalseValue(e: FlowTypeTruthValue): boolean {
        return (e === FlowTypeTruthValue.False || e === FlowTypeTruthValue.Unknown);
    }
}

class VarInfo {
    readonly declaredType: ResolvedType;
    readonly isConst: boolean;
    readonly mustDefined: boolean;
    readonly flowType: ResolvedType;

    constructor(dtype: ResolvedType, isConst: boolean, mustDefined: boolean, ftype: ResolvedType) {
        this.declaredType = dtype;
        this.flowType = ftype;
        this.isConst = isConst;
        this.mustDefined = mustDefined;
    }

    assign(ftype: ResolvedType): VarInfo {
        assert(!this.isConst);
        return new VarInfo(this.declaredType, this.isConst, true, ftype);
    }

    infer(ftype: ResolvedType): VarInfo {
        return new VarInfo(this.declaredType, this.isConst, true, ftype);
    }

    static join(assembly: Assembly, ...values: VarInfo[]): VarInfo {
        assert(values.length !== 0);
        return new VarInfo(values[0].declaredType, values[0].isConst, values.every((vi) => vi.mustDefined), assembly.typeUnion(values.map((vi) => vi.flowType)));
    }
}

type ExpressionReturnResult = {
    etype: ResolvedType,
    value: FlowTypeTruthValue
};

class TypeEnvironment {
    readonly terms: Map<string, ResolvedType>;

    readonly args: Map<string, VarInfo> | undefined;
    readonly captured: Map<string, VarInfo> | undefined;
    readonly locals: Map<string, VarInfo>[] | undefined;

    readonly expressionResult: ExpressionReturnResult | undefined;
    readonly returnResult: ResolvedType | undefined;
    readonly yieldResult: ResolvedType | undefined;

    readonly yieldTrgtInfo: MIRTempRegister[];

    readonly frozenVars: Set<string>;

    private constructor(terms: Map<string, ResolvedType>,
        args: Map<string, VarInfo> | undefined, captured: Map<string, VarInfo> | undefined, locals: Map<string, VarInfo>[] | undefined,
        expressionResult: ExpressionReturnResult | undefined, rflow: ResolvedType | undefined, yflow: ResolvedType | undefined,
        yieldTrgtInfo: MIRTempRegister[], frozenVars: Set<string>) {
        this.terms = terms;

        this.args = args;
        this.captured = captured;
        this.locals = locals;

        this.expressionResult = expressionResult;
        this.returnResult = rflow;
        this.yieldResult = yflow;

        this.yieldTrgtInfo = yieldTrgtInfo;

        this.frozenVars = frozenVars;
    }

    private updateVarInfo(name: string, nv: VarInfo): TypeEnvironment {
        if (this.getLocalVarInfo(name) !== undefined) {
            let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => frame.has(name) ? new Map<string, VarInfo>(frame).set(name, nv) : new Map<string, VarInfo>(frame));
            return new TypeEnvironment(this.terms, this.args, this.captured, localcopy, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
        }
        else if ((this.args as Map<string, VarInfo>).has(name)) {
            const argscopy = new Map<string, VarInfo>(this.args as Map<string, VarInfo>).set(name, nv);
            return new TypeEnvironment(this.terms, argscopy, this.captured, this.locals, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
        }
        else {
            const capturedcopy = new Map<string, VarInfo>(this.captured as Map<string, VarInfo>).set(name, nv);
            return new TypeEnvironment(this.terms, this.args, capturedcopy, this.locals, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
        }
    }

    static createInitialEnvForCall(terms: Map<string, ResolvedType>, args: Map<string, VarInfo>, captured?: Map<string, VarInfo>): TypeEnvironment {
        return new TypeEnvironment(terms, args, captured || new Map<string, VarInfo>(), [new Map<string, VarInfo>()], undefined, undefined, undefined, [], new Set<string>());
    }

    hasNormalFlow(): boolean {
        return this.locals !== undefined;
    }

    getExpressionResult(): ExpressionReturnResult {
        assert(this.expressionResult !== undefined);
        return this.expressionResult as ExpressionReturnResult;
    }

    setExpressionResult(assembly: Assembly, etype: ResolvedType, value?: FlowTypeTruthValue): TypeEnvironment {
        assert(this.hasNormalFlow());
        let rvalue = value;
        if (rvalue === undefined) {
            rvalue = etype.isNoneType() ? FlowTypeTruthValue.False : FlowTypeTruthValue.Unknown;
        }

        return new TypeEnvironment(this.terms, this.args, this.captured, this.locals, { etype: etype, value: rvalue }, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
    }

    static convertToBoolFlowsOnExpressionResult(assembly: Assembly, options: TypeEnvironment[]): [TypeEnvironment[], TypeEnvironment[]] {
        assert(options.every((opt) => assembly.subtypeOf(opt.getExpressionResult().etype, assembly.typeUnion([assembly.getSpecialNoneType(), assembly.getSpecialBoolType()]))));

        const tvals = options.filter((opt) => opt.getExpressionResult().value !== FlowTypeTruthValue.False)
            .map((opt) => opt.setExpressionResult(assembly, assembly.getSpecialBoolType(), FlowTypeTruthValue.True));

        const fvals = options.filter((opt) => opt.getExpressionResult().value !== FlowTypeTruthValue.True)
            .map((opt) => opt.setExpressionResult(assembly, assembly.getSpecialBoolType(), FlowTypeTruthValue.False));

        return [tvals, fvals];
    }

    static convertToNoneSomeFlowsOnExpressionResult(assembly: Assembly, options: TypeEnvironment[]): [TypeEnvironment[], TypeEnvironment[]] {
        const nvals = options.filter((opt) => !assembly.restrictNone(opt.getExpressionResult().etype).isEmptyType())
            .map((opt) => opt.setExpressionResult(assembly, assembly.restrictNone(opt.getExpressionResult().etype), FlowTypeTruthValue.False));

        const svals = options.filter((opt) => !assembly.restrictSome(opt.getExpressionResult().etype).isEmptyType())
            .map((opt) => opt.setExpressionResult(assembly, assembly.restrictSome(opt.getExpressionResult().etype), opt.getExpressionResult().value));

        return [nvals, svals];
    }

    setAbort(): TypeEnvironment {
        assert(this.hasNormalFlow());
        return new TypeEnvironment(this.terms, this.args, this.captured, undefined, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
    }

    setReturn(assembly: Assembly, rtype: ResolvedType): TypeEnvironment {
        assert(this.hasNormalFlow());
        const rrtype = this.returnResult !== undefined ? assembly.typeUnion([this.returnResult, rtype]) : rtype;
        return new TypeEnvironment(this.terms, this.args, this.captured, undefined, this.expressionResult, rrtype, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
    }

    setYield(assembly: Assembly, ytype: ResolvedType): TypeEnvironment {
        assert(this.hasNormalFlow());
        const rytype = this.yieldResult !== undefined ? assembly.typeUnion([this.yieldResult, ytype]) : ytype;
        return new TypeEnvironment(this.terms, this.args, this.captured, undefined, this.expressionResult, this.returnResult, rytype, this.yieldTrgtInfo, this.frozenVars);
    }

    pushLocalScope(): TypeEnvironment {
        assert(this.hasNormalFlow());
        let localscopy = [...(this.locals as Map<string, VarInfo>[]), new Map<string, VarInfo>()];
        return new TypeEnvironment(this.terms, this.args, this.captured, localscopy, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
    }

    popLocalScope(): TypeEnvironment {
        let localscopy = this.locals !== undefined ? (this.locals as Map<string, VarInfo>[]).slice(0, -1) : undefined;
        return new TypeEnvironment(this.terms, this.args, this.captured, localscopy, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
    }

    isInYieldBlock(): boolean {
        return this.yieldTrgtInfo.length !== 0;
    }

    pushYieldTarget(trgt: MIRTempRegister): TypeEnvironment {
        let nyield = [...this.yieldTrgtInfo, trgt];
        return new TypeEnvironment(this.terms, this.args, this.captured, this.locals, this.expressionResult, this.returnResult, this.yieldResult, nyield, this.frozenVars);
    }

    popYieldTargetInfo(): TypeEnvironment {
        let nyield = this.yieldTrgtInfo.slice(0, this.yieldTrgtInfo.length - 1);
        return new TypeEnvironment(this.terms, this.args, this.captured, this.locals, this.expressionResult, this.returnResult, this.yieldResult, nyield, this.frozenVars);
    }

    getYieldTargetInfo(): MIRTempRegister {
        return this.yieldTrgtInfo[this.yieldTrgtInfo.length - 1];
    }

    private getLocalVarInfo(name: string): VarInfo | undefined {
        const locals = this.locals as Map<string, VarInfo>[];
        for (let i = locals.length - 1; i >= 0; --i) {
            if (locals[i].has(name)) {
                return (locals[i].get(name) as VarInfo);
            }
        }

        return undefined;
    }

    isVarNameDefined(name: string): boolean {
        return this.getLocalVarInfo(name) !== undefined || (this.args as Map<string, VarInfo>).has(name) || (this.captured as Map<string, VarInfo>).has(name);
    }

    lookupVar(name: string): VarInfo | null {
        return this.getLocalVarInfo(name) || (this.args as Map<string, VarInfo>).get(name) || (this.captured as Map<string, VarInfo>).get(name) || null;
    }

    lookupVarScope(name: string): "captured" | "arg" | "local" {
        const local = this.getLocalVarInfo(name);
        if (local !== undefined) {
            return "local";
        }

        return (this.args as Map<string, VarInfo>).has(name) ? "arg" : "captured";
    }

    addVar(name: string, isConst: boolean, dtype: ResolvedType, isDefined: boolean, ftype: ResolvedType): TypeEnvironment {
        let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => new Map<string, VarInfo>(frame));
        localcopy[localcopy.length - 1].set(name, new VarInfo(dtype, isConst, isDefined, ftype));
        return new TypeEnvironment(this.terms, this.args, this.captured, localcopy, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
    }

    setVar(name: string, ftype: ResolvedType): TypeEnvironment {
        const oldv = this.lookupVar(name) as VarInfo;
        const newv = oldv.assign(ftype);

        return this.updateVarInfo(name, newv);
    }

    multiVarUpdate(allDeclared: [boolean, string, ResolvedType, (string|number)[], ResolvedType][], allAssigned: [string, (string|number)[] | undefined, ResolvedType][]): TypeEnvironment {
        //TODO: many copies here could make this more efficient
        let nenv: TypeEnvironment = this;

        for (let i = 0; i < allDeclared.length; ++i) {
            const declv = allDeclared[i];
            nenv = nenv.addVar(declv[1], declv[0], declv[2], true, declv[4]);
        }

        for (let i = 0; i < allAssigned.length; ++i) {
            const assignv = allAssigned[i];
            nenv = nenv.setVar(assignv[0], assignv[2]);
        }

        return nenv;
    }

    assumeVar(name: string, ftype: ResolvedType): TypeEnvironment {
        const oldv = this.lookupVar(name) as VarInfo;
        const newv = oldv.infer(ftype);

        return this.updateVarInfo(name, newv);
    }

    getCurrentFrameNames(): string[] {
        let res: string[] = [];
        (this.locals as Map<string, VarInfo>[])[(this.locals as Map<string, VarInfo>[]).length - 1].forEach((v, k) => {
            res.push(k);
        });
        return res;
    }

    getAllLocalNames(): Set<string> {
        let names = new Set<string>();
        (this.locals as Map<string, VarInfo>[]).forEach((frame) => {
            frame.forEach((v, k) => {
                names.add(k);
            });
        });
        return names;
    }

    freezeVars(): TypeEnvironment {
        let svars = new Set<string>();
        for (let i = 0; i < (this.locals as Map<string, VarInfo>[]).length; ++i) {
            (this.locals as Map<string, VarInfo>[])[i].forEach((v, k) => svars.add(k));
        }

        return new TypeEnvironment(this.terms, this.args, this.captured, this.locals, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, svars);
    }

    static join(assembly: Assembly, ...opts: TypeEnvironment[]): TypeEnvironment {
        assert(opts.length !== 0);

        const fopts = opts.filter((opt) => opt.locals !== undefined);

        let argnames: string[] = [];
        let capturednames: string[] = [];
        fopts.forEach((opt) => {
            (opt.args as Map<string, VarInfo>).forEach((v, k) => argnames.push(k));
            (opt.captured as Map<string, VarInfo>).forEach((v, k) => capturednames.push(k));
        });

        let args = fopts.length !== 0 ? new Map<string, VarInfo>() : undefined;
        if (args !== undefined) {
            argnames.forEach((aname) => {
                const vinfo = VarInfo.join(assembly, ...fopts.map((opt) => (opt.args as Map<string, VarInfo>).get(aname) as VarInfo));
                (args as Map<string, VarInfo>).set(aname, vinfo);
            });
        }

        let captured = fopts.length !== 0 ? new Map<string, VarInfo>() : undefined;
        if (captured !== undefined) {
            capturednames.forEach((aname) => {
                const vinfo = VarInfo.join(assembly, ...fopts.map((opt) => (opt.captured as Map<string, VarInfo>).get(aname) as VarInfo));
                (captured as Map<string, VarInfo>).set(aname, vinfo);
            });
        }

        let locals = fopts.length !== 0 ? ([] as Map<string, VarInfo>[]) : undefined;
        if (locals !== undefined) {
            for (let i = 0; i < (fopts[0].locals as Map<string, VarInfo>[]).length; ++i) {
                let localsi = new Map<string, VarInfo>();
                (fopts[0].locals as Map<string, VarInfo>[])[i].forEach((v, k) => {
                    localsi.set(k, VarInfo.join(assembly, ...fopts.map((opt) => opt.lookupVar(k) as VarInfo)));
                });

                locals.push(localsi);
            }
        }

        const expresall = fopts.filter((opt) => opt.expressionResult !== undefined).map((opt) => opt.getExpressionResult());
        assert(expresall.length === 0 || expresall.length === fopts.length);
        const expres = expresall.length !== 0 ? ({ etype: assembly.typeUnion(expresall.map((opt) => opt.etype)), value: FlowTypeTruthOps.join(...expresall.map((opt) => opt.value)) }) : undefined;

        const rflow = opts.filter((opt) => opt.returnResult !== undefined).map((opt) => opt.returnResult as ResolvedType);
        const yflow = opts.filter((opt) => opt.yieldResult !== undefined).map((opt) => opt.yieldResult as ResolvedType);

        return new TypeEnvironment(opts[0].terms, args, captured, locals, expres, rflow.length !== 0 ? assembly.typeUnion(rflow) : undefined, yflow.length !== 0 ? assembly.typeUnion(yflow) : undefined, opts[0].yieldTrgtInfo, opts[0].frozenVars);
    }
}

export {
    FlowTypeTruthValue, FlowTypeTruthOps,
    VarInfo, ExpressionReturnResult,
    TypeEnvironment
};
