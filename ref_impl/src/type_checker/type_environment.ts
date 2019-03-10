//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import assert = require("assert");

import { Assembly } from "../ast/assembly";
import { ResolvedType } from "../ast/resolved_type";

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

    readonly args: Map<string, VarInfo>;
    readonly captured: Map<string, VarInfo>;
    readonly locals: Map<string, VarInfo>[] | undefined;

    readonly expressionResult: ExpressionReturnResult | undefined;
    readonly returnResult: ResolvedType | undefined;
    readonly yieldResult: ResolvedType | undefined;

    readonly frozenVars: Set<string>;

    private constructor(terms: Map<string, ResolvedType>,
        args: Map<string, VarInfo>, captured: Map<string, VarInfo>, locals: Map<string, VarInfo>[] | undefined,
        expressionResult: ExpressionReturnResult | undefined, rflow: ResolvedType | undefined, yflow: ResolvedType | undefined,
        frozenVars: Set<string>) {
        this.terms = terms;

        this.args = args;
        this.captured = captured;
        this.locals = locals;

        this.expressionResult = expressionResult;
        this.returnResult = rflow;
        this.yieldResult = yflow;

        this.frozenVars = frozenVars;
    }

    private updateVarInfo(name: string, nv: VarInfo): TypeEnvironment {
        if (this.getLocalVarInfo(name) !== undefined) {
            let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => frame.has(name) ? new Map<string, VarInfo>(frame).set(name, nv) : new Map<string, VarInfo>(frame));
            return new TypeEnvironment(this.terms, this.args, this.captured, localcopy, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
        }
        else if (this.args.has(name)) {
            const argscopy = new Map<string, VarInfo>(this.args).set(name, nv);
            return new TypeEnvironment(this.terms, argscopy, this.captured, this.locals, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
        }
        else {
            const capturedcopy = new Map<string, VarInfo>(this.captured).set(name, nv);
            return new TypeEnvironment(this.terms, this.args, capturedcopy, this.locals, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
        }
    }

    static createInitialEnvForCall(terms: Map<string, ResolvedType>, args: Map<string, VarInfo>, captured?: Map<string, VarInfo>): TypeEnvironment {
        return new TypeEnvironment(terms, args, captured || new Map<string, VarInfo>(), [new Map<string, VarInfo>()], undefined, undefined, undefined, new Set<string>());
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

        return new TypeEnvironment(this.terms, this.args, this.captured, this.locals, { etype: etype, value: rvalue }, this.returnResult, this.yieldResult, this.frozenVars);
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

    setReturn(assembly: Assembly, rtype: ResolvedType): TypeEnvironment {
        assert(this.hasNormalFlow());
        const rrtype = this.returnResult !== undefined ? assembly.typeUnion([this.returnResult, rtype]) : rtype;
        return new TypeEnvironment(this.terms, this.args, this.captured, undefined, this.expressionResult, rrtype, this.yieldResult, this.frozenVars);
    }

    setYield(assembly: Assembly, ytype: ResolvedType): TypeEnvironment {
        assert(this.hasNormalFlow());
        const rytype = this.yieldResult !== undefined ? assembly.typeUnion([this.yieldResult, ytype]) : ytype;
        return new TypeEnvironment(this.terms, this.args, this.captured, undefined, this.expressionResult, this.returnResult, rytype, this.frozenVars);
    }

    pushLocalScope(): TypeEnvironment {
        assert(this.hasNormalFlow());
        let localscopy = [...(this.locals as Map<string, VarInfo>[]), new Map<string, VarInfo>()];
        return new TypeEnvironment(this.terms, this.args, this.captured, localscopy, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
    }

    popLocalScope(): TypeEnvironment {
        let localscopy = this.locals !== undefined ? (this.locals as Map<string, VarInfo>[]).slice(0, -1) : undefined;
        return new TypeEnvironment(this.terms, this.args, this.captured, localscopy, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
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
        return this.getLocalVarInfo(name) !== undefined || this.args.has(name) || this.captured.has(name);
    }

    lookupVar(name: string): VarInfo | null {
        return this.getLocalVarInfo(name) || this.args.get(name) || this.captured.get(name) || null;
    }

    lookupVarScope(name: string): "captured" | "arg" | "local" {
        const local = this.getLocalVarInfo(name);
        if (local !== undefined) {
            return "local";
        }

        return this.args.has(name) ? "arg" : "captured";
    }

    addVar(name: string, isConst: boolean, dtype: ResolvedType, isDefined: boolean, ftype: ResolvedType): TypeEnvironment {
        let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => new Map<string, VarInfo>(frame));
        localcopy[localcopy.length - 1].set(name, new VarInfo(dtype, isConst, isDefined, ftype));
        return new TypeEnvironment(this.terms, this.args, this.captured, localcopy, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
    }

    setVar(name: string, ftype: ResolvedType): TypeEnvironment {
        const oldv = this.lookupVar(name) as VarInfo;
        const newv = oldv.assign(ftype);

        return this.updateVarInfo(name, newv);
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

        return new TypeEnvironment(this.terms, this.args, this.captured, this.locals, this.expressionResult, this.returnResult, this.yieldResult, svars);
    }

    static join(assembly: Assembly, ...opts: TypeEnvironment[]): TypeEnvironment {
        assert(opts.length !== 0);

        let argnames: string[] = [];
        let capturednames: string[] = [];
        opts.forEach((opt) => {
            opt.args.forEach((v, k) => argnames.push(k));
            opt.captured.forEach((v, k) => capturednames.push(k));
        });

        let args = new Map<string, VarInfo>();
        argnames.forEach((aname) => {
            const vinfo = VarInfo.join(assembly, ...opts.map((opt) => opt.args.get(aname) as VarInfo));
            args.set(aname, vinfo);
        });

        let captured = new Map<string, VarInfo>();
        capturednames.forEach((aname) => {
            const vinfo = VarInfo.join(assembly, ...opts.map((opt) => opt.captured.get(aname) as VarInfo));
            captured.set(aname, vinfo);
        });

        const fopts = opts.filter((opt) => opt.locals !== undefined);

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

        return new TypeEnvironment(opts[0].terms, args, captured, locals, expres, rflow.length !== 0 ? assembly.typeUnion(rflow) : undefined, yflow.length !== 0 ? assembly.typeUnion(yflow) : undefined, opts[0].frozenVars);
    }
}

export {
    FlowTypeTruthValue, FlowTypeTruthOps,
    VarInfo, ExpressionReturnResult,
    TypeEnvironment
};
