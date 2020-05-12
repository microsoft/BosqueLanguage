//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import assert = require("assert");

import { Assembly } from "../ast/assembly";
import { ResolvedType } from "../ast/resolved_type";
import { MIRTempRegister, MIRInvokeKey } from "../compiler/mir_ops";
import { PCode } from "../compiler/mir_emitter";

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
    readonly isCaptured: boolean;
    readonly mustDefined: boolean;
    readonly flowType: ResolvedType;

    constructor(dtype: ResolvedType, isConst: boolean, isCaptured: boolean, mustDefined: boolean, ftype: ResolvedType) {
        this.declaredType = dtype;
        this.flowType = ftype;
        this.isConst = isConst;
        this.isCaptured = isCaptured;
        this.mustDefined = mustDefined;
    }

    assign(ftype: ResolvedType): VarInfo {
        assert(!this.isConst);
        return new VarInfo(this.declaredType, this.isConst, this.isCaptured, true, ftype);
    }

    infer(ftype: ResolvedType): VarInfo {
        return new VarInfo(this.declaredType, this.isConst, this.isCaptured, true, ftype);
    }

    static join(assembly: Assembly, ...values: VarInfo[]): VarInfo {
        assert(values.length !== 0);

        return new VarInfo(values[0].declaredType, values[0].isConst, values[0].isCaptured, values.every((vi) => vi.mustDefined), assembly.typeUpperBound(values.map((vi) => vi.flowType)));
    }
}

type ExpressionReturnResult = {
    etype: ResolvedType,
    value: FlowTypeTruthValue
};

type StructuredAssignmentPathStep = {
    fromtype: ResolvedType,
    t: ResolvedType,
    step: "tuple" | "record" | "elist" | "nominal";
    ival: number;
    nval: string;
};

class TypeEnvironment {
    readonly scope: MIRInvokeKey;
    readonly terms: Map<string, ResolvedType>;

    readonly refparams: string[];
    readonly pcodes: Map<string, { pcode: PCode, captured: string[] }>;

    readonly args: Map<string, VarInfo> | undefined;
    readonly locals: Map<string, VarInfo>[] | undefined;
    readonly result: ResolvedType;

    readonly expressionResult: ExpressionReturnResult | undefined;
    readonly returnResult: ResolvedType | undefined;
    readonly yieldResult: ResolvedType | undefined;

    readonly yieldTrgtInfo: [MIRTempRegister, string][];

    readonly frozenVars: Set<string>;

    private constructor(scope: MIRInvokeKey, terms: Map<string, ResolvedType>, refparams: string[], pcodes: Map<string, { pcode: PCode, captured: string[] }>,
        args: Map<string, VarInfo> | undefined, locals: Map<string, VarInfo>[] | undefined, result: ResolvedType,
        expressionResult: ExpressionReturnResult | undefined, rflow: ResolvedType | undefined, yflow: ResolvedType | undefined,
        yieldTrgtInfo: [MIRTempRegister, string][], frozenVars: Set<string>) {
        this.scope = scope;
        this.terms = terms;

        this.refparams = refparams;
        this.pcodes = pcodes;

        this.args = args;
        this.locals = locals;
        this.result = result;

        this.expressionResult = expressionResult;
        this.returnResult = rflow;
        this.yieldResult = yflow;

        this.yieldTrgtInfo = yieldTrgtInfo;

        this.frozenVars = frozenVars;
    }

    private updateVarInfo(name: string, nv: VarInfo): TypeEnvironment {
        if (this.getLocalVarInfo(name) !== undefined) {
            let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => frame.has(name) ? new Map<string, VarInfo>(frame).set(name, nv) : new Map<string, VarInfo>(frame));
            return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, localcopy, this.result, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
        }
        else {
            const argscopy = new Map<string, VarInfo>(this.args as Map<string, VarInfo>).set(name, nv);
            return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, argscopy, this.locals, this.result, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
        }
    }

    static createInitialEnvForCall(scope: MIRInvokeKey, terms: Map<string, ResolvedType>, refparams: string[], pcodes: Map<string, { pcode: PCode, captured: string[] }>, args: Map<string, VarInfo>, result: ResolvedType): TypeEnvironment {
        return new TypeEnvironment(scope, terms, refparams, pcodes, args, [new Map<string, VarInfo>()], result, undefined, undefined, undefined, [], new Set<string>());
    }

    hasNormalFlow(): boolean {
        return this.locals !== undefined;
    }

    getExpressionResult(): ExpressionReturnResult {
        assert(this.expressionResult !== undefined);
        return this.expressionResult as ExpressionReturnResult;
    }

    setExpressionResult(etype: ResolvedType, value?: FlowTypeTruthValue): TypeEnvironment {
        assert(this.hasNormalFlow());
        let rvalue = value;
        if (rvalue === undefined) {
            rvalue = etype.isNoneType() ? FlowTypeTruthValue.False : FlowTypeTruthValue.Unknown;
        }

        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, this.locals, this.result, { etype: etype, value: rvalue }, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
    }

    static convertToBoolFlowsOnExpressionResult(assembly: Assembly, options: TypeEnvironment[]): [TypeEnvironment[], TypeEnvironment[]] {
        assert(options.every((opt) => assembly.subtypeOf(opt.getExpressionResult().etype, assembly.typeUpperBound([assembly.getSpecialNoneType(), assembly.getSpecialBoolType()]))));

        const tvals = options.filter((opt) => opt.getExpressionResult().value !== FlowTypeTruthValue.False)
            .map((opt) => opt.setExpressionResult(assembly.getSpecialBoolType(), FlowTypeTruthValue.True));

        const fvals = options.filter((opt) => opt.getExpressionResult().value !== FlowTypeTruthValue.True)
            .map((opt) => opt.setExpressionResult(assembly.getSpecialBoolType(), FlowTypeTruthValue.False));

        return [tvals, fvals];
    }

    static convertToNoneSomeFlowsOnExpressionResult(assembly: Assembly, options: TypeEnvironment[]): [TypeEnvironment[], TypeEnvironment[]] {
        const nvals = options.filter((opt) => !assembly.restrictNone(opt.getExpressionResult().etype).isEmptyType())
            .map((opt) => opt.setExpressionResult(assembly.restrictNone(opt.getExpressionResult().etype), FlowTypeTruthValue.False));

        const svals = options.filter((opt) => !assembly.restrictSome(opt.getExpressionResult().etype).isEmptyType())
            .map((opt) => opt.setExpressionResult(assembly.restrictSome(opt.getExpressionResult().etype), opt.getExpressionResult().value));

        return [nvals, svals];
    }

    setAbort(): TypeEnvironment {
        assert(this.hasNormalFlow());
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, undefined, this.result, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
    }

    setReturn(assembly: Assembly, rtype: ResolvedType): TypeEnvironment {
        assert(this.hasNormalFlow());
        const rrtype = this.returnResult !== undefined ? assembly.typeUpperBound([this.returnResult, rtype]) : rtype;
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, undefined, this.result, this.expressionResult, rrtype, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
    }

    setYield(assembly: Assembly, ytype: ResolvedType): TypeEnvironment {
        assert(this.hasNormalFlow());
        const rytype = this.yieldResult !== undefined ? assembly.typeUpperBound([this.yieldResult, ytype]) : ytype;
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, undefined, this.result, this.expressionResult, this.returnResult, rytype, this.yieldTrgtInfo, this.frozenVars);
    }

    pushLocalScope(): TypeEnvironment {
        assert(this.hasNormalFlow());
        let localscopy = [...(this.locals as Map<string, VarInfo>[]), new Map<string, VarInfo>()];
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, localscopy, this.result, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
    }

    popLocalScope(): TypeEnvironment {
        let localscopy = this.locals !== undefined ? (this.locals as Map<string, VarInfo>[]).slice(0, -1) : undefined;
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, localscopy, this.result, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
    }

    isInYieldBlock(): boolean {
        return this.yieldTrgtInfo.length !== 0;
    }

    pushYieldTarget(trgt: MIRTempRegister, block: string): TypeEnvironment {
        let nyield = [...this.yieldTrgtInfo, [trgt, block]] as [MIRTempRegister, string][];
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, this.locals, this.result, this.expressionResult, this.returnResult, this.yieldResult, nyield, this.frozenVars);
    }

    popYieldTargetInfo(): TypeEnvironment {
        let nyield = this.yieldTrgtInfo.slice(0, this.yieldTrgtInfo.length - 1);
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, this.locals, this.result, this.expressionResult, this.returnResult, this.yieldResult, nyield, this.frozenVars);
    }

    getYieldTargetInfo(): [MIRTempRegister, string] {
        return this.yieldTrgtInfo[this.yieldTrgtInfo.length - 1];
    }

    getLocalVarInfo(name: string): VarInfo | undefined {
        const locals = this.locals as Map<string, VarInfo>[];
        for (let i = locals.length - 1; i >= 0; --i) {
            if (locals[i].has(name)) {
                return (locals[i].get(name) as VarInfo);
            }
        }

        return undefined;
    }

    isVarNameDefined(name: string): boolean {
        return this.getLocalVarInfo(name) !== undefined || (this.args as Map<string, VarInfo>).has(name);
    }

    lookupVar(name: string): VarInfo | null {
        return this.getLocalVarInfo(name) || (this.args as Map<string, VarInfo>).get(name) || null;
    }

    lookupPCode(pc: string): { pcode: PCode, captured: string[] } | undefined {
        return this.pcodes.get(pc);
    }

    addVar(name: string, isConst: boolean, dtype: ResolvedType, isDefined: boolean, ftype: ResolvedType): TypeEnvironment {
        let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => new Map<string, VarInfo>(frame));
        localcopy[localcopy.length - 1].set(name, new VarInfo(dtype, isConst, false, isDefined, ftype));
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, localcopy, this.result, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
    }

    setVar(name: string, ftype: ResolvedType): TypeEnvironment {
        const oldv = this.lookupVar(name) as VarInfo;
        const newv = oldv.assign(ftype);

        return this.updateVarInfo(name, newv);
    }

    multiVarUpdate(allDeclared: [boolean, string, ResolvedType, StructuredAssignmentPathStep[], ResolvedType][], allAssigned: [string, StructuredAssignmentPathStep[], ResolvedType][]): TypeEnvironment {
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

        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, this.locals, this.result, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, svars);
    }

    static join(assembly: Assembly, ...opts: TypeEnvironment[]): TypeEnvironment {
        assert(opts.length !== 0);

        const fopts = opts.filter((opt) => opt.locals !== undefined);

        let argnames: string[] = [];
        fopts.forEach((opt) => {
            (opt.args as Map<string, VarInfo>).forEach((v, k) => argnames.push(k));
        });

        let args = fopts.length !== 0 ? new Map<string, VarInfo>() : undefined;
        if (args !== undefined) {
            argnames.forEach((aname) => {
                const vinfo = VarInfo.join(assembly, ...fopts.map((opt) => (opt.args as Map<string, VarInfo>).get(aname) as VarInfo));
                (args as Map<string, VarInfo>).set(aname, vinfo);
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

        let expres: ExpressionReturnResult | undefined = undefined;
        if(expresall.length !== 0) {
            const retype = assembly.typeUpperBound(expresall.map((opt) => opt.etype));
            const rflow = FlowTypeTruthOps.join(...expresall.map((opt) => opt.value));
            expres = { etype: retype, value: rflow };
        }

        const rflow = opts.filter((opt) => opt.returnResult !== undefined).map((opt) => opt.returnResult as ResolvedType);
        const yflow = opts.filter((opt) => opt.yieldResult !== undefined).map((opt) => opt.yieldResult as ResolvedType);

        return new TypeEnvironment(opts[0].scope, opts[0].terms, opts[0].refparams, opts[0].pcodes, args, locals, opts[0].result, expres, rflow.length !== 0 ? assembly.typeUpperBound(rflow) : undefined, yflow.length !== 0 ? assembly.typeUpperBound(yflow) : undefined, opts[0].yieldTrgtInfo, opts[0].frozenVars);
    }
}

export {
    FlowTypeTruthValue, FlowTypeTruthOps,
    VarInfo, ExpressionReturnResult, StructuredAssignmentPathStep,
    TypeEnvironment
};
