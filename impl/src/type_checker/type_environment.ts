//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import assert = require("assert");

import { Assembly } from "../ast/assembly";
import { ResolvedType } from "../ast/resolved_type";
import { MIRInvokeKey } from "../compiler/mir_ops";
import { PCode } from "../compiler/mir_emitter";
import { ConstantExpressionValue } from "../ast/body";

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

class ValueType {
    readonly layout: ResolvedType;
    readonly flowtype: ResolvedType;

    constructor(layout: ResolvedType, flowtype: ResolvedType) {
        this.layout = layout;
        this.flowtype = flowtype;
    }

    inferFlow(nflow: ResolvedType): ValueType {
        return new ValueType(this.layout, nflow);
    }

    static createUniform(ttype: ResolvedType): ValueType {
        return new ValueType(ttype, ttype);
    }

    static join(assembly: Assembly, ...args: ValueType[]): ValueType {
        assert(args.length !== 0);

        const jlayout = assembly.typeUpperBound(args.map((ei) => ei.layout));
        assert(jlayout.isSameType(args[0].layout)); //we should not let this happen!!!

        const jflow = assembly.typeUpperBound(args.map((ei) => ei.flowtype));
        return new ValueType(jlayout, jflow);
    }
}

class ExpressionReturnResult {
    readonly valtype: ValueType;
    readonly truthval: FlowTypeTruthValue;

    readonly expvar: string | undefined;

    constructor(valtype: ValueType, tval: FlowTypeTruthValue, expvar: string | undefined) {
        this.valtype = valtype;
        this.truthval = tval;

        this.expvar = expvar;
    }

    static join(assembly: Assembly, expvar: string, ...args: ExpressionReturnResult[]): ExpressionReturnResult {
        assert(args.length !== 0);

        const jtype = ValueType.join(assembly, ...args.map((ei) => ei.valtype));
        const jtv = FlowTypeTruthOps.join(...args.map((ei) => ei.truthval));

        return new ExpressionReturnResult(jtype, jtv, expvar);
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

        const jdef = values.every((vi) => vi.mustDefined);
        const jtype = assembly.typeUpperBound(values.map((vi) => vi.flowType));
        return new VarInfo(values[0].declaredType, values[0].isConst, values[0].isCaptured, jdef, jtype);
    }
}

type StructuredAssignmentPathStep = {
    fromtype: ResolvedType,
    t: ResolvedType,
    step: "tuple" | "record" | "elist" | "nominal";
    ival: number;
    nval: string;
};

type StructuredAssignmentCheck = {
    action: "eqchk" | "typechk",
    srctype: ResolvedType,
    oftype: ResolvedType | undefined,
    isoptional: boolean,
    eqvalue: ConstantExpressionValue | undefined
};

class TypeEnvironment {
    readonly scope: MIRInvokeKey;
    readonly terms: Map<string, ResolvedType>;

    readonly pcodes: Map<string, { pcode: PCode, captured: string[] }>;

    readonly args: Map<string, VarInfo> | undefined;
    readonly locals: Map<string, VarInfo>[] | undefined;

    readonly inferResult: ResolvedType | undefined;
    readonly inferYield: (ResolvedType | undefined)[];

    readonly expressionResult: ExpressionReturnResult | undefined;
    readonly returnResult: ResolvedType | undefined;
    readonly yieldResult: ResolvedType | undefined;

    readonly frozenVars: Set<string>;

    private constructor(scope: MIRInvokeKey, terms: Map<string, ResolvedType>, pcodes: Map<string, { pcode: PCode, captured: string[] }>,
        args: Map<string, VarInfo> | undefined, locals: Map<string, VarInfo>[] | undefined, result: ResolvedType | undefined, inferYield: (ResolvedType | undefined)[],
        expressionResult: ExpressionReturnResult | undefined, rflow: ResolvedType | undefined, yflow: ResolvedType | undefined,
        frozenVars: Set<string>) {

        this.scope = scope;
        this.terms = terms;

        this.pcodes = pcodes;

        this.args = args;
        this.locals = locals;

        this.inferResult = result;
        this.inferYield = inferYield;

        this.expressionResult = expressionResult;
        this.returnResult = rflow;
        this.yieldResult = yflow;

        this.frozenVars = frozenVars;
    }

    private updateVarInfo(name: string, nv: VarInfo): TypeEnvironment {
        if (this.getLocalVarInfo(name) !== undefined) {
            let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => frame.has(name) ? new Map<string, VarInfo>(frame).set(name, nv) : new Map<string, VarInfo>(frame));
            return new TypeEnvironment(this.scope, this.terms, this.pcodes, this.args, localcopy, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
        }
        else {
            const argscopy = new Map<string, VarInfo>(this.args as Map<string, VarInfo>).set(name, nv);
            return new TypeEnvironment(this.scope, this.terms, this.pcodes, argscopy, this.locals, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
        }
    }

    static createInitialEnvForCall(scope: MIRInvokeKey, terms: Map<string, ResolvedType>, pcodes: Map<string, { pcode: PCode, captured: string[] }>, args: Map<string, VarInfo>, inferResult: ResolvedType | undefined): TypeEnvironment {
        return new TypeEnvironment(scope, terms, pcodes, args, [new Map<string, VarInfo>()], inferResult, [], undefined, undefined, undefined, new Set<string>());
    }

    hasNormalFlow(): boolean {
        return this.locals !== undefined;
    }

    getExpressionResult(): ExpressionReturnResult {
        assert(this.hasNormalFlow() && this.expressionResult !== undefined);

        return this.expressionResult as ExpressionReturnResult;
    }

    inferVarsOfType(ftype: ResolvedType, ...vars: (string | undefined)[]): TypeEnvironment {
        let cenv = this as TypeEnvironment;

        for(let i = 0; i < vars.length; ++i) {
            const vv = vars[i];
            if (vv !== undefined) {
                cenv = cenv.updateVarInfo(vv, (cenv.lookupVar(vv) as VarInfo).infer(ftype));
            }
        }

        return cenv;
    }

    clearExpressionResult(): TypeEnvironment {
        return new TypeEnvironment(this.scope, this.terms, this.pcodes, this.args, this.locals, this.inferResult, this.inferYield, undefined, this.returnResult, this.yieldResult, this.frozenVars);
    }

    setUniformResultExpression(etype: ResolvedType, value?: FlowTypeTruthValue): TypeEnvironment {
        assert(this.hasNormalFlow());

        const einfo = new ExpressionReturnResult(new ValueType(etype, etype), value || FlowTypeTruthValue.Unknown, undefined);
        return new TypeEnvironment(this.scope, this.terms, this.pcodes, this.args, this.locals, this.inferResult, this.inferYield, einfo, this.returnResult, this.yieldResult, this.frozenVars);
    }

    setBoolResultExpression(btype: ResolvedType, value: FlowTypeTruthValue): TypeEnvironment {
        assert(this.hasNormalFlow());

        const einfo = new ExpressionReturnResult(ValueType.createUniform(btype), value || FlowTypeTruthValue.Unknown, undefined);
        return new TypeEnvironment(this.scope, this.terms, this.pcodes, this.args, this.locals, this.inferResult, this.inferYield, einfo, this.returnResult, this.yieldResult, this.frozenVars);
    }

    setVarResultExpression(layouttype: ResolvedType, flowtype: ResolvedType, vname: string): TypeEnvironment {
        assert(this.hasNormalFlow());

        const einfo = new ExpressionReturnResult(new ValueType(layouttype, flowtype), FlowTypeTruthValue.Unknown, vname);
        return new TypeEnvironment(this.scope, this.terms, this.pcodes, this.args, this.locals, this.inferResult, this.inferYield, einfo, this.returnResult, this.yieldResult, this.frozenVars);
    }

    updateResultExpression(layouttype: ResolvedType, flowtype: ResolvedType): TypeEnvironment {
        assert(this.hasNormalFlow());

        const einfo = new ExpressionReturnResult(new ValueType(layouttype, flowtype), this.getExpressionResult().truthval, this.getExpressionResult().expvar);
        return new TypeEnvironment(this.scope, this.terms, this.pcodes, this.args, this.locals, this.inferResult, this.inferYield, einfo, this.returnResult, this.yieldResult, this.frozenVars);
    }

    setResultExpression(layouttype: ResolvedType, flowtype: ResolvedType, value: FlowTypeTruthValue | undefined, vname: string | undefined): TypeEnvironment {
        assert(this.hasNormalFlow());

        const einfo = new ExpressionReturnResult(new ValueType(layouttype, flowtype), value || this.getExpressionResult().truthval, vname || this.getExpressionResult().expvar);
        return new TypeEnvironment(this.scope, this.terms, this.pcodes, this.args, this.locals, this.inferResult, this.inferYield, einfo, this.returnResult, this.yieldResult, this.frozenVars);
    }

    private setResultExpressionWVarOpt(vtype: ValueType, evar: string | undefined, value?: FlowTypeTruthValue): TypeEnvironment {
        assert(this.hasNormalFlow());

        const rvalue = value || FlowTypeTruthValue.Unknown;
        const einfo = new ExpressionReturnResult(vtype, rvalue, evar);
        const nte = new TypeEnvironment(this.scope, this.terms, this.pcodes, this.args, this.locals, this.inferResult, this.inferYield, einfo, this.returnResult, this.yieldResult, this.frozenVars);

        return evar === undefined ? nte : nte.updateVarInfo(evar, (nte.lookupVar(evar) as VarInfo).infer(vtype.flowtype));
    }

    static convertToBoolFlowsOnResult(assembly: Assembly, options: TypeEnvironment[]): {tenvs: TypeEnvironment[], fenvs: TypeEnvironment[]} {
        assert(options.every((opt) => assembly.subtypeOf(opt.getExpressionResult().valtype.flowtype, assembly.getSpecialBoolType())));

        const tvals = options.filter((opt) => opt.getExpressionResult().truthval !== FlowTypeTruthValue.False)
            .map((opt) => opt.setResultExpressionWVarOpt(ValueType.createUniform(assembly.getSpecialBoolType()), opt.getExpressionResult().expvar, FlowTypeTruthValue.True));

        const fvals = options.filter((opt) => opt.getExpressionResult().truthval !== FlowTypeTruthValue.True)
            .map((opt) => opt.setResultExpressionWVarOpt(ValueType.createUniform(assembly.getSpecialBoolType()), opt.getExpressionResult().expvar, FlowTypeTruthValue.False));

        return {tenvs: tvals, fenvs: fvals};
    }

    static convertToTypeNotTypeFlowsOnResult(assembly: Assembly, witht: ResolvedType, options: TypeEnvironment[]): {tenvs: TypeEnvironment[], fenvs: TypeEnvironment[]} {
        let tp: TypeEnvironment[] = [];
        let fp: TypeEnvironment[] = [];
        
        for(let i = 0; i < options.length; ++i) {
            const opt = options[i];
            const vtype = opt.getExpressionResult().valtype;
            const pccs = assembly.splitTypes(vtype.flowtype, witht);

            if(!pccs.tp.isEmptyType()) {
                tp.push(opt.setResultExpressionWVarOpt(vtype.inferFlow(pccs.tp), opt.getExpressionResult().expvar, opt.getExpressionResult().truthval));
            }
            if(!pccs.fp.isEmptyType()) {
                fp.push(opt.setResultExpressionWVarOpt(vtype.inferFlow(pccs.fp), opt.getExpressionResult().expvar, opt.getExpressionResult().truthval));
            }
        }
        return {tenvs: tp, fenvs: fp};
    }

    static convertToHasIndexNotHasIndexFlowsOnResult(assembly: Assembly, idx: number, options: TypeEnvironment[]): {tenvs: TypeEnvironment[], fenvs: TypeEnvironment[]} {
        let tp: TypeEnvironment[] = [];
        let fp: TypeEnvironment[] = [];
        
        for(let i = 0; i < options.length; ++i) {
            const opt = options[i];
            const vtype = opt.getExpressionResult().valtype;
            const pccs = assembly.splitIndex(vtype.flowtype, idx);

            if(!pccs.tp.isEmptyType()) {
                tp.push(opt.setResultExpressionWVarOpt(vtype.inferFlow(pccs.tp), opt.getExpressionResult().expvar));
            }
            if(!pccs.fp.isEmptyType()) {
                fp.push(opt.setResultExpressionWVarOpt(vtype.inferFlow(pccs.fp), opt.getExpressionResult().expvar));
            }
        }
        return {tenvs: tp, fenvs: fp};
    }

    static convertToHasIndexNotHasPropertyFlowsOnResult(assembly: Assembly, pname: string, options: TypeEnvironment[]): {tenvs: TypeEnvironment[], fenvs: TypeEnvironment[]} {
        let tp: TypeEnvironment[] = [];
        let fp: TypeEnvironment[] = [];
        
        for(let i = 0; i < options.length; ++i) {
            const opt = options[i];
            const vtype = opt.getExpressionResult().valtype;
            const pccs = assembly.splitProperty(vtype.flowtype, pname);

            if(!pccs.tp.isEmptyType()) {
                tp.push(opt.setResultExpressionWVarOpt(vtype.inferFlow(pccs.tp), opt.getExpressionResult().expvar));
            }
            if(!pccs.fp.isEmptyType()) {
                fp.push(opt.setResultExpressionWVarOpt(vtype.inferFlow(pccs.fp), opt.getExpressionResult().expvar));
            }
        }
        return {tenvs: tp, fenvs: fp};
    }

    setAbort(): TypeEnvironment {
        assert(this.hasNormalFlow());
        return new TypeEnvironment(this.scope, this.terms, this.pcodes, this.args, undefined, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
    }

    setReturn(assembly: Assembly, rtype: ResolvedType): TypeEnvironment {
        assert(this.hasNormalFlow());
        const rrtype = this.returnResult !== undefined ? assembly.typeUpperBound([this.returnResult, rtype]) : rtype;
        return new TypeEnvironment(this.scope, this.terms, this.pcodes, this.args, undefined, this.inferResult, this.inferYield, this.expressionResult, rrtype, this.yieldResult, this.frozenVars);
    }

    setYield(assembly: Assembly, ytype: ResolvedType): TypeEnvironment {
        assert(this.hasNormalFlow());
        const rytype = this.yieldResult !== undefined ? assembly.typeUpperBound([this.yieldResult, ytype]) : ytype;
        return new TypeEnvironment(this.scope, this.terms, this.pcodes, this.args, undefined, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, rytype, this.frozenVars);
    }

    pushLocalScope(): TypeEnvironment {
        assert(this.hasNormalFlow());
        let localscopy = [...(this.locals as Map<string, VarInfo>[]), new Map<string, VarInfo>()];
        return new TypeEnvironment(this.scope, this.terms, this.pcodes, this.args, localscopy, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
    }

    popLocalScope(): TypeEnvironment {
        let localscopy = this.locals !== undefined ? (this.locals as Map<string, VarInfo>[]).slice(0, -1) : undefined;
        return new TypeEnvironment(this.scope, this.terms, this.pcodes, this.args, localscopy, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
    }

    isInYieldBlock(): boolean {
        return this.inferYield.length !== 0;
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

    addVar(name: string, isConst: boolean, dtype: ResolvedType, isDefined: boolean, infertype: ResolvedType): TypeEnvironment {
        assert(this.hasNormalFlow());

        let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => new Map<string, VarInfo>(frame));
        localcopy[localcopy.length - 1].set(name, new VarInfo(dtype, isConst, false, isDefined, infertype));

        return new TypeEnvironment(this.scope, this.terms, this.pcodes, this.args, localcopy, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
    }

    setVar(name: string, flowtype: ResolvedType): TypeEnvironment {
        assert(this.hasNormalFlow());

        const oldv = this.lookupVar(name) as VarInfo;
        const nv = oldv.assign(flowtype);

        let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => frame.has(name) ? new Map<string, VarInfo>(frame).set(name, nv) : new Map<string, VarInfo>(frame));
        return new TypeEnvironment(this.scope, this.terms, this.pcodes, this.args, localcopy, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
    }

    setRefVar(name: string): TypeEnvironment {
        assert(this.hasNormalFlow());

        const oldv = this.lookupVar(name) as VarInfo;
        const nv = oldv.assign(oldv.declaredType);

        let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => frame.has(name) ? new Map<string, VarInfo>(frame).set(name, nv) : new Map<string, VarInfo>(frame));
        return new TypeEnvironment(this.scope, this.terms, this.pcodes, this.args, localcopy, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
    }

    multiVarUpdate(allDeclared: [boolean, string, ResolvedType, StructuredAssignmentPathStep[], ResolvedType][], allAssigned: [string, StructuredAssignmentPathStep[], ResolvedType][]): TypeEnvironment {
        assert(this.hasNormalFlow());

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

    freezeVars(inferyield: ResolvedType | undefined): TypeEnvironment {
        assert(this.hasNormalFlow());

        let svars = new Set<string>();
        for (let i = 0; i < (this.locals as Map<string, VarInfo>[]).length; ++i) {
            (this.locals as Map<string, VarInfo>[])[i].forEach((v, k) => svars.add(k));
        }

        const iyeild = [...this.inferYield, inferyield];

        return new TypeEnvironment(this.scope, this.terms, this.pcodes, this.args, this.locals, this.inferResult, iyeild, this.expressionResult, this.returnResult, this.yieldResult, svars);
    }

    static join(assembly: Assembly, ...opts: TypeEnvironment[]): TypeEnvironment {
        assert(opts.length !== 0);

        if (opts.length === 1) {
            return opts[0];
        }
        else {
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
            if (expresall.length !== 0) {
                const retype = ValueType.join(assembly, ...expresall.map((opt) => opt.valtype));
                const rflow = FlowTypeTruthOps.join(...expresall.map((opt) => opt.truthval));
                const evar = expresall.every((ee) => ee.expvar === expresall[0].expvar) ? expresall[0].expvar : undefined;
                expres = new ExpressionReturnResult(retype, rflow, evar);
            }

            const rflow = opts.filter((opt) => opt.returnResult !== undefined).map((opt) => opt.returnResult as ResolvedType);
            const yflow = opts.filter((opt) => opt.yieldResult !== undefined).map((opt) => opt.yieldResult as ResolvedType);

            return new TypeEnvironment(opts[0].scope, opts[0].terms, opts[0].pcodes, args, locals, opts[0].inferResult, opts[0].inferYield, expres, rflow.length !== 0 ? assembly.typeUpperBound(rflow) : undefined, yflow.length !== 0 ? assembly.typeUpperBound(yflow) : undefined, opts[0].frozenVars);
        }
    }
}

export {
    FlowTypeTruthValue, FlowTypeTruthOps, ValueType,
    VarInfo, ExpressionReturnResult, StructuredAssignmentPathStep, StructuredAssignmentCheck,
    TypeEnvironment
};
