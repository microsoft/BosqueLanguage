"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const assert = require("assert");
var FlowTypeTruthValue;
(function (FlowTypeTruthValue) {
    FlowTypeTruthValue["True"] = "True";
    FlowTypeTruthValue["False"] = "False";
    FlowTypeTruthValue["Unknown"] = "Unknown";
})(FlowTypeTruthValue || (FlowTypeTruthValue = {}));
exports.FlowTypeTruthValue = FlowTypeTruthValue;
class FlowTypeTruthOps {
    static equal(e1, e2) {
        return e1 === e2;
    }
    static subvalue(e1, e2) {
        return e2 === FlowTypeTruthOps.join(e1, e2);
    }
    static join(...values) {
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
    static maybeTrueValue(e) {
        return (e === FlowTypeTruthValue.True || e === FlowTypeTruthValue.Unknown);
    }
    static maybeFalseValue(e) {
        return (e === FlowTypeTruthValue.False || e === FlowTypeTruthValue.Unknown);
    }
}
exports.FlowTypeTruthOps = FlowTypeTruthOps;
class VarInfo {
    constructor(dtype, isConst, isCaptured, mustDefined, ftype) {
        this.declaredType = dtype;
        this.flowType = ftype;
        this.isConst = isConst;
        this.isCaptured = isCaptured;
        this.mustDefined = mustDefined;
    }
    assign(ftype) {
        assert(!this.isConst);
        return new VarInfo(this.declaredType, this.isConst, this.isCaptured, true, ftype);
    }
    infer(ftype) {
        return new VarInfo(this.declaredType, this.isConst, this.isCaptured, true, ftype);
    }
    static join(assembly, ...values) {
        assert(values.length !== 0);
        return new VarInfo(values[0].declaredType, values[0].isConst, values[0].isCaptured, values.every((vi) => vi.mustDefined), assembly.typeUnion(values.map((vi) => vi.flowType)));
    }
}
exports.VarInfo = VarInfo;
class TypeEnvironment {
    constructor(scope, terms, refparams, pcodes, args, locals, result, expressionResult, rflow, yflow, yieldTrgtInfo, frozenVars) {
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
    updateVarInfo(name, nv) {
        if (this.getLocalVarInfo(name) !== undefined) {
            let localcopy = this.locals.map((frame) => frame.has(name) ? new Map(frame).set(name, nv) : new Map(frame));
            return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, localcopy, this.result, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
        }
        else {
            const argscopy = new Map(this.args).set(name, nv);
            return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, argscopy, this.locals, this.result, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
        }
    }
    static createInitialEnvForCall(scope, terms, refparams, pcodes, args, result) {
        return new TypeEnvironment(scope, terms, refparams, pcodes, args, [new Map()], result, undefined, undefined, undefined, [], new Set());
    }
    hasNormalFlow() {
        return this.locals !== undefined;
    }
    getExpressionResult() {
        assert(this.expressionResult !== undefined);
        return this.expressionResult;
    }
    setExpressionResult(etype, value) {
        assert(this.hasNormalFlow());
        let rvalue = value;
        if (rvalue === undefined) {
            rvalue = etype.isNoneType() ? FlowTypeTruthValue.False : FlowTypeTruthValue.Unknown;
        }
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, this.locals, this.result, { etype: etype, value: rvalue }, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
    }
    static convertToBoolFlowsOnExpressionResult(assembly, options) {
        assert(options.every((opt) => assembly.subtypeOf(opt.getExpressionResult().etype, assembly.typeUnion([assembly.getSpecialNoneType(), assembly.getSpecialBoolType()]))));
        const tvals = options.filter((opt) => opt.getExpressionResult().value !== FlowTypeTruthValue.False)
            .map((opt) => opt.setExpressionResult(assembly.getSpecialBoolType(), FlowTypeTruthValue.True));
        const fvals = options.filter((opt) => opt.getExpressionResult().value !== FlowTypeTruthValue.True)
            .map((opt) => opt.setExpressionResult(assembly.getSpecialBoolType(), FlowTypeTruthValue.False));
        return [tvals, fvals];
    }
    static convertToNoneSomeFlowsOnExpressionResult(assembly, options) {
        const nvals = options.filter((opt) => !assembly.restrictNone(opt.getExpressionResult().etype).isEmptyType())
            .map((opt) => opt.setExpressionResult(assembly.restrictNone(opt.getExpressionResult().etype), FlowTypeTruthValue.False));
        const svals = options.filter((opt) => !assembly.restrictSome(opt.getExpressionResult().etype).isEmptyType())
            .map((opt) => opt.setExpressionResult(assembly.restrictSome(opt.getExpressionResult().etype), opt.getExpressionResult().value));
        return [nvals, svals];
    }
    setAbort() {
        assert(this.hasNormalFlow());
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, undefined, this.result, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
    }
    setReturn(assembly, rtype) {
        assert(this.hasNormalFlow());
        const rrtype = this.returnResult !== undefined ? assembly.typeUnion([this.returnResult, rtype]) : rtype;
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, undefined, this.result, this.expressionResult, rrtype, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
    }
    setYield(assembly, ytype) {
        assert(this.hasNormalFlow());
        const rytype = this.yieldResult !== undefined ? assembly.typeUnion([this.yieldResult, ytype]) : ytype;
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, undefined, this.result, this.expressionResult, this.returnResult, rytype, this.yieldTrgtInfo, this.frozenVars);
    }
    pushLocalScope() {
        assert(this.hasNormalFlow());
        let localscopy = [...this.locals, new Map()];
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, localscopy, this.result, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
    }
    popLocalScope() {
        let localscopy = this.locals !== undefined ? this.locals.slice(0, -1) : undefined;
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, localscopy, this.result, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
    }
    isInYieldBlock() {
        return this.yieldTrgtInfo.length !== 0;
    }
    pushYieldTarget(trgt, block) {
        let nyield = [...this.yieldTrgtInfo, [trgt, block]];
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, this.locals, this.result, this.expressionResult, this.returnResult, this.yieldResult, nyield, this.frozenVars);
    }
    popYieldTargetInfo() {
        let nyield = this.yieldTrgtInfo.slice(0, this.yieldTrgtInfo.length - 1);
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, this.locals, this.result, this.expressionResult, this.returnResult, this.yieldResult, nyield, this.frozenVars);
    }
    getYieldTargetInfo() {
        return this.yieldTrgtInfo[this.yieldTrgtInfo.length - 1];
    }
    getLocalVarInfo(name) {
        const locals = this.locals;
        for (let i = locals.length - 1; i >= 0; --i) {
            if (locals[i].has(name)) {
                return locals[i].get(name);
            }
        }
        return undefined;
    }
    isVarNameDefined(name) {
        return this.getLocalVarInfo(name) !== undefined || this.args.has(name);
    }
    lookupVar(name) {
        return this.getLocalVarInfo(name) || this.args.get(name) || null;
    }
    lookupPCode(pc) {
        return this.pcodes.get(pc);
    }
    addVar(name, isConst, dtype, isDefined, ftype) {
        let localcopy = this.locals.map((frame) => new Map(frame));
        localcopy[localcopy.length - 1].set(name, new VarInfo(dtype, isConst, false, isDefined, ftype));
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, localcopy, this.result, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, this.frozenVars);
    }
    setVar(name, ftype) {
        const oldv = this.lookupVar(name);
        const newv = oldv.assign(ftype);
        return this.updateVarInfo(name, newv);
    }
    multiVarUpdate(allDeclared, allAssigned) {
        let nenv = this;
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
    assumeVar(name, ftype) {
        const oldv = this.lookupVar(name);
        const newv = oldv.infer(ftype);
        return this.updateVarInfo(name, newv);
    }
    getCurrentFrameNames() {
        let res = [];
        this.locals[this.locals.length - 1].forEach((v, k) => {
            res.push(k);
        });
        return res;
    }
    getAllLocalNames() {
        let names = new Set();
        this.locals.forEach((frame) => {
            frame.forEach((v, k) => {
                names.add(k);
            });
        });
        return names;
    }
    freezeVars() {
        let svars = new Set();
        for (let i = 0; i < this.locals.length; ++i) {
            this.locals[i].forEach((v, k) => svars.add(k));
        }
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, this.locals, this.result, this.expressionResult, this.returnResult, this.yieldResult, this.yieldTrgtInfo, svars);
    }
    static join(assembly, ...opts) {
        assert(opts.length !== 0);
        const fopts = opts.filter((opt) => opt.locals !== undefined);
        let argnames = [];
        fopts.forEach((opt) => {
            opt.args.forEach((v, k) => argnames.push(k));
        });
        let args = fopts.length !== 0 ? new Map() : undefined;
        if (args !== undefined) {
            argnames.forEach((aname) => {
                const vinfo = VarInfo.join(assembly, ...fopts.map((opt) => opt.args.get(aname)));
                args.set(aname, vinfo);
            });
        }
        let locals = fopts.length !== 0 ? [] : undefined;
        if (locals !== undefined) {
            for (let i = 0; i < fopts[0].locals.length; ++i) {
                let localsi = new Map();
                fopts[0].locals[i].forEach((v, k) => {
                    localsi.set(k, VarInfo.join(assembly, ...fopts.map((opt) => opt.lookupVar(k))));
                });
                locals.push(localsi);
            }
        }
        const expresall = fopts.filter((opt) => opt.expressionResult !== undefined).map((opt) => opt.getExpressionResult());
        assert(expresall.length === 0 || expresall.length === fopts.length);
        let expres = undefined;
        if (expresall.length !== 0) {
            const retype = assembly.typeUnion(expresall.map((opt) => opt.etype));
            const rflow = FlowTypeTruthOps.join(...expresall.map((opt) => opt.value));
            expres = { etype: retype, value: rflow };
        }
        const rflow = opts.filter((opt) => opt.returnResult !== undefined).map((opt) => opt.returnResult);
        const yflow = opts.filter((opt) => opt.yieldResult !== undefined).map((opt) => opt.yieldResult);
        return new TypeEnvironment(opts[0].scope, opts[0].terms, opts[0].refparams, opts[0].pcodes, args, locals, opts[0].result, expres, rflow.length !== 0 ? assembly.typeUnion(rflow) : undefined, yflow.length !== 0 ? assembly.typeUnion(yflow) : undefined, opts[0].yieldTrgtInfo, opts[0].frozenVars);
    }
}
exports.TypeEnvironment = TypeEnvironment;
//# sourceMappingURL=type_environment.js.map