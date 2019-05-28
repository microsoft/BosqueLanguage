//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { Value, TypedStringValue, EntityValueSimple, ValueOps, ListValue, HashSetValue, HashMapValue, TupleValue, RecordValue, LambdaValue } from "./value";
import { Environment, PrePostError, raiseRuntimeError, FunctionScope, InvariantError, NotImplementedRuntimeError } from "./interpreter_environment";
import { MIRAssembly, MIRTupleType, MIRTupleTypeEntry, MIRRecordTypeEntry, MIRRecordType, MIREntityType, MIREntityTypeDecl, MIRFieldDecl, MIROOTypeDecl, MIRType, MIRGlobalDecl, MIRConstDecl, MIRFunctionDecl, MIRStaticDecl, MIRConceptTypeDecl, MIRMethodDecl, MIRInvokeDecl, MIRFunctionType } from "../compiler/mir_assembly";
import { MIRBody, MIROp, MIROpTag, MIRLoadConst, MIRArgument, MIRTempRegister, MIRRegisterArgument, MIRConstantTrue, MIRConstantString, MIRConstantInt, MIRConstantNone, MIRConstantFalse, MIRLoadConstTypedString, MIRAccessNamespaceConstant, MIRAccessConstField, MIRLoadFieldDefaultValue, MIRAccessCapturedVariable, MIRAccessArgVariable, MIRAccessLocalVariable, MIRConstructorPrimary, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionSingletons, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionMixed, MIRConstructorTuple, MIRConstructorRecord, MIRConstructorLambda, MIRCallNamespaceFunction, MIRCallStaticFunction, MIRAccessFromIndex, MIRProjectFromIndecies, MIRAccessFromProperty, MIRAccessFromField, MIRProjectFromProperties, MIRProjectFromFields, MIRProjectFromTypeTuple, MIRProjectFromTypeRecord, MIRProjectFromTypeConcept, MIRModifyWithIndecies, MIRModifyWithProperties, MIRModifyWithFields, MIRStructuredExtendTuple, MIRStructuredExtendRecord, MIRStructuredExtendObject, MIRInvokeKnownTarget, MIRInvokeVirtualTarget, MIRCallLambda, MIRPrefixOp, MIRBinOp, MIRBinCmp, MIRBinEq, MIRRegAssign, MIRVarStore, MIRReturnAssign, MIRJump, MIRJumpCond, MIRJumpNone, MIRVarLifetimeStart, MIRVarLifetimeEnd, MIRTruthyConvert, MIRDebug, MIRPhi, MIRVarLocal, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRIsTypeOf, MIRLogicStore, MIRAbort } from "../compiler/mir_ops";

import * as assert from "assert";
import { BuiltinCalls, BuiltinCallSig } from "./builtins";

class Interpreter {
    private m_env: Environment;
    private m_ep: (call: LambdaValue, cargs: Value[]) => Value;

    private m_doInvariantCheck: boolean;
    private m_doPrePostCheck: boolean;
    private m_doAssertCheck: boolean;

    constructor(assembly: MIRAssembly, invCheck: boolean, prePostCheck: boolean, assertEnabled: boolean) {
        this.m_env = new Environment(assembly);

        this.m_ep = (call: LambdaValue, cargs: Value[]): Value => Interpreter.evaluateReEntrantCall(this, call, cargs);

        this.m_doInvariantCheck = invCheck;
        this.m_doPrePostCheck = prePostCheck;
        this.m_doAssertCheck = assertEnabled;
    }

    private getArgValue(fscope: FunctionScope, arg: MIRArgument): Value {
        if (arg instanceof MIRRegisterArgument) {
            if (arg instanceof MIRTempRegister) {
                return fscope.lookupTmpReg(arg.regID);
            }
            else {
                return fscope.lookupVar(arg.nameID);
            }
        }
        else {
            if (arg instanceof MIRConstantNone) {
                return undefined;
            }
            else if (arg instanceof MIRConstantTrue) {
                return true;
            }
            else if (arg instanceof MIRConstantFalse) {
                return false;
            }
            else if (arg instanceof MIRConstantInt) {
                return Number.parseInt(arg.value);
            }
            else {
                assert(arg instanceof MIRConstantString);
                return ValueOps.unescapeString((arg as MIRConstantString).value);
            }
        }
    }

    private checkPreConds(file: string, conds: MIRBody[], args: Map<string, Value>) {
        if (this.m_doPrePostCheck && conds.length !== 0) {
            const cok = conds.every((cond) => {
                const cres = this.evaluateNakedMIRBody(file, cond, args);
                return typeof (cres) === "boolean" && cres;
            });

            if (!cok) {
                throw new PrePostError(true);
            }
        }
    }

    private checkPostConds(file: string, conds: MIRBody[], args: Map<string, Value>, result: Value) {
        if (this.m_doPrePostCheck && conds.length !== 0) {
            const argswres = new Map<string, Value>(args).set("_return_", result);
            const cok = conds.every((cond) => {
                const cres = this.evaluateNakedMIRBody(file, cond, argswres);
                return typeof (cres) === "boolean" && cres;
            });

            if (!cok) {
                throw new PrePostError(false);
            }
        }
    }

    private checkInvariants(entity: MIREntityTypeDecl, evalue: EntityValueSimple) {
        if (this.m_doPrePostCheck && entity.invariants.length !== 0) {
            const args = new Map<string, Value>().set("this", evalue);
            const cok = entity.invariants.every((cond) => {
                const cres = this.evaluateNakedMIRBody(entity.srcFile, cond, args);
                return typeof (cres) === "boolean" && cres;
            });

            if (!cok) {
                throw new InvariantError(entity.ns + "::" + entity.name);
            }
        }
    }

    private evaluateNakedMIRBody(file: string, mirbody: MIRBody, args?: Map<string, Value>): Value {
        this.m_env.pushCallFrame(args || new Map<string, Value>(), new Map<string, Value>(), mirbody, file);
        this.evaluateOpFlows();
        const result = this.m_env.getActiveScope().lookupVar("_return_");
        this.m_env.popCallFrame();

        return result;
    }

    private evaluateMirBody(invdecl: MIRInvokeDecl, args: Map<string, Value>, captured?: Map<string, Value>): Value {
        let result = undefined;

        const mirbody = invdecl.body as MIRBody;
        if (typeof (mirbody.body) === "string") {
            result = (BuiltinCalls.get(mirbody.body) as BuiltinCallSig).call(null, this.m_ep, invdecl, this.m_env.assembly, args);
        }
        else {
            this.m_env.pushCallFrame(args, captured || new Map<string, Value>(), mirbody, mirbody.file);
            this.checkPreConds(mirbody.file, invdecl.preconditions, args);

            this.evaluateOpFlows();
            result = this.m_env.getActiveScope().lookupVar("_return_");

            this.checkPostConds(mirbody.file, invdecl.postconditions, args, result);
            this.m_env.popCallFrame();
        }

        return result;
    }

    private static evaluateReEntrantCall(interpreter: Interpreter, v: LambdaValue, cargs: Value[]): Value {
        let args = new Map<string, Value>();
        for (let i = 0; i < v.invoke.params.length; ++i) {
            args.set(v.invoke.params[i].name, cargs[i]);
        }
        if (v.invoke.optRestName !== undefined) {
            args.set(v.invoke.optRestName, cargs[v.invoke.params.length]);
        }

        interpreter.m_env.pushCallFrame(args, v.capturedVars, v.invoke.body as MIRBody, v.invoke.srcFile);
        interpreter.evaluateOpFlows();
        const result = interpreter.m_env.getActiveScope().lookupVar("_return_");
        interpreter.m_env.popCallFrame();

        return result;
    }

    private evaluateCollectionConstructor_Empty(op: MIRConstructorPrimaryCollectionEmpty): Value {
        const ctype = MIREntityType.create(op.tkey);
        const ootype = this.m_env.assembly.entityMap.get(op.tkey) as MIREntityTypeDecl;

        if (ootype.name === "List") {
            return new ListValue(ctype, []);
        }
        else if (ootype.name === "HashSet") {
            return HashSetValue.create(ctype, []);
        }
        else {
            assert(ootype.name === "HashMap");

            return HashMapValue.create(ctype, [] as TupleValue[]);
        }
    }

    private evaluateCollectionConstructor_Singleton(op: MIRConstructorPrimaryCollectionSingletons, fscope: FunctionScope): Value {
        const ctype = MIREntityType.create(op.tkey);
        const args = op.args.map((arg) => this.getArgValue(fscope, arg));
        const ootype = this.m_env.assembly.entityMap.get(op.tkey) as MIREntityTypeDecl;

        if (ootype.name === "List") {
            return new ListValue(ctype, args);
        }
        else if (ootype.name === "HashSet") {
            return HashSetValue.create(ctype, args);
        }
        else {
            assert(ootype.name === "HashMap");

            return HashMapValue.create(ctype, args as TupleValue[]);
        }
    }

    private evaluateCollectionConstructor_Copy(op: MIRConstructorPrimaryCollectionCopies, fscope: FunctionScope): Value {
        const ctype = MIREntityType.create(op.tkey);
        const args = ([] as Value[]).concat(...op.args.map((arg) => ValueOps.getContainerContentsEnumeration(this.getArgValue(fscope, arg))));
        const ootype = this.m_env.assembly.entityMap.get(op.tkey) as MIREntityTypeDecl;

        if (ootype.name === "List") {
            return new ListValue(ctype, args);
        }
        else if (ootype.name === "HashSet") {
            return HashSetValue.create(ctype, args);
        }
        else {
            assert(ootype.name === "HashMap");

            return HashMapValue.create(ctype, args as TupleValue[]);
        }
    }

    private evaluateCollectionConstructor_Mixed(op: MIRConstructorPrimaryCollectionMixed, fscope: FunctionScope): Value {
        const ctype = MIREntityType.create(op.tkey);
        const args = ([] as Value[]).concat(...op.args.map((arg) => arg[0] ? ValueOps.getContainerContentsEnumeration(this.getArgValue(fscope, arg[1])) : [this.getArgValue(fscope, arg[1])]));
        const ootype = this.m_env.assembly.entityMap.get(op.tkey) as MIREntityTypeDecl;

        if (ootype.name === "List") {
            return new ListValue(ctype, args);
        }
        else if (ootype.name === "HashSet") {
            return HashSetValue.create(ctype, args);
        }
        else {
            assert(ootype.name === "HashMap");

            return HashMapValue.create(ctype, args as TupleValue[]);
        }
    }

    ///////////////////////////////////////////

    private evaluateOP(op: MIROp, fscope: FunctionScope) {
        fscope.setCurrentLine(op.sinfo.line);

        switch (op.tag) {
            case MIROpTag.LoadConst: {
                const lc = op as MIRLoadConst;
                fscope.assignTmpReg(lc.trgt.regID, this.getArgValue(fscope, lc.src));
                break;
            }
            case MIROpTag.LoadConstTypedString: {
                const lts = op as MIRLoadConstTypedString;
                const oftype = (this.m_env.assembly.entityMap.get(lts.tkey) || this.m_env.assembly.conceptMap.get(lts.tkey)) as MIROOTypeDecl;
                fscope.assignTmpReg(lts.trgt.regID, new TypedStringValue(oftype, this.m_env.assembly.typeMap.get(lts.tskey) as MIRType, ValueOps.unescapeTypedString(lts.ivalue)));
                break;
            }
            case MIROpTag.AccessNamespaceConstant: {
                const lg = op as MIRAccessNamespaceConstant;
                const gval = this.m_env.assembly.globalDecls.get(lg.gkey) as MIRGlobalDecl;
                fscope.assignTmpReg(lg.trgt.regID, this.evaluateNakedMIRBody(gval.srcFile, gval.value));
                break;
            }
            case MIROpTag.AccessConstField: {
                const lcf = op as MIRAccessConstField;
                const cval = this.m_env.assembly.constDecls.get(lcf.ckey) as MIRConstDecl;
                fscope.assignTmpReg(lcf.trgt.regID, this.evaluateNakedMIRBody(cval.srcFile, cval.value as MIRBody));
                break;
            }
            case MIROpTag.LoadFieldDefaultValue: {
                const lcf = op as MIRLoadFieldDefaultValue;
                const cval = this.m_env.assembly.memberFields.get(lcf.fkey) as MIRFieldDecl;
                fscope.assignTmpReg(lcf.trgt.regID, this.evaluateNakedMIRBody(cval.srcFile, cval.value as MIRBody));
                break;
            }
            case MIROpTag.AccessCapturedVariable: {
                const lcv = op as MIRAccessCapturedVariable;
                fscope.assignTmpReg(lcv.trgt.regID, fscope.lookupVar(lcv.name.nameID));
                break;
            }
            case MIROpTag.AccessArgVariable: {
                const lav = op as MIRAccessArgVariable;
                fscope.assignTmpReg(lav.trgt.regID, fscope.lookupVar(lav.name.nameID));
                break;
            }
            case MIROpTag.AccessLocalVariable: {
                const llv = op as MIRAccessLocalVariable;
                fscope.assignTmpReg(llv.trgt.regID, fscope.lookupVar(llv.name.nameID));
                break;
            }
            case MIROpTag.ConstructorPrimary: {
                const cp = op as MIRConstructorPrimary;
                const ctype = this.m_env.assembly.entityMap.get(cp.tkey) as MIREntityTypeDecl;
                const fvals = cp.args.map<[string, Value]>((arg, i) => [ctype.fieldLayout[i], this.getArgValue(fscope, arg)]);
                const evalue = new EntityValueSimple(MIREntityType.create(cp.tkey), fvals);
                if (this.m_doInvariantCheck) {
                    this.checkInvariants(ctype, evalue);
                }
                fscope.assignTmpReg(cp.trgt.regID, evalue);
                break;
            }
            case MIROpTag.ConstructorPrimaryCollectionEmpty: {
                const cc = op as MIRConstructorPrimaryCollectionEmpty;
                const cvalue = this.evaluateCollectionConstructor_Empty(cc);
                fscope.assignTmpReg(cc.trgt.regID, cvalue);
                break;
            }
            case MIROpTag.ConstructorPrimaryCollectionSingletons: {
                const cc = op as MIRConstructorPrimaryCollectionSingletons;
                const cvalue = this.evaluateCollectionConstructor_Singleton(cc, fscope);
                fscope.assignTmpReg(cc.trgt.regID, cvalue);
                break;
            }
            case MIROpTag.ConstructorPrimaryCollectionCopies: {
                const cc = op as MIRConstructorPrimaryCollectionCopies;
                const cvalue = this.evaluateCollectionConstructor_Copy(cc, fscope);
                fscope.assignTmpReg(cc.trgt.regID, cvalue);
                break;
            }
            case MIROpTag.ConstructorPrimaryCollectionMixed: {
                const cc = op as MIRConstructorPrimaryCollectionMixed;
                const cvalue = this.evaluateCollectionConstructor_Mixed(cc, fscope);
                fscope.assignTmpReg(cc.trgt.regID, cvalue);
                break;
            }
            case MIROpTag.ConstructorTuple: {
                const tc = op as MIRConstructorTuple;
                let tentries: MIRTupleTypeEntry[] = [];
                let tvalues: Value[] = [];
                for (let i = 0; i < tc.args.length; ++i) {
                    const v = this.getArgValue(fscope, tc.args[i]);
                    tentries.push(new MIRTupleTypeEntry(ValueOps.getValueType(v), false));
                    tvalues.push(v);
                }
                fscope.assignTmpReg(tc.trgt.regID, new TupleValue(MIRTupleType.create(false, tentries), tvalues));
                break;
            }
            case MIROpTag.ConstructorRecord: {
                const tc = op as MIRConstructorRecord;
                let tentries: MIRRecordTypeEntry[] = [];
                let tvalues: [string, Value][] = [];
                for (let i = 0; i < tc.args.length; ++i) {
                    const f = tc.args[i][0];
                    const v = this.getArgValue(fscope, tc.args[i][1]);
                    tentries.push(new MIRRecordTypeEntry(f, ValueOps.getValueType(v), false));
                    tvalues.push([f, v]);
                }
                fscope.assignTmpReg(tc.trgt.regID, new RecordValue(MIRRecordType.create(false, tentries), tvalues));
                break;
            }
            case MIROpTag.ConstructorLambda: {
                const lc = op as MIRConstructorLambda;
                const linvoke = this.m_env.assembly.lambdaDecls.get(lc.lkey) as MIRInvokeDecl;
                const lsig = (this.m_env.assembly.typeMap.get(lc.lsigkey) as MIRType).options[0] as MIRFunctionType;
                let captured = new Map<string, Value>();
                linvoke.captured.forEach((v, k) => {
                    captured.set(k, fscope.lookupVar(k));
                });

                fscope.assignTmpReg(lc.trgt.regID, new LambdaValue(lsig, linvoke, captured));
                break;
            }
            case MIROpTag.CallNamespaceFunction: {
                const fc = op as MIRCallNamespaceFunction;
                const fdecl = this.m_env.assembly.functionDecls.get(fc.fkey) as MIRFunctionDecl;
                let args = new Map<string, Value>();
                for (let i = 0; i < fdecl.invoke.params.length; ++i) {
                    args.set(fdecl.invoke.params[i].name, this.getArgValue(fscope, fc.args[i]));
                }
                if (fdecl.invoke.optRestName !== undefined) {
                    args.set(fdecl.invoke.optRestName, this.getArgValue(fscope, fc.args[fdecl.invoke.params.length]));
                }
                fscope.assignTmpReg(fc.trgt.regID, this.evaluateMirBody(fdecl.invoke, args));
                break;
            }
            case MIROpTag.CallStaticFunction: {
                const fc = op as MIRCallStaticFunction;
                const fdecl = this.m_env.assembly.staticDecls.get(fc.skey) as MIRStaticDecl;
                let args = new Map<string, Value>();
                for (let i = 0; i < fdecl.invoke.params.length; ++i) {
                    args.set(fdecl.invoke.params[i].name, this.getArgValue(fscope, fc.args[i]));
                }
                if (fdecl.invoke.optRestName !== undefined) {
                    args.set(fdecl.invoke.optRestName, this.getArgValue(fscope, fc.args[fdecl.invoke.params.length]));
                }
                fscope.assignTmpReg(fc.trgt.regID, this.evaluateMirBody(fdecl.invoke, args));
                break;
            }
            case MIROpTag.MIRAccessFromIndex: {
                const ai = op as MIRAccessFromIndex;
                fscope.assignTmpReg(ai.trgt.regID, (this.getArgValue(fscope, ai.arg) as TupleValue).values[ai.idx]);
                break;
            }
            case MIROpTag.MIRProjectFromIndecies: {
                const pi = op as MIRProjectFromIndecies;
                const arg = this.getArgValue(fscope, pi.arg) as TupleValue;
                let tentries: MIRTupleTypeEntry[] = [];
                let tvalues: Value[] = [];
                for (let i = 0; i < pi.indecies.length; ++i) {
                    tentries.push(new MIRTupleTypeEntry(ValueOps.getValueType(arg.values[pi.indecies[i]]), false));
                    tvalues.push(arg.values[pi.indecies[i]]);
                }
                fscope.assignTmpReg(pi.trgt.regID, new TupleValue(MIRTupleType.create(false, tentries), tvalues));
                break;
            }
            case MIROpTag.MIRAccessFromProperty: {
                const ap = op as MIRAccessFromProperty;
                const arg = this.getArgValue(fscope, ap.arg) as RecordValue;
                const pidx = arg.values.findIndex((kv) => kv[0] === ap.property);
                fscope.assignTmpReg(ap.trgt.regID, pidx !== -1 ? arg.values[pidx][1] : undefined);
                break;
            }
            case MIROpTag.MIRProjectFromProperties: {
                const pi = op as MIRProjectFromProperties;
                const arg = this.getArgValue(fscope, pi.arg) as RecordValue;
                let rentries: MIRRecordTypeEntry[] = [];
                let rvalues: [string, Value][] = [];
                for (let i = 0; i < pi.properties.length; ++i) {
                    const pidx = arg.values.findIndex((av) => av[0] === pi.properties[i]);
                    rentries.push(new MIRRecordTypeEntry(pi.properties[i], ValueOps.getValueType(pidx !== -1 ? arg.values[pidx][1] : undefined), false));
                    rvalues.push(pidx !== -1 ? arg.values[pidx] : [pi.properties[i], undefined]);
                }
                fscope.assignTmpReg(pi.trgt.regID, new RecordValue(MIRRecordType.create(false, rentries), rvalues));
                break;
            }
            case MIROpTag.MIRAccessFromField: {
                const af = op as MIRAccessFromField;
                const arg = this.getArgValue(fscope, af.arg) as EntityValueSimple;
                fscope.assignTmpReg(af.trgt.regID, (arg.fields.find((kv) => kv[0] === af.field) as [string, Value])[1]);
                break;
            }
            case MIROpTag.MIRProjectFromFields: {
                const pf = op as MIRProjectFromFields;
                const arg = this.getArgValue(fscope, pf.arg) as EntityValueSimple;
                let rentries: MIRRecordTypeEntry[] = [];
                let rvalues: [string, Value][] = [];
                for (let i = 0; i < pf.fields.length; ++i) {
                    const fidx = arg.fields.findIndex((av) => av[0] === pf.fields[i]);
                    rentries.push(new MIRRecordTypeEntry(pf.fields[i], ValueOps.getValueType(fidx !== -1 ? arg.fields[fidx][1] : undefined), false));
                    rvalues.push(fidx !== -1 ? arg.fields[fidx] : [pf.fields[i], undefined]);
                }
                fscope.assignTmpReg(pf.trgt.regID, new RecordValue(MIRRecordType.create(false, rentries), rvalues));
                break;
            }
            case MIROpTag.MIRProjectFromTypeTuple: {
                const pt = op as MIRProjectFromTypeTuple;
                const projectType = (this.m_env.assembly.typeMap.get(pt.ptype) as MIRType).options[0] as MIRTupleType;
                const arg = this.getArgValue(fscope, pt.arg) as TupleValue;
                if (projectType.isOpen) {
                    fscope.assignTmpReg(pt.trgt.regID, new TupleValue(arg.ttype, [...arg.values]));
                }
                else {
                    let tentries: MIRTupleTypeEntry[] = [];
                    let tvalues: Value[] = [];
                    for (let i = 0; i < projectType.entries.length && i < arg.values.length; ++i) {
                        tentries.push(arg.ttype.entries[i]);
                        tvalues.push(arg.values[i]);
                    }
                    fscope.assignTmpReg(pt.trgt.regID, new TupleValue(MIRTupleType.create(false, tentries), tvalues));
                }
                break;
            }
            case MIROpTag.MIRProjectFromTypeRecord: {
                const pr = op as MIRProjectFromTypeRecord;
                const projectType = (this.m_env.assembly.typeMap.get(pr.ptype) as MIRType).options[0] as MIRRecordType;
                const arg = this.getArgValue(fscope, pr.arg) as RecordValue;
                if (projectType.isOpen) {
                    fscope.assignTmpReg(pr.trgt.regID, new RecordValue(arg.rtype, [...arg.values]));
                }
                else {
                    let rentries: MIRRecordTypeEntry[] = [];
                    let rvalues: [string, Value][] = [];
                    for (let i = 0; i < projectType.entries.length; ++i) {
                        const ridx = arg.values.findIndex((rv) => rv[0] === projectType.entries[i].name);
                        if (ridx !== -1) {
                            rentries.push(arg.rtype.entries[ridx]);
                            rvalues.push(arg.values[ridx]);
                        }
                    }
                    fscope.assignTmpReg(pr.trgt.regID, new RecordValue(MIRRecordType.create(false, rentries), rvalues));
                }
                break;
            }
            case MIROpTag.MIRProjectFromTypeConcept: {
                const pc = op as MIRProjectFromTypeConcept;
                const arg = this.getArgValue(fscope, pc.arg) as EntityValueSimple;
                const projectfields = new Set<string>();
                pc.ctypes.map((ckey) => this.m_env.assembly.conceptMap.get(ckey) as MIRConceptTypeDecl).forEach((cdecl) => cdecl.fieldMap.forEach((v, k) => projectfields.add(k)));

                let rentries: MIRRecordTypeEntry[] = [];
                let rvalues: [string, Value][] = [];
                [...projectfields].sort().forEach((f) => {
                    const pv = (arg.fields.find((kv) => kv[0] === f) as [string, Value])[1];
                    rentries.push(new MIRRecordTypeEntry(f, ValueOps.getValueType(pv), false));
                    rvalues.push([f, pv]);
                });
                fscope.assignTmpReg(pc.trgt.regID, new RecordValue(MIRRecordType.create(false, rentries), rvalues));
                break;
            }
            case MIROpTag.MIRModifyWithIndecies: {
                const mi = op as MIRModifyWithIndecies;
                const arg = this.getArgValue(fscope, mi.arg) as TupleValue;
                let tentries = [...arg.ttype.entries];
                let tvalues = [...arg.values];
                for (let i = 0; i < mi.updates.length; ++i) {
                    const update = mi.updates[i];
                    if (update[0] >= tentries.length) {
                        let extendCount = (update[0] - tentries.length) + 1;
                        for (let j = 0; j < extendCount; ++j) {
                            tentries.push(new MIRTupleTypeEntry(ValueOps.getValueType(undefined), false));
                            tvalues.push(undefined);
                        }
                    }
                    const uarg = this.getArgValue(fscope, update[1]);
                    tentries[update[0]] = new MIRTupleTypeEntry(ValueOps.getValueType(uarg), false);
                    tvalues[update[0]] = uarg;
                }
                fscope.assignTmpReg(mi.trgt.regID, new TupleValue(MIRTupleType.create(false, tentries), tvalues));
                break;
            }
            case MIROpTag.MIRModifyWithProperties: {
                const mp = op as MIRModifyWithProperties;
                const arg = this.getArgValue(fscope, mp.arg) as RecordValue;
                let rentries = [...arg.rtype.entries];
                let rvalues = [...arg.values];
                for (let i = 0; i < mp.updates.length; ++i) {
                    const pname = mp.updates[i][0];
                    const pvalue = this.getArgValue(fscope, mp.updates[i][1]);
                    const pidx = rentries.findIndex((entry) => entry.name === pname);
                    if (pidx !== -1) {
                        rentries[pidx] = new MIRRecordTypeEntry(pname, ValueOps.getValueType(pvalue), false);
                        rvalues[pidx] = [pname, pvalue];
                    }
                    else {
                        rentries.push(new MIRRecordTypeEntry(pname, ValueOps.getValueType(pvalue), false));
                        rvalues.push([pname, pvalue]);
                    }
                }
                rentries.sort((a, b) => a.name.localeCompare(b.name));
                rvalues.sort((a, b) => a[0].localeCompare(b[0]));
                fscope.assignTmpReg(mp.trgt.regID, new RecordValue(MIRRecordType.create(false, rentries), rvalues));
                break;
            }
            case MIROpTag.MIRModifyWithFields: {
                const mf = op as MIRModifyWithFields;
                const arg = this.getArgValue(fscope, mf.arg) as EntityValueSimple;
                let fvals = [...arg.fields];
                for (let i = 0; i < mf.updates.length; ++i) {
                    const fidx = fvals.findIndex((entry) => entry[0] === mf.updates[i][0]);
                    fvals[fidx] = [mf.updates[i][0], this.getArgValue(fscope, mf.updates[i][1])];
                }
                const evalue = new EntityValueSimple(arg.etype, fvals);
                if (this.m_doInvariantCheck) {
                    this.checkInvariants(this.m_env.assembly.entityMap.get(evalue.etype.ekey) as MIREntityTypeDecl, evalue);
                }
                fscope.assignTmpReg(mf.trgt.regID, evalue);
                break;
            }
            case MIROpTag.MIRStructuredExtendTuple: {
                const st = op as MIRStructuredExtendTuple;
                const arg = this.getArgValue(fscope, st.arg) as TupleValue;
                const ext = this.getArgValue(fscope, st.update) as TupleValue;
                const ntuple = new TupleValue(MIRTupleType.create(false, [...arg.ttype.entries, ...ext.ttype.entries]), [...arg.values, ...ext.values]);
                fscope.assignTmpReg(st.trgt.regID, ntuple);
                break;
            }
            case MIROpTag.MIRStructuredExtendRecord: {
                const sr = op as MIRStructuredExtendRecord;
                const arg = this.getArgValue(fscope, sr.arg) as RecordValue;
                const ext = this.getArgValue(fscope, sr.update) as RecordValue;
                let rentries = [...arg.rtype.entries];
                let rvalues = [...arg.values];
                for (let i = 0; i < ext.rtype.entries.length; ++i) {
                    const pname = ext.rtype.entries[i].name;
                    const pidx = rentries.findIndex((entry) => entry.name === pname);
                    if (pidx !== -1) {
                        rentries[pidx] = ext.rtype.entries[i];
                        rvalues[pidx] = ext.values[i];
                    }
                    else {
                        rentries.push(ext.rtype.entries[i]);
                        rvalues.push(ext.values[i]);
                    }
                }
                rentries.sort((a, b) => a.name.localeCompare(b.name));
                rvalues.sort((a, b) => a[0].localeCompare(b[0]));
                fscope.assignTmpReg(sr.trgt.regID, new RecordValue(MIRRecordType.create(false, rentries), rvalues));
                break;
            }
            case MIROpTag.MIRStructuredExtendObject: {
                const so = op as MIRStructuredExtendObject;
                const arg = this.getArgValue(fscope, so.arg) as EntityValueSimple;
                const ext = this.getArgValue(fscope, so.update) as RecordValue;
                let fvals = [...arg.fields];
                for (let i = 0; i < ext.rtype.entries.length; ++i) {
                    const fidx = fvals.findIndex((entry) => entry[0] === ext.rtype.entries[i].name);
                    fvals[fidx] = [ext.rtype.entries[i].name, ext.values[i][1]];
                }
                const evalue = new EntityValueSimple(arg.etype, fvals);
                if (this.m_doInvariantCheck) {
                    this.checkInvariants(this.m_env.assembly.entityMap.get(evalue.etype.ekey) as MIREntityTypeDecl, evalue);
                }
                fscope.assignTmpReg(so.trgt.regID, evalue);
                break;
            }
            case MIROpTag.MIRInvokeKnownTarget: {
                const invk = op as MIRInvokeKnownTarget;
                const fdecl = this.m_env.assembly.methodDecls.get(invk.mkey) as MIRMethodDecl;
                let args = new Map<string, Value>();
                for (let i = 0; i < fdecl.invoke.params.length; ++i) {
                    args.set(fdecl.invoke.params[i].name, this.getArgValue(fscope, invk.args[i]));
                }
                if (fdecl.invoke.optRestName !== undefined) {
                    args.set(fdecl.invoke.optRestName, this.getArgValue(fscope, invk.args[fdecl.invoke.params.length]));
                }
                fscope.assignTmpReg(invk.trgt.regID, this.evaluateMirBody(fdecl.invoke, args));
                break;
            }
            case MIROpTag.MIRInvokeVirtualTarget: {
                const invk = op as MIRInvokeVirtualTarget;
                const tvalue = this.getArgValue(fscope, invk.args[0]);
                const ttype = ValueOps.getValueType(tvalue).options[0] as MIREntityType;

                const edecl = this.m_env.assembly.entityMap.get(ttype.ekey) as MIREntityTypeDecl;
                const fdecl = edecl.vcallMap.get(invk.vresolve) as MIRMethodDecl;

                let args = new Map<string, Value>();
                for (let i = 0; i < fdecl.invoke.params.length; ++i) {
                    args.set(fdecl.invoke.params[i].name, this.getArgValue(fscope, invk.args[i]));
                }
                if (fdecl.invoke.optRestName !== undefined) {
                    args.set(fdecl.invoke.optRestName, this.getArgValue(fscope, invk.args[fdecl.invoke.params.length]));
                }
                fscope.assignTmpReg(invk.trgt.regID, this.evaluateMirBody(fdecl.invoke, args));
                break;
            }
            case MIROpTag.MIRCallLambda: {
                const cl = op as MIRCallLambda;
                const lvalue = this.getArgValue(fscope, cl.lambda) as LambdaValue;
                let args = new Map<string, Value>();
                for (let i = 0; i < lvalue.invoke.params.length; ++i) {
                    args.set(lvalue.invoke.params[i].name, this.getArgValue(fscope, cl.args[i]));
                }
                if (lvalue.invoke.optRestName !== undefined) {
                    args.set(lvalue.invoke.optRestName, this.getArgValue(fscope, cl.args[lvalue.invoke.params.length]));
                }
                let captured = new Map<string, Value>(lvalue.capturedVars);
                fscope.assignTmpReg(cl.trgt.regID, this.evaluateMirBody(lvalue.invoke, args, captured));
                break;
            }
            case MIROpTag.MIRPrefixOp: {
                const pfx = op as MIRPrefixOp;
                const pvalue = this.getArgValue(fscope, pfx.arg);
                if (pfx.op === "!") {
                    fscope.assignTmpReg(pfx.trgt.regID, !ValueOps.convertBoolOrNoneToBool(pvalue));
                }
                else {
                    fscope.assignTmpReg(pfx.trgt.regID, pfx.op === "-" ? -(pvalue as number) : pvalue);
                }
                break;
            }
            case MIROpTag.MIRBinOp: {
                const bop = op as MIRBinOp;
                const lhv = this.getArgValue(fscope, bop.lhs) as number;
                const rhv = this.getArgValue(fscope, bop.rhs) as number;
                switch (bop.op) {
                    case "+":
                        fscope.assignTmpReg(bop.trgt.regID, lhv + rhv);
                        break;
                    case "-":
                        fscope.assignTmpReg(bop.trgt.regID, lhv - rhv);
                        break;
                    case "*":
                        fscope.assignTmpReg(bop.trgt.regID, lhv * rhv);
                        break;
                    case "/":
                        fscope.assignTmpReg(bop.trgt.regID, Math.floor(lhv / rhv));
                        break;
                    default:
                        fscope.assignTmpReg(bop.trgt.regID, lhv % rhv);
                        break;
                }
                break;
            }
            case MIROpTag.MIRBinEq: {
                const beq = op as MIRBinEq;
                const lhv = this.getArgValue(fscope, beq.lhs);
                const rhv = this.getArgValue(fscope, beq.rhs);
                const eq = ValueOps.valueEqualTo(lhv, rhv);
                fscope.assignTmpReg(beq.trgt.regID, (beq.op === "!=") ? !eq : eq);
                break;
            }
            case MIROpTag.MIRBinCmp: {
                const bcp = op as MIRBinCmp;
                const lhv = this.getArgValue(fscope, bcp.lhs);
                const rhv = this.getArgValue(fscope, bcp.rhs);

                if (bcp.op === "<" || bcp.op === "<=") {
                    const lt = ValueOps.valueLessThan(lhv, rhv);
                    fscope.assignTmpReg(bcp.trgt.regID, (bcp.op === "<") ? lt : lt || ValueOps.valueEqualTo(lhv, rhv));
                }
                else {
                    const gt = ValueOps.valueLessThan(rhv, lhv);
                    fscope.assignTmpReg(bcp.trgt.regID, (bcp.op === ">") ? gt : gt || ValueOps.valueEqualTo(rhv, lhv));
                }
                break;
            }
            case MIROpTag.MIRIsTypeOfNone: {
                const ton = op as MIRIsTypeOfNone;
                const argv = this.getArgValue(fscope, ton.arg);
                fscope.assignTmpReg(ton.trgt.regID, argv === undefined);
                break;
            }
            case MIROpTag.MIRIsTypeOfSome: {
                const tos = op as MIRIsTypeOfSome;
                const argv = this.getArgValue(fscope, tos.arg);
                fscope.assignTmpReg(tos.trgt.regID, argv !== undefined);
                break;
            }
            case MIROpTag.MIRIsTypeOf: {
                const tog = op as MIRIsTypeOf;
                const argv = this.getArgValue(fscope, tog.arg);
                const istype = this.m_env.assembly.typeMap.get(tog.oftype) as MIRType;
                fscope.assignTmpReg(tog.trgt.regID, this.m_env.assembly.subtypeOf(ValueOps.getValueType(argv), istype));
                break;
            }
            case MIROpTag.MIRRegAssign: {
                const regop = op as MIRRegAssign;
                fscope.assignTmpReg(regop.trgt.regID, this.getArgValue(fscope, regop.src));
                break;
            }
            case MIROpTag.MIRTruthyConvert: {
                const tcop = op as MIRTruthyConvert;
                fscope.assignTmpReg(tcop.trgt.regID, ValueOps.convertBoolOrNoneToBool(this.getArgValue(fscope, tcop.src)));
                break;
            }
            case MIROpTag.MIRLogicStore: {
                const llop = op as MIRLogicStore;
                const lhv = this.getArgValue(fscope, llop.lhs) as boolean;
                const rhv = this.getArgValue(fscope, llop.rhs) as boolean;
                fscope.assignTmpReg(llop.trgt.regID, llop.op === "&" ? (lhv && rhv) : (lhv || rhv));
                break;
            }
            case MIROpTag.MIRVarStore: {
                const vs = op as MIRVarStore;
                fscope.assignVar(vs.name.nameID, this.getArgValue(fscope, vs.src));
                break;
            }
            case MIROpTag.MIRReturnAssign: {
                const ra = op as MIRReturnAssign;
                fscope.assignVar(ra.name.nameID, this.getArgValue(fscope, ra.src));
                break;
            }
            case MIROpTag.MIRAbort: {
                const abrt = op as MIRAbort;
                if (this.m_doAssertCheck || abrt.releaseEnable) {
                    raiseRuntimeError();
                }
                break;
            }
            case MIROpTag.MIRDebug: {
                const dbg = op as MIRDebug;
                if (dbg.value === undefined) {
                    throw new NotImplementedRuntimeError("MIRDebug -- debug attach");
                }
                else {
                    const pval = this.getArgValue(fscope, dbg.value);
                    process.stdout.write(ValueOps.diagnosticPrintValue(pval) + "\n");
                }
                break;
            }
            case MIROpTag.MIRJump: {
                const jop = op as MIRJump;
                fscope.setLastJumpSource();
                fscope.setActiveBlock(jop.trgtblock);
                break;
            }
            case MIROpTag.MIRJumpCond: {
                const cjop = op as MIRJumpCond;
                const bv = ValueOps.convertBoolOrNoneToBool(this.getArgValue(fscope, cjop.arg));
                fscope.setLastJumpSource();
                fscope.setActiveBlock(bv ? cjop.trueblock : cjop.falseblock);
                break;
            }
            case MIROpTag.MIRJumpNone: {
                const njop = op as MIRJumpNone;
                const bv = this.getArgValue(fscope, njop.arg) === undefined;
                fscope.setLastJumpSource();
                fscope.setActiveBlock(bv ? njop.noneblock : njop.someblock);
                break;
            }
            case MIROpTag.MIRPhi: {
                const pop = op as MIRPhi;
                const uvar = pop.src.get(fscope.getLastJumpSource()) as MIRRegisterArgument;
                if (pop.trgt instanceof MIRTempRegister) {
                    fscope.assignTmpReg(pop.trgt.regID, this.getArgValue(fscope, uvar));
                }
                else {
                    assert(pop.trgt instanceof MIRVarLocal);

                    fscope.assignVar(pop.trgt.nameID, this.getArgValue(fscope, uvar));
                }
                break;
            }
            case MIROpTag.MIRVarLifetimeStart: {
                const vlstart = op as MIRVarLifetimeStart;
                fscope.declareVar(vlstart.name, undefined);
                break;
            }
            case MIROpTag.MIRVarLifetimeEnd: {
                const vlend = op as MIRVarLifetimeEnd;
                fscope.clearVar(vlend.name);
                break;
            }
            default:
                raiseRuntimeError();
                break;
        }
    }

    private evaluateBlock(block: MIROp[], fscope: FunctionScope) {
        for (let i = 0; i < block.length; ++i) {
            this.evaluateOP(block[i], fscope);
        }
    }

    private evaluateOpFlows() {
        let fscope: FunctionScope = this.m_env.getActiveScope();
        fscope.setActiveBlock("entry");
        while (fscope.getActiveBlock().label !== "exit") {
            const blck = fscope.getActiveOps();
            this.evaluateBlock(blck, fscope);
        }

        this.evaluateBlock(fscope.getActiveOps(), fscope);
    }

    evaluateRootNamespaceCall(ns: string, func: string, cargs: Value[]): Value {
        const fdecl = this.m_env.assembly.functionDecls.get(`${ns}::${func}`) as MIRFunctionDecl;

        let args = new Map<string, Value>();
        for (let i = 0; i < fdecl.invoke.params.length; ++i) {
            args.set(fdecl.invoke.params[i].name, cargs[i]);
        }

        return this.evaluateMirBody(fdecl.invoke, args);
    }
}

export { Interpreter };
