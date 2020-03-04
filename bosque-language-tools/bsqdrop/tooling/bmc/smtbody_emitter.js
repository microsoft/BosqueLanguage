"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const mir_assembly_1 = require("../../compiler/mir_assembly");
const mir_ops_1 = require("../../compiler/mir_ops");
const smt_exp_1 = require("./smt_exp");
const assert = require("assert");
function NOT_IMPLEMENTED(msg) {
    throw new Error(`Not Implemented: ${msg}`);
}
class SMTBodyEmitter {
    constructor(assembly, typegen) {
        this.standard_gas = 4;
        this.collection_gas = 5;
        this.string_gas = 10;
        this.regex_gas = 3;
        this.errorCodes = new Map();
        this.gasLimits = new Map().set("default", this.standard_gas).set("collection", this.collection_gas).set("string", this.string_gas).set("regex", this.regex_gas);
        this.currentFile = "[No File]";
        this.tmpvarctr = 0;
        this.currentSCC = new Set();
        this.vtypes = new Map();
        this.subtypeOrderCtr = 0;
        this.subtypeFMap = new Map();
        this.vfieldLookups = [];
        this.vfieldProjects = [];
        this.vfieldUpdates = [];
        this.vobjmerges = [];
        this.assembly = assembly;
        this.typegen = typegen;
        this.currentRType = typegen.noneType;
    }
    generateTempName() {
        return `@tmpvar@${this.tmpvarctr++}`;
    }
    generateErrorCreate(sinfo, rtype) {
        const errorinfo = `${this.currentFile} @ line ${sinfo.line} -- column ${sinfo.column}`;
        if (!this.errorCodes.has(errorinfo)) {
            this.errorCodes.set(errorinfo, this.errorCodes.size);
        }
        const errid = this.errorCodes.get(errorinfo);
        return new smt_exp_1.SMTValue(`(result_error@${rtype} (result_error ${errid}))`);
    }
    getErrorIds(...sinfos) {
        const ekeys = sinfos.map((sinfo) => `${this.currentFile} @ line ${sinfo.line} -- column ${sinfo.column}`);
        return [...new Set(ekeys.map((k) => this.errorCodes.get(k)))].sort();
    }
    getGasKeyForOperation(ikey) {
        if (ikey.startsWith("NSCore::List<") || ikey.startsWith("NSCore::Set<") || ikey.startsWith("NSCore::Map<")) {
            return "collection";
        }
        else if (ikey.startsWith("NSCore::String")) {
            return "string";
        }
        else if (ikey.startsWith("NSCore::Regex")) {
            return "regex";
        }
        else {
            return "default";
        }
    }
    getGasForOperation(ikey) {
        return this.gasLimits.get(this.getGasKeyForOperation(ikey));
    }
    generateBMCLimitCreate(ikey, rtype) {
        const errid = this.getGasKeyForOperation(ikey);
        return new smt_exp_1.SMTValue(`(result_error@${rtype} (result_bmc "${errid}"))`);
    }
    varNameToSMTName(name) {
        if (name === "_return_") {
            return "_return_";
        }
        else {
            return this.typegen.mangleStringForSMT(name);
        }
    }
    varToSMTName(varg) {
        return this.varNameToSMTName(varg.nameID);
    }
    invokenameToSMT(ivk) {
        return this.typegen.mangleStringForSMT(ivk);
    }
    getArgType(arg) {
        if (arg instanceof mir_ops_1.MIRRegisterArgument) {
            return this.vtypes.get(arg.nameID);
        }
        else {
            if (arg instanceof mir_ops_1.MIRConstantNone) {
                return this.typegen.noneType;
            }
            else if (arg instanceof mir_ops_1.MIRConstantTrue || arg instanceof mir_ops_1.MIRConstantFalse) {
                return this.typegen.boolType;
            }
            else if (arg instanceof mir_ops_1.MIRConstantInt) {
                return this.typegen.intType;
            }
            else {
                return this.typegen.stringType;
            }
        }
    }
    generateConstantExp(cval, into) {
        if (cval instanceof mir_ops_1.MIRConstantNone) {
            return this.typegen.coerce(new smt_exp_1.SMTValue("bsqkey_none"), this.typegen.noneType, into);
        }
        else if (cval instanceof mir_ops_1.MIRConstantTrue) {
            return this.typegen.coerce(new smt_exp_1.SMTValue("true"), this.typegen.boolType, into);
        }
        else if (cval instanceof mir_ops_1.MIRConstantFalse) {
            return this.typegen.coerce(new smt_exp_1.SMTValue("false"), this.typegen.boolType, into);
        }
        else if (cval instanceof mir_ops_1.MIRConstantInt) {
            return this.typegen.coerce(new smt_exp_1.SMTValue(cval.value), this.typegen.intType, into);
        }
        else {
            assert(cval instanceof mir_ops_1.MIRConstantString);
            return this.typegen.coerce(new smt_exp_1.SMTValue(cval.value), this.typegen.stringType, into);
        }
    }
    argToSMT(arg, into) {
        if (arg instanceof mir_ops_1.MIRRegisterArgument) {
            return this.typegen.coerce(new smt_exp_1.SMTValue(this.varToSMTName(arg)), this.getArgType(arg), into);
        }
        else {
            return this.generateConstantExp(arg, into);
        }
    }
    generateTruthyConvert(arg) {
        const argtype = this.getArgType(arg);
        if (this.assembly.subtypeOf(argtype, this.typegen.noneType)) {
            return new smt_exp_1.SMTValue("false");
        }
        else if (this.assembly.subtypeOf(argtype, this.typegen.boolType)) {
            return this.argToSMT(arg, this.typegen.boolType);
        }
        else if (this.typegen.typecheckAllKeys(argtype)) {
            return new smt_exp_1.SMTValue(`(= ${this.argToSMT(arg, this.typegen.keyType).emit()} (bsqkey_bool true))`);
        }
        else {
            return new smt_exp_1.SMTValue(`(= ${this.argToSMT(arg, this.typegen.anyType).emit()} (bsqterm_key (bsqkey_bool true)))`);
        }
    }
    generateNoneCheck(arg) {
        const argtype = this.getArgType(arg);
        if (this.assembly.subtypeOf(argtype, this.typegen.noneType)) {
            return new smt_exp_1.SMTValue("true");
        }
        else if (!this.assembly.subtypeOf(this.typegen.noneType, argtype)) {
            return new smt_exp_1.SMTValue("false");
        }
        else if (this.typegen.typecheckAllKeys(argtype)) {
            return new smt_exp_1.SMTValue(`(= ${this.argToSMT(arg, this.typegen.keyType).emit()} bsqkey_none)`);
        }
        else {
            return new smt_exp_1.SMTValue(`(= ${this.argToSMT(arg, this.typegen.anyType).emit()} bsqterm_none)`);
        }
    }
    generateLoadConstSafeString(op) {
        if (op.vfunckey === undefined) {
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue(`(bsq_safestring@cons "${this.typegen.mangleStringForSMT(op.tskey)}" ${op.ivalue})`));
        }
        else {
            const pfunc = (this.assembly.invokeDecls.get(op.vfunckey) || this.assembly.primitiveInvokeDecls.get(op.vfunckey));
            const rval = new smt_exp_1.SMTValue(`(bsq_safestring@cons "${this.typegen.mangleStringForSMT(op.tskey)}" ${op.ivalue})`);
            const tv = this.generateTempName();
            const ivrtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(pfunc.resultType));
            const resulttype = this.typegen.getSMTTypeFor(this.currentRType);
            const ichk = new smt_exp_1.SMTLet(tv, new smt_exp_1.SMTValue(`(${this.invokenameToSMT(op.vfunckey)} ${op.ivalue})`));
            const checkerror = new smt_exp_1.SMTValue(`(is-result_error@${ivrtype} ${tv})`);
            const extracterror = (ivrtype !== resulttype) ? new smt_exp_1.SMTValue(`(result_error@${this.typegen.getSMTTypeFor(this.currentRType)} (result_error_code@${ivrtype} ${tv}))`) : new smt_exp_1.SMTValue(tv);
            const resultv = ichk.bind(new smt_exp_1.SMTValue(`(result_success_value@${ivrtype} ${tv})`));
            const cond = new smt_exp_1.SMTValue(`(or ${checkerror} (= ${resultv} false))`);
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTCond(cond, extracterror, rval));
        }
    }
    generateLoadConstTypedString(op) {
        if (op.pfunckey === undefined) {
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue(`(bsq_stringof@cons "${this.typegen.mangleStringForSMT(op.tskey)}" ${op.ivalue})`));
        }
        else {
            const pfunc = (this.assembly.invokeDecls.get(op.pfunckey) || this.assembly.primitiveInvokeDecls.get(op.pfunckey));
            const rval = new smt_exp_1.SMTValue(`(bsq_stringof@cons "${this.typegen.mangleStringForSMT(op.tskey)}" ${op.ivalue})`);
            const tv = this.generateTempName();
            const ivrtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(pfunc.resultType));
            const resulttype = this.typegen.getSMTTypeFor(this.currentRType);
            const ichk = new smt_exp_1.SMTLet(tv, new smt_exp_1.SMTValue(`(${this.invokenameToSMT(op.pfunckey)} ${op.ivalue})`));
            const checkerror = new smt_exp_1.SMTValue(`(is-result_error@${ivrtype} ${tv})`);
            const extracterror = (ivrtype !== resulttype) ? new smt_exp_1.SMTValue(`(result_error@${this.typegen.getSMTTypeFor(this.currentRType)} (result_error_code@${ivrtype} ${tv}))`) : new smt_exp_1.SMTValue(tv);
            const resultT = this.typegen.assembly.conceptDecls.get(pfunc.resultType).terms.get("T");
            const errtname = [...this.typegen.assembly.entityDecls].find((dcl) => dcl[0].startsWith("NSCore::Err<") && dcl[1].terms.get("T").trkey === resultT.trkey);
            const successf = this.typegen.generateConstructorTest(errtname[0]);
            const resultv = ichk.bind(new smt_exp_1.SMTValue(`(result_success_value@${ivrtype} ${tv})`));
            const cond = new smt_exp_1.SMTValue(`(or ${checkerror} (${successf} ${resultv}))`);
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTCond(cond, extracterror, rval));
        }
    }
    generateAccessConstantValue(cp) {
        const cdecl = this.assembly.constantDecls.get(cp.ckey);
        const tv = this.generateTempName();
        const ivrtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(cdecl.declaredType));
        const resulttype = this.typegen.getSMTTypeFor(this.currentRType);
        const constexp = new smt_exp_1.SMTValue(this.invokenameToSMT(cdecl.value));
        const checkerror = new smt_exp_1.SMTValue(`(is-result_error@${ivrtype} ${tv})`);
        const extracterror = (ivrtype !== resulttype) ? new smt_exp_1.SMTValue(`(result_error@${this.typegen.getSMTTypeFor(this.currentRType)} (result_error_code@${ivrtype} ${tv}))`) : new smt_exp_1.SMTValue(tv);
        const normalassign = new smt_exp_1.SMTLet(this.varToSMTName(cp.trgt), new smt_exp_1.SMTValue(`(result_success_value@${ivrtype} ${tv})`));
        return new smt_exp_1.SMTLet(tv, constexp, new smt_exp_1.SMTCond(checkerror, extracterror, normalassign));
    }
    generateLoadFieldDefaultValue(ld) {
        const fdecl = this.assembly.fieldDecls.get(ld.fkey);
        const tv = this.generateTempName();
        const ivrtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(fdecl.declaredType));
        const resulttype = this.typegen.getSMTTypeFor(this.currentRType);
        const constexp = new smt_exp_1.SMTValue(this.invokenameToSMT(fdecl.value));
        const checkerror = new smt_exp_1.SMTValue(`(is-result_error@${ivrtype} ${tv})`);
        const extracterror = (ivrtype !== resulttype) ? new smt_exp_1.SMTValue(`(result_error@${resulttype} (result_error_code@${ivrtype} ${tv}))`) : new smt_exp_1.SMTValue(tv);
        const normalassign = new smt_exp_1.SMTLet(this.varToSMTName(ld.trgt), new smt_exp_1.SMTValue(`(result_success_value@${ivrtype} ${tv})`));
        return new smt_exp_1.SMTLet(tv, constexp, new smt_exp_1.SMTCond(checkerror, extracterror, normalassign));
    }
    generateMIRInvokeInvariantCheckDirect(ivop) {
        const fields = [...this.typegen.assembly.entityDecls.get(ivop.tkey).fields].sort((a, b) => a.name.localeCompare(b.name));
        let vals = fields.map((f) => `(${this.typegen.generateEntityAccessor(f.enclosingDecl, f.fkey)} ${this.argToSMT(ivop.rcvr, this.typegen.getMIRType(ivop.tkey)).emit()})`);
        const tv = this.generateTempName();
        const ivrtype = this.typegen.getSMTTypeFor(this.typegen.boolType);
        const resulttype = this.typegen.getSMTTypeFor(this.currentRType);
        const checkerror = new smt_exp_1.SMTValue(`(is-result_error@${ivrtype} ${tv})`);
        const extracterror = (ivrtype !== resulttype) ? new smt_exp_1.SMTValue(`(result_error@${resulttype} (result_error_code@${ivrtype} ${tv}))`) : new smt_exp_1.SMTValue(tv);
        const normalassign = new smt_exp_1.SMTLet(this.varToSMTName(ivop.trgt), new smt_exp_1.SMTValue(`(result_success_value@${ivrtype} ${tv})`));
        const invokeexp = new smt_exp_1.SMTValue(`(${this.invokenameToSMT(ivop.ikey)} ${vals.join(" ")})`);
        return new smt_exp_1.SMTLet(tv, invokeexp, new smt_exp_1.SMTCond(checkerror, extracterror, normalassign));
    }
    generateMIRConstructorPrimary(cp) {
        const ctype = this.assembly.entityDecls.get(cp.tkey);
        const fvals = cp.args.map((arg, i) => {
            const ftype = this.typegen.getMIRType(ctype.fields[i].declaredType);
            return this.argToSMT(arg, ftype).emit();
        });
        const smtctype = this.typegen.generateEntityConstructor(cp.tkey);
        const cexp = ctype.fields.length === 0 ? new smt_exp_1.SMTValue(smtctype) : new smt_exp_1.SMTValue(`(${smtctype} ${fvals.join(" ")})`);
        return new smt_exp_1.SMTLet(this.varToSMTName(cp.trgt), cexp);
    }
    generateMIRConstructorPrimaryCollectionEmpty(cpce) {
        const cpcetype = this.typegen.getMIRType(cpce.tkey);
        const smtctype = this.typegen.generateEntityConstructor(cpce.tkey);
        if (this.typegen.typecheckIsName(cpcetype, /NSCore::List<.*>/)) {
            return new smt_exp_1.SMTLet(this.varToSMTName(cpce.trgt), new smt_exp_1.SMTValue(`(${smtctype} 0 ${this.typegen.generateEmptyDataArrayFor(cpce.tkey)})`));
        }
        else if (this.typegen.typecheckIsName(cpcetype, /NSCore::Set<.*>/)) {
            return new smt_exp_1.SMTLet(this.varToSMTName(cpce.trgt), new smt_exp_1.SMTValue(`(${smtctype} 0 ${this.typegen.generateEmptyHasArrayFor(cpce.tkey)} ${this.typegen.generateEmptyDataArrayFor(cpce.tkey)} bsqterm_none)`));
        }
        else {
            return new smt_exp_1.SMTLet(this.varToSMTName(cpce.trgt), new smt_exp_1.SMTValue(`(${smtctype} 0 ${this.typegen.generateEmptyHasArrayFor(cpce.tkey)} ${this.typegen.generateEmptyKeyArrayFor(cpce.tkey)} ${this.typegen.generateEmptyDataArrayFor(cpce.tkey)} bsqterm_none)`));
        }
    }
    generateMIRConstructorPrimaryCollectionSingletons(cpcs) {
        const cpcstype = this.typegen.getMIRType(cpcs.tkey);
        const smtctype = this.typegen.generateEntityConstructor(cpcs.tkey);
        if (this.typegen.typecheckIsName(cpcstype, /NSCore::List<.*>/)) {
            const oftype = this.assembly.entityDecls.get(cpcs.tkey).terms.get("T");
            let consv = this.typegen.generateEmptyDataArrayFor(cpcs.tkey);
            for (let i = 0; i < cpcs.args.length; ++i) {
                consv = `(store ${consv} ${i} ${this.argToSMT(cpcs.args[i], oftype).emit()})`;
            }
            return new smt_exp_1.SMTLet(this.varToSMTName(cpcs.trgt), new smt_exp_1.SMTValue(`(${smtctype} ${cpcs.args.length} ${consv})`));
        }
        else if (this.typegen.typecheckIsName(cpcstype, /NSCore::Set<.*>/)) {
            const oftype = this.assembly.entityDecls.get(cpcs.tkey).terms.get("T");
            const realkeytype = this.typegen.getKeyProjectedTypeFrom(oftype);
            const kltype = [...this.typegen.assembly.entityDecls].find((edecl) => edecl[1].ns === "NSCore" && edecl[1].name === "KeyList" && edecl[1].terms.get("K").trkey === realkeytype.trkey);
            const klcons = this.typegen.generateEntityConstructor(kltype[1].tkey);
            const klstore = this.typegen.getKeyListTypeForSet(this.assembly.entityDecls.get(cpcs.tkey));
            let consv = `(${smtctype} %CTR% %HAS% %DATA% %KEY%)`;
            for (let i = cpcs.args.length - 1; i >= 1; --i) {
                const arg = cpcs.args[i];
                const key = this.typegen.getKeyFrom(this.argToSMT(arg, oftype).emit(), oftype);
                const ctrvar = this.generateTempName();
                const ctrup = `(ite (select %HAS% ${key}) %CTR% (+ %CTR% 1))`;
                const hasvar = this.generateTempName();
                const hasup = `(store %HAS% ${key} true)`;
                const datavar = this.generateTempName();
                const dataup = `(store %DATA% ${key} ${this.argToSMT(arg, oftype).emit()})`;
                const keyvar = this.generateTempName();
                const keycons = `(${klcons} ${key} %KEY%)`;
                const keyforce = this.typegen.coerce(new smt_exp_1.SMTValue(keycons), this.typegen.getMIRType(kltype[1].tkey), klstore).emit();
                const keyup = `(ite (select %HAS% ${key}) %KEY% ${keyforce})`;
                const body = consv.replace(/%CTR%/g, ctrvar).replace(/%HAS%/g, hasvar).replace(/%DATA%/g, datavar).replace(/%KEY%/g, keyvar);
                consv = `(let ((${ctrvar} ${ctrup}) (${hasvar} ${hasup}) (${datavar} ${dataup}) (${keyvar} ${keyup})) ${body})`;
            }
            const key = this.typegen.getKeyFrom(this.argToSMT(cpcs.args[0], oftype).emit(), oftype);
            const val = this.argToSMT(cpcs.args[0], oftype).emit();
            const kl = new smt_exp_1.SMTValue(`(${klcons} ${key} bsqterm_none)`);
            const final = consv
                .replace(/%CTR%/g, "1")
                .replace(/%HAS%/g, `(store ${this.typegen.generateEmptyHasArrayFor(cpcs.tkey)} ${key} true)`)
                .replace(/%DATA%/g, `(store ${this.typegen.generateEmptyDataArrayFor(cpcs.tkey)} ${key} ${val})`)
                .replace(/%KEY%/g, this.typegen.coerce(kl, this.typegen.getMIRType(kltype[1].tkey), klstore).emit());
            return new smt_exp_1.SMTLet(this.varToSMTName(cpcs.trgt), new smt_exp_1.SMTValue(final));
        }
        else {
            const ktype = this.assembly.entityDecls.get(cpcs.tkey).terms.get("K");
            const vtype = this.assembly.entityDecls.get(cpcs.tkey).terms.get("V");
            const realkeytype = this.typegen.getKeyProjectedTypeFrom(ktype);
            const entrytype = [...this.typegen.assembly.entityDecls].find((edecl) => edecl[1].ns === "NSCore" && edecl[1].name === "MapEntry" && edecl[1].terms.get("K").trkey === ktype.trkey && edecl[1].terms.get("V").trkey === vtype.trkey);
            const entrykey = this.typegen.generateEntityAccessor(entrytype[1].tkey, entrytype[1].fields.find((fd) => fd.name === "key").fkey);
            const entryvalue = this.typegen.generateEntityAccessor(entrytype[1].tkey, entrytype[1].fields.find((fd) => fd.name === "value").fkey);
            const kltype = [...this.typegen.assembly.entityDecls].find((edecl) => edecl[1].ns === "NSCore" && edecl[1].name === "KeyList" && edecl[1].terms.get("K").trkey === realkeytype.trkey);
            const klcons = this.typegen.generateEntityConstructor(kltype[1].tkey);
            const klstore = this.typegen.getKeyListTypeForMap(this.assembly.entityDecls.get(cpcs.tkey));
            let consv = `(${smtctype} %CTR% %HAS% %ENTRYKEY% %ENTRYDATA% %KEY%)`;
            for (let i = cpcs.args.length - 1; i >= 1; --i) {
                const arg = cpcs.args[i];
                const entrykeyexp = `(${entrykey} ${this.argToSMT(arg, this.typegen.getMIRType(entrytype[1].tkey)).emit()})`;
                const entryvalexp = `(${entryvalue} ${this.argToSMT(arg, this.typegen.getMIRType(entrytype[1].tkey)).emit()})`;
                const key = this.typegen.getKeyFrom(entrykeyexp, ktype);
                const ctrvar = this.generateTempName();
                const ctrup = `(ite (select %HAS% ${key}) %CTR% (+ %CTR% 1))`;
                const hasvar = this.generateTempName();
                const hasup = `(store %HAS% ${key} true)`;
                const entrykeyvar = this.generateTempName();
                const entrykeyup = `(store %ENTRYKEY% ${key} ${entrykeyexp})`;
                const entrydatavar = this.generateTempName();
                const entrydataup = `(store %ENTRYDATA% ${key} ${entryvalexp})`;
                const keyvar = this.generateTempName();
                const keycons = `(${klcons} ${key} %KEY%)`;
                const keyforce = this.typegen.coerce(new smt_exp_1.SMTValue(keycons), this.typegen.getMIRType(kltype[1].tkey), klstore).emit();
                const keyup = `(ite (select %HAS% ${key}) %KEY% ${keyforce})`;
                const body = consv.replace(/%CTR%/g, ctrvar).replace(/%HAS%/g, hasvar).replace(/%ENTRYKEY%/g, entrykeyvar).replace(/%ENTRYDATA%/g, entrydatavar).replace(/%KEY%/g, keyvar);
                consv = `(let ((${ctrvar} ${ctrup}) (${hasvar} ${hasup}) (${entrykeyvar} ${entrykeyup}) (${entrydatavar} ${entrydataup})  (${keyvar} ${keyup})) ${body})`;
            }
            const entrykeyexp0 = `(${entrykey} ${this.argToSMT(cpcs.args[0], this.typegen.getMIRType(entrytype[1].tkey)).emit()})`;
            const entryvalexp0 = `(${entryvalue} ${this.argToSMT(cpcs.args[0], this.typegen.getMIRType(entrytype[1].tkey)).emit()})`;
            const key = this.typegen.getKeyFrom(entrykeyexp0, ktype);
            const kl = new smt_exp_1.SMTValue(`(${klcons} ${key} bsqterm_none)`);
            const final = consv
                .replace(/%CTR%/g, "1")
                .replace(/%HAS%/g, `(store ${this.typegen.generateEmptyHasArrayFor(cpcs.tkey)} ${key} true)`)
                .replace(/%ENTRYKEY%/g, `(store ${this.typegen.generateEmptyKeyArrayFor(cpcs.tkey)} ${key} ${entrykeyexp0})`)
                .replace(/%ENTRYDATA%/g, `(store ${this.typegen.generateEmptyDataArrayFor(cpcs.tkey)} ${key} ${entryvalexp0})`)
                .replace(/%KEY%/g, this.typegen.coerce(kl, this.typegen.getMIRType(kltype[1].tkey), klstore).emit());
            return new smt_exp_1.SMTLet(this.varToSMTName(cpcs.trgt), new smt_exp_1.SMTValue(final));
        }
    }
    generateDataKindLoad(rtype, cf) {
        const idf = this.typegen.generateInitialDataKindFlag(rtype);
        return idf === "unknown" ? cf : idf;
    }
    generateMIRConstructorTuple(op) {
        let fvals = "3";
        let cvals = "bsqtuple_array_empty";
        for (let i = 0; i < op.args.length; ++i) {
            cvals = `(store ${cvals} ${i} ${this.argToSMT(op.args[i], this.typegen.anyType).emit()})`;
            fvals = `(@fj ${this.argToSMT(op.args[i], this.typegen.anyType)} ${fvals})`;
        }
        return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue(`(bsq_tuple@cons ${this.generateDataKindLoad(this.typegen.getMIRType(op.resultTupleType), fvals)} ${cvals})`));
    }
    generateMIRConstructorRecord(op) {
        let fvals = "3";
        let cvals = "bsqrecord_array_empty";
        for (let i = 0; i < op.args.length; ++i) {
            cvals = `(store ${cvals} "${op.args[i][0]}" ${this.argToSMT(op.args[i][1], this.typegen.anyType).emit()})`;
            fvals = `(@fj ${this.argToSMT(op.args[i][1], this.typegen.anyType)} ${fvals})`;
        }
        return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue(`(bsq_record@cons ${this.generateDataKindLoad(this.typegen.getMIRType(op.resultRecordType), fvals)} ${cvals})`));
    }
    generateMIRConstructorEphemeralValueList(op) {
        const etype = this.typegen.getMIRType(op.resultEphemeralListType).options[0];
        let args = [];
        for (let i = 0; i < op.args.length; ++i) {
            args.push(this.argToSMT(op.args[i], etype.entries[i]).emit());
        }
        return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue(`(${this.typegen.generateEntityConstructor(etype.trkey)} ${args.join(" ")})`));
    }
    generateMIRAccessFromIndexExpression(arg, idx, resultAccessType) {
        const tuptype = this.getArgType(arg);
        const hasidx = this.typegen.tupleHasIndex(tuptype, idx);
        if (hasidx === "no") {
            return this.typegen.coerce(new smt_exp_1.SMTValue("bsqkey_none"), this.typegen.noneType, resultAccessType);
        }
        else {
            const tupcontents = this.typegen.typecheckTuple(tuptype) ? `(bsq_tuple_entries ${this.varToSMTName(arg)})` : `(bsq_tuple_entries (bsqterm_tuple_value ${this.varToSMTName(arg)}))`;
            const select = new smt_exp_1.SMTValue(`(select ${tupcontents} ${idx})`);
            if (hasidx === "yes") {
                return this.typegen.coerce(select, this.typegen.anyType, resultAccessType);
            }
            else {
                const getop = new smt_exp_1.SMTCond(new smt_exp_1.SMTValue(`(= ${select.emit()} bsqterm@clear)`), new smt_exp_1.SMTValue("bsqterm_none"), select);
                return this.typegen.coerce(getop, this.typegen.anyType, resultAccessType);
            }
        }
    }
    generateMIRProjectFromIndecies(op, resultAccessType) {
        const intotypes = this.typegen.typecheckEphemeral(resultAccessType) ? resultAccessType.options[0].entries : [];
        let vals = [];
        for (let i = 0; i < op.indecies.length; ++i) {
            vals.push(this.generateMIRAccessFromIndexExpression(op.arg, op.indecies[i], intotypes[i] || this.typegen.anyType).emit());
        }
        if (this.typegen.typecheckEphemeral(resultAccessType)) {
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue(`(${this.typegen.generateEntityConstructor(resultAccessType.trkey)} ${vals.join(" ")})`));
        }
        else {
            let fvals = "3";
            let cvals = "bsqtuple_array_empty";
            for (let i = 0; i < vals.length; ++i) {
                cvals = `(store ${cvals} ${i} ${vals[i]})`;
                fvals = `(@fj ${vals[i]} ${fvals})`;
            }
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue(`(bsq_tuple@cons ${this.generateDataKindLoad(resultAccessType, fvals)} ${cvals})`));
        }
    }
    generateMIRModifyWithIndecies(op, resultTupleType) {
        const updmax = Math.max(...op.updates.map((upd) => upd[0] + 1));
        let fvals = "3";
        let cvals = "bsqtuple_array_empty";
        for (let i = 0; i < updmax; ++i) {
            const upd = op.updates.find((update) => update[0] === i);
            if (upd !== undefined) {
                cvals = `(store ${cvals} ${i} ${this.argToSMT(upd[1], this.typegen.anyType).emit()})`;
                fvals = `(@fj ${this.argToSMT(upd[1], this.typegen.anyType).emit()} ${fvals})`;
            }
            else {
                cvals = `(store ${cvals} ${i} ${this.generateMIRAccessFromIndexExpression(op.arg, i, this.typegen.anyType).emit()})`;
                fvals = `(@fj ${this.generateMIRAccessFromIndexExpression(op.arg, i, this.typegen.anyType).emit()} ${fvals})`;
            }
        }
        const rmax = this.typegen.getMaxTupleLength(resultTupleType);
        let tc = this.typegen.typecheckTuple(this.getArgType(op.arg)) ? `(bsq_tuple_entries ${this.varToSMTName(op.arg)})` : `(bsq_tuple_entries (bsqterm_tuple_value ${this.varToSMTName(op.arg)}))`;
        for (let i = updmax; i < rmax; ++i) {
            cvals = `(store ${cvals} ${i} (select ${tc} ${i}))`;
            fvals = `(@fj (select ${tc} ${i}) ${fvals})`;
        }
        return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue(`(bsq_tuple@cons ${this.generateDataKindLoad(this.typegen.getMIRType(op.resultTupleType), fvals)} ${cvals})`));
    }
    generateMIRStructuredExtendTuple(op, resultTupleType) {
        //this is the exact number of indecies in arg -- see typecheck
        const btuple = this.typegen.getMaxTupleLength(this.typegen.getMIRType(op.argInferType));
        const ftuple = this.typegen.getMaxTupleLength(resultTupleType);
        let cvals = this.typegen.typecheckTuple(this.getArgType(op.arg)) ? `(bsq_tuple_entries ${this.varToSMTName(op.arg)})` : `(bsq_tuple_entries (bsqterm_tuple_value ${this.varToSMTName(op.arg)}))`;
        let mvals = this.typegen.typecheckTuple(this.getArgType(op.update)) ? `(bsq_tuple_entries ${this.varToSMTName(op.update)})` : `(bsq_tuple_entries (bsqterm_tuple_value ${this.varToSMTName(op.update)}))`;
        for (let i = 0; i < ftuple; ++i) {
            cvals = `(store ${cvals} ${btuple + i} (select ${mvals} ${i}))`;
        }
        let fvals = `(@fj ${this.argToSMT(op.arg, this.typegen.anyType).emit()} ${this.argToSMT(op.update, this.typegen.anyType).emit()})`;
        return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue(`(bsq_tuple@cons ${this.generateDataKindLoad(this.typegen.getMIRType(op.resultTupleType), fvals)} ${cvals})`));
    }
    generateMIRAccessFromPropertyExpression(arg, property, resultAccessType) {
        const rectype = this.getArgType(arg);
        const hasproperty = this.typegen.recordHasField(rectype, property);
        if (hasproperty === "no") {
            return this.typegen.coerce(new smt_exp_1.SMTValue("bsqkey_none"), this.typegen.noneType, resultAccessType);
        }
        else {
            const reccontents = this.typegen.typecheckRecord(rectype) ? `(bsq_record_entries ${this.varToSMTName(arg)})` : `(bsq_record_entries (bsqterm_record_value ${this.varToSMTName(arg)}))`;
            const select = new smt_exp_1.SMTValue(`(select ${reccontents} "${property}")`);
            if (hasproperty === "yes") {
                return this.typegen.coerce(select, this.typegen.anyType, resultAccessType);
            }
            else {
                const getop = new smt_exp_1.SMTCond(new smt_exp_1.SMTValue(`(= ${select.emit()} bsqterm@clear)`), new smt_exp_1.SMTValue("bsqterm_none"), select);
                return this.typegen.coerce(getop, this.typegen.anyType, resultAccessType);
            }
        }
    }
    generateMIRProjectFromProperties(op, resultAccessType) {
        const intotypes = this.typegen.typecheckEphemeral(resultAccessType) ? resultAccessType.options[0].entries : [];
        let vals = [];
        for (let i = 0; i < op.properties.length; ++i) {
            vals.push(this.generateMIRAccessFromPropertyExpression(op.arg, op.properties[i], intotypes[i] || this.typegen.anyType).emit());
        }
        if (this.typegen.typecheckEphemeral(resultAccessType)) {
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue(`(${this.typegen.generateEntityConstructor(resultAccessType.trkey)} ${vals.join(" ")})`));
        }
        else {
            let fvals = "3";
            let cvals = "bsqrecord_array_empty";
            for (let i = 0; i < vals.length; ++i) {
                cvals = `(store ${cvals} "${op.properties[i]}" ${vals[i]})`;
                fvals = `(@fj ${vals[i]} ${fvals})`;
            }
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue(`(bsq_record@cons ${this.generateDataKindLoad(resultAccessType, fvals)} ${cvals})`));
        }
    }
    generateMIRModifyWithProperties(op, resultRecordType) {
        const pmax = this.typegen.getMaxPropertySet(resultRecordType);
        let fvals = "3";
        let cvals = "bsqrecord_array_empty";
        let tc = this.typegen.typecheckRecord(this.getArgType(op.arg)) ? `(bsq_record_entries ${this.varToSMTName(op.arg)})` : `(bsq_record_entries (bsqterm_record_value ${this.varToSMTName(op.arg)}))`;
        for (let i = 0; i < pmax.length; ++i) {
            const pname = pmax[i];
            const upd = op.updates.find((update) => update[0] === pname);
            if (upd !== undefined) {
                cvals = `(store ${cvals} "${pname}" ${this.argToSMT(upd[1], this.typegen.anyType).emit()})`;
                fvals = `(@fj ${this.argToSMT(upd[1], this.typegen.anyType).emit()} ${fvals})`;
            }
            else {
                cvals = `(store ${cvals} "${pname}" (select ${tc} "${pname}"))`;
                fvals = `(@fj (select ${tc} "${pname}") ${fvals})`;
            }
        }
        return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue(`(bsq_record@cons ${this.generateDataKindLoad(this.typegen.getMIRType(op.resultRecordType), fvals)} ${cvals})`));
    }
    generateMIRStructuredExtendRecord(op, resultRecordType) {
        const argvals = this.typegen.typecheckRecord(this.getArgType(op.arg)) ? `(bsq_record_entries ${this.varToSMTName(op.arg)})` : `(bsq_record_entries (bsqterm_record_value ${this.varToSMTName(op.arg)}))`;
        let cvals = argvals;
        let fvals = "3";
        const rprops = this.typegen.getMaxPropertySet(resultRecordType);
        const mtype = this.typegen.getMIRType(op.updateInferType);
        for (let i = 0; i < rprops.length; ++i) {
            const pname = rprops[i];
            const uhas = this.typegen.recordHasField(mtype, pname);
            if (uhas === "no") {
                //nothing to do for cvals
                fvals = `(@fj (select ${argvals} "${pname}") ${fvals})`;
            }
            else if (uhas === "yes") {
                cvals = `(store ${cvals} "${pname}" ${this.generateMIRAccessFromPropertyExpression(op.update, pname, this.typegen.anyType)})`;
                fvals = `(@fj ${this.generateMIRAccessFromPropertyExpression(op.update, pname, this.typegen.anyType)} ${fvals})`;
            }
            else {
                let mvals = this.typegen.typecheckRecord(this.getArgType(op.update)) ? `(bsq_record_entries ${this.varToSMTName(op.update)})` : `(bsq_record_entries (bsqterm_record_value ${this.varToSMTName(op.update)}))`;
                const check = new smt_exp_1.SMTValue(`(= (select ${mvals} "${pname}") bsqterm@clear)`);
                const caccess = new smt_exp_1.SMTCond(check, new smt_exp_1.SMTValue(`(select ${argvals} "${pname}")`), new smt_exp_1.SMTValue(`(select ${mvals} "${pname}")`));
                cvals = `(store ${cvals} "${pname}" ${caccess})`;
                fvals = `(@fj ${caccess} ${fvals})`;
            }
        }
        return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue(`(bsq_record@cons ${this.generateDataKindLoad(this.typegen.getMIRType(op.resultRecordType), fvals)} ${cvals})`));
    }
    generateVFieldLookup(arg, infertype, fdecl) {
        const lname = `resolve_${fdecl.fkey}_from_${infertype.trkey}`;
        let decl = this.vfieldLookups.find((lookup) => lookup.lname === lname);
        if (decl === undefined) {
            this.vfieldLookups.push({ infertype: infertype, fdecl: fdecl, lname: lname });
        }
        return new smt_exp_1.SMTValue(`(${this.typegen.mangleStringForSMT(lname)} ${this.argToSMT(arg, infertype).emit()})`);
    }
    generateMIRAccessFromField(op, resultAccessType) {
        const inferargtype = this.typegen.getMIRType(op.argInferType);
        const fdecl = this.assembly.fieldDecls.get(op.field);
        const ftype = this.typegen.getMIRType(fdecl.declaredType);
        if (this.typegen.typecheckUEntity(inferargtype)) {
            const access = new smt_exp_1.SMTValue(`(${this.typegen.generateEntityAccessor(this.typegen.getEntityEKey(inferargtype), op.field)} ${this.argToSMT(op.arg, inferargtype).emit()})`);
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(access, ftype, resultAccessType));
        }
        else {
            const access = this.generateVFieldLookup(op.arg, inferargtype, fdecl);
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(access, ftype, resultAccessType));
        }
    }
    generateVFieldProject(arg, infertype, fdecls) {
        const pname = `project_${fdecls.map((fd) => fd.fkey).sort().join("*")}_from_${infertype.trkey}`;
        let decl = this.vfieldProjects.find((lookup) => lookup.pname === pname);
        if (decl === undefined) {
            this.vfieldProjects.push({ infertype: infertype, fdecls: fdecls, pname: pname });
        }
        return new smt_exp_1.SMTValue(`(${this.typegen.mangleStringForSMT(pname)} ${this.argToSMT(arg, infertype)})`);
    }
    generateMIRProjectFromFields(op) {
        const inferargtype = this.typegen.getMIRType(op.argInferType);
        if (this.typegen.typecheckUEntity(inferargtype)) {
            let fvals = "3";
            let cvals = "bsqrecord_array_empty";
            for (let i = 0; i < op.fields.length; ++i) {
                const fdecl = this.assembly.fieldDecls.get(op.fields[i]);
                const ftype = this.typegen.getMIRType(fdecl.declaredType);
                const access = new smt_exp_1.SMTValue(`(${this.typegen.generateEntityAccessor(this.typegen.getEntityEKey(inferargtype), op.fields[i])} ${this.argToSMT(op.arg, inferargtype).emit()})`);
                cvals = `(store ${cvals} "${fdecl.name}" ${this.typegen.coerce(access, ftype, this.typegen.anyType)})`;
                fvals = `(@fj ${this.typegen.coerce(access, ftype, this.typegen.anyType)} ${fvals})`;
            }
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue(`(bsq_record@cons ${this.generateDataKindLoad(this.typegen.getMIRType(op.resultProjectType), fvals)} ${cvals})`));
        }
        else {
            const access = this.generateVFieldProject(op.arg, inferargtype, op.fields.map((f) => this.assembly.fieldDecls.get(f)));
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), access);
        }
    }
    generateVFieldUpdates(arg, infertype, fupds) {
        const upnames = fupds.map((fud) => `${fud[0].fkey}->${this.getArgType(fud[1])}`);
        const uname = `update_${upnames.sort().join("*")}_in_${infertype.trkey}`;
        let decl = this.vfieldUpdates.find((lookup) => lookup.uname === uname);
        if (decl === undefined) {
            this.vfieldUpdates.push({ infertype: infertype, fupds: fupds, uname: uname });
        }
        return new smt_exp_1.SMTValue(`(${this.typegen.mangleStringForSMT(uname)} ${this.argToSMT(arg, infertype)} ${fupds.map((upd) => this.argToSMT(upd[1], this.getArgType(upd[1])).emit()).join(" ")})`);
    }
    generateMIRModifyWithFields(op) {
        const inferargtype = this.typegen.getMIRType(op.argInferType);
        if (this.typegen.typecheckUEntity(inferargtype)) {
            const ekey = this.typegen.getEntityEKey(inferargtype);
            const utype = this.typegen.assembly.entityDecls.get(ekey);
            let cvals = [];
            for (let i = 0; i < utype.fields.length; ++i) {
                const fdecl = utype.fields[i];
                const ftype = this.typegen.getMIRType(fdecl.declaredType);
                const upd = op.updates.find((update) => update[0] == fdecl.fkey);
                if (upd !== undefined) {
                    cvals.push(this.argToSMT(upd[1], ftype).emit());
                }
                else {
                    cvals.push(`(${this.typegen.generateEntityAccessor(ekey, fdecl.fkey)} ${this.argToSMT(op.arg, inferargtype).emit()})`);
                }
            }
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue(`(${this.typegen.generateEntityConstructor(ekey)} ${cvals.join(" ")})`));
        }
        else {
            const access = this.generateVFieldUpdates(op.arg, inferargtype, op.updates.map((upd) => [this.assembly.fieldDecls.get(upd[0]), upd[1]]));
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), access);
        }
    }
    generateVFieldExtend(arg, infertype, merge, infermerge, fieldResolves) {
        const upnames = fieldResolves.map((fr) => `${fr[0]}->${fr[1].fkey}`);
        const mname = `merge_${infertype.trkey}_${upnames.join("*")}_with_${infermerge.trkey}`;
        let decl = this.vobjmerges.find((lookup) => lookup.mname === mname);
        if (decl === undefined) {
            this.vobjmerges.push({ infertype: infertype, merge: merge, infermergetype: infermerge, fieldResolves: fieldResolves, mname: mname });
        }
        return new smt_exp_1.SMTValue(`(${this.typegen.mangleStringForSMT(mname)} ${this.argToSMT(arg, infertype)} ${this.argToSMT(merge, infermerge)})`);
    }
    generateMIRStructuredExtendObject(op) {
        const inferargtype = this.typegen.getMIRType(op.argInferType);
        const mergeargtype = this.typegen.getMIRType(op.updateInferType);
        if (this.typegen.typecheckUEntity(inferargtype)) {
            const ekey = this.typegen.getEntityEKey(inferargtype);
            const utype = this.typegen.assembly.entityDecls.get(ekey);
            let cvals = [];
            for (let i = 0; i < utype.fields.length; ++i) {
                const fdecl = utype.fields[i];
                const ftype = this.typegen.getMIRType(fdecl.declaredType);
                const fp = op.fieldResolves.find((tfp) => tfp[1] === fdecl.fkey);
                const faccess = `(${this.typegen.generateEntityAccessor(ekey, fdecl.fkey)} ${this.argToSMT(op.arg, inferargtype).emit()})`;
                if (fp === undefined) {
                    cvals.push(faccess);
                }
                else {
                    const hasp = this.typegen.recordHasField(mergeargtype, fp[0]);
                    if (hasp === "no") {
                        cvals.push(faccess);
                    }
                    else if (hasp === "yes") {
                        cvals.push(this.generateMIRAccessFromPropertyExpression(op.arg, fp[0], ftype).emit());
                    }
                    else {
                        let mvals = this.typegen.typecheckRecord(this.getArgType(op.update)) ? `(bsq_record_entries ${this.varToSMTName(op.update)})` : `(bsq_record_entries (bsqterm_record_value ${this.varToSMTName(op.update)}))`;
                        const check = new smt_exp_1.SMTValue(`(= (select ${mvals} "${fp[0]}") bsqterm@clear)`);
                        cvals.push(new smt_exp_1.SMTCond(check, new smt_exp_1.SMTValue(faccess), new smt_exp_1.SMTValue(`(select ${mvals} "${fp[0]}")`)).emit());
                    }
                }
            }
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue(`(${this.typegen.generateEntityConstructor(ekey)} ${cvals.join(" ")})`));
        }
        else {
            const access = this.generateVFieldExtend(op.arg, inferargtype, op.update, mergeargtype, op.fieldResolves.map((fr) => [fr[0], this.assembly.fieldDecls.get(fr[1])]));
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), access);
        }
    }
    generateMIRLoadFromEpehmeralList(op) {
        return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue(`(${this.typegen.generateEntityAccessor(op.argInferType, `entry_${op.idx}`)} ${this.varToSMTName(op.arg)})`));
    }
    generateMIRInvokeFixedFunction(ivop, gas) {
        let vals = [];
        const idecl = (this.assembly.invokeDecls.get(ivop.mkey) || this.assembly.primitiveInvokeDecls.get(ivop.mkey));
        for (let i = 0; i < ivop.args.length; ++i) {
            vals.push(this.argToSMT(ivop.args[i], this.assembly.typeMap.get(idecl.params[i].type)).emit());
        }
        const tv = this.generateTempName();
        const ivrtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(idecl.resultType));
        const resulttype = this.typegen.getSMTTypeFor(this.currentRType);
        const checkerror = new smt_exp_1.SMTValue(`(is-result_error@${ivrtype} ${tv})`);
        const extracterror = (ivrtype !== resulttype) ? new smt_exp_1.SMTValue(`(result_error@${resulttype} (result_error_code@${ivrtype} ${tv}))`) : new smt_exp_1.SMTValue(tv);
        const normalassign = new smt_exp_1.SMTLet(this.varToSMTName(ivop.trgt), new smt_exp_1.SMTValue(`(result_success_value@${ivrtype} ${tv})`));
        if (this.currentSCC === undefined || !this.currentSCC.has(ivop.mkey)) {
            const invokeexp = new smt_exp_1.SMTValue(vals.length !== 0 ? `(${this.invokenameToSMT(ivop.mkey)} ${vals.join(" ")})` : this.invokenameToSMT(ivop.mkey));
            return new smt_exp_1.SMTLet(tv, invokeexp, new smt_exp_1.SMTCond(checkerror, extracterror, normalassign));
        }
        else {
            if (gas === 0) {
                const invokeexp = this.generateBMCLimitCreate(ivop.mkey, ivrtype);
                return new smt_exp_1.SMTLet(tv, invokeexp, new smt_exp_1.SMTCond(checkerror, extracterror, normalassign));
            }
            else {
                const invokeexp = new smt_exp_1.SMTValue(vals.length !== 0 ? `(${this.invokenameToSMT(ivop.mkey)}@gas${gas} ${vals.join(" ")})` : this.invokenameToSMT(ivop.mkey));
                return new smt_exp_1.SMTLet(tv, invokeexp, new smt_exp_1.SMTCond(checkerror, extracterror, normalassign));
            }
        }
    }
    generateEquals(op, lhsinfertype, lhs, rhsinfertype, rhs, isstrict) {
        let coreop = "";
        if (isstrict) {
            coreop = `(= ${this.argToSMT(lhs, lhsinfertype).emit()} ${this.argToSMT(rhs, rhsinfertype).emit()})`;
        }
        else {
            coreop = `(= ${this.argToSMT(lhs, this.typegen.keyType).emit()} ${this.argToSMT(rhs, this.typegen.keyType).emit()})`;
        }
        return op === "!=" ? `(not ${coreop})` : coreop;
    }
    generateCompare(op, lhsinfertype, lhs, rhsinfertype, rhs) {
        return `(${op} ${this.argToSMT(lhs, lhsinfertype).emit()} ${this.argToSMT(rhs, rhsinfertype).emit()})`;
    }
    generateSubtypeTupleCheck(argv, argtype, oftype) {
        const subtypesig = `subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)} ((atuple (Array Int BTerm))) Bool`;
        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let checks = [];
            //do all the checks that argtype satisfies all the requirements of oftype -- maybe a bit inefficiently
            for (let i = 0; i < oftype.entries.length; ++i) {
                const chk = this.generateTypeCheck(`(select atuple ${i})`, this.typegen.anyType, this.typegen.anyType, oftype.entries[i].type);
                if (oftype.entries[i].isOptional) {
                    checks.push(`(or (= (select atuple ${i}) bsqterm@clear) ${chk})`);
                }
                else {
                    checks.push(`(not (= (select atuple ${i}) bsqterm@clear))`);
                    checks.push(chk);
                }
            }
            //do checks that argtype doesn't have any other indecies
            if (this.typegen.typecheckTuple(argtype)) {
                const tlen = this.typegen.getMaxTupleLength(argtype);
                for (let i = oftype.entries.length; i < tlen; ++i) {
                    checks.push(`(= (select atuple ${i}) bsqterm@clear)`);
                }
            }
            else {
                let nv = "bsqtuple_array_empty";
                for (let i = 0; i < oftype.entries.length; ++i) {
                    nv = `(store ${nv} ${i} (select atuple ${i}))`;
                }
                checks.push(`(= ${nv} atuple)`);
            }
            let op = "";
            if (checks.includes("false")) {
                op = "false";
            }
            else {
                checks = checks.filter((chk) => chk !== "true");
                if (checks.length === 0) {
                    op = "true";
                }
                else if (checks.length === 1) {
                    op = checks[0];
                }
                else {
                    op = `(and ${checks.join(" ")})`;
                }
            }
            const decl = "(define-fun " + subtypesig
                + "\n  " + op
                + ")\n";
            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }
        return `(subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)} ${argv})`;
    }
    generateSubtypeRecordCheck(argv, argtype, oftype) {
        const subtypesig = `subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)} ((arecord (Array String BTerm))) Bool`;
        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let checks = [];
            //do all the checks that argtype satisfies all the requirements of oftype -- maybe a bit inefficiently
            for (let i = 0; i < oftype.entries.length; ++i) {
                const pname = oftype.entries[i].name;
                const chk = this.generateTypeCheck(`(select arecord "${pname}")`, this.typegen.anyType, this.typegen.anyType, oftype.entries[i].type);
                if (oftype.entries[i].isOptional) {
                    checks.push(`(or (= (select arecord "${pname}") bsqterm@clear) ${chk})`);
                }
                else {
                    checks.push(`(not (= (select arecord "${pname}") bsqterm@clear))`);
                    checks.push(chk);
                }
            }
            //do checks that argtype doesn't have any other properties
            if (this.typegen.typecheckRecord(argtype)) {
                const allprops = this.typegen.getMaxPropertySet(argtype);
                for (let i = 0; i < allprops.length; ++i) {
                    const pname = allprops[i];
                    if (oftype.entries.find((entry) => entry.name === pname) === undefined) {
                        checks.push(`(= (select arecord "${pname}") bsqterm@clear)`);
                    }
                }
            }
            else {
                let nv = "bsqrecord_array_empty";
                for (let i = 0; i < oftype.entries.length; ++i) {
                    const pname = oftype.entries[i].name;
                    nv = `(store ${nv} "${pname}" (select arecord "${pname}"))`;
                }
                checks.push(`(= ${nv} arecord)`);
            }
            let op = "";
            if (checks.includes("false")) {
                op = "false";
            }
            else {
                checks = checks.filter((chk) => chk !== "true");
                if (checks.length === 0) {
                    op = "true";
                }
                else if (checks.length === 1) {
                    op = checks[0];
                }
                else {
                    op = `(and ${checks.join(" ")})`;
                }
            }
            const decl = "(define-fun " + subtypesig
                + "\n  " + op
                + ")\n";
            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }
        return `(subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)} ${argv})`;
    }
    generateSubtypeConceptCheck(argv, argtype, oftype) {
        const subtypesig = `subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)} ((val BTerm)) Bool`;
        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            const moftype = this.typegen.getMIRType(oftype.trkey);
            let getenum = new smt_exp_1.SMTLet("nenum", new smt_exp_1.SMTValue(`(bsqterm_get_nominal_type val)`));
            let fchk = this.generateConceptArrayLookup(`(bsqterm_get_nominal_type val)`, oftype);
            let chkrest = new smt_exp_1.SMTValue(fchk);
            let rchk = "[INVALID]";
            if (this.typegen.assembly.subtypeOf(this.typegen.recordType, moftype)) {
                rchk = "true";
            }
            else if (this.typegen.assembly.subtypeOf(moftype, this.typegen.apiType)) {
                rchk = `(not (= (bsqterm_record_flag val) 0))`;
            }
            else if (this.typegen.assembly.subtypeOf(moftype, this.typegen.podType)) {
                rchk = `(= (bsqterm_tuple_flag val) 0)`;
            }
            else {
                rchk = "false";
            }
            let chkrecord = new smt_exp_1.SMTCond(new smt_exp_1.SMTValue("(= nenum MIRNominalTypeEnum_Record)"), new smt_exp_1.SMTValue(rchk), chkrest);
            let tchk = "[INVALID]";
            if (this.typegen.assembly.subtypeOf(this.typegen.tupleType, moftype)) {
                tchk = "true";
            }
            else if (this.typegen.assembly.subtypeOf(moftype, this.typegen.apiType)) {
                tchk = `(not (= (bsqterm_tuple_flag val) 0))`;
            }
            else if (this.typegen.assembly.subtypeOf(moftype, this.typegen.podType)) {
                tchk = `(= (bsqterm_tuple_flag val) 3)`;
            }
            else {
                tchk = "false";
            }
            let chktuple = new smt_exp_1.SMTCond(new smt_exp_1.SMTValue("(= nenum MIRNominalTypeEnum_Tuple)"), new smt_exp_1.SMTValue(tchk), chkrecord);
            console.log(getenum.emit());
            console.log(chktuple.emit());
            const op = getenum.bind(chktuple);
            console.log(op.emit());
            const decl = "(define-fun " + subtypesig
                + "\n  " + op.emit("  ")
                + ")\n";
            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }
        return `(subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)} ${argv})`;
    }
    generateFastTupleTypeCheck(arg, argtype, oftype) {
        if (this.typegen.typecheckIsName(argtype, /^NSCore::Bool$/) || this.typegen.typecheckIsName(argtype, /^NSCore::Int$/) || this.typegen.typecheckIsName(argtype, /^NSCore::String$/)) {
            return "false";
        }
        else if (this.typegen.typecheckIsName(argtype, /^NSCore::SafeString<.*>$/) || this.typegen.typecheckIsName(argtype, /^NSCore::StringOf<.*>$/)) {
            return "false";
        }
        else if (this.typegen.typecheckIsName(argtype, /^NSCore::GUID$/) || this.typegen.typecheckIsName(argtype, /^NSCore::LogicalTime$/)
            || this.typegen.typecheckIsName(argtype, /^NSCore::DataHash$/) || this.typegen.typecheckIsName(argtype, /^NSCore::CryptoHash$/)) {
            return "false";
        }
        else if (this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.enumtype) || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.idkeytype)
            || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.guididkeytype) || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.logicaltimeidkeytype)
            || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.contenthashidkeytype)) {
            return "false";
        }
        else {
            if (this.typegen.typecheckAllKeys(argtype)) {
                return "false";
            }
            else if (this.typegen.typecheckIsName(argtype, /^NSCore::Buffer<.*>$/)) {
                return "false";
            }
            else if (this.typegen.typecheckIsName(argtype, /^NSCore::ISOTime$/) || this.typegen.typecheckIsName(argtype, /^NSCore::Regex$/)) {
                return "false";
            }
            else if (this.typegen.typecheckRecord(argtype)) {
                return "false";
            }
            else if (this.typegen.typecheckUEntity(argtype)) {
                return "false";
            }
            else if (this.typegen.typecheckTuple(argtype)) {
                return this.generateSubtypeTupleCheck(`(bsq_tuple_entries ${arg})`, argtype, oftype);
            }
            else {
                const tsc = this.generateSubtypeTupleCheck(`(bsq_tuple_entries (bsqterm_tuple_value ${arg}))`, argtype, oftype);
                return `(and (is-bsqterm_tuple ${arg}) ${tsc})`;
            }
        }
    }
    generateFastRecordTypeCheck(arg, argtype, oftype) {
        if (this.typegen.typecheckIsName(argtype, /^NSCore::Bool$/) || this.typegen.typecheckIsName(argtype, /^NSCore::Int$/) || this.typegen.typecheckIsName(argtype, /^NSCore::String$/)) {
            return "false";
        }
        else if (this.typegen.typecheckIsName(argtype, /^NSCore::SafeString<.*>$/) || this.typegen.typecheckIsName(argtype, /^NSCore::StringOf<.*>$/)) {
            return "false";
        }
        else if (this.typegen.typecheckIsName(argtype, /^NSCore::GUID$/) || this.typegen.typecheckIsName(argtype, /^NSCore::LogicalTime$/)
            || this.typegen.typecheckIsName(argtype, /^NSCore::DataHash$/) || this.typegen.typecheckIsName(argtype, /^NSCore::CryptoHash$/)) {
            return "false";
        }
        else if (this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.enumtype) || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.idkeytype)
            || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.guididkeytype) || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.logicaltimeidkeytype)
            || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.contenthashidkeytype)) {
            return "false";
        }
        else {
            if (this.typegen.typecheckAllKeys(argtype)) {
                return "false";
            }
            if (this.typegen.typecheckAllKeys(argtype)) {
                return "false";
            }
            else if (this.typegen.typecheckIsName(argtype, /^NSCore::Buffer<.*>$/)) {
                return "false";
            }
            else if (this.typegen.typecheckIsName(argtype, /^NSCore::ISOTime$/) || this.typegen.typecheckIsName(argtype, /^NSCore::Regex$/)) {
                return "false";
            }
            else if (this.typegen.typecheckTuple(argtype)) {
                return "false";
            }
            else if (this.typegen.typecheckUEntity(argtype)) {
                return "false";
            }
            else if (this.typegen.typecheckRecord(argtype)) {
                return this.generateSubtypeRecordCheck(`(bsq_record_entries ${arg})`, argtype, oftype);
            }
            else {
                const tsc = this.generateSubtypeRecordCheck(`(bsq_record_entries (bsqterm_record_value ${arg}))`, argtype, oftype);
                return `(and (is-bsqterm_record ${arg}) ${tsc})`;
            }
        }
    }
    generateFastEntityTypeCheck(arg, argtype, oftype) {
        if (this.typegen.typecheckIsName(argtype, /^NSCore::Bool$/) || this.typegen.typecheckIsName(argtype, /^NSCore::Int$/) || this.typegen.typecheckIsName(argtype, /^NSCore::String$/)) {
            return oftype.ekey === argtype.trkey ? "true" : "false";
        }
        else if (this.typegen.typecheckIsName(argtype, /^NSCore::SafeString<.*>$/) || this.typegen.typecheckIsName(argtype, /^NSCore::StringOf<.*>$/)) {
            return oftype.ekey === argtype.trkey ? "true" : "false";
        }
        else if (this.typegen.typecheckIsName(argtype, /^NSCore::GUID$/) || this.typegen.typecheckIsName(argtype, /^NSCore::LogicalTime$/)
            || this.typegen.typecheckIsName(argtype, /^NSCore::DataHash$/) || this.typegen.typecheckIsName(argtype, /^NSCore::CryptoHash$/)) {
            return oftype.ekey === argtype.trkey ? "true" : "false";
        }
        else if (this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.enumtype) || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.idkeytype)
            || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.guididkeytype) || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.logicaltimeidkeytype)
            || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.contenthashidkeytype)) {
            return oftype.ekey === argtype.trkey ? "true" : "false";
        }
        else {
            if (this.typegen.typecheckAllKeys(argtype)) {
                return `(= (bsqkey_get_nominal_type ${arg}) "${this.typegen.mangleStringForSMT(oftype.ekey)}")`;
            }
            else if (this.typegen.typecheckIsName(argtype, /^NSCore::Buffer<.*>$/)) {
                return oftype.ekey === argtype.trkey ? "true" : "false";
            }
            else if (this.typegen.typecheckIsName(argtype, /^NSCore::ISOTime$/) || this.typegen.typecheckIsName(argtype, /^NSCore::Regex$/)) {
                return oftype.ekey === argtype.trkey ? "true" : "false";
            }
            else if (this.typegen.typecheckTuple(argtype) || this.typegen.typecheckRecord(argtype)) {
                return "false";
            }
            else if (this.typegen.typecheckUEntity(argtype)) {
                return oftype.ekey === argtype.trkey ? "true" : "false";
            }
            else {
                return `(= (bsqterm_get_nominal_type ${arg}) "${this.typegen.mangleStringForSMT(oftype.ekey)}")`;
            }
        }
    }
    generateConceptArrayLookup(access, oftype) {
        const lookups = oftype.ckeys.map((ckey) => {
            const sizestr = this.typegen.getSubtypesArrayCount(ckey);
            return sizestr === 0 ? "false" : `(select MIRConceptSubtypeArray$${this.typegen.mangleStringForSMT(ckey)} ${access})`;
        });
        if (lookups.find((op) => op === "false")) {
            return "false";
        }
        else if (lookups.length === 1) {
            return lookups[0];
        }
        else {
            return `(and ${lookups.join(" ")})`;
        }
    }
    generateFastConceptTypeCheck(arg, argtype, oftype) {
        if (oftype.trkey === "NSCore::Any") {
            return "true";
        }
        if (oftype.trkey === "NSCore::Some") {
            if (!this.typegen.assembly.subtypeOf(this.typegen.noneType, argtype)) {
                return "true";
            }
            else {
                if (this.typegen.typecheckAllKeys(argtype)) {
                    return `(not (= ${arg} bsqkey_none))`;
                }
                else {
                    return `(not (= ${arg} bsqterm_none))`;
                }
            }
        }
        const moftype = this.typegen.getMIRType(oftype.trkey);
        if (this.typegen.typecheckIsName(argtype, /^NSCore::Bool$/) || this.typegen.typecheckIsName(argtype, /^NSCore::Int$/) || this.typegen.typecheckIsName(argtype, /^NSCore::String$/)) {
            return this.typegen.assembly.subtypeOf(argtype, moftype) ? "true" : "false";
        }
        else if (this.typegen.typecheckIsName(argtype, /^NSCore::SafeString<.*>$/) || this.typegen.typecheckIsName(argtype, /^NSCore::StringOf<.*>$/)) {
            return this.typegen.assembly.subtypeOf(argtype, moftype) ? "true" : "false";
        }
        else if (this.typegen.typecheckIsName(argtype, /^NSCore::GUID$/) || this.typegen.typecheckIsName(argtype, /^NSCore::LogicalTime$/)
            || this.typegen.typecheckIsName(argtype, /^NSCore::DataHash$/) || this.typegen.typecheckIsName(argtype, /^NSCore::CryptoHash$/)) {
            return this.typegen.assembly.subtypeOf(argtype, moftype) ? "true" : "false";
        }
        else if (this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.enumtype) || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.idkeytype)
            || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.guididkeytype) || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.logicaltimeidkeytype)
            || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.contenthashidkeytype)) {
            return this.typegen.assembly.subtypeOf(argtype, moftype) ? "true" : "false";
        }
        else {
            if (this.typegen.typecheckAllKeys(argtype)) {
                return this.generateConceptArrayLookup(`(bsqkey_get_nominal_type ${arg})`, oftype);
            }
            else if (this.typegen.typecheckIsName(argtype, /^NSCore::Buffer<.*>$/)) {
                return this.typegen.assembly.subtypeOf(argtype, moftype) ? "true" : "false";
            }
            else if (this.typegen.typecheckIsName(argtype, /^NSCore::ISOTime$/) || this.typegen.typecheckIsName(argtype, /^NSCore::Regex$/)) {
                return this.typegen.assembly.subtypeOf(argtype, moftype) ? "true" : "false";
            }
            else if (this.typegen.typecheckTuple(argtype)) {
                if (this.typegen.assembly.subtypeOf(this.typegen.tupleType, moftype)) {
                    return "true";
                }
                if (this.typegen.assembly.subtypeOf(moftype, this.typegen.apiType)) {
                    return `(not (= (bsqterm_tuple_flag ${arg}) 0))`;
                }
                if (this.typegen.assembly.subtypeOf(moftype, this.typegen.podType)) {
                    return `(= (bsqterm_tuple_flag ${arg}) 3)`;
                }
                return "false";
            }
            else if (this.typegen.typecheckRecord(argtype)) {
                if (this.typegen.assembly.subtypeOf(this.typegen.tupleType, moftype)) {
                    return "true";
                }
                if (this.typegen.assembly.subtypeOf(moftype, this.typegen.apiType)) {
                    return `(not (= (bsqterm_record_flag ${arg}) 0))`;
                }
                if (this.typegen.assembly.subtypeOf(moftype, this.typegen.podType)) {
                    return `(= (bsqterm_record_flag ${arg}) 3)`;
                }
                return "false";
            }
            else if (this.typegen.typecheckUEntity(argtype)) {
                return this.typegen.assembly.subtypeOf(argtype, moftype) ? "true" : "false";
            }
            else {
                const simplenominalok = moftype.options.every((copt) => {
                    const cc = this.typegen.getMIRType(copt.trkey);
                    const maybetuple = this.typegen.assembly.subtypeOf(this.typegen.tupleType, cc);
                    const mayberecord = this.typegen.assembly.subtypeOf(this.typegen.recordType, cc);
                    const maybepod = this.typegen.assembly.subtypeOf(this.typegen.podType, cc);
                    const maybeapi = this.typegen.assembly.subtypeOf(this.typegen.apiType, cc);
                    return !(maybetuple || mayberecord || maybepod || maybeapi);
                });
                if (simplenominalok) {
                    return this.generateConceptArrayLookup(`(bsqterm_get_nominal_type ${arg})`, oftype);
                }
                else {
                    return this.generateSubtypeConceptCheck(arg, argtype, oftype);
                }
            }
        }
    }
    generateTypeCheck(arg, argtype, inferargtype, oftype) {
        if (inferargtype.trkey !== argtype.trkey) {
            arg = this.typegen.coerce(new smt_exp_1.SMTValue(arg), argtype, inferargtype).emit();
        }
        if (this.typegen.assembly.subtypeOf(inferargtype, oftype)) {
            return "true";
        }
        const tests = oftype.options.map((topt) => {
            const mtype = this.typegen.getMIRType(topt.trkey);
            assert(mtype !== undefined, "We should generate all the component types by default??");
            if (topt instanceof mir_assembly_1.MIREntityType) {
                return this.generateFastEntityTypeCheck(arg, inferargtype, topt);
            }
            else if (topt instanceof mir_assembly_1.MIRConceptType) {
                return this.generateFastConceptTypeCheck(arg, inferargtype, topt);
            }
            else if (topt instanceof mir_assembly_1.MIRTupleType) {
                return this.generateFastTupleTypeCheck(arg, inferargtype, topt);
            }
            else {
                assert(topt instanceof mir_assembly_1.MIRRecordType);
                return this.generateFastRecordTypeCheck(arg, inferargtype, topt);
            }
        })
            .filter((test) => test !== "false");
        if (tests.length === 0) {
            return "false";
        }
        else if (tests.includes("true")) {
            return "true";
        }
        else if (tests.length === 1) {
            return tests[0];
        }
        else {
            return `(or ${tests.join(" ")})`;
        }
    }
    generateMIRPackStore(op) {
        if (Array.isArray(op.src)) {
            let ops = new smt_exp_1.SMTLet(this.varToSMTName(op.names[0]), this.argToSMT(op.src[0], this.getArgType(op.names[0])));
            for (let i = 1; i < op.src.length; ++i) {
                ops = ops.bind(new smt_exp_1.SMTLet(this.varToSMTName(op.names[i]), this.argToSMT(op.src[i], this.getArgType(op.names[i]))));
            }
            return ops;
        }
        else {
            const eltype = this.getArgType(op.src).options[0];
            const tlist = eltype.entries;
            const getter0 = new smt_exp_1.SMTValue(`(${this.typegen.generateEntityAccessor(eltype.trkey, `entry_0`)} ${this.varToSMTName(op.src)})`);
            let ops = new smt_exp_1.SMTLet(this.varToSMTName(op.names[0]), getter0);
            for (let i = 1; i < tlist.length; ++i) {
                const getteri = new smt_exp_1.SMTValue(`(${this.typegen.generateEntityAccessor(eltype.trkey, `entry_${i}`)} ${this.varToSMTName(op.src)})`);
                ops = ops.bind(new smt_exp_1.SMTLet(this.varToSMTName(op.names[i]), getteri));
            }
            return ops;
        }
    }
    generateStmt(op, fromblck, gas) {
        switch (op.tag) {
            case mir_ops_1.MIROpTag.MIRLoadConst: {
                const lcv = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(lcv.trgt), this.generateConstantExp(lcv.src, this.getArgType(lcv.trgt)));
            }
            case mir_ops_1.MIROpTag.MIRLoadConstRegex: {
                const lcr = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(lcr.trgt), new smt_exp_1.SMTValue(`(bsq_regex@cons "${lcr.restr}")`));
            }
            case mir_ops_1.MIROpTag.MIRLoadConstSafeString: {
                return this.generateLoadConstSafeString(op);
            }
            case mir_ops_1.MIROpTag.MIRLoadConstTypedString: {
                return this.generateLoadConstTypedString(op);
            }
            case mir_ops_1.MIROpTag.MIRAccessConstantValue: {
                const acv = op;
                return this.generateAccessConstantValue(acv);
            }
            case mir_ops_1.MIROpTag.MIRLoadFieldDefaultValue: {
                const ldv = op;
                return this.generateLoadFieldDefaultValue(ldv);
            }
            case mir_ops_1.MIROpTag.MIRAccessArgVariable: {
                const lav = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(lav.trgt), this.argToSMT(lav.name, this.getArgType(lav.trgt)));
            }
            case mir_ops_1.MIROpTag.MIRAccessLocalVariable: {
                const llv = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(llv.trgt), this.argToSMT(llv.name, this.getArgType(llv.trgt)));
            }
            case mir_ops_1.MIROpTag.MIRInvokeInvariantCheckDirect: {
                const icd = op;
                return this.generateMIRInvokeInvariantCheckDirect(icd);
            }
            case mir_ops_1.MIROpTag.MIRInvokeInvariantCheckVirtualTarget: {
                return NOT_IMPLEMENTED("MIRInvokeInvariantCheckVirtualTarget");
            }
            case mir_ops_1.MIROpTag.MIRConstructorPrimary: {
                const cp = op;
                return this.generateMIRConstructorPrimary(cp);
            }
            case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
                const cpce = op;
                return this.generateMIRConstructorPrimaryCollectionEmpty(cpce);
            }
            case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                const cpcs = op;
                return this.generateMIRConstructorPrimaryCollectionSingletons(cpcs);
            }
            case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionCopies: {
                return NOT_IMPLEMENTED("MIRConstructorPrimaryCollectionCopies");
            }
            case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                return NOT_IMPLEMENTED("MIRConstructorPrimaryCollectionMixed");
            }
            case mir_ops_1.MIROpTag.MIRConstructorTuple: {
                const tc = op;
                return this.generateMIRConstructorTuple(tc);
            }
            case mir_ops_1.MIROpTag.MIRConstructorRecord: {
                const tr = op;
                return this.generateMIRConstructorRecord(tr);
            }
            case mir_ops_1.MIROpTag.MIRConstructorEphemeralValueList: {
                const te = op;
                return this.generateMIRConstructorEphemeralValueList(te);
            }
            case mir_ops_1.MIROpTag.MIRAccessFromIndex: {
                const ai = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(ai.trgt), this.generateMIRAccessFromIndexExpression(ai.arg, ai.idx, this.typegen.getMIRType(ai.resultAccessType)));
            }
            case mir_ops_1.MIROpTag.MIRProjectFromIndecies: {
                const pi = op;
                return this.generateMIRProjectFromIndecies(pi, this.typegen.getMIRType(pi.resultProjectType));
            }
            case mir_ops_1.MIROpTag.MIRAccessFromProperty: {
                const ap = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(ap.trgt), this.generateMIRAccessFromPropertyExpression(ap.arg, ap.property, this.typegen.getMIRType(ap.resultAccessType)));
            }
            case mir_ops_1.MIROpTag.MIRProjectFromProperties: {
                const pp = op;
                return this.generateMIRProjectFromProperties(pp, this.typegen.getMIRType(pp.resultProjectType));
            }
            case mir_ops_1.MIROpTag.MIRAccessFromField: {
                const af = op;
                return this.generateMIRAccessFromField(af, this.typegen.getMIRType(af.resultAccessType));
            }
            case mir_ops_1.MIROpTag.MIRProjectFromFields: {
                const pf = op;
                return this.generateMIRProjectFromFields(pf);
            }
            case mir_ops_1.MIROpTag.MIRProjectFromTypeTuple: {
                return NOT_IMPLEMENTED("MIRProjectFromTypeTuple");
            }
            case mir_ops_1.MIROpTag.MIRProjectFromTypeRecord: {
                return NOT_IMPLEMENTED("MIRProjectFromTypeRecord");
            }
            case mir_ops_1.MIROpTag.MIRProjectFromTypeNominal: {
                return NOT_IMPLEMENTED("MIRProjectFromTypeNominal");
            }
            case mir_ops_1.MIROpTag.MIRModifyWithIndecies: {
                const mi = op;
                return this.generateMIRModifyWithIndecies(mi, this.typegen.getMIRType(mi.resultTupleType));
            }
            case mir_ops_1.MIROpTag.MIRModifyWithProperties: {
                const mp = op;
                return this.generateMIRModifyWithProperties(mp, this.typegen.getMIRType(mp.resultRecordType));
            }
            case mir_ops_1.MIROpTag.MIRModifyWithFields: {
                const mf = op;
                return this.generateMIRModifyWithFields(mf);
            }
            case mir_ops_1.MIROpTag.MIRStructuredExtendTuple: {
                const si = op;
                return this.generateMIRStructuredExtendTuple(si, this.typegen.getMIRType(si.resultTupleType));
            }
            case mir_ops_1.MIROpTag.MIRStructuredExtendRecord: {
                const sp = op;
                return this.generateMIRStructuredExtendRecord(sp, this.typegen.getMIRType(sp.resultRecordType));
            }
            case mir_ops_1.MIROpTag.MIRStructuredExtendObject: {
                const so = op;
                return this.generateMIRStructuredExtendObject(so);
            }
            case mir_ops_1.MIROpTag.MIRLoadFromEpehmeralList: {
                const le = op;
                return this.generateMIRLoadFromEpehmeralList(le);
            }
            case mir_ops_1.MIROpTag.MIRInvokeFixedFunction: {
                const invk = op;
                return this.generateMIRInvokeFixedFunction(invk, gas);
            }
            case mir_ops_1.MIROpTag.MIRInvokeVirtualTarget: {
                return NOT_IMPLEMENTED("MIRInvokeVirtualTarget");
            }
            case mir_ops_1.MIROpTag.MIRPrefixOp: {
                const pfx = op;
                if (pfx.op === "!") {
                    const tval = this.generateTruthyConvert(pfx.arg);
                    return new smt_exp_1.SMTLet(this.varToSMTName(pfx.trgt), new smt_exp_1.SMTValue(`(not ${tval.emit()})`));
                }
                else {
                    if (pfx.op === "-") {
                        if (pfx.arg instanceof mir_ops_1.MIRConstantInt) {
                            return new smt_exp_1.SMTLet(this.varToSMTName(pfx.trgt), new smt_exp_1.SMTValue(`-${pfx.arg.value}`));
                        }
                        else {
                            return new smt_exp_1.SMTLet(this.varToSMTName(pfx.trgt), new smt_exp_1.SMTValue(`(* -1 ${this.argToSMT(pfx.arg, this.typegen.intType).emit()})`));
                        }
                    }
                    else {
                        return new smt_exp_1.SMTLet(this.varToSMTName(pfx.trgt), this.argToSMT(pfx.arg, this.typegen.intType));
                    }
                }
            }
            case mir_ops_1.MIROpTag.MIRBinOp: {
                const bop = op;
                if (bop.op === "*") {
                    if (bop.rhs instanceof mir_ops_1.MIRConstantInt || bop.lhs instanceof mir_ops_1.MIRConstantInt) {
                        return new smt_exp_1.SMTLet(this.varToSMTName(bop.trgt), new smt_exp_1.SMTValue(`(* ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                    }
                    else {
                        return new smt_exp_1.SMTLet(this.varToSMTName(bop.trgt), new smt_exp_1.SMTValue(`(mult_op ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                    }
                }
                else if (bop.op === "/") {
                    if (bop.rhs instanceof mir_ops_1.MIRConstantInt || bop.lhs instanceof mir_ops_1.MIRConstantInt) {
                        const divres = new smt_exp_1.SMTLet(this.varToSMTName(bop.trgt), new smt_exp_1.SMTValue(`(/ ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                        return new smt_exp_1.SMTCond(new smt_exp_1.SMTValue(`(= ${this.argToSMT(bop.rhs, this.typegen.intType).emit()} 0)`), this.generateErrorCreate(op.sinfo, this.typegen.getSMTTypeFor(this.currentRType)), divres);
                    }
                    else {
                        const divres = new smt_exp_1.SMTLet(this.varToSMTName(bop.trgt), new smt_exp_1.SMTValue(`(div_op ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                        return new smt_exp_1.SMTCond(new smt_exp_1.SMTValue(`(= ${this.argToSMT(bop.rhs, this.typegen.intType).emit()} 0)`), this.generateErrorCreate(op.sinfo, this.typegen.getSMTTypeFor(this.currentRType)), divres);
                    }
                }
                else if (bop.op === "%") {
                    const modres = new smt_exp_1.SMTLet(this.varToSMTName(bop.trgt), new smt_exp_1.SMTValue(`(mod_op ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                    return new smt_exp_1.SMTCond(new smt_exp_1.SMTValue(`(or (< ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} 0) (<= ${this.argToSMT(bop.rhs, this.typegen.intType).emit()} 0))`), this.generateErrorCreate(op.sinfo, this.typegen.getSMTTypeFor(this.currentRType)), modres);
                }
                else {
                    return new smt_exp_1.SMTLet(this.varToSMTName(bop.trgt), new smt_exp_1.SMTValue(`(${bop.op} ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                }
            }
            case mir_ops_1.MIROpTag.MIRGetKey: {
                return NOT_IMPLEMENTED("MIRGetKey");
            }
            case mir_ops_1.MIROpTag.MIRBinEq: {
                const beq = op;
                const lhvtypeinfer = this.typegen.getMIRType(beq.lhsInferType);
                const rhvtypeinfer = this.typegen.getMIRType(beq.rhsInferType);
                return new smt_exp_1.SMTLet(this.varToSMTName(beq.trgt), new smt_exp_1.SMTValue(this.generateEquals(beq.op, lhvtypeinfer, beq.lhs, rhvtypeinfer, beq.rhs, !beq.relaxed)));
            }
            case mir_ops_1.MIROpTag.MIRBinCmp: {
                const bcmp = op;
                const lhvtypeinfer = this.typegen.getMIRType(bcmp.lhsInferType);
                const rhvtypeinfer = this.typegen.getMIRType(bcmp.rhsInferType);
                return new smt_exp_1.SMTLet(this.varToSMTName(bcmp.trgt), new smt_exp_1.SMTValue(this.generateCompare(bcmp.op, lhvtypeinfer, bcmp.lhs, rhvtypeinfer, bcmp.rhs)));
            }
            case mir_ops_1.MIROpTag.MIRIsTypeOfNone: {
                const ton = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(ton.trgt), this.generateNoneCheck(ton.arg));
            }
            case mir_ops_1.MIROpTag.MIRIsTypeOfSome: {
                const tos = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(tos.trgt), new smt_exp_1.SMTValue(`(not ${this.generateNoneCheck(tos.arg).emit()})`));
            }
            case mir_ops_1.MIROpTag.MIRIsTypeOf: {
                const top = op;
                const oftype = this.typegen.getMIRType(top.oftype);
                const argtype = this.getArgType(top.arg);
                const infertype = this.typegen.getMIRType(top.argInferType);
                return new smt_exp_1.SMTLet(this.varToSMTName(top.trgt), new smt_exp_1.SMTValue(this.generateTypeCheck(this.argToSMT(top.arg, infertype).emit(), argtype, infertype, oftype)));
            }
            case mir_ops_1.MIROpTag.MIRRegAssign: {
                const regop = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(regop.trgt), this.argToSMT(regop.src, this.getArgType(regop.trgt)));
            }
            case mir_ops_1.MIROpTag.MIRTruthyConvert: {
                const tcop = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(tcop.trgt), this.generateTruthyConvert(tcop.src));
            }
            case mir_ops_1.MIROpTag.MIRVarStore: {
                const vsop = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(vsop.name), this.argToSMT(vsop.src, this.getArgType(vsop.name)));
            }
            case mir_ops_1.MIROpTag.MIRPackStore: {
                const vps = op;
                return this.generateMIRPackStore(vps);
            }
            case mir_ops_1.MIROpTag.MIRReturnAssign: {
                const raop = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(raop.name), this.argToSMT(raop.src, this.getArgType(raop.name)));
            }
            case mir_ops_1.MIROpTag.MIRAbort: {
                const aop = op;
                return this.generateErrorCreate(aop.sinfo, this.typegen.getSMTTypeFor(this.currentRType));
            }
            case mir_ops_1.MIROpTag.MIRDebug: {
                return undefined;
            }
            case mir_ops_1.MIROpTag.MIRJump: {
                return undefined;
            }
            case mir_ops_1.MIROpTag.MIRJumpCond: {
                const cjop = op;
                const smttest = this.generateTruthyConvert(cjop.arg);
                return new smt_exp_1.SMTCond(smttest, smt_exp_1.SMTFreeVar.generate("#true_trgt#"), smt_exp_1.SMTFreeVar.generate("#false_trgt#"));
            }
            case mir_ops_1.MIROpTag.MIRJumpNone: {
                const njop = op;
                return new smt_exp_1.SMTCond(this.generateNoneCheck(njop.arg), smt_exp_1.SMTFreeVar.generate("#true_trgt#"), smt_exp_1.SMTFreeVar.generate("#false_trgt#"));
            }
            case mir_ops_1.MIROpTag.MIRPhi: {
                const pop = op;
                const uvar = pop.src.get(fromblck);
                return new smt_exp_1.SMTLet(this.varToSMTName(pop.trgt), this.argToSMT(uvar, this.getArgType(pop.trgt)));
            }
            case mir_ops_1.MIROpTag.MIRVarLifetimeStart:
            case mir_ops_1.MIROpTag.MIRVarLifetimeEnd: {
                return undefined;
            }
            default: {
                return NOT_IMPLEMENTED(`Missing case ${op.tag}`);
            }
        }
    }
    generateBlockExps(block, fromblock, blocks, gas) {
        const exps = [];
        for (let i = 0; i < block.ops.length; ++i) {
            const exp = this.generateStmt(block.ops[i], fromblock, gas);
            if (exp !== undefined) {
                exps.push(exp);
            }
        }
        if (block.label === "exit") {
            const resulttype = this.typegen.getSMTTypeFor(this.currentRType);
            let rexp = new smt_exp_1.SMTValue(`(result_success@${resulttype} _return_)`);
            for (let i = exps.length - 1; i >= 0; --i) {
                rexp = exps[i].bind(rexp, "#body#");
            }
            return rexp;
        }
        else {
            const jop = block.ops[block.ops.length - 1];
            if (jop.tag === mir_ops_1.MIROpTag.MIRAbort) {
                let rexp = exps[exps.length - 1];
                for (let i = exps.length - 2; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }
                return rexp;
            }
            else if (jop.tag === mir_ops_1.MIROpTag.MIRJump) {
                let rexp = this.generateBlockExps(blocks.get(jop.trgtblock), block.label, blocks, gas);
                for (let i = exps.length - 1; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }
                return rexp;
            }
            else {
                assert(jop.tag === mir_ops_1.MIROpTag.MIRJumpCond || jop.tag === mir_ops_1.MIROpTag.MIRJumpNone);
                let tblock = ((jop.tag === mir_ops_1.MIROpTag.MIRJumpCond) ? blocks.get(jop.trueblock) : blocks.get(jop.noneblock));
                let texp = this.generateBlockExps(tblock, block.label, blocks, gas);
                let fblock = ((jop.tag === mir_ops_1.MIROpTag.MIRJumpCond) ? blocks.get(jop.falseblock) : blocks.get(jop.someblock));
                let fexp = this.generateBlockExps(fblock, block.label, blocks, gas);
                let rexp = exps[exps.length - 1].bind(texp, "#true_trgt#").bind(fexp, "#false_trgt#");
                for (let i = exps.length - 2; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }
                return rexp;
            }
        }
    }
    generateSMTInvoke(idecl, cscc, gas, gasdown) {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.getMIRType(idecl.resultType);
        this.currentSCC = cscc;
        let argvars = new Map();
        idecl.params.forEach((arg) => argvars.set(arg.name, this.assembly.typeMap.get(arg.type)));
        const args = idecl.params.map((arg) => `(${this.varNameToSMTName(arg.name)} ${this.typegen.getSMTTypeFor(this.typegen.getMIRType(arg.type))})`);
        const restype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(idecl.resultType));
        const decl = `(define-fun ${this.invokenameToSMT(idecl.key)}${gas !== undefined ? `@gas${gas}` : ""} (${args.join(" ")}) Result@${restype}`;
        if (idecl instanceof mir_assembly_1.MIRInvokeBodyDecl) {
            this.vtypes = new Map();
            idecl.body.vtypes.forEach((tkey, name) => {
                this.vtypes.set(name, this.typegen.getMIRType(tkey));
            });
            const blocks = idecl.body.body;
            const body = this.generateBlockExps(blocks.get("entry"), "[NO PREVIOUS]", blocks, gasdown);
            return `${decl} \n${body.emit("  ")})`;
        }
        else {
            assert(idecl instanceof mir_assembly_1.MIRInvokePrimitiveDecl);
            const params = idecl.params.map((arg) => this.varNameToSMTName(arg.name));
            return `${decl} \n  ${this.generateBuiltinBody(idecl, params).emit("  ")}\n)`;
        }
    }
    generateBuiltinBody(idecl, params) {
        const rtype = this.typegen.getMIRType(idecl.resultType);
        let bodyres = undefined;
        const enclkey = (idecl.enclosingDecl || "[NA]");
        switch (idecl.implkey) {
            case "enum_create": {
                bodyres = new smt_exp_1.SMTValue(`(bsq_enum@cons "${this.typegen.mangleStringForSMT(enclkey)}" ${params[0]})`);
                break;
            }
            case "list_size":
            case "set_size":
            case "map_size": {
                bodyres = this.typegen.generateSpecialTypeFieldAccessExp(enclkey, "size", params[0]);
                break;
            }
            case "list_unsafe_get": {
                bodyres = new smt_exp_1.SMTValue(`(select ${this.typegen.generateSpecialTypeFieldAccess(enclkey, "entries", params[0])} ${params[1]})`);
                break;
            }
            case "list_unsafe_add": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "entries", params[0]);
                const csize = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                bodyres = new smt_exp_1.SMTValue(`(${cons} (+ ${csize} 1) (store ${entries} ${csize} ${params[1]}))`);
                break;
            }
            case "list_unsafe_set": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "entries", params[0]);
                const csize = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                bodyres = new smt_exp_1.SMTValue(`(${cons} ${csize} (store ${entries} ${params[1]} ${params[2]}))`);
                break;
            }
            case "set_has_key":
            case "map_has_key": {
                bodyres = new smt_exp_1.SMTValue(`(select ${this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0])} ${params[1]})`);
                break;
            }
            case "map_at_key": {
                bodyres = new smt_exp_1.SMTValue(`(select ${this.typegen.generateSpecialTypeFieldAccess(enclkey, "keys", params[0])} ${params[1]})`);
                break;
            }
            case "set_at_val":
            case "map_at_val": {
                bodyres = new smt_exp_1.SMTValue(`(select ${this.typegen.generateSpecialTypeFieldAccess(enclkey, "values", params[0])} ${params[1]})`);
                break;
            }
            case "set_get_keylist":
            case "map_get_keylist": {
                bodyres = this.typegen.generateSpecialTypeFieldAccessExp(enclkey, "keylist", params[0]);
                break;
            }
            case "set_clear_val": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const size = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                const has = this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0]);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "values", params[0]);
                const klctype = this.typegen.getKeyListTypeForSet(this.typegen.assembly.entityDecls.get(enclkey));
                const kll = this.typegen.coerce(new smt_exp_1.SMTValue(params[2]), this.typegen.getMIRType(idecl.params[2].type), klctype);
                bodyres = new smt_exp_1.SMTValue(`(${cons} (- ${size} 1) (store ${has} ${params[1]} false) ${entries} ${kll.emit()})`);
                break;
            }
            case "map_clear_val": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const size = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                const has = this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0]);
                const keys = this.typegen.generateSpecialTypeFieldAccess(enclkey, "keys", params[0]);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "values", params[0]);
                const klctype = this.typegen.getKeyListTypeForMap(this.typegen.assembly.entityDecls.get(enclkey));
                const kll = this.typegen.coerce(new smt_exp_1.SMTValue(params[2]), this.typegen.getMIRType(idecl.params[2].type), klctype);
                bodyres = new smt_exp_1.SMTValue(`(${cons} (- ${size} 1) (store ${has} ${params[1]} false) ${keys} ${entries} ${kll.emit()})`);
                break;
            }
            case "set_unsafe_update": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const size = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                const has = this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0]);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "values", params[0]);
                const kl = this.typegen.generateSpecialTypeFieldAccess(enclkey, "keylist", params[0]);
                bodyres = new smt_exp_1.SMTValue(`(${cons} ${size} ${has} (store ${entries} ${params[1]} ${params[2]}) ${kl})`);
                break;
            }
            case "map_unsafe_update": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const size = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                const has = this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0]);
                const keys = this.typegen.generateSpecialTypeFieldAccess(enclkey, "keys", params[0]);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "values", params[0]);
                const kl = this.typegen.generateSpecialTypeFieldAccess(enclkey, "keylist", params[0]);
                bodyres = new smt_exp_1.SMTValue(`(${cons} ${size} ${has} ${keys} (store ${entries} ${params[1]} ${params[3]}) ${kl})`);
                break;
            }
            case "set_unsafe_add": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const size = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                const has = this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0]);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "values", params[0]);
                const klctype = this.typegen.getKeyListTypeForSet(this.typegen.assembly.entityDecls.get(enclkey));
                const kll = this.typegen.coerce(new smt_exp_1.SMTValue(params[3]), this.typegen.getMIRType(idecl.params[3].type), klctype);
                bodyres = new smt_exp_1.SMTValue(`(${cons} (+ ${size} 1) (store ${has} ${params[1]} true) (store ${entries} ${params[1]} ${params[2]}) ${kll.emit()})`);
                break;
            }
            case "map_unsafe_add": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const size = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                const has = this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0]);
                const keys = this.typegen.generateSpecialTypeFieldAccess(enclkey, "keys", params[0]);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "values", params[0]);
                const klctype = this.typegen.getKeyListTypeForMap(this.typegen.assembly.entityDecls.get(enclkey));
                const kll = this.typegen.coerce(new smt_exp_1.SMTValue(params[4]), this.typegen.getMIRType(idecl.params[4].type), klctype);
                bodyres = new smt_exp_1.SMTValue(`(${cons} (+ ${size} 1) (store ${has} ${params[1]} true) (store ${keys} ${params[1]} ${params[2]}) (store ${entries} ${params[1]} ${params[3]}) ${kll.emit()})`);
                break;
            }
            default: {
                bodyres = new smt_exp_1.SMTValue(`[Builtin not defined -- ${idecl.iname}]`);
                break;
            }
        }
        return new smt_exp_1.SMTValue(`(result_success@${this.typegen.getSMTTypeFor(rtype)} ${bodyres.emit()})`);
    }
}
exports.SMTBodyEmitter = SMTBodyEmitter;
//# sourceMappingURL=smtbody_emitter.js.map