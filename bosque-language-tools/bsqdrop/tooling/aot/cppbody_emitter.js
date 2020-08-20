"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const mir_assembly_1 = require("../../compiler/mir_assembly");
const mir_ops_1 = require("../../compiler/mir_ops");
const mir_info_1 = require("../../compiler/mir_info");
const assert = require("assert");
const type_repr_1 = require("./type_repr");
const cpp_regex_1 = require("./cpp_regex");
function NOT_IMPLEMENTED(msg) {
    throw new Error(`Not Implemented: ${msg}`);
}
function filenameClean(file) {
    return file.replace(/[\\]/g, "/");
}
class CPPBodyEmitter {
    constructor(assembly, typegen) {
        this.allPropertyNames = new Set();
        this.allConstStrings = new Map();
        this.allConstBigInts = new Map();
        this.currentFile = "[No File]";
        this.vtypes = new Map();
        this.generatedBlocks = new Map();
        this.subtypeOrderCtr = 0;
        this.subtypeFMap = new Map();
        this.checkedConcepts = new Set();
        this.vfieldLookups = [];
        this.vfieldProjects = [];
        this.vfieldUpdates = [];
        this.vobjmerges = [];
        this.assembly = assembly;
        this.typegen = typegen;
        this.currentRType = typegen.noneType;
    }
    static cleanStrRepr(s) {
        return "\"" + s.substring(1, s.length - 1) + "\"";
    }
    labelToCpp(label) {
        return label;
    }
    varNameToCppName(name) {
        if (name === "this") {
            return this.typegen.mangleStringForCpp("$this");
        }
        else if (name === "$$return") {
            return "$$return";
        }
        else {
            return this.typegen.mangleStringForCpp(name);
        }
    }
    varToCppName(varg) {
        return this.varNameToCppName(varg.nameID);
    }
    invokenameToCPP(ivk) {
        return this.typegen.mangleStringForCpp(ivk);
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
            return this.typegen.coerce("BSQ_VALUE_NONE", this.typegen.noneType, into);
        }
        else if (cval instanceof mir_ops_1.MIRConstantTrue) {
            return this.typegen.coerce("true", this.typegen.boolType, into);
        }
        else if (cval instanceof mir_ops_1.MIRConstantFalse) {
            return this.typegen.coerce("false", this.typegen.boolType, into);
        }
        else if (cval instanceof mir_ops_1.MIRConstantInt) {
            return this.typegen.coerce(cval.value, this.typegen.intType, into);
        }
        else if (cval instanceof mir_ops_1.MIRConstantBigInt) {
            const sname = "BIGINT__" + this.allConstBigInts.size;
            if (!this.allConstBigInts.has(cval.value)) {
                this.allConstBigInts.set(cval.value, sname);
            }
            const bint = `(Runtime::${this.allConstBigInts.get(cval.value)})`;
            return this.typegen.coerce(bint, this.typegen.bigIntType, into);
        }
        else if (cval instanceof mir_ops_1.MIRConstantFloat64) {
            return this.typegen.coerce(cval.digits(), this.typegen.float64Type, into);
        }
        else {
            assert(cval instanceof mir_ops_1.MIRConstantString);
            const sval = CPPBodyEmitter.cleanStrRepr(cval.value);
            const sname = "STR__" + this.allConstStrings.size;
            if (!this.allConstStrings.has(sval)) {
                this.allConstStrings.set(sval, sname);
            }
            const strval = `(&Runtime::${this.allConstStrings.get(sval)})`;
            return this.typegen.coerce(strval, this.typegen.stringType, into);
        }
    }
    argToCpp(arg, into) {
        if (arg instanceof mir_ops_1.MIRRegisterArgument) {
            return this.typegen.coerce(this.varToCppName(arg), this.getArgType(arg), into);
        }
        else {
            return this.generateConstantExp(arg, into);
        }
    }
    generateTruthyConvert(arg) {
        const argtype = this.getArgType(arg);
        if (this.assembly.subtypeOf(argtype, this.typegen.noneType)) {
            return "false";
        }
        else if (this.assembly.subtypeOf(argtype, this.typegen.boolType)) {
            return this.argToCpp(arg, this.typegen.boolType);
        }
        else {
            return `BSQ_GET_VALUE_TRUTHY(${this.varToCppName(arg)})`;
        }
    }
    generateNoneCheck(arg) {
        const argtype = this.getArgType(arg);
        if (this.assembly.subtypeOf(argtype, this.typegen.noneType)) {
            return "true";
        }
        else if (!this.assembly.subtypeOf(this.typegen.noneType, argtype)) {
            return "false";
        }
        else {
            return `BSQ_IS_VALUE_NONE(${this.varToCppName(arg)})`;
        }
    }
    generateLoadConstSafeString(op) {
        const sval = CPPBodyEmitter.cleanStrRepr(op.ivalue);
        const sname = "STR__" + this.allConstStrings.size;
        if (!this.allConstStrings.has(sval)) {
            this.allConstStrings.set(sval, sname);
        }
        const strval = `Runtime::${this.allConstStrings.get(sval)}`;
        const scopevar = this.varNameToCppName("$scope$");
        return `${this.varToCppName(op.trgt)} =  BSQ_NEW_ADD_SCOPE(${scopevar}, BSQSafeString, ${strval}.sdata, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(op.tskey)});`;
    }
    generateLoadConstTypedString(op) {
        const sval = CPPBodyEmitter.cleanStrRepr(op.ivalue);
        const sname = "STR__" + this.allConstStrings.size;
        if (!this.allConstStrings.has(sval)) {
            this.allConstStrings.set(sval, sname);
        }
        const strval = `Runtime::${this.allConstStrings.get(sval)}`;
        const scopevar = this.varNameToCppName("$scope$");
        let opstrs = [];
        if (op.pfunckey !== undefined) {
            const pfunc = (this.typegen.assembly.invokeDecls.get(op.pfunckey) || this.typegen.assembly.primitiveInvokeDecls.get(op.pfunckey));
            const errtype = this.typegen.getMIRType(op.errtype);
            const pexp = `${this.invokenameToCPP(op.pfunckey)}(&${strval}, ${scopevar})`;
            const tcexp = this.generateTypeCheck(pexp, this.typegen.getMIRType(pfunc.resultType), this.typegen.getMIRType(pfunc.resultType), errtype);
            opstrs.push(`if(${tcexp}) { BSQ_ABORT("Failed string validation", "${filenameClean(this.currentFile)}", ${op.sinfo.line}); }`);
        }
        opstrs.push(`${this.varToCppName(op.trgt)} =  BSQ_NEW_ADD_SCOPE(${scopevar}, BSQStringOf, ${strval}.sdata, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(op.tskey)});`);
        return opstrs.join(" ");
    }
    generateAccessConstantValue(cp) {
        const cdecl = this.assembly.constantDecls.get(cp.ckey);
        const scopevar = this.typegen.getRefCountableStatus(this.typegen.getMIRType(cdecl.declaredType)) !== "no" ? this.varNameToCppName("$scope$") : "";
        return `${this.varToCppName(cp.trgt)} = ${this.invokenameToCPP(cdecl.value)}(${scopevar});`;
    }
    generateLoadFieldDefaultValue(ld) {
        const fdecl = this.assembly.fieldDecls.get(ld.fkey);
        const scopevar = this.typegen.getRefCountableStatus(this.typegen.getMIRType(fdecl.declaredType)) !== "no" ? this.varNameToCppName("$scope$") : "";
        return `${this.varToCppName(ld.trgt)} = ${this.invokenameToCPP(fdecl.value)}(${scopevar});`;
    }
    generateMIRInvokeInvariantCheckDirect(ivop) {
        const fields = [...this.typegen.assembly.entityDecls.get(ivop.tkey).fields].sort((a, b) => a.name.localeCompare(b.name));
        const args = fields.map((f) => `${this.argToCpp(ivop.rcvr, this.typegen.getMIRType(ivop.tkey))}->${this.typegen.mangleStringForCpp(f.fkey)}`);
        return `${this.varToCppName(ivop.trgt)} = ${this.invokenameToCPP(ivop.ikey)}(${args.join(", ")});`;
    }
    generateMIRConstructorPrimary(cp) {
        const ctype = this.assembly.entityDecls.get(cp.tkey);
        const cppcrepr = this.typegen.getCPPReprFor(this.typegen.getMIRType(cp.tkey));
        if (cppcrepr instanceof type_repr_1.StructRepr) {
            const fvals = cp.args.map((arg, i) => {
                const ftype = this.typegen.getMIRType(ctype.fields[i].declaredType);
                return this.argToCpp(arg, ftype);
            });
            return `${this.varToCppName(cp.trgt)} = std::move(${cppcrepr.base}(${fvals.join(", ")}));`;
        }
        else {
            const fvals = cp.args.map((arg, i) => {
                const ftype = this.typegen.getMIRType(ctype.fields[i].declaredType);
                return this.typegen.generateConstructorArgInc(ftype, this.argToCpp(arg, ftype));
            });
            const scopevar = this.varNameToCppName("$scope$");
            return `${this.varToCppName(cp.trgt)} = BSQ_NEW_ADD_SCOPE(${scopevar}, ${cppcrepr.base}${fvals.length !== 0 ? (", " + fvals.join(", ")) : ""});`;
        }
    }
    generateMIRConstructorPrimaryCollectionEmpty(cpce) {
        const cpetype = this.typegen.getMIRType(cpce.tkey);
        const cppctype = this.typegen.getCPPReprFor(cpetype).base;
        const scopevar = this.varNameToCppName("$scope$");
        const conscall = `BSQ_NEW_ADD_SCOPE(${scopevar}, ${cppctype}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(cpce.tkey)})`;
        return `${this.varToCppName(cpce.trgt)} = ${conscall};`;
    }
    generateMIRConstructorPrimaryCollectionSingletons(cpcs) {
        const cpcstype = this.typegen.getMIRType(cpcs.tkey);
        const cppctype = this.typegen.getCPPReprFor(cpcstype).base;
        let conscall = "";
        const scopevar = this.varNameToCppName("$scope$");
        const ntype = `MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(cpcs.tkey)}`;
        if (this.typegen.typecheckIsName(cpcstype, /NSCore::List<.*>/)) {
            const oftype = this.assembly.entityDecls.get(cpcs.tkey).terms.get("T");
            const cvals = cpcs.args.map((arg) => this.typegen.generateConstructorArgInc(oftype, this.argToCpp(arg, oftype)));
            conscall = `BSQ_NEW_ADD_SCOPE(${scopevar}, ${cppctype}, ${ntype}, { ${cvals.join(", ")} })`;
        }
        else if (this.typegen.typecheckIsName(cpcstype, /NSCore::Stack<.*>/)) {
            const oftype = this.assembly.entityDecls.get(cpcs.tkey).terms.get("T");
            const cvals = cpcs.args.map((arg) => this.typegen.generateConstructorArgInc(oftype, this.argToCpp(arg, oftype)));
            conscall = `BSQ_NEW_ADD_SCOPE(${scopevar}, ${cppctype}, ${ntype}, { ${cvals.join(", ")} })`;
        }
        else if (this.typegen.typecheckIsName(cpcstype, /NSCore::Queue<.*>/)) {
            const oftype = this.assembly.entityDecls.get(cpcs.tkey).terms.get("T");
            const cvals = cpcs.args.map((arg) => this.typegen.generateConstructorArgInc(oftype, this.argToCpp(arg, oftype)));
            conscall = `BSQ_NEW_ADD_SCOPE(${scopevar}, ${cppctype}, ${ntype}, { ${cvals.join(", ")} })`;
        }
        else if (this.typegen.typecheckIsName(cpcstype, /NSCore::Set<.*>/) || this.typegen.typecheckIsName(cpcstype, /NSCore::DynamicSet<.*>/)) {
            const oftype = this.assembly.entityDecls.get(cpcs.tkey).terms.get("T");
            const cvals = cpcs.args.map((arg) => this.argToCpp(arg, oftype));
            const trepr = this.typegen.getCPPReprFor(oftype);
            const tops = this.typegen.getFunctorsForType(oftype);
            const pvals = `BSQSet<${trepr.std}, ${tops.dec}, ${tops.display}, ${tops.less}, ${tops.eq}>::processSingletonSetInit<${tops.inc}>({ ${cvals} })`;
            conscall = `BSQ_NEW_ADD_SCOPE(${scopevar}, ${cppctype}, ${ntype}, ${pvals})`;
        }
        else {
            const ktype = this.assembly.entityDecls.get(cpcs.tkey).terms.get("K");
            const vtype = this.assembly.entityDecls.get(cpcs.tkey).terms.get("V");
            const entrytype = [...this.typegen.assembly.entityDecls].find((edecl) => edecl[1].ns === "NSCore" && edecl[1].name === "MapEntry" && edecl[1].terms.get("K").trkey === ktype.trkey && edecl[1].terms.get("V").trkey === vtype.trkey);
            const entryentity = entrytype[1];
            const oftype = this.typegen.getMIRType(entryentity.tkey);
            const entrykaccess = this.typegen.mangleStringForCpp(entryentity.fields.find((fd) => fd.name === "key").fkey);
            const entryvaccess = this.typegen.mangleStringForCpp(entryentity.fields.find((fd) => fd.name === "value").fkey);
            const cvals = cpcs.args.map((arg) => `std::make_pair(${this.argToCpp(arg, oftype)}.${entrykaccess}, ${this.argToCpp(arg, oftype)}.${entryvaccess})`);
            const krepr = this.typegen.getCPPReprFor(ktype);
            const kops = this.typegen.getFunctorsForType(ktype);
            const vrepr = this.typegen.getCPPReprFor(vtype);
            const vops = this.typegen.getFunctorsForType(vtype);
            const pvals = `BSQMap<${krepr.std}, ${kops.dec}, ${kops.display}, ${kops.less}, ${kops.eq}, ${vrepr.std}, ${vops.dec}, ${vops.display}>::processSingletonMapInit<${kops.inc}, ${vops.inc}>({ ${cvals} })`;
            conscall = `BSQ_NEW_ADD_SCOPE(${scopevar}, ${cppctype}, ${ntype}, ${pvals})`;
        }
        return `${this.varToCppName(cpcs.trgt)} = ${conscall};`;
    }
    generateMIRConstructorTuple(op) {
        const args = op.args.map((arg) => this.argToCpp(arg, this.typegen.anyType));
        if (args.length === 0) {
            return `${this.varToCppName(op.trgt)} = BSQTuple::_empty;`;
        }
        else {
            const iflag = this.typegen.generateInitialDataKindFlag(this.typegen.getMIRType(op.resultTupleType));
            return `${this.varToCppName(op.trgt)} = BSQTuple::createFromSingle<${iflag}>({ ${args.join(", ")} });`;
        }
    }
    generateMIRConstructorRecord(op) {
        const args = op.args.map((arg) => `std::make_pair(MIRPropertyEnum::${arg[0]}, ${this.argToCpp(arg[1], this.typegen.anyType)})`);
        if (args.length === 0) {
            return `${this.varToCppName(op.trgt)} = BSQRecord::_empty;`;
        }
        else {
            const iflag = this.typegen.generateInitialDataKindFlag(this.typegen.getMIRType(op.resultRecordType));
            return `${this.varToCppName(op.trgt)} = BSQRecord::createFromSingle<${iflag}>({ ${args.join(", ")} });`;
        }
    }
    generateMIRConstructorEphemeralValueList(op) {
        const etype = this.typegen.getMIRType(op.resultEphemeralListType).options[0];
        let args = [];
        for (let i = 0; i < op.args.length; ++i) {
            args.push(this.argToCpp(op.args[i], etype.entries[i]));
        }
        return `${this.varToCppName(op.trgt)} = ${this.typegen.mangleStringForCpp(etype.trkey)}{${args.join(", ")}};`;
    }
    generateMIRAccessFromIndexExpression(arg, idx, resultAccessType) {
        const tuptype = this.getArgType(arg);
        const hasidx = this.typegen.tupleHasIndex(tuptype, idx);
        if (hasidx === "no") {
            return `${this.typegen.coerce("BSQ_VALUE_NONE", this.typegen.noneType, resultAccessType)}`;
        }
        else {
            const trepr = this.typegen.getCPPReprFor(tuptype);
            let select = "";
            if (trepr instanceof type_repr_1.StructRepr) {
                select = `${this.varToCppName(arg)}.atFixed<${idx}>()`;
            }
            else {
                select = `BSQ_GET_VALUE_PTR(${this.varToCppName(arg)}, BSQTuple)->atFixed<${idx}>()`;
            }
            return `${this.typegen.coerce(select, this.typegen.anyType, resultAccessType)}`;
        }
    }
    generateMIRProjectFromIndecies(op, resultAccessType) {
        const intotypes = this.typegen.typecheckEphemeral(resultAccessType) ? resultAccessType.options[0].entries : [];
        let vals = [];
        for (let i = 0; i < op.indecies.length; ++i) {
            vals.push(this.generateMIRAccessFromIndexExpression(op.arg, op.indecies[i], intotypes[i] || this.typegen.anyType));
        }
        if (this.typegen.typecheckEphemeral(resultAccessType)) {
            return `${this.varToCppName(op.trgt)} = ${this.typegen.mangleStringForCpp(resultAccessType.trkey)}{${vals.join(", ")}};`;
        }
        else {
            const iflag = this.typegen.generateInitialDataKindFlag(resultAccessType);
            return `${this.varToCppName(op.trgt)} = BSQTuple::createFromSingle<${iflag}>({ ${vals.join(", ")} });`;
        }
    }
    generateMIRModifyWithIndecies(op, resultTupleType) {
        const updmax = Math.max(...op.updates.map((upd) => upd[0] + 1));
        let cvals = [];
        for (let i = 0; i < updmax; ++i) {
            const upd = op.updates.find((update) => update[0] === i);
            if (upd !== undefined) {
                cvals.push(this.argToCpp(upd[1], this.typegen.anyType));
            }
            else {
                cvals.push(this.generateMIRAccessFromIndexExpression(op.arg, i, this.typegen.anyType));
            }
        }
        const rmax = this.typegen.getMaxTupleLength(resultTupleType);
        for (let i = updmax; i < rmax; ++i) {
            //may put none in the constructor list but ok since we note correct length and will ignore these if extranious
            cvals.push(this.generateMIRAccessFromIndexExpression(op.arg, i, this.typegen.anyType));
        }
        const iflag = this.typegen.generateInitialDataKindFlag(resultTupleType);
        return `${this.varToCppName(op.trgt)} = BSQTuple::createFromSingle<${iflag}>({ ${cvals.join(", ")} });`;
    }
    generateMIRStructuredExtendTuple(op, resultTupleType) {
        //this is the exact number of indecies in arg -- see typecheck
        const btuple = this.typegen.getMaxTupleLength(this.typegen.getMIRType(op.argInferType));
        let cvals = [];
        for (let i = 0; i < btuple; ++i) {
            cvals.push(this.generateMIRAccessFromIndexExpression(op.arg, i, this.typegen.anyType));
        }
        const rmax = this.typegen.getMaxTupleLength(resultTupleType);
        for (let i = btuple; i < rmax; ++i) {
            //may put none in the constructor list but ok since we note correct length and will ignore these if extranious
            cvals.push(this.generateMIRAccessFromIndexExpression(op.update, i - btuple, this.typegen.anyType));
        }
        const iflag = this.typegen.generateInitialDataKindFlag(resultTupleType);
        return `${this.varToCppName(op.trgt)} = BSQTuple::createFromSingle<${iflag}>({ ${cvals.join(", ")} });`;
    }
    generateMIRHasPropertyExpression(arg, property) {
        const rrepr = this.typegen.getCPPReprFor(this.getArgType(arg));
        if (rrepr instanceof type_repr_1.StructRepr) {
            return `${this.varToCppName(arg)}.hasProperty<MIRPropertyEnum::${property}>()`;
        }
        else {
            return `BSQ_GET_VALUE_PTR(${this.varToCppName(arg)}, BSQRecord)->hasProperty<MIRPropertyEnum::${property}>()`;
        }
    }
    generateMIRAccessFromPropertyExpression(arg, property, resultAccessType) {
        const rectype = this.getArgType(arg);
        const hasproperty = this.typegen.recordHasField(rectype, property);
        if (hasproperty === "no") {
            return `${this.typegen.coerce("BSQ_VALUE_NONE", this.typegen.noneType, resultAccessType)}`;
        }
        else {
            const rrepr = this.typegen.getCPPReprFor(rectype);
            let select = "";
            if (rrepr instanceof type_repr_1.StructRepr) {
                select = `${this.varToCppName(arg)}.atFixed<MIRPropertyEnum::${property}>()`;
            }
            else {
                select = `BSQ_GET_VALUE_PTR(${this.varToCppName(arg)}, BSQRecord)->atFixed<MIRPropertyEnum::${property}>()`;
            }
            return `${this.typegen.coerce(select, this.typegen.anyType, resultAccessType)}`;
        }
    }
    generateMIRProjectFromProperties(op, resultAccessType) {
        const intotypes = this.typegen.typecheckEphemeral(resultAccessType) ? resultAccessType.options[0].entries : [];
        let vals = [];
        for (let i = 0; i < op.properties.length; ++i) {
            vals.push(this.generateMIRAccessFromPropertyExpression(op.arg, op.properties[i], intotypes[i] || this.typegen.anyType));
        }
        if (this.typegen.typecheckEphemeral(resultAccessType)) {
            return `${this.varToCppName(op.trgt)} = ${this.typegen.mangleStringForCpp(resultAccessType.trkey)}{${vals.join(", ")}};`;
        }
        else {
            const rargs = [];
            for (let i = 0; i < op.properties.length; ++i) {
                rargs.push(`{ MIRRecordEnum::${op.properties[i]}, ${vals[i]} }`);
            }
            const iflag = this.typegen.generateInitialDataKindFlag(resultAccessType);
            return `${this.varToCppName(op.trgt)} = BSQRecord::createFromSingle<${iflag}>({ ${rargs.join(", ")} });`;
        }
    }
    generateAccessRecordPtr(argv) {
        const arg = this.varToCppName(argv);
        const rrepr = this.typegen.getCPPReprFor(this.getArgType(argv));
        if (rrepr instanceof type_repr_1.StructRepr) {
            return `&(${arg})`;
        }
        else {
            return `BSQ_GET_VALUE_PTR(${arg}, BSQRecord)`;
        }
    }
    generateMIRModifyWithProperties(op, resultRecordType) {
        const pmax = this.typegen.getMaxPropertySet(resultRecordType);
        let cvals = [];
        for (let i = 0; i < pmax.length; ++i) {
            const pname = pmax[i];
            const upd = op.updates.find((update) => update[0] === pname);
            if (upd !== undefined) {
                cvals.push(`{ MIRRecordEnum::${pname}, ${this.argToCpp(upd[1], this.typegen.anyType)} }`);
            }
        }
        const iflag = this.typegen.generateInitialDataKindFlag(resultRecordType);
        return `${this.varToCppName(op.trgt)} = BSQRecord::createFromUpdate<${iflag}>(${this.generateAccessRecordPtr(op.arg)}, { ${cvals.join(", ")} });`;
    }
    generateMIRStructuredExtendRecord(op, resultRecordType) {
        const rprops = this.typegen.getMaxPropertySet(resultRecordType);
        const mtype = this.typegen.getMIRType(op.updateInferType);
        let cvals = [];
        for (let i = 0; i < rprops.length; ++i) {
            const pname = rprops[i];
            const uhas = this.typegen.recordHasField(mtype, pname);
            if (uhas === "no") {
                //nothing to do
            }
            else if (uhas === "yes") {
                cvals.push(`{ MIRRecordEnum::${pname}, ${this.generateMIRAccessFromPropertyExpression(op.update, pname, this.typegen.anyType)} }`);
            }
            else {
                const check = `${this.generateAccessRecordPtr(op.update)}->hasProperty(MIRPropertyEnum::${pname})`;
                cvals.push(`${check} ? ${this.generateMIRAccessFromPropertyExpression(op.update, pname, this.typegen.anyType)}) : ${this.generateMIRAccessFromPropertyExpression(op.arg, pname, this.typegen.anyType)})`);
            }
        }
        const iflag = this.typegen.generateInitialDataKindFlag(resultRecordType);
        return `${this.varToCppName(op.trgt)} = BSQRecord::createFromUpdate<${iflag}>(${this.generateAccessRecordPtr(op.arg)}, { ${cvals.join(", ")} });`;
    }
    generateVFieldLookup(arg, tag, infertype, fdecl) {
        const lname = `resolve_${fdecl.fkey}_from_${infertype.trkey}`;
        let decl = this.vfieldLookups.find((lookup) => lookup.lname === lname);
        if (decl === undefined) {
            this.vfieldLookups.push({ infertype: infertype, fdecl: fdecl, lname: lname });
        }
        return `${this.typegen.mangleStringForCpp(lname)}(${tag}, ${this.argToCpp(arg, infertype)})`;
    }
    generateMIRAccessFromFieldExpression(arg, inferargtype, field, resultAccessType) {
        const nrepr = this.typegen.getCPPReprFor(inferargtype);
        let select = "";
        if (this.typegen.typecheckUEntity(inferargtype)) {
            if (nrepr instanceof type_repr_1.RefRepr) {
                select = `${this.argToCpp(arg, inferargtype)}->${this.typegen.mangleStringForCpp(field)}`;
            }
            else {
                select = `${this.argToCpp(arg, inferargtype)}.${this.typegen.mangleStringForCpp(field)}`;
            }
        }
        else {
            let tag = "";
            if (nrepr instanceof type_repr_1.KeyValueRepr || nrepr instanceof type_repr_1.ValueRepr) {
                tag = `BSQ_GET_VALUE_PTR(${this.argToCpp(arg, inferargtype)}, BSQRef)->nominalType`;
            }
            else {
                tag = `${this.argToCpp(arg, inferargtype)}.nominalType`;
            }
            select = this.generateVFieldLookup(arg, tag, inferargtype, this.assembly.fieldDecls.get(field));
        }
        const ftype = this.typegen.getMIRType(this.assembly.fieldDecls.get(field).declaredType);
        return `${this.typegen.coerce(select, ftype, resultAccessType)}`;
    }
    generateMIRAccessFromField(op, resultAccessType) {
        const inferargtype = this.typegen.getMIRType(op.argInferType);
        return `${this.varToCppName(op.trgt)} = ${this.generateMIRAccessFromFieldExpression(op.arg, inferargtype, op.field, resultAccessType)};`;
    }
    generateVFieldProject(arg, infertype, fprojs, resultAccessType) {
        const upnames = fprojs.map((fp) => fp.fkey);
        const uname = `project_${upnames.sort().join("*")}_in_${infertype.trkey}`;
        let decl = this.vfieldProjects.find((lookup) => lookup.uname === uname);
        if (decl === undefined) {
            this.vfieldProjects.push({ infertype: infertype, fprojs: fprojs, resultAccessType: resultAccessType, uname: uname });
        }
        return `${this.typegen.mangleStringForCpp(uname)}(${this.argToCpp(arg, infertype)})`;
    }
    generateMIRProjectFromFields(op, resultAccessType) {
        const inferargtype = this.typegen.getMIRType(op.argInferType);
        if (this.typegen.typecheckUEntity(inferargtype)) {
            if (this.typegen.typecheckEphemeral(resultAccessType)) {
                let cvals = [];
                op.fields.map((f, i) => {
                    const rtype = this.typegen.getEpehmeralType(resultAccessType).entries[i];
                    cvals.push(this.generateMIRAccessFromFieldExpression(op.arg, inferargtype, f, rtype));
                });
                return `${this.varToCppName(op.trgt)} = ${this.typegen.mangleStringForCpp(op.resultProjectType)}{${cvals.join(", ")}};`;
            }
            else {
                let cvals = [];
                op.fields.map((f) => {
                    const fdecl = this.assembly.fieldDecls.get(f);
                    const val = this.generateMIRAccessFromFieldExpression(op.arg, inferargtype, f, this.typegen.anyType);
                    cvals.push(`{ MIRRecordEnum::${fdecl.name}, ${val} }`);
                });
                const iflag = this.typegen.generateInitialDataKindFlag(this.typegen.getMIRType(op.resultProjectType));
                return `${this.varToCppName(op.trgt)} = BSQRecord::createFromSingle<${iflag}>({ ${cvals.join(", ")} });`;
            }
        }
        else {
            const vproject = this.generateVFieldProject(op.arg, inferargtype, op.fields.map((f) => this.assembly.fieldDecls.get(f)), resultAccessType);
            return `${this.varToCppName(op.trgt)} = ${vproject};`;
        }
    }
    generateVFieldUpdate(arg, infertype, fupds, resultAccessType) {
        const upnames = fupds.map((fud) => `${fud[0].fkey}->${this.getArgType(fud[1])}`);
        const uname = `update_${upnames.sort().join("*")}_in_${infertype.trkey}`;
        let decl = this.vfieldUpdates.find((lookup) => lookup.uname === uname);
        if (decl === undefined) {
            this.vfieldUpdates.push({ infertype: infertype, fupds: fupds, resultAccessType: resultAccessType, uname: uname });
        }
        return `${this.typegen.mangleStringForCpp(uname)}(${this.argToCpp(arg, infertype)}, ${fupds.map((upd) => this.argToCpp(upd[1], this.getArgType(upd[1]))).join(", ")})`;
    }
    generateMIRModifyWithFields(op, resultAccessType) {
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
                    cvals.push([this.argToCpp(upd[1], ftype), ftype]);
                }
                else {
                    cvals.push([`${this.argToCpp(op.arg, inferargtype)}->${this.typegen.mangleStringForCpp(fdecl.fkey)}`, ftype]);
                }
            }
            const cppcrepr = this.typegen.getCPPReprFor(inferargtype);
            if (cppcrepr instanceof type_repr_1.StructRepr) {
                const fvals = cvals.map((val) => {
                    return val[0];
                });
                return `${this.varToCppName(op.trgt)} = std::move(${cppcrepr.base}(${fvals.length !== 0 ? (", " + fvals.join(", ")) : ""}));`;
            }
            else {
                const fvals = cvals.map((val) => {
                    return this.typegen.generateConstructorArgInc(val[1], val[0]);
                });
                const scopevar = this.varNameToCppName("$scope$");
                return `${this.varToCppName(op.trgt)} = BSQ_NEW_ADD_SCOPE(${scopevar}, ${cppcrepr.base}${fvals.length !== 0 ? (", " + fvals.join(", ")) : ""});`;
            }
        }
        else {
            const access = this.generateVFieldUpdate(op.arg, inferargtype, op.updates.map((upd) => [this.assembly.fieldDecls.get(upd[0]), upd[1]]), resultAccessType);
            return `${this.varToCppName(op.trgt)} = ${access};`;
        }
    }
    generateVFieldExtend(arg, infertype, merge, infermerge, fieldResolves, resultAccessType) {
        const upnames = fieldResolves.map((fr) => `${fr[0]}->${fr[1].fkey}`);
        const mname = `merge_${infertype.trkey}_${upnames.join("*")}_with_${infermerge.trkey}`;
        let decl = this.vobjmerges.find((lookup) => lookup.mname === mname);
        if (decl === undefined) {
            this.vobjmerges.push({ infertype: infertype, merge: merge, infermergetype: infermerge, fieldResolves: fieldResolves, resultAccessType: resultAccessType, mname: mname });
        }
        return `${this.typegen.mangleStringForCpp(mname)}(${this.argToCpp(arg, infertype)}, ${this.argToCpp(merge, infermerge)})`;
    }
    generateMIRStructuredExtendObject(op, resultAccessType) {
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
                const faccess = [`${this.argToCpp(op.arg, inferargtype)}->${this.typegen.mangleStringForCpp(fdecl.fkey)}`, ftype];
                if (fp === undefined) {
                    cvals.push(faccess);
                }
                else {
                    const hasp = this.typegen.recordHasField(mergeargtype, fp[0]);
                    if (hasp === "no") {
                        cvals.push(faccess);
                    }
                    else if (hasp === "yes") {
                        cvals.push([this.generateMIRAccessFromPropertyExpression(op.arg, fp[0], ftype), ftype]);
                    }
                    else {
                        const check = this.generateMIRHasPropertyExpression(op.update, fp[0]);
                        const update = `(${check} ? ${this.generateMIRAccessFromPropertyExpression(op.update, fp[0], ftype)}) : ${faccess})`;
                        cvals.push([update, ftype]);
                    }
                }
            }
            const cppcrepr = this.typegen.getCPPReprFor(inferargtype);
            if (cppcrepr instanceof type_repr_1.StructRepr) {
                const fvals = cvals.map((val) => {
                    return val[0];
                });
                return `${this.varToCppName(op.trgt)} = std::move(${cppcrepr.base}(${fvals.length !== 0 ? (", " + fvals.join(", ")) : ""}));`;
            }
            else {
                const fvals = cvals.map((val) => {
                    return this.typegen.generateConstructorArgInc(val[1], val[0]);
                });
                const scopevar = this.varNameToCppName("$scope$");
                return `${this.varToCppName(op.trgt)} = BSQ_NEW_ADD_SCOPE(${scopevar}, ${cppcrepr.base}${fvals.length !== 0 ? (", " + fvals.join(", ")) : ""});`;
            }
        }
        else {
            const access = this.generateVFieldExtend(op.arg, inferargtype, op.update, mergeargtype, op.fieldResolves.map((fr) => [fr[0], this.assembly.fieldDecls.get(fr[1])]), resultAccessType);
            return `${this.varToCppName(op.trgt)} = ${access};`;
        }
    }
    generateMIRLoadFromEpehmeralList(op) {
        return `${this.varToCppName(op.trgt)} = ${this.varToCppName(op.arg)}.entry_${op.idx};`;
    }
    generateMIRInvokeFixedFunction(ivop) {
        let vals = [];
        const idecl = (this.assembly.invokeDecls.get(ivop.mkey) || this.assembly.primitiveInvokeDecls.get(ivop.mkey));
        for (let i = 0; i < ivop.args.length; ++i) {
            vals.push(this.argToCpp(ivop.args[i], this.typegen.getMIRType(idecl.params[i].type)));
        }
        const rtype = this.typegen.getMIRType(ivop.resultType);
        if (this.typegen.getRefCountableStatus(rtype) !== "no") {
            vals.push(this.varNameToCppName("$scope$"));
        }
        return `${this.varToCppName(ivop.trgt)} = ${this.invokenameToCPP(ivop.mkey)}(${vals.join(", ")});`;
    }
    generateEquals(op, lhsinfertype, lhs, rhsinfertype, rhs, isstrict) {
        let coreop = "";
        if (isstrict) {
            const repr = this.typegen.getCPPReprFor(lhsinfertype);
            coreop = `EqualFunctor_${repr.base}{}(${this.argToCpp(lhs, lhsinfertype)}, ${this.argToCpp(rhs, rhsinfertype)})`;
        }
        else {
            coreop = `EqualFunctor_KeyValue{}(${this.argToCpp(lhs, this.typegen.keyType)}, ${this.argToCpp(rhs, this.typegen.keyType)})`;
        }
        return op === "!=" ? `!${coreop}` : coreop;
    }
    generateLess(lhsinfertype, lhs, rhsinfertype, rhs, isstrict) {
        if (isstrict) {
            const repr = this.typegen.getCPPReprFor(lhsinfertype);
            return `LessFunctor_${repr.base}{}(${this.argToCpp(lhs, lhsinfertype)}, ${this.argToCpp(rhs, rhsinfertype)})`;
        }
        else {
            return `LessFunctor_KeyValue{}(${this.argToCpp(lhs, this.typegen.keyType)}, ${this.argToCpp(rhs, this.typegen.keyType)})`;
        }
    }
    generateCompare(op, lhsinfertype, lhs, rhsinfertype, rhs) {
        if (op === "<") {
            return this.generateLess(lhsinfertype, lhs, rhsinfertype, rhs, true);
        }
        else if (op === "<=") {
            return `${this.generateLess(lhsinfertype, lhs, rhsinfertype, rhs, true)} || ${this.generateEquals("=", lhsinfertype, lhs, rhsinfertype, rhs, true)}`;
        }
        else if (op === ">") {
            return this.generateLess(rhsinfertype, rhs, lhsinfertype, lhs, true);
        }
        else {
            return `${this.generateLess(rhsinfertype, rhs, lhsinfertype, lhs, true)} || ${this.generateEquals("=", rhsinfertype, rhs, lhsinfertype, lhs, true)}`;
        }
    }
    generateSubtypeTupleCheck(argv, argtype, oftype) {
        const argrepr = this.typegen.getCPPReprFor(argtype);
        const subtypesig = `bool subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_TTC(${argrepr.std} arg)`;
        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let ttuple = "";
            if (argrepr instanceof type_repr_1.StructRepr) {
                ttuple = `BSQTuple* tt = &arg;`;
            }
            else {
                ttuple = `BSQTuple* tt = BSQ_GET_VALUE_PTR(arg, BSQTuple);`;
            }
            let checks = [];
            checks.push(`(tt->entries.size() <= ${oftype.entries.length})`);
            //do all the checks that argtype satisfies all the requirements of oftype -- maybe a bit inefficiently
            for (let i = 0; i < oftype.entries.length; ++i) {
                const chk = this.generateTypeCheck(`tt->atFixed<${i}>()`, this.typegen.anyType, this.typegen.anyType, oftype.entries[i].type);
                if (oftype.entries[i].isOptional) {
                    checks.push(`(!tt->hasIndex<${i}>() || ${chk})`);
                }
                else {
                    checks.push(`tt->hasIndex<${i}>()`);
                    checks.push(chk);
                }
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
                    op = `(${checks.join(" && ")})`;
                }
            }
            const decl = subtypesig
                + "\n{\n"
                + `    ${ttuple}\n`
                + `    return ${op};\n`
                + `}\n`;
            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }
        return `subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_TTC(${argv})`;
    }
    generateTupleSpecialConceptCheck(argv, argtype, oftype) {
        const argrepr = this.typegen.getCPPReprFor(argtype);
        const subtypesig = `bool subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_TSC(${argrepr.std} arg)`;
        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let ttuple = "";
            if (argrepr instanceof type_repr_1.StructRepr) {
                ttuple = `BSQTuple* tt = &arg;`;
            }
            else {
                ttuple = `BSQTuple* tt = BSQ_GET_VALUE_PTR(arg, BSQTuple);`;
            }
            const checks = [];
            if (oftype.ckeys.some((cc) => this.typegen.assembly.subtypeOf(this.typegen.parsableType, this.typegen.getMIRType(cc)))) {
                checks.push(`DATA_KIND_PARSABLE_FLAG`);
            }
            if (oftype.ckeys.some((cc) => this.typegen.assembly.subtypeOf(this.typegen.podType, this.typegen.getMIRType(cc)))) {
                checks.push(`DATA_KIND_POD_FLAG`);
            }
            if (oftype.ckeys.some((cc) => this.typegen.assembly.subtypeOf(this.typegen.apiType, this.typegen.getMIRType(cc)))) {
                checks.push(`DATA_KIND_POD_FLAG`);
            }
            const decl = subtypesig
                + "\n{\n"
                + `    ${ttuple}\n`
                + `    DATA_KIND_FLAG cf = (${checks.join(" | ")});\n`
                + `    return cf == (cf & tt->flag);\n`
                + `}\n`;
            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }
        return `subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_TSC(${argv})`;
    }
    generateSubtypeRecordCheck(argv, argtype, oftype) {
        const argrepr = this.typegen.getCPPReprFor(argtype);
        const subtypesig = `bool subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_TRC(${argrepr.std} arg)`;
        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let trecord = "";
            if (argrepr instanceof type_repr_1.StructRepr) {
                trecord = `BSQRecord* tr = &arg;`;
            }
            else {
                trecord = `BSQRecord* tr = BSQ_GET_VALUE_PTR(arg, BSQRecord);`;
            }
            let checks = [];
            //do all the checks that argtype satisfies all the requirements of oftype -- maybe a bit inefficiently
            for (let i = 0; i < oftype.entries.length; ++i) {
                const pname = oftype.entries[i].name;
                const chk = this.generateTypeCheck(`tr->atFixed<MIRPropertyEnum::${pname}>()`, this.typegen.anyType, this.typegen.anyType, oftype.entries[i].type);
                if (oftype.entries[i].isOptional) {
                    checks.push(`(!tr->hasProperty<MIRPropertyEnum::${pname}>() || ${chk})`);
                }
                else {
                    checks.push(`tr->hasProperty<MIRPropertyEnum::${pname}>()`);
                    checks.push(chk);
                }
            }
            //do checks that argtype doesn't have any other properties
            if (this.typegen.typecheckRecord(argtype)) {
                const allprops = this.typegen.getMaxPropertySet(argtype);
                for (let i = 0; i < allprops.length; ++i) {
                    const pname = allprops[i];
                    if (oftype.entries.find((entry) => entry.name === pname) === undefined) {
                        checks.push(`!tr->hasProperty<MIRPropertyEnum::${pname}>()`);
                    }
                }
            }
            else {
                const pprops = oftype.entries.map((entry) => `MIRPropertyEnum::${entry.name}`);
                checks.push(`tr->checkPropertySet(${oftype.entries.length}${oftype.entries.length !== 0 ? ", " : ""} ${pprops.join(", ")})`);
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
                    op = `(${checks.join(" && ")})`;
                }
            }
            const decl = subtypesig
                + "\n{\n"
                + `    ${trecord}\n`
                + `    return ${op};\n`
                + `}\n`;
            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }
        return `subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_TRC(${argv})`;
    }
    generateRecordSpecialConceptCheck(argv, argtype, oftype) {
        const argrepr = this.typegen.getCPPReprFor(argtype);
        const subtypesig = `bool subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_RSC(${argrepr.std} arg)`;
        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let ttuple = "";
            if (argrepr instanceof type_repr_1.StructRepr) {
                ttuple = `BSQRecord* tr = &arg;`;
            }
            else {
                ttuple = `BSQRecord* tr = BSQ_GET_VALUE_PTR(arg, BSQRecord);`;
            }
            const checks = [];
            if (oftype.ckeys.some((cc) => this.typegen.assembly.subtypeOf(this.typegen.parsableType, this.typegen.getMIRType(cc)))) {
                checks.push(`DATA_KIND_PARSABLE_FLAG`);
            }
            if (oftype.ckeys.some((cc) => this.typegen.assembly.subtypeOf(this.typegen.podType, this.typegen.getMIRType(cc)))) {
                checks.push(`DATA_KIND_POD_FLAG`);
            }
            if (oftype.ckeys.some((cc) => this.typegen.assembly.subtypeOf(this.typegen.apiType, this.typegen.getMIRType(cc)))) {
                checks.push(`DATA_KIND_POD_FLAG`);
            }
            const decl = subtypesig
                + "\n{\n"
                + `    ${ttuple}\n`
                + `    DATA_KIND_FLAG cf = (${checks.join(" | ")});\n`
                + `    return cf == (cf & tr->flag);\n`
                + `}\n`;
            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }
        return `subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_RSC(${argv})`;
    }
    generateFastTupleTypeCheck(arg, argtype, inferargtype, oftype) {
        if (!inferargtype.options.some((opt) => opt instanceof mir_assembly_1.MIRTupleType)) {
            return "false";
        }
        else {
            const argrepr = this.typegen.getCPPReprFor(argtype);
            const tsc = this.generateSubtypeTupleCheck(arg, argtype, oftype);
            if (argrepr instanceof type_repr_1.StructRepr) {
                return tsc;
            }
            else {
                return `(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQTuple*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr && ${tsc})`;
            }
        }
    }
    generateFastRecordTypeCheck(arg, argtype, inferargtype, oftype) {
        if (!inferargtype.options.some((opt) => opt instanceof mir_assembly_1.MIRRecordType)) {
            return "false";
        }
        else {
            const argrepr = this.typegen.getCPPReprFor(argtype);
            const tsc = this.generateSubtypeTupleCheck(arg, argtype, oftype);
            if (argrepr instanceof type_repr_1.StructRepr) {
                return tsc;
            }
            else {
                return `(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQRecord*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr && ${tsc})`;
            }
        }
    }
    generateSubtypeArrayLookup(typeenum, oftype) {
        this.checkedConcepts.add(oftype.trkey);
        const arraystr = `MIRConceptSubtypeArray__${this.typegen.mangleStringForCpp(oftype.trkey)}`;
        return `BSQObject::checkSubtype(${typeenum}, ${arraystr})`;
    }
    generateFastConceptTypeCheck(arg, argtype, inferargtype, oftype) {
        if (this.typegen.typecheckIsName(inferargtype, /^NSCore::None$/) || this.typegen.typecheckUEntity(inferargtype)) {
            return this.typegen.assembly.subtypeOf(inferargtype, this.typegen.getMIRType(oftype.trkey)) ? "true" : "false";
        }
        else {
            let enumacc = "";
            if (this.typegen.typecheckTuple(inferargtype)) {
                enumacc = "MIRNominalTypeEnum_Tuple";
            }
            else if (this.typegen.typecheckRecord(inferargtype)) {
                enumacc = "MIRNominalTypeEnum_Record";
            }
            else {
                const argrepr = this.typegen.getCPPReprFor(argtype);
                if (argrepr instanceof type_repr_1.KeyValueRepr) {
                    enumacc = `getNominalTypeOf_KeyValue(${arg})`;
                }
                else {
                    enumacc = `getNominalTypeOf_Value(${arg})`;
                }
            }
            let ttest = "false";
            if (inferargtype.options.some((iopt) => iopt instanceof mir_assembly_1.MIRTupleType)) {
                const tupmax = mir_assembly_1.MIRType.createSingle(mir_assembly_1.MIRConceptType.create([this.typegen.tupleType.trkey, this.typegen.podType.trkey, this.typegen.parsableType.trkey]));
                const maybespecial = this.typegen.assembly.subtypeOf(tupmax, this.typegen.getMIRType(oftype.trkey)); //if this isn't true then special subtype will never be true
                const trival = this.typegen.assembly.subtypeOf(this.typegen.tupleType, this.typegen.getMIRType(oftype.trkey)); //if this is true then the default subtypeArray is enough
                if (maybespecial && !trival) {
                    ttest = `(enumacc == MIRNominalTypeEnum_Tuple) && ${this.generateTupleSpecialConceptCheck(arg, argtype, oftype)}`;
                }
            }
            let rtest = "false";
            if (inferargtype.options.some((iopt) => iopt instanceof mir_assembly_1.MIRRecordType)) {
                const recmax = mir_assembly_1.MIRType.createSingle(mir_assembly_1.MIRConceptType.create([this.typegen.recordType.trkey, this.typegen.podType.trkey, this.typegen.parsableType.trkey]));
                const maybespecial = this.typegen.assembly.subtypeOf(recmax, this.typegen.getMIRType(oftype.trkey)); //if this isn't true then special subtype will never be true
                const trival = this.typegen.assembly.subtypeOf(this.typegen.recordType, this.typegen.getMIRType(oftype.trkey)); //if this is true then the default subtypeArray is enough
                if (maybespecial && !trival) {
                    rtest = `(enumacc == MIRNominalTypeEnum_Record) && ${this.generateRecordSpecialConceptCheck(arg, argtype, oftype)})`;
                }
            }
            const ntest = this.generateSubtypeArrayLookup(enumacc, oftype);
            const tests = [ntest, ttest, rtest].filter((test) => test !== "false");
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
                return `(${tests.join(" || ")})`;
            }
        }
    }
    generateFastEntityTypeCheck(arg, argtype, inferargtype, oftype) {
        if (this.typegen.typecheckIsName(inferargtype, /^NSCore::None$/) || this.typegen.typecheckUEntity(inferargtype)) {
            return inferargtype.trkey == oftype.trkey ? "true" : "false";
        }
        else {
            const argrepr = this.typegen.getCPPReprFor(argtype);
            if (argrepr instanceof type_repr_1.StructRepr) {
                //could be a tuple or record
                return "false";
            }
            else if (argrepr instanceof type_repr_1.KeyValueRepr) {
                return `(getNominalTypeOf_KeyValue(${arg}) == MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(oftype.ekey)})`;
            }
            else {
                return `(getNominalTypeOf_Value(${arg}) == MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(oftype.ekey)})`;
            }
        }
    }
    generateEphemeralTypeCheck(argv, argtype, oftype) {
        const argrepr = this.typegen.getCPPReprFor(argtype);
        const subtypesig = `bool subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_EL(${argrepr.std} arg)`;
        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let checks = [];
            //do all the checks that argtype satisfies all the requirements of oftype 
            for (let i = 0; i < oftype.entries.length; ++i) {
                const etype = argtype.options[0].entries[i];
                checks.push(this.generateTypeCheck(`arg.entry_${i}`, etype, etype, oftype.entries[i]));
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
                    op = `(${checks.join(" && ")})`;
                }
            }
            const decl = subtypesig
                + "\n{\n"
                + `    return ${op};\n`
                + `}\n`;
            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }
        return `subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_EL(${argv})`;
    }
    generateTypeCheck(arg, argtype, inferargtype, oftype) {
        if (this.typegen.assembly.subtypeOf(inferargtype, oftype)) {
            //this case also include oftype == Any
            return "true";
        }
        const argrepr = this.typegen.getCPPReprFor(argtype);
        if (oftype.trkey === "NSCore::Some") {
            if (!this.typegen.assembly.subtypeOf(this.typegen.noneType, inferargtype)) {
                return "true";
            }
            else {
                if (argrepr instanceof type_repr_1.NoneRepr) {
                    return "false";
                }
                else if (argrepr instanceof type_repr_1.RefRepr || argrepr instanceof type_repr_1.StructRepr) {
                    return "true";
                }
                else {
                    return `BSQ_IS_VALUE_NONNONE(${arg})`;
                }
            }
        }
        const tests = oftype.options.map((topt) => {
            const mtype = this.typegen.getMIRType(topt.trkey);
            assert(mtype !== undefined, "We should generate all the component types by default??");
            if (topt instanceof mir_assembly_1.MIREntityType) {
                return this.generateFastEntityTypeCheck(arg, argtype, inferargtype, topt);
            }
            else if (topt instanceof mir_assembly_1.MIRConceptType) {
                return this.generateFastConceptTypeCheck(arg, argtype, inferargtype, topt);
            }
            else if (topt instanceof mir_assembly_1.MIRTupleType) {
                return this.generateFastTupleTypeCheck(arg, argtype, inferargtype, topt);
            }
            else if (topt instanceof mir_assembly_1.MIRRecordType) {
                return this.generateFastRecordTypeCheck(arg, argtype, inferargtype, topt);
            }
            else {
                assert(topt instanceof mir_assembly_1.MIREphemeralListType);
                return this.generateEphemeralTypeCheck(arg, argtype, topt);
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
            return `(${tests.join(" || ")})`;
        }
    }
    generateMIRPackSlice(op) {
        const etype = this.typegen.getMIRType(op.sltype).options[0];
        let args = [];
        for (let i = 0; i < etype.entries.length; ++i) {
            args.push(`${this.varToCppName(op.src)}.entry_${i}`);
        }
        return `${this.varToCppName(op.trgt)} = ${this.typegen.mangleStringForCpp(etype.trkey)}{${args.join(", ")}};`;
    }
    generateMIRPackSliceExtend(op) {
        const fromtype = this.getArgType(op.basepack).options[0];
        const etype = this.typegen.getMIRType(op.sltype).options[0];
        let args = [];
        for (let i = 0; i < fromtype.entries.length; ++i) {
            args.push(`${this.varToCppName(op.basepack)}.entry_${i}`);
        }
        for (let i = 0; i < op.ext.length; ++i) {
            args.push(this.argToCpp(op.ext[i], etype.entries[fromtype.entries.length + i]));
        }
        return `${this.varToCppName(op.trgt)} = ${this.typegen.mangleStringForCpp(etype.trkey)}{${args.join(", ")}};`;
    }
    generateStmt(op) {
        switch (op.tag) {
            case mir_ops_1.MIROpTag.MIRLoadConst: {
                const lcv = op;
                return `${this.varToCppName(lcv.trgt)} = ${this.generateConstantExp(lcv.src, this.getArgType(lcv.trgt))};`;
            }
            case mir_ops_1.MIROpTag.MIRLoadConstRegex: {
                const lcr = op;
                const scopevar = this.varNameToCppName("$scope$");
                return `${this.varToCppName(lcr.trgt)} = BSQ_NEW_ADD_SCOPE(${scopevar}, BSQRegex, ${lcr.restr});`;
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
                return `${this.varToCppName(lav.trgt)} = ${this.argToCpp(lav.name, this.getArgType(lav.trgt))};`;
            }
            case mir_ops_1.MIROpTag.MIRAccessLocalVariable: {
                const llv = op;
                return `${this.varToCppName(llv.trgt)} = ${this.argToCpp(llv.name, this.getArgType(llv.trgt))};`;
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
                return this.generateMIRConstructorTuple(op);
            }
            case mir_ops_1.MIROpTag.MIRConstructorRecord: {
                return this.generateMIRConstructorRecord(op);
            }
            case mir_ops_1.MIROpTag.MIRConstructorEphemeralValueList: {
                return this.generateMIRConstructorEphemeralValueList(op);
            }
            case mir_ops_1.MIROpTag.MIRAccessFromIndex: {
                const ai = op;
                return `${this.varToCppName(ai.trgt)} = ${this.generateMIRAccessFromIndexExpression(ai.arg, ai.idx, this.typegen.getMIRType(ai.resultAccessType))};`;
            }
            case mir_ops_1.MIROpTag.MIRProjectFromIndecies: {
                const pi = op;
                return this.generateMIRProjectFromIndecies(pi, this.typegen.getMIRType(pi.resultProjectType));
            }
            case mir_ops_1.MIROpTag.MIRAccessFromProperty: {
                const ap = op;
                return `${this.varToCppName(ap.trgt)} = ${this.generateMIRAccessFromPropertyExpression(ap.arg, ap.property, this.typegen.getMIRType(ap.resultAccessType))};`;
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
                return this.generateMIRProjectFromFields(pf, this.typegen.getMIRType(pf.resultProjectType));
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
                return this.generateMIRModifyWithFields(mf, this.typegen.getMIRType(mf.resultNominalType));
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
                return this.generateMIRStructuredExtendObject(so, this.typegen.getMIRType(so.resultNominalType));
            }
            case mir_ops_1.MIROpTag.MIRLoadFromEpehmeralList: {
                const le = op;
                return this.generateMIRLoadFromEpehmeralList(le);
            }
            case mir_ops_1.MIROpTag.MIRInvokeFixedFunction: {
                const invk = op;
                return this.generateMIRInvokeFixedFunction(invk);
            }
            case mir_ops_1.MIROpTag.MIRInvokeVirtualTarget: {
                return NOT_IMPLEMENTED("MIRInvokeVirtualTarget");
            }
            case mir_ops_1.MIROpTag.MIRPrefixOp: {
                const pfx = op;
                if (pfx.op === "!") {
                    return `${this.varToCppName(pfx.trgt)} = !${this.argToCpp(pfx.arg, this.typegen.boolType)};`;
                }
                else {
                    if (pfx.op === "-") {
                        if (pfx.arg instanceof mir_ops_1.MIRConstantInt) {
                            return `${this.varToCppName(pfx.trgt)} = -${pfx.arg.value};`;
                        }
                        else if (pfx.arg instanceof mir_ops_1.MIRConstantBigInt) {
                            const scope = this.typegen.mangleStringForCpp("$scope$");
                            return `${this.varToCppName(pfx.trgt)} = BSQ_NEW_ADD_SCOPE(${scope}, BSQBigInt, "-${pfx.arg.digits()}");`;
                        }
                        else if (pfx.arg instanceof mir_ops_1.MIRConstantFloat64) {
                            return `${this.varToCppName(pfx.trgt)} = -${pfx.arg.digits()};`;
                        }
                        else {
                            const opt = this.getArgType(pfx.trgt);
                            if (this.typegen.typecheckIsName(opt, /^NSCore::Int$/)) {
                                return `${this.varToCppName(pfx.trgt)} = -${this.argToCpp(pfx.arg, this.typegen.intType)};`;
                            }
                            else if (this.typegen.typecheckIsName(opt, /^NSCore::BigInt$/)) {
                                const scope = this.typegen.mangleStringForCpp("$scope$");
                                return `${this.varToCppName(pfx.trgt)} = BSQBigInt::negate(${scope}, ${this.argToCpp(pfx.arg, this.typegen.bigIntType)});`;
                            }
                            else {
                                return `${this.varToCppName(pfx.trgt)} = -${this.argToCpp(pfx.arg, this.typegen.float64Type)};`;
                            }
                        }
                    }
                    else {
                        return `${this.varToCppName(pfx.trgt)} = ${this.argToCpp(pfx.arg, this.getArgType(pfx.trgt))};`;
                    }
                }
            }
            case mir_ops_1.MIROpTag.MIRBinOp: {
                const bop = op;
                const opt = this.getArgType(bop.trgt);
                if (this.typegen.typecheckIsName(opt, /^NSCore::Int$/)) {
                    if (bop.op !== "/") {
                        const chkedop = new Map().set("+", "__builtin_add_overflow").set("-", "__builtin_sub_overflow").set("*", "__builtin_mul_overflow").get(bop.op);
                        const opp = `if(${chkedop}(${this.argToCpp(bop.lhs, this.typegen.intType)}, ${this.argToCpp(bop.rhs, this.typegen.intType)}, &${this.varToCppName(bop.trgt)}) || INT_OOF_BOUNDS(${this.varToCppName(bop.trgt)})) { BSQ_ABORT("INT Overflow", "${filenameClean(this.currentFile)}", ${bop.sinfo.line}); }`;
                        return opp;
                    }
                    else {
                        const chk = `if(${this.argToCpp(bop.rhs, this.typegen.intType)} == 0) { BSQ_ABORT("Div by 0", "${filenameClean(this.currentFile)}", ${bop.sinfo.line}); }`;
                        const opp = `${this.varToCppName(bop.trgt)} = ${this.argToCpp(bop.lhs, this.typegen.intType)} / ${this.argToCpp(bop.rhs, this.typegen.intType)};`;
                        return chk + " " + opp;
                    }
                }
                else if (this.typegen.typecheckIsName(opt, /^NSCore::BigInt$/)) {
                    const bigop = new Map().set("+", "add").set("-", "sub").set("*", "mult").set("/", "div").get(bop.op);
                    const opp = `${this.varToCppName(bop.trgt)} = BSQBigInt::${bigop}(${this.argToCpp(bop.lhs, this.typegen.bigIntType)}, ${this.argToCpp(bop.rhs, this.typegen.bigIntType)});`;
                    if (bop.op !== "/") {
                        return opp;
                    }
                    else {
                        const chk = `if(${this.argToCpp(bop.rhs, this.typegen.bigIntType)}->eqI64(0)) { BSQ_ABORT("Div by 0", "${filenameClean(this.currentFile)}", ${bop.sinfo.line}); }`;
                        return chk + " " + opp;
                    }
                }
                else {
                    return `${this.varToCppName(bop.trgt)} = ${this.argToCpp(bop.lhs, this.typegen.float64Type)} ${bop.op} ${this.argToCpp(bop.rhs, this.typegen.float64Type)};`;
                }
            }
            case mir_ops_1.MIROpTag.MIRBinEq: {
                const beq = op;
                const lhvtypeinfer = this.typegen.getMIRType(beq.lhsInferType);
                const rhvtypeinfer = this.typegen.getMIRType(beq.rhsInferType);
                return `${this.varToCppName(beq.trgt)} = ${this.generateEquals(beq.op, lhvtypeinfer, beq.lhs, rhvtypeinfer, beq.rhs, !beq.relaxed)};`;
            }
            case mir_ops_1.MIROpTag.MIRBinCmp: {
                const bcmp = op;
                const lhvtypeinfer = this.typegen.getMIRType(bcmp.lhsInferType);
                const rhvtypeinfer = this.typegen.getMIRType(bcmp.rhsInferType);
                return `${this.varToCppName(bcmp.trgt)} = ${this.generateCompare(bcmp.op, lhvtypeinfer, bcmp.lhs, rhvtypeinfer, bcmp.rhs)};`;
            }
            case mir_ops_1.MIROpTag.MIRIsTypeOfNone: {
                const ton = op;
                return `${this.varToCppName(ton.trgt)} = ${this.generateNoneCheck(ton.arg)};`;
            }
            case mir_ops_1.MIROpTag.MIRIsTypeOfSome: {
                const tos = op;
                return `${this.varToCppName(tos.trgt)} = !${this.generateNoneCheck(tos.arg)};`;
            }
            case mir_ops_1.MIROpTag.MIRIsTypeOf: {
                const top = op;
                const oftype = this.typegen.getMIRType(top.oftype);
                const argtype = this.getArgType(top.arg);
                const infertype = this.typegen.getMIRType(top.argInferType);
                return `${this.varToCppName(top.trgt)} = ${this.generateTypeCheck(this.argToCpp(top.arg, argtype), argtype, infertype, oftype)};`;
            }
            case mir_ops_1.MIROpTag.MIRRegAssign: {
                const regop = op;
                return `${this.varToCppName(regop.trgt)} = ${this.argToCpp(regop.src, this.getArgType(regop.trgt))};`;
            }
            case mir_ops_1.MIROpTag.MIRTruthyConvert: {
                const tcop = op;
                return `${this.varToCppName(tcop.trgt)} = ${this.generateTruthyConvert(tcop.src)};`;
            }
            case mir_ops_1.MIROpTag.MIRVarStore: {
                const vsop = op;
                return `${this.varToCppName(vsop.name)} = ${this.argToCpp(vsop.src, this.getArgType(vsop.name))};`;
            }
            case mir_ops_1.MIROpTag.MIRPackSlice: {
                const vps = op;
                return this.generateMIRPackSlice(vps);
            }
            case mir_ops_1.MIROpTag.MIRPackExtend: {
                const vpe = op;
                return this.generateMIRPackSliceExtend(vpe);
            }
            case mir_ops_1.MIROpTag.MIRReturnAssign: {
                const raop = op;
                return `${this.varToCppName(raop.name)} = ${this.argToCpp(raop.src, this.getArgType(raop.name))};`;
            }
            case mir_ops_1.MIROpTag.MIRAbort: {
                const aop = op;
                return `BSQ_ABORT("${aop.info}", "${filenameClean(this.currentFile)}", ${aop.sinfo.line});`;
            }
            case mir_ops_1.MIROpTag.MIRDebug: {
                //debug is a nop in AOT release mode but we allow it for our debugging purposes
                const dbgop = op;
                if (dbgop.value === undefined) {
                    return "assert(false);";
                }
                else {
                    return `{ std::cout << diagnostic_format(${this.argToCpp(dbgop.value, this.typegen.anyType)}) << "\\n"; }`;
                }
            }
            case mir_ops_1.MIROpTag.MIRJump: {
                const jop = op;
                return `goto ${this.labelToCpp(jop.trgtblock)};`;
            }
            case mir_ops_1.MIROpTag.MIRJumpCond: {
                const cjop = op;
                return `if(${this.argToCpp(cjop.arg, this.typegen.boolType)}) {goto ${this.labelToCpp(cjop.trueblock)};} else {goto ${cjop.falseblock};}`;
            }
            case mir_ops_1.MIROpTag.MIRJumpNone: {
                const njop = op;
                return `if(${this.generateNoneCheck(njop.arg)}) {goto ${this.labelToCpp(njop.noneblock)};} else {goto ${njop.someblock};}`;
            }
            case mir_ops_1.MIROpTag.MIRPhi: {
                return undefined; //handle this as a special case in the block processing code
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
    generateBlock(block) {
        let gblock = [];
        let blocki = 0;
        while (blocki < block.ops.length - 1 && block.ops[blocki] instanceof mir_ops_1.MIRPhi) {
            const phiop = block.ops[blocki];
            phiop.src.forEach((src, fblock) => {
                const assign = `${this.varToCppName(phiop.trgt)} = ${this.argToCpp(src, this.getArgType(phiop.trgt))};`;
                const inblock = this.generatedBlocks.get(fblock);
                //last entry is the jump so put before that but after all other statements
                const jmp = inblock[inblock.length - 1];
                inblock[inblock.length - 1] = assign;
                inblock.push(jmp);
            });
            ++blocki;
        }
        while (blocki < block.ops.length) {
            const gop = this.generateStmt(block.ops[blocki]);
            if (gop !== undefined) {
                gblock.push(gop);
            }
            ++blocki;
        }
        if (block.label === "exit") {
            const rctype = this.typegen.getRefCountableStatus(this.currentRType);
            if (rctype !== "no") {
                gblock.push(this.typegen.buildReturnOpForType(this.currentRType, "$$return", "$callerscope$"));
            }
            gblock.push("return $$return;");
        }
        this.generatedBlocks.set(block.label, gblock);
    }
    generateCPPVarDecls(body, params) {
        const scopevar = this.varNameToCppName("$scope$");
        const refscope = `    BSQRefScope ${scopevar};`;
        let vdecls = new Map();
        body.vtypes.forEach((tkey, name) => {
            if (params.findIndex((p) => p.name === name) === -1) {
                const declt = this.typegen.getCPPReprFor(this.typegen.getMIRType(tkey)).std;
                if (!vdecls.has(declt)) {
                    vdecls.set(declt, []);
                }
                vdecls.get(declt).push(this.varNameToCppName(name));
            }
        });
        let vdeclscpp = [];
        if (vdecls.has("bool")) {
            vdeclscpp.push(`bool ${vdecls.get("bool").join(", ")};`);
        }
        [...vdecls].sort((a, b) => a[0].localeCompare(b[0])).forEach((kv) => {
            if (kv[0] !== "bool") {
                vdeclscpp.push(kv[1].map((vname) => `${kv[0]} ${vname}`).join("; ") + ";");
            }
        });
        return [refscope, ...vdeclscpp].join("\n    ");
    }
    generateCPPInvoke(idecl) {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.getMIRType(idecl.resultType);
        const args = idecl.params.map((arg) => `${this.typegen.getCPPReprFor(this.typegen.getMIRType(arg.type)).std} ${this.varNameToCppName(arg.name)}`);
        const restype = this.typegen.getCPPReprFor(this.typegen.getMIRType(idecl.resultType)).std;
        if (this.typegen.getRefCountableStatus(this.typegen.getMIRType(idecl.resultType)) !== "no") {
            args.push(`BSQRefScope& $callerscope$`);
        }
        const decl = `${restype} ${this.invokenameToCPP(idecl.key)}(${args.join(", ")})`;
        if (idecl instanceof mir_assembly_1.MIRInvokeBodyDecl) {
            this.vtypes = new Map();
            idecl.body.vtypes.forEach((tkey, name) => {
                this.vtypes.set(name, this.assembly.typeMap.get(tkey));
            });
            this.generatedBlocks = new Map();
            const blocks = mir_info_1.topologicalOrder(idecl.body.body);
            for (let i = 0; i < blocks.length; ++i) {
                this.generateBlock(blocks[i]);
            }
            const blockstrs = [...this.generatedBlocks].map((blck) => {
                const lbl = `${this.labelToCpp(blck[0])}:\n`;
                const stmts = blck[1].map((stmt) => "    " + stmt).join("\n");
                if (lbl.startsWith("entry:")) {
                    return stmts;
                }
                else {
                    return lbl + stmts;
                }
            });
            const scopestrs = this.generateCPPVarDecls(idecl.body, idecl.params);
            return { fwddecl: decl + ";", fulldecl: `${decl}\n{\n${scopestrs}\n\n${blockstrs.join("\n\n")}\n}\n` };
        }
        else {
            assert(idecl instanceof mir_assembly_1.MIRInvokePrimitiveDecl);
            const params = idecl.params.map((arg) => this.varNameToCppName(arg.name));
            return { fwddecl: decl + ";", fulldecl: `${decl} { ${this.generateBuiltinBody(idecl, params)} }\n` };
        }
    }
    getEnclosingListTypeForListOp(idecl) {
        return this.typegen.getMIRType(idecl.enclosingDecl);
    }
    getListContentsInfoForListOp(idecl) {
        return this.typegen.assembly.entityDecls.get(idecl.enclosingDecl).terms.get("T");
    }
    getListResultTypeFor(idecl) {
        const le = this.typegen.assembly.entityDecls.get(idecl.resultType);
        const ltype = this.typegen.getMIRType(le.tkey);
        const ctype = le.terms.get("T");
        return [this.typegen.getCPPReprFor(ltype).base, this.typegen.getCPPReprFor(ctype).base, `MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(le.tkey)}`];
    }
    getSetContentsInfoForListOp(idecl) {
        return this.typegen.assembly.entityDecls.get(idecl.enclosingDecl).terms.get("T");
    }
    createListOpsFor(ltype, ctype) {
        const lrepr = this.typegen.getCPPReprFor(ltype).base;
        const crepr = this.typegen.getCPPReprFor(ctype);
        const cops = this.typegen.getFunctorsForType(ctype);
        return `BSQListOps<${lrepr}, ${crepr.std}, ${cops.inc}, ${cops.dec}, ${cops.display}>`;
    }
    createLambdaFor(pc) {
        const pci = this.assembly.invokeDecls.get(pc.code) || this.assembly.primitiveInvokeDecls.get(pc.code);
        let params = [];
        let args = [];
        for (let i = 0; i < pci.params.length - pc.cargs.length; ++i) {
            const prepr = this.typegen.getCPPReprFor(this.typegen.getMIRType(pci.params[i].type));
            params.push(`${prepr.std} $arg_${i}`);
            args.push(`$arg_${i}`);
        }
        const cargs = pc.cargs.map((ca) => this.typegen.mangleStringForCpp(ca));
        const rrepr = this.typegen.getCPPReprFor(this.typegen.getMIRType(pci.resultType));
        return `[&](${params.join(", ")}) -> ${rrepr.std} { return ${this.typegen.mangleStringForCpp(pc.code)}(${[...args, ...cargs].join(", ")}); }`;
    }
    generateBuiltinBody(idecl, params) {
        const scopevar = this.varNameToCppName("$scope$");
        let bodystr = ";";
        switch (idecl.implkey) {
            case "validator_accepts": {
                const rs = this.assembly.literalRegexs.get(this.assembly.validatorRegexs.get(idecl.enclosingDecl));
                bodystr = cpp_regex_1.compileRegexCppMatch(rs, params[0], "$$return");
                break;
            }
            case "enum_create": {
                bodystr = `auto $$return = BSQEnum{ (uint32_t)BSQ_GET_VALUE_TAGGED_INT(${params[0]}), MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(this.currentRType.trkey)} };`;
                break;
            }
            case "string_count": {
                bodystr = `auto $$return = ${params[0]}->sdata.size();`;
                break;
            }
            case "string_charat": {
                bodystr = `auto $$return = BSQ_NEW_NO_RC(BSQString, ${params[0]}->sdata[${params[1]}]);`;
                break;
            }
            case "string_concat": {
                const body = `acc.append((*iter)->sdata);`;
                const sstr = `std::string acc; for(auto iter = ${params[0]}->entries.cbegin(); iter != ${params[0]}->entries.cend(); ++iter) { ${body} }`;
                bodystr = `${sstr}; auto $$return = BSQ_NEW_NO_RC(BSQString, std::move(acc));`;
                break;
            }
            case "string_substring": {
                bodystr = `auto $$return = BSQ_NEW_NO_RC(BSQString, ${params[0]}->substr(${params[1]}, ${params[2]} - ${params[1]});`;
                break;
            }
            case "safestring_string": {
                bodystr = `auto $$return =  BSQ_NEW_NO_RC(BSQString, BSQ_GET_VALUE_PTR(${params[0]}, BSQSafeString)->sdata);`;
                break;
            }
            case "safestring_unsafe_from": {
                bodystr = `auto $$return = BSQ_NEW_NO_RC(BSQSafeString, ${params[0]}->sdata, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(this.currentRType.trkey)});`;
                break;
            }
            case "stringof_string": {
                bodystr = `auto $$return =  BSQ_NEW_NO_RC(BSQString, BSQ_GET_VALUE_PTR(${params[0]}, BSQStringOf)->sdata);`;
                break;
            }
            case "stringof_unsafe_from": {
                bodystr = `auto $$return = BSQ_NEW_NO_RC(BSQStringOf, ${params[0]}->sdata, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(this.currentRType.trkey)});`;
                break;
            }
            case "list_size": {
                bodystr = `auto $$return = (int64_t)(${params[0]}->entries.size());`;
                break;
            }
            case "list_unsafe_get": {
                bodystr = `auto $$return = ${params[0]}->entries[${params[1]}];`;
                break;
            }
            case "list_all": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const lambda = this.createLambdaFor(idecl.pcodes.get("p"));
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_all(${params[0]}, ${lambda});`;
                break;
            }
            case "list_any": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const lambda = this.createLambdaFor(idecl.pcodes.get("p"));
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_any(${params[0]}, ${lambda});`;
                break;
            }
            case "list_none": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const lambda = this.createLambdaFor(idecl.pcodes.get("p"));
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_none(${params[0]}, ${lambda});`;
                break;
            }
            case "list_count": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const lambda = this.createLambdaFor(idecl.pcodes.get("p"));
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_count(${params[0]}, ${lambda});`;
                break;
            }
            case "list_countnot": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const lambda = this.createLambdaFor(idecl.pcodes.get("p"));
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_countnot(${params[0]}, ${lambda});`;
                break;
            }
            case "list_indexof": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const lambda = this.createLambdaFor(idecl.pcodes.get("p"));
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_indexof(${params[0]}, ${params[1]}, ${params[2]}, ${lambda});`;
                break;
            }
            case "list_indexoflast": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const lambda = this.createLambdaFor(idecl.pcodes.get("p"));
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_indexoflast(${params[0]}, ${params[1]}, ${params[2]}, ${lambda});`;
                break;
            }
            case "list_indexofnot": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const lambda = this.createLambdaFor(idecl.pcodes.get("p"));
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_indexofnot(${params[0]}, ${params[1]}, ${params[2]}, ${lambda});`;
                break;
            }
            case "list_indexofnotlast": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const lambda = this.createLambdaFor(idecl.pcodes.get("p"));
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_indexofnotlast(${params[0]}, ${params[1]}, ${params[2]}, ${lambda});`;
                break;
            }
            case "list_count_keytype": {
                assert(false, "Need to implement");
                break;
            }
            case "list_indexof_keytype": {
                assert(false, "Need to implement");
                break;
            }
            case "list_indexoflast_keytype": {
                assert(false, "Need to implement");
                break;
            }
            case "list_min": {
                assert(false, "Need to implement");
                break;
            }
            case "list_max": {
                assert(false, "Need to implement");
                break;
            }
            case "list_sum": {
                assert(false, "Need to implement");
                break;
            }
            case "list_filter": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const lambda = this.createLambdaFor(idecl.pcodes.get("p"));
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_filter(${params[0]}, ${lambda});`;
                break;
            }
            case "list_filternot": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const lambda = this.createLambdaFor(idecl.pcodes.get("p"));
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_filternot(${params[0]}, ${lambda});`;
                break;
            }
            case "list_oftype": {
                assert(false, "Need to implement");
                break;
            }
            case "list_cast": {
                assert(false, "Need to implement");
                break;
            }
            case "list_slice": {
                assert(false, "Need to implement");
                break;
            }
            case "list_takewhile": {
                assert(false, "Need to implement");
                break;
            }
            case "list_discardwhile": {
                assert(false, "Need to implement");
                break;
            }
            case "list_takeuntil": {
                assert(false, "Need to implement");
                break;
            }
            case "list_discarduntil": {
                assert(false, "Need to implement");
                break;
            }
            case "list_unique": {
                assert(false, "Need to implement");
                break;
            }
            case "list_reverse": {
                assert(false, "Need to implement");
                break;
            }
            case "list_map": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const [utype, ucontents, utag] = this.getListResultTypeFor(idecl);
                const lambda = this.createLambdaFor(idecl.pcodes.get("f"));
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_map<${utype}, ${ucontents}, ${utag}>(${params[0]}, ${lambda});`;
                break;
            }
            case "list_mapindex": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const [utype, ucontents, utag] = this.getListResultTypeFor(idecl);
                const lambda = this.createLambdaFor(idecl.pcodes.get("f"));
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_mapindex<${utype}, ${ucontents}, ${utag}>(${params[0]}, ${lambda});`;
                break;
            }
            case "set_has_key": {
                const tcmp = this.typegen.getFunctorsForType(this.getSetContentsInfoForListOp(idecl)).eq;
                bodystr = `auto $$return = std::binary_search(${params[0]}->entries.begin(), ${params[0]}->entries.end(), ${params[1]}, ${tcmp}{});`;
                break;
            }
            /*
            case "list_unsafe_add": {
                bodystr = `auto $$return = ${params[0]}->unsafeAdd(${scopevar}, ${params[1]});`
                break;
            }
            case "list_unsafe_set": {
                bodystr = `auto $$return = ${params[0]}->unsafeSet(${scopevar}, BSQ_GET_VALUE_TAGGED_INT(${params[1]}), ${params[2]});`
                break;
            }
            case "set_has_key":
            case "map_has_key": {
                bodystr = `auto $$return = ${params[0]}->entries.find(${params[1]}) != ${params[0]}->entries.cend();`;
                break;
            }
            case "map_at_key": {
                bodystr = `auto $$return = (${params[0]}->entries.find(${params[1]}))->second.first;`;
                break;
            }
            case "set_at_val": {
                bodystr = `auto $$return = (${params[0]}->entries.find(${params[1]}))->second;`;
                break;
            }
            case "map_at_val": {
                bodystr = `auto $$return = (${params[0]}->entries.find(${params[1]}))->second.second;`;
                break;
            }
            case "set_get_keylist":
            case "map_get_keylist": {
                bodystr = "auto $$return = " + `${params[0]}->keys` + ";";
                break;
            }
            case "set_clear_val":
            case "map_clear_val": {
                bodystr = "auto $$return = " + `${params[0]}->clearKey(${params[1]}, ${params[2]}, ${scopevar});`;
                break;
            }
            case "set_unsafe_update": {
                bodystr = `auto $$return = ${params[0]}->update(${params[1]}, ${params[2]}, ${scopevar});`;
                break;
            }
            case "map_unsafe_update": {
                bodystr = `auto $$return = ${params[0]}->update(${params[1]}, ${params[2]}, ${params[3]}, ${scopevar});`;
                break;
            }
            case "set_unsafe_add": {
                bodystr = `auto $$return = ${params[0]}->add(${params[1]}, ${params[2]}, ${params[3]}, ${scopevar});`;
                break;
            }
            case "map_unsafe_add": {
                bodystr = `auto $$return = ${params[0]}->add(${params[1]}, ${params[2]}, ${params[3]}, ${params[4]}, ${scopevar});`;
                break;
            }
            */
            default: {
                assert(false, `Need to implement -- ${idecl.iname}`);
                break;
            }
        }
        const refscope = `BSQRefScope ${scopevar};`;
        let returnmgr = "";
        if (this.typegen.getRefCountableStatus(this.currentRType) !== "no") {
            returnmgr = this.typegen.buildReturnOpForType(this.currentRType, "$$return", "$callerscope$");
        }
        return "\n    " + refscope + "\n    " + bodystr + "\n    " + returnmgr + "\n    " + "return $$return;\n";
    }
}
exports.CPPBodyEmitter = CPPBodyEmitter;
//# sourceMappingURL=cppbody_emitter.js.map