//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIRInvokeDecl, MIRInvokeBodyDecl, MIRInvokePrimitiveDecl, MIRConstantDecl, MIRFieldDecl, MIREntityTypeDecl, MIREntityType, MIRTupleType, MIRRecordType, MIRConceptType, MIREphemeralListType, MIRRegex } from "../../compiler/mir_assembly";
import { SMTTypeEmitter } from "./smttype_emitter";
import { MIRArgument, MIRRegisterArgument, MIRConstantNone, MIRConstantFalse, MIRConstantTrue, MIRConstantInt, MIRConstantArgument, MIRConstantString, MIROp, MIROpTag, MIRLoadConst, MIRAccessArgVariable, MIRAccessLocalVariable, MIRInvokeFixedFunction, MIRPrefixOp, MIRBinOp, MIRBinEq, MIRBinCmp, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRRegAssign, MIRTruthyConvert, MIRVarStore, MIRReturnAssign, MIRJumpCond, MIRJumpNone, MIRAbort, MIRPhi, MIRBasicBlock, MIRJump, MIRConstructorTuple, MIRConstructorRecord, MIRAccessFromIndex, MIRAccessFromProperty, MIRInvokeKey, MIRAccessConstantValue, MIRLoadFieldDefaultValue, MIRConstructorPrimary, MIRAccessFromField, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionSingletons, MIRIsTypeOf, MIRProjectFromIndecies, MIRModifyWithIndecies, MIRStructuredExtendTuple, MIRProjectFromProperties, MIRModifyWithProperties, MIRStructuredExtendRecord, MIRLoadConstTypedString, MIRConstructorEphemeralValueList, MIRProjectFromFields, MIRModifyWithFields, MIRStructuredExtendObject, MIRLoadConstSafeString, MIRInvokeInvariantCheckDirect, MIRLoadFromEpehmeralList, MIRNominalTypeKey, MIRConstantBigInt, MIRConstantFloat64, MIRFieldKey, MIRPackSlice, MIRPackExtend, MIRResolvedTypeKey, MIRBinLess, MIRConstantRegex } from "../../compiler/mir_ops";
import { SMTExp, SMTValue, SMTCond, SMTLet, SMTFreeVar } from "./smt_exp";
import { SourceInfo } from "../../ast/parser";

import * as assert from "assert";
import { compileRegexSMTMatch } from "./smt_regex";

function NOT_IMPLEMENTED<T>(msg: string): T {
    throw new Error(`Not Implemented: ${msg}`);
}

class SMTBodyEmitter {
    readonly assembly: MIRAssembly;
    readonly typegen: SMTTypeEmitter;

    private standard_gas = 4;
    private collection_gas = 5;
    private string_gas = 10;
    private regex_gas = 3;

    private errorCodes = new Map<string, number>();
    private gasLimits = new Map<string, number>().set("default", this.standard_gas).set("collection", this.collection_gas).set("string",this.string_gas).set("regex", this.regex_gas);

    readonly allConstRegexes: Map<string, string> = new Map<string, string>();

    private currentFile: string = "[No File]";
    private currentRType: MIRType;
    private tmpvarctr = 0;
    private currentSCC = new Set<string>();

    private vtypes: Map<string, MIRType> = new Map<string, MIRType>();

    private subtypeOrderCtr = 0;
    subtypeFMap: Map<string, {order: number, decl: string}> = new Map<string, {order: number, decl: string}>();
    checkedConcepts: Set<MIRResolvedTypeKey> = new Set<MIRResolvedTypeKey>();

    vfieldLookups: { infertype: MIRType, fdecl: MIRFieldDecl, lname: string }[] = [];
    vfieldProjects: { infertype: MIRType, fprojs: MIRFieldDecl[], resultAccessType: MIRType, uname: string }[] = [];
    vfieldUpdates: { infertype: MIRType, fupds: [MIRFieldDecl, MIRArgument][], resultAccessType: MIRType, uname: string }[] = [];
    vobjmerges: { infertype: MIRType, merge: MIRArgument, infermergetype: MIRType, fieldResolves: [string, MIRFieldDecl][], resultAccessType: MIRType, mname: string }[] = [];

    constructor(assembly: MIRAssembly, typegen: SMTTypeEmitter) {
        this.assembly = assembly;
        this.typegen = typegen;

        this.currentRType = typegen.noneType;
    }

    private static cleanStrRepr(s: string): string {
        return "\"" + s.substring(1, s.length - 1) + "\"";
    }

    generateTempName(): string {
        return `@tmpvar@${this.tmpvarctr++}`;
    }

    generateErrorCreate(sinfo: SourceInfo, rtype: string): SMTValue {
        const errorinfo = `${this.currentFile} @ line ${sinfo.line} -- column ${sinfo.column}`;
        if (!this.errorCodes.has(errorinfo)) {
            this.errorCodes.set(errorinfo, this.errorCodes.size);
        }
        const errid = this.errorCodes.get(errorinfo) as number;

        return new SMTValue(`(result_error@${rtype} (result_error ${errid}))`);
    }

    getErrorIds(...sinfos: SourceInfo[]): number[] {
        const ekeys = sinfos.map((sinfo) => `${this.currentFile} @ line ${sinfo.line} -- column ${sinfo.column}`);
        return [...new Set<number>(ekeys.map((k) => this.errorCodes.get(k) as number))].sort();
    }

    getGasKeyForOperation(ikey: MIRInvokeKey): "collection" | "string" | "regex" | "default" {
        if(ikey.startsWith("NSCore::List<") || ikey.startsWith("NSCore::Set<") || ikey.startsWith("NSCore::Map<")) {
            return "collection";
        }
        else if(ikey.startsWith("NSCore::String")) {
            return "string";
        }
        else if(ikey.startsWith("NSCore::Regex")) {
            return "regex";
        }
        else {
            return "default";
        }
    }

    getGasForOperation(ikey: MIRInvokeKey): number {
        return this.gasLimits.get(this.getGasKeyForOperation(ikey)) as number;
    }

    generateBMCLimitCreate(ikey: MIRInvokeKey, rtype: string): SMTValue {
        const errid = this.getGasKeyForOperation(ikey);
        return new SMTValue(`(result_error@${rtype} (result_bmc "${errid}"))`);
    }

    isSafeInvoke(idecl: MIRInvokeDecl): boolean {
        return idecl.pragmas.some((pragma) => pragma[0].trkey === "NSCore::AssumeSafe" || pragma[0].trkey === "NSCore::KnownSafe");
    }

    varNameToSMTName(name: string): string {
        if (name === "$$return") {
            return "$$return";
        }
        else {
            return this.typegen.mangleStringForSMT(name);
        }
    }

    varToSMTName(varg: MIRRegisterArgument): string {
        return this.varNameToSMTName(varg.nameID);
    }

    invokenameToSMT(ivk: MIRInvokeKey): string {
        return this.typegen.mangleStringForSMT(ivk);
    }

    getArgType(arg: MIRArgument): MIRType {
        if (arg instanceof MIRRegisterArgument) {
            return this.vtypes.get(arg.nameID) as MIRType;
        }
        else {
            if (arg instanceof MIRConstantNone) {
                return this.typegen.noneType;
            }
            else if (arg instanceof MIRConstantTrue || arg instanceof MIRConstantFalse) {
                return this.typegen.boolType;
            }
            else if (arg instanceof MIRConstantInt) {
                return this.typegen.intType;
            }
            else if (arg instanceof MIRConstantString) {
                return this.typegen.stringType;
            }
            else {
                return this.typegen.regexType;
            }
        }
    }

    generateConstantExp(cval: MIRConstantArgument, into: MIRType): SMTExp {
        if (cval instanceof MIRConstantNone) {
            return this.typegen.coerce(new SMTValue("bsqkey_none"), this.typegen.noneType, into);
        }
        else if (cval instanceof MIRConstantTrue) {
            return this.typegen.coerce(new SMTValue("true"), this.typegen.boolType, into);
        }
        else if (cval instanceof MIRConstantFalse) {
            return this.typegen.coerce(new SMTValue("false"), this.typegen.boolType, into);
        }
        else if (cval instanceof MIRConstantInt) {
            return this.typegen.coerce(new SMTValue(cval.value), this.typegen.intType, into);
        }
        else if (cval instanceof MIRConstantBigInt) {
            return this.typegen.coerce(new SMTValue(cval.digits()), this.typegen.bigIntType, into);
        }
        else if (cval instanceof MIRConstantFloat64) {
            return this.typegen.coerce(new SMTValue(cval.digits()), this.typegen.float64Type, into);
        }
        else if (cval instanceof MIRConstantString) {
            const sval = SMTBodyEmitter.cleanStrRepr((cval as MIRConstantString).value);
            return this.typegen.coerce(new SMTValue(sval), this.typegen.stringType, into);
        }
        else {
            assert(cval instanceof MIRConstantRegex);

            const rval = (cval as MIRConstantRegex).value;
            const rname = "REGEX__" + this.allConstRegexes.size;
            if (!this.allConstRegexes.has(rval)) {
                this.allConstRegexes.set(rval, rname);
            }

            const regexval = `${this.allConstRegexes.get(rval) as string}`;
            return this.typegen.coerce(new SMTValue(regexval), this.typegen.regexType, into);
        }
    }

    argToSMT(arg: MIRArgument, into: MIRType): SMTExp {
        if (arg instanceof MIRRegisterArgument) {
            return this.typegen.coerce(new SMTValue(this.varToSMTName(arg)), this.getArgType(arg), into);
        }
        else {
            return this.generateConstantExp(arg as MIRConstantArgument, into);
        }
    }

    generateTruthyConvert(arg: MIRArgument): SMTExp {
        const argtype = this.getArgType(arg);

        if (this.assembly.subtypeOf(argtype, this.typegen.noneType)) {
            return new SMTValue("false");
        }
        else if (this.assembly.subtypeOf(argtype, this.typegen.boolType)) {
            return this.argToSMT(arg, this.typegen.boolType);
        }
        else if (this.typegen.typecheckAllKeys(argtype)) {
            return new SMTValue(`(= ${this.argToSMT(arg, this.typegen.keyType).emit()} (bsqkey_bool true))`);
        }
        else {
            return new SMTValue(`(= ${this.argToSMT(arg, this.typegen.anyType).emit()} (bsqterm_key (bsqkey_bool true)))`);
        }
    }

    generateNoneCheck(arg: MIRArgument): SMTExp {
        const argtype = this.getArgType(arg);

        if (this.assembly.subtypeOf(argtype, this.typegen.noneType)) {
            return new SMTValue("true");
        }
        else if (!this.assembly.subtypeOf(this.typegen.noneType, argtype)) {
            return new SMTValue("false");
        }
        else if(this.typegen.typecheckAllKeys(argtype)) {
            return new SMTValue(`(= ${this.argToSMT(arg, this.typegen.keyType).emit()} bsqkey_none)`);
        }
        else {
            return new SMTValue(`(= ${this.argToSMT(arg, this.typegen.anyType).emit()} bsqterm_none)`);
        }
    }

    generateLoadConstSafeString(op: MIRLoadConstSafeString): SMTExp {
        const sval = SMTBodyEmitter.cleanStrRepr(op.ivalue);

        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_safestring@cons MIRNominalTypeEnum_${this.typegen.mangleStringForSMT(op.tskey)} ${sval})`));
    }

    generateLoadConstTypedString(op: MIRLoadConstTypedString): SMTExp {
        const sval = SMTBodyEmitter.cleanStrRepr(op.ivalue);

        if (op.pfunckey === undefined) {
            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_stringof@cons MIRNominalTypeEnum_${this.typegen.mangleStringForSMT(op.tskey)} ${sval})`));
        }
        else {
            const pfunc = (this.assembly.invokeDecls.get(op.pfunckey) || this.assembly.primitiveInvokeDecls.get(op.pfunckey)) as MIRInvokeDecl;

            const rval = new SMTValue(`(bsq_stringof@cons MIRNominalTypeEnum_${this.typegen.mangleStringForSMT(op.tskey)} ${sval})`);
            const ivrtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(pfunc.resultType));
            
            const emitstr = new SMTLet(this.varToSMTName(op.trgt), rval);
            const failchk = this.generateErrorCreate(op.sinfo, this.typegen.getSMTTypeFor(this.currentRType));

            const tv = this.generateTempName();
            const iserr = new SMTValue(`(is-result_error@${ivrtype} ${tv})`);
            const errchk = this.generateTypeCheck(`(result_success_value@${ivrtype} ${tv})`, this.typegen.getMIRType(pfunc.resultType), this.typegen.getMIRType(pfunc.resultType), this.typegen.getMIRType(op.errtype as MIRResolvedTypeKey));
            const condop = new SMTCond(new SMTValue(`(or ${iserr.emit()} ${errchk})`), failchk, emitstr);
    
            return new SMTLet(tv, new SMTValue(`(${this.invokenameToSMT(op.pfunckey)} ${sval})`), condop);
        }
    }

    generateAccessConstantValue(cp: MIRAccessConstantValue): SMTExp {
        const cdecl = this.assembly.constantDecls.get(cp.ckey) as MIRConstantDecl;

        const tv = this.generateTempName();
        const ivrtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(cdecl.declaredType));
        const resulttype = this.typegen.getSMTTypeFor(this.currentRType);

        const constexp = new SMTValue(this.invokenameToSMT(cdecl.value));
        const checkerror = new SMTValue(`(is-result_error@${ivrtype} ${tv})`);
        const extracterror = (ivrtype !== resulttype) ? new SMTValue(`(result_error@${this.typegen.getSMTTypeFor(this.currentRType)} (result_error_code@${ivrtype} ${tv}))`) : new SMTValue(tv);
        const normalassign = new SMTLet(this.varToSMTName(cp.trgt), new SMTValue(`(result_success_value@${ivrtype} ${tv})`));

        return new SMTLet(tv, constexp, new SMTCond(checkerror, extracterror, normalassign));
    }

    generateLoadFieldDefaultValue(ld: MIRLoadFieldDefaultValue): SMTExp {
        const fdecl = this.assembly.fieldDecls.get(ld.fkey) as MIRFieldDecl;

        const tv = this.generateTempName();
        const ivrtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(fdecl.declaredType));
        const resulttype = this.typegen.getSMTTypeFor(this.currentRType);

        const constexp = new SMTValue(this.invokenameToSMT(fdecl.value as MIRInvokeKey));
        const checkerror = new SMTValue(`(is-result_error@${ivrtype} ${tv})`);
        const extracterror = (ivrtype !== resulttype) ? new SMTValue(`(result_error@${resulttype} (result_error_code@${ivrtype} ${tv}))`) : new SMTValue(tv);
        const normalassign = new SMTLet(this.varToSMTName(ld.trgt), new SMTValue(`(result_success_value@${ivrtype} ${tv})`));

        return new SMTLet(tv, constexp, new SMTCond(checkerror, extracterror, normalassign));
    }

    generateMIRInvokeInvariantCheckDirect(ivop: MIRInvokeInvariantCheckDirect): SMTExp {
        const fields = [...(this.typegen.assembly.entityDecls.get(ivop.tkey) as MIREntityTypeDecl).fields].sort((a, b) => a.name.localeCompare(b.name));
        let vals: string[] = fields.map((f) => `(${this.typegen.generateEntityAccessor(ivop.tkey, f.fkey)} ${this.argToSMT(ivop.rcvr, this.typegen.getMIRType(ivop.tkey)).emit()})`);
        
        const tv = this.generateTempName();
        const ivrtype = this.typegen.getSMTTypeFor(this.typegen.boolType);
        const resulttype = this.typegen.getSMTTypeFor(this.currentRType);

        const checkerror = new SMTValue(`(is-result_error@${ivrtype} ${tv})`);
        const extracterror = (ivrtype !== resulttype) ? new SMTValue(`(result_error@${resulttype} (result_error_code@${ivrtype} ${tv}))`) : new SMTValue(tv);
        const normalassign = new SMTLet(this.varToSMTName(ivop.trgt), new SMTValue(`(result_success_value@${ivrtype} ${tv})`));

        const invokeexp = new SMTValue(`(${this.invokenameToSMT(ivop.ikey)} ${vals.join(" ")})`);
        return new SMTLet(tv, invokeexp, new SMTCond(checkerror, extracterror, normalassign));
    }

    generateMIRConstructorPrimary(cp: MIRConstructorPrimary): SMTExp {
        const ctype = this.assembly.entityDecls.get(cp.tkey) as MIREntityTypeDecl;
        const fvals = cp.args.map((arg, i) => {
            const ftype = this.typegen.getMIRType(ctype.fields[i].declaredType);
            return this.argToSMT(arg, ftype).emit();
        });

        const smtctype = this.typegen.generateEntityConstructor(cp.tkey);
        const cexp = ctype.fields.length === 0 ? new SMTValue(smtctype) : new SMTValue(`(${smtctype} ${fvals.join(" ")})`);
        return new SMTLet(this.varToSMTName(cp.trgt), cexp);
    }

    generateMIRConstructorPrimaryCollectionEmpty(cpce: MIRConstructorPrimaryCollectionEmpty): SMTExp {
        const cpcetype = this.typegen.getMIRType(cpce.tkey);
        const smtctype = this.typegen.generateEntityConstructor(cpce.tkey);
        
        if(this.typegen.typecheckIsName(cpcetype, /NSCore::List<.*>/)) {
            return new SMTLet(this.varToSMTName(cpce.trgt), new SMTValue(`(${smtctype} 0 ${this.typegen.generateEmptyDataArrayFor(cpce.tkey)})`));
        }
        else if(this.typegen.typecheckIsName(cpcetype, /NSCore::Stack<.*>/)) {
            return new SMTLet(this.varToSMTName(cpce.trgt), new SMTValue(`(${smtctype} 0 ${this.typegen.generateEmptyDataArrayFor(cpce.tkey)})`));
        }
        else if(this.typegen.typecheckIsName(cpcetype, /NSCore::Queue<.*>/)) {
            return new SMTLet(this.varToSMTName(cpce.trgt), new SMTValue(`(${smtctype} 0 0 ${this.typegen.generateEmptyDataArrayFor(cpce.tkey)})`));
        }
        else if(this.typegen.typecheckIsName(cpcetype, /NSCore::Set<.*>/) || this.typegen.typecheckIsName(cpcetype, /NSCore::DynamicSet<.*>/)) {
            return new SMTLet(this.varToSMTName(cpce.trgt), new SMTValue(`(${smtctype} 0 ${this.typegen.generateEmptyHasArrayFor(cpce.tkey)} bsqterm_none)`));
        }
        else {
           return new SMTLet(this.varToSMTName(cpce.trgt), new SMTValue(`(${smtctype} 0 ${this.typegen.generateEmptyHasArrayFor(cpce.tkey)} ${this.typegen.generateEmptyDataArrayFor(cpce.tkey)} bsqterm_none)`));
        }
    }

    generateMIRConstructorPrimaryCollectionSingletons(cpcs: MIRConstructorPrimaryCollectionSingletons): SMTExp {
        const cpcstype = this.typegen.getMIRType(cpcs.tkey);
        const smtctype = this.typegen.generateEntityConstructor(cpcs.tkey);

        if(this.typegen.typecheckIsName(cpcstype, /NSCore::List<.*>/)) {
            const oftype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
            let consv = this.typegen.generateEmptyDataArrayFor(cpcs.tkey);
            for (let i = 0; i < cpcs.args.length; ++i) {
                consv = `(store ${consv} ${i} ${this.argToSMT(cpcs.args[i], oftype).emit()})`;
            }

            return new SMTLet(this.varToSMTName(cpcs.trgt), new SMTValue(`(${smtctype} ${cpcs.args.length} ${consv})`));
        }
        else if(this.typegen.typecheckIsName(cpcstype, /NSCore::Stack<.*>/)) {
            const oftype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
            let consv = this.typegen.generateEmptyDataArrayFor(cpcs.tkey);
            for (let i = 0; i < cpcs.args.length; ++i) {
                consv = `(store ${consv} ${i} ${this.argToSMT(cpcs.args[i], oftype).emit()})`;
            }

            return new SMTLet(this.varToSMTName(cpcs.trgt), new SMTValue(`(${smtctype} ${cpcs.args.length} ${consv})`));
        }
        else if(this.typegen.typecheckIsName(cpcstype, /NSCore::Queue<.*>/)) {
            const oftype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
            let consv = this.typegen.generateEmptyDataArrayFor(cpcs.tkey);
            for (let i = 0; i < cpcs.args.length; ++i) {
                consv = `(store ${consv} ${i} ${this.argToSMT(cpcs.args[i], oftype).emit()})`;
            }

            return new SMTLet(this.varToSMTName(cpcs.trgt), new SMTValue(`(${smtctype} 0 ${cpcs.args.length} ${consv})`));
        }
        else if(this.typegen.typecheckIsName(cpcstype, /NSCore::Set<.*>/) || this.typegen.typecheckIsName(cpcstype, /NSCore::DynamicSet<.*>/)) {
            const oftype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("T") as MIRType;

            const kltype = [...this.typegen.assembly.entityDecls].find((edecl) => edecl[1].ns === "NSCore" && edecl[1].name === "KeyList" && (edecl[1].terms.get("K") as MIRType).trkey === oftype.trkey) as [string, MIREntityTypeDecl];
            const klcons = this.typegen.generateEntityConstructor(kltype[1].tkey);
            const klstore = this.typegen.getKeyListTypeForSet(this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl);

            let consv = `(${smtctype} %CTR% %HAS% %KEY%)`;
            for (let i = cpcs.args.length - 1; i >= 1; --i) {
                const arg = cpcs.args[i];

                const key = this.argToSMT(arg, oftype).emit();
                const ctrvar = this.generateTempName();
                const ctrup = `(ite (select %HAS% ${key}) %CTR% (+ %CTR% 1))`;

                const hasvar = this.generateTempName();
                const hasup = `(store %HAS% ${key} true)`;

                const keyvar = this.generateTempName();
                const keycons = `(${klcons} ${key} %KEY%)`;
                const keyforce = this.typegen.coerce(new SMTValue(keycons), this.typegen.getMIRType(kltype[1].tkey), klstore).emit();
                const keyup = `(ite (select %HAS% ${key}) %KEY% ${keyforce})`;

                const body = consv.replace(/%CTR%/g, ctrvar).replace(/%HAS%/g, hasvar).replace(/%KEY%/g, keyvar);
                consv = `(let ((${ctrvar} ${ctrup}) (${hasvar} ${hasup}) (${keyvar} ${keyup})) ${body})`
            }
            const key = this.argToSMT(cpcs.args[0], oftype).emit();
            const kl = new SMTValue(`(${klcons} ${key} bsqterm_none)`);
            const final = consv
                .replace(/%CTR%/g, "1")
                .replace(/%HAS%/g, `(store ${this.typegen.generateEmptyHasArrayFor(cpcs.tkey)} ${key} true)`)
                .replace(/%KEY%/g, this.typegen.coerce(kl, this.typegen.getMIRType(kltype[1].tkey), klstore).emit());

            return new SMTLet(this.varToSMTName(cpcs.trgt), new SMTValue(final));
        }
        else {
            const ktype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("K") as MIRType;
            const vtype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("V") as MIRType;

            const entrytype = [...this.typegen.assembly.entityDecls].find((edecl) => edecl[1].ns === "NSCore" && edecl[1].name === "MapEntry" && (edecl[1].terms.get("K") as MIRType).trkey === ktype.trkey && (edecl[1].terms.get("V") as MIRType).trkey === vtype.trkey) as [string, MIREntityTypeDecl];
            const entrykey = this.typegen.generateEntityAccessor(entrytype[1].tkey, (entrytype[1].fields.find((fd) => fd.name === "key") as MIRFieldDecl).fkey);
            const entryvalue = this.typegen.generateEntityAccessor(entrytype[1].tkey, (entrytype[1].fields.find((fd) => fd.name === "value") as MIRFieldDecl).fkey);

            const kltype = [...this.typegen.assembly.entityDecls].find((edecl) => edecl[1].ns === "NSCore" && edecl[1].name === "KeyList" && (edecl[1].terms.get("K") as MIRType).trkey === ktype.trkey) as [string, MIREntityTypeDecl];
            const klcons = this.typegen.generateEntityConstructor(kltype[1].tkey);
            const klstore = this.typegen.getKeyListTypeForMap(this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl);

            let consv = `(${smtctype} %CTR% %HAS% %ENTRYDATA% %KEY%)`;
            for (let i = cpcs.args.length - 1; i >= 1; --i) {
                const arg = cpcs.args[i];
                const entrykeyexp = `(${entrykey} ${this.argToSMT(arg, this.typegen.getMIRType(entrytype[1].tkey)).emit()})`;
                const entryvalexp = `(${entryvalue} ${this.argToSMT(arg, this.typegen.getMIRType(entrytype[1].tkey)).emit()})`;

                const key = entrykeyexp;
                const ctrvar = this.generateTempName();
                const ctrup = `(ite (select %HAS% ${key}) %CTR% (+ %CTR% 1))`;

                const hasvar = this.generateTempName();
                const hasup = `(store %HAS% ${key} true)`;

                const entrydatavar = this.generateTempName();
                const entrydataup = `(store %ENTRYDATA% ${key} ${entryvalexp})`;

                const keyvar = this.generateTempName();
                const keycons = `(${klcons} ${key} %KEY%)`;
                const keyforce = this.typegen.coerce(new SMTValue(keycons), this.typegen.getMIRType(kltype[1].tkey), klstore).emit();
                const keyup = `(ite (select %HAS% ${key}) %KEY% ${keyforce})`;

                const body = consv.replace(/%CTR%/g, ctrvar).replace(/%HAS%/g, hasvar).replace(/%ENTRYDATA%/g, entrydatavar).replace(/%KEY%/g, keyvar);
                consv = `(let ((${ctrvar} ${ctrup}) (${hasvar} ${hasup}) (${entrydatavar} ${entrydataup})  (${keyvar} ${keyup})) ${body})`
            }
            const entrykeyexp0 = `(${entrykey} ${this.argToSMT(cpcs.args[0], this.typegen.getMIRType(entrytype[1].tkey)).emit()})`;
            const entryvalexp0 = `(${entryvalue} ${this.argToSMT(cpcs.args[0], this.typegen.getMIRType(entrytype[1].tkey)).emit()})`;

            const key = entrykeyexp0;
            const kl = new SMTValue(`(${klcons} ${key} bsqterm_none)`);
            const final = consv
                .replace(/%CTR%/g, "1")
                .replace(/%HAS%/g, `(store ${this.typegen.generateEmptyHasArrayFor(cpcs.tkey)} ${key} true)`)
                .replace(/%ENTRYDATA%/g, `(store ${this.typegen.generateEmptyDataArrayFor(cpcs.tkey)} ${key} ${entryvalexp0})`)
                .replace(/%KEY%/g, this.typegen.coerce(kl, this.typegen.getMIRType(kltype[1].tkey), klstore).emit());

            return new SMTLet(this.varToSMTName(cpcs.trgt), new SMTValue(final));
        }
    }

    generateDataKindLoad(rtype: MIRType, cf: string): string {
        const idf = this.typegen.generateInitialDataKindFlag(rtype);
        return idf === "unknown" ? cf : idf;
    }

    generateMIRConstructorTuple(op: MIRConstructorTuple): SMTExp {
        let fvals = "StructuralSpecialTypeInfo@Clear";
        let cvals = "bsqtuple_array_empty";
        for (let i = 0; i < op.args.length; ++i) {
            cvals = `(store ${cvals} ${i} ${this.argToSMT(op.args[i], this.typegen.anyType).emit()})`;
            fvals = `(@fj ${this.argToSMT(op.args[i], this.typegen.anyType)} ${fvals})`;
        }

        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_tuple@cons ${this.generateDataKindLoad(this.typegen.getMIRType(op.resultTupleType), fvals)} ${cvals})`));
    }

    generateMIRConstructorRecord(op: MIRConstructorRecord): SMTExp {
        let fvals = "StructuralSpecialTypeInfo@Clear";
        let cvals = "bsqrecord_array_empty";
        for (let i = 0; i < op.args.length; ++i) {
            cvals = `(store ${cvals} "${op.args[i][0]}" ${this.argToSMT(op.args[i][1], this.typegen.anyType).emit()})`;
            fvals = `(@fj ${this.argToSMT(op.args[i][1], this.typegen.anyType)} ${fvals})`;
        }

        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_record@cons ${this.generateDataKindLoad(this.typegen.getMIRType(op.resultRecordType), fvals)} ${cvals})`));
    }

    generateMIRConstructorEphemeralValueList(op: MIRConstructorEphemeralValueList): SMTExp {
        const etype = this.typegen.getMIRType(op.resultEphemeralListType).options[0] as MIREphemeralListType;

        let args: string[] = [];
        for(let i = 0; i < op.args.length; ++i) {
            args.push(this.argToSMT(op.args[i], etype.entries[i]).emit());
        } 

        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(${this.typegen.generateEntityConstructor(etype.trkey)} ${args.join(" ")})`));
    }

    generateMIRAccessFromIndexExpression(arg: MIRArgument, idx: number, resultAccessType: MIRType): SMTExp {
        const tuptype = this.getArgType(arg);
        const hasidx = this.typegen.tupleHasIndex(tuptype, idx);
    
        if(hasidx === "no") {
            return this.typegen.coerce(new SMTValue("bsqkey_none"), this.typegen.noneType, resultAccessType);
        }
        else {
            const tupcontents = this.typegen.typecheckTuple(tuptype) ? `(bsq_tuple_entries ${this.varToSMTName(arg)})` : `(bsq_tuple_entries (bsqterm_tuple_value ${this.varToSMTName(arg)}))`;
            const select = new SMTValue(`(select ${tupcontents} ${idx})`);
            if(hasidx === "yes") {
                return this.typegen.coerce(select, this.typegen.anyType, resultAccessType);
            }
            else {
                const getop = new SMTCond(new SMTValue(`(= ${select.emit()} bsqterm@clear)`), new SMTValue("bsqterm_none"), select); 
                return this.typegen.coerce(getop, this.typegen.anyType, resultAccessType);
            }
        }
    }

    generateMIRProjectFromIndecies(op: MIRProjectFromIndecies, resultAccessType: MIRType): SMTExp { 
        const intotypes = this.typegen.typecheckEphemeral(resultAccessType) ? (resultAccessType.options[0] as MIREphemeralListType).entries : [];
        let vals: string[] = [];

        for (let i = 0; i < op.indecies.length; ++i) {
            vals.push(this.generateMIRAccessFromIndexExpression(op.arg, op.indecies[i], intotypes[i] || this.typegen.anyType).emit());
        }

        if (this.typegen.typecheckEphemeral(resultAccessType)) {
            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(${this.typegen.generateEntityConstructor(resultAccessType.trkey)} ${vals.join(" ")})`));
        }
        else {
            let fvals = "StructuralSpecialTypeInfo@Clear";
            let cvals = "bsqtuple_array_empty";
            for (let i = 0; i < vals.length; ++i) {
                cvals = `(store ${cvals} ${i} ${vals[i]})`;
                fvals = `(@fj ${vals[i]} ${fvals})`;
            }

            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_tuple@cons ${this.generateDataKindLoad(resultAccessType, fvals)} ${cvals})`));
        }
    }
    
    generateMIRModifyWithIndecies(op: MIRModifyWithIndecies, resultTupleType: MIRType): SMTExp {
        const updmax = Math.max(...op.updates.map((upd) => upd[0] + 1));

        let fvals = "StructuralSpecialTypeInfo@Clear";
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

        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_tuple@cons ${this.generateDataKindLoad(this.typegen.getMIRType(op.resultTupleType), fvals)} ${cvals})`));
    }

    generateMIRStructuredExtendTuple(op: MIRStructuredExtendTuple, resultTupleType: MIRType): SMTExp {
        //this is the exact number of indecies in arg -- see typecheck
        const btuple = this.typegen.getMaxTupleLength(this.typegen.getMIRType(op.argInferType));
        const ftuple = this.typegen.getMaxTupleLength(resultTupleType);

        let cvals = this.typegen.typecheckTuple(this.getArgType(op.arg)) ? `(bsq_tuple_entries ${this.varToSMTName(op.arg)})` : `(bsq_tuple_entries (bsqterm_tuple_value ${this.varToSMTName(op.arg)}))`;
        let mvals = this.typegen.typecheckTuple(this.getArgType(op.update)) ? `(bsq_tuple_entries ${this.varToSMTName(op.update)})` : `(bsq_tuple_entries (bsqterm_tuple_value ${this.varToSMTName(op.update)}))`;
        
        for (let i = 0; i < ftuple; ++i) {
            cvals = `(store ${cvals} ${btuple + i} (select ${mvals} ${i}))`;
        }

        let fvals = `(@fj ${this.argToSMT(op.arg, this.typegen.anyType).emit()} ${this.argToSMT(op.update, this.typegen.anyType).emit()})`;
        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_tuple@cons ${this.generateDataKindLoad(this.typegen.getMIRType(op.resultTupleType), fvals)} ${cvals})`));
    }

    generateMIRAccessFromPropertyExpression(arg: MIRArgument, property: string, resultAccessType: MIRType): SMTExp {
        const rectype = this.getArgType(arg);
        const hasproperty = this.typegen.recordHasField(rectype, property);
    
        if(hasproperty === "no") {
            return this.typegen.coerce(new SMTValue("bsqkey_none"), this.typegen.noneType, resultAccessType);
        }
        else {
            const reccontents = this.typegen.typecheckRecord(rectype) ? `(bsq_record_entries ${this.varToSMTName(arg)})` : `(bsq_record_entries (bsqterm_record_value ${this.varToSMTName(arg)}))`;
            const select = new SMTValue(`(select ${reccontents} "${property}")`);
            if(hasproperty === "yes") {
                return this.typegen.coerce(select, this.typegen.anyType, resultAccessType);
            }
            else {
                const getop = new SMTCond(new SMTValue(`(= ${select.emit()} bsqterm@clear)`), new SMTValue("bsqterm_none"), select); 
                return this.typegen.coerce(getop, this.typegen.anyType, resultAccessType);
            }
        }
    }

    generateMIRProjectFromProperties(op: MIRProjectFromProperties, resultAccessType: MIRType): SMTExp {
        const intotypes = this.typegen.typecheckEphemeral(resultAccessType) ? (resultAccessType.options[0] as MIREphemeralListType).entries : [];
        let vals: string[] = [];

        for (let i = 0; i < op.properties.length; ++i) {
            vals.push(this.generateMIRAccessFromPropertyExpression(op.arg, op.properties[i], intotypes[i] || this.typegen.anyType).emit());
        }

        if (this.typegen.typecheckEphemeral(resultAccessType)) {
            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(${this.typegen.generateEntityConstructor(resultAccessType.trkey)} ${vals.join(" ")})`));
        }
        else {
            let fvals = "StructuralSpecialTypeInfo@Clear";
            let cvals = "bsqrecord_array_empty";
            for (let i = 0; i < vals.length; ++i) {
                cvals = `(store ${cvals} "${op.properties[i]}" ${vals[i]})`;
                fvals = `(@fj ${vals[i]} ${fvals})`;
            }

            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_record@cons ${this.generateDataKindLoad(resultAccessType, fvals)} ${cvals})`));
        }
    }

    generateMIRModifyWithProperties(op: MIRModifyWithProperties, resultRecordType: MIRType): SMTExp {
        const pmax = this.typegen.getMaxPropertySet(resultRecordType);

        let fvals = "StructuralSpecialTypeInfo@Clear";
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
                cvals = `(store ${cvals} "${pname}" (select ${tc} "${pname}"))`
                fvals = `(@fj (select ${tc} "${pname}") ${fvals})`;
            }
        }

        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_record@cons ${this.generateDataKindLoad(this.typegen.getMIRType(op.resultRecordType), fvals)} ${cvals})`));
    }

    generateMIRStructuredExtendRecord(op: MIRStructuredExtendRecord, resultRecordType: MIRType): SMTExp {
        const argvals = this.typegen.typecheckRecord(this.getArgType(op.arg)) ? `(bsq_record_entries ${this.varToSMTName(op.arg)})` : `(bsq_record_entries (bsqterm_record_value ${this.varToSMTName(op.arg)}))`;
        let cvals = argvals;
        let fvals = "StructuralSpecialTypeInfo@Clear";

        const rprops = this.typegen.getMaxPropertySet(resultRecordType);
        const mtype = this.typegen.getMIRType(op.updateInferType);
        for(let i = 0; i < rprops.length; ++i) {
            const pname = rprops[i];
            const uhas = this.typegen.recordHasField(mtype, pname);
            if(uhas === "no") {
                //nothing to do for cvals
                fvals = `(@fj (select ${argvals} "${pname}") ${fvals})`;
            }
            else if (uhas === "yes") {
                cvals = `(store ${cvals} "${pname}" ${this.generateMIRAccessFromPropertyExpression(op.update, pname, this.typegen.anyType)})`;
                fvals = `(@fj ${this.generateMIRAccessFromPropertyExpression(op.update, pname, this.typegen.anyType)} ${fvals})`;
            }
            else {
                let mvals = this.typegen.typecheckRecord(this.getArgType(op.update)) ? `(bsq_record_entries ${this.varToSMTName(op.update)})` : `(bsq_record_entries (bsqterm_record_value ${this.varToSMTName(op.update)}))`;
        
                const check = new SMTValue(`(= (select ${mvals} "${pname}") bsqterm@clear)`);
                const caccess = new SMTCond(check, new SMTValue(`(select ${argvals} "${pname}")`), new SMTValue(`(select ${mvals} "${pname}")`));

                cvals = `(store ${cvals} "${pname}" ${caccess})`;
                fvals = `(@fj ${caccess} ${fvals})`;
            }
        }

        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_record@cons ${this.generateDataKindLoad(this.typegen.getMIRType(op.resultRecordType), fvals)} ${cvals})`));
    }

    generateVFieldLookup(arg: MIRArgument, tag: string, infertype: MIRType, fdecl: MIRFieldDecl): SMTExp {
        const lname = `resolve_${fdecl.fkey}_from_${infertype.trkey}`;
        let decl = this.vfieldLookups.find((lookup) => lookup.lname === lname);
        if(decl === undefined) {
            this.vfieldLookups.push({ infertype: infertype, fdecl: fdecl, lname: lname });
        }

        return new SMTValue(`(${this.typegen.mangleStringForSMT(lname)} ${tag} ${this.argToSMT(arg, infertype).emit()})`);
    }

    generateMIRAccessFromFieldExpression(arg: MIRArgument, inferargtype: MIRType, field: MIRFieldKey, resultAccessType: MIRType): SMTExp {
        const ftype = this.typegen.getMIRType((this.assembly.fieldDecls.get(field) as MIRFieldDecl).declaredType);
        
        if (this.typegen.typecheckUEntity(inferargtype)) {
            const access = new SMTValue(`(${this.typegen.generateEntityAccessor(this.typegen.getEntityEKey(inferargtype), field)} ${this.argToSMT(arg, inferargtype).emit()})`);
            return this.typegen.coerce(access, ftype, resultAccessType);
        }
        else {
            let tag = "";
            if(this.typegen.typecheckAllKeys(inferargtype)) {
                tag = `(bsqkey_get_nominal_type ${this.argToSMT(arg, inferargtype)})`;
            }
            else {
                tag = `(bsqterm_get_nominal_type ${this.argToSMT(arg, inferargtype)})`;
            }

            
            const access = this.generateVFieldLookup(arg, tag, inferargtype, this.assembly.fieldDecls.get(field) as MIRFieldDecl);
            return this.typegen.coerce(access, ftype, resultAccessType);
        }
    }

    generateVFieldProject(arg: MIRArgument, infertype: MIRType, fprojs: MIRFieldDecl[], resultAccessType: MIRType): string {
        const upnames = fprojs.map((fp) => fp.fkey);
        const uname = `project_${upnames.sort().join("*")}_in_${infertype.trkey}`;
        let decl = this.vfieldProjects.find((lookup) => lookup.uname === uname);
        if(decl === undefined) {
            this.vfieldProjects.push({ infertype: infertype, fprojs: fprojs, resultAccessType: resultAccessType, uname: uname });
        }

        return `${this.typegen.mangleStringForSMT(uname)}(${this.argToSMT(arg, infertype)})`;
    }

    generateMIRProjectFromFields(op: MIRProjectFromFields, resultAccessType: MIRType): SMTExp {
        const inferargtype = this.typegen.getMIRType(op.argInferType);

        if (this.typegen.typecheckUEntity(inferargtype)) {
            if (this.typegen.typecheckEphemeral(resultAccessType)) {
                let cvals: string[] = [];
                op.fields.map((f, i) => {
                    const rtype = this.typegen.getEpehmeralType(resultAccessType).entries[i];
                    cvals.push(this.generateMIRAccessFromFieldExpression(op.arg, inferargtype, f, rtype).emit());
                });

                return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(${this.typegen.generateEntityConstructor(resultAccessType.trkey)} ${cvals.join(" ")})`));
            }
            else {
                let fvals = "StructuralSpecialTypeInfo@Clear";
                let cvals = "bsqrecord_array_empty";
                for (let i = 0; i < op.fields.length; ++i) {
                    const fdecl = this.assembly.fieldDecls.get(op.fields[i]) as MIRFieldDecl;
                    const access = this.generateMIRAccessFromFieldExpression(op.arg, inferargtype, op.fields[i], this.typegen.anyType);

                    cvals = `(store ${cvals} "${fdecl.name}" ${access})`;
                    fvals = `(@fj ${access} ${fvals})`;
                }

                return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_record@cons ${this.generateDataKindLoad(this.typegen.getMIRType(op.resultProjectType), fvals)} ${cvals})`));
            }
        }
        else {
            const vproject = this.generateVFieldProject(op.arg, inferargtype, op.fields.map((f) => this.assembly.fieldDecls.get(f) as MIRFieldDecl), resultAccessType);
            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(vproject));
        }
    }

    generateVFieldUpdate(arg: MIRArgument, infertype: MIRType, fupds: [MIRFieldDecl, MIRArgument][], resultAccessType: MIRType): string {
        const upnames = fupds.map((fud) => `${fud[0].fkey}->${this.getArgType(fud[1])}`);
        const uname = `update_${upnames.sort().join("*")}_in_${infertype.trkey}`;
        let decl = this.vfieldUpdates.find((lookup) => lookup.uname === uname);
        if(decl === undefined) {
            this.vfieldUpdates.push({ infertype: infertype, fupds: fupds, resultAccessType: resultAccessType, uname: uname });
        }

        return `${this.typegen.mangleStringForSMT(uname)}(${this.argToSMT(arg, infertype)}, ${fupds.map((upd) => this.argToSMT(upd[1], this.getArgType(upd[1]))).join(", ")})`;
    }

    generateMIRModifyWithFields(op: MIRModifyWithFields, resultAccessType: MIRType): SMTExp {
        const inferargtype = this.typegen.getMIRType(op.argInferType);
        
        if (this.typegen.typecheckUEntity(inferargtype)) {
            const ekey = this.typegen.getEntityEKey(inferargtype);
            const utype = this.typegen.assembly.entityDecls.get(ekey) as MIREntityTypeDecl;
            let cvals: string[] = [];
            for (let i = 0; i < utype.fields.length; ++i) {
                const fdecl = utype.fields[i];
                const ftype = this.typegen.getMIRType(fdecl.declaredType);

                const upd = op.updates.find((update) => update[0] == fdecl.fkey);
                if(upd !== undefined) {
                    cvals.push(this.argToSMT(upd[1], ftype).emit());
                }
                else {
                    cvals.push(`(${this.typegen.generateEntityAccessor(ekey, fdecl.fkey)} ${this.argToSMT(op.arg, inferargtype).emit()})`);
                }
            }

            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(${this.typegen.generateEntityConstructor(ekey)} ${cvals.join(" ")})`));
        }
        else {
            const access = this.generateVFieldUpdate(op.arg, inferargtype, op.updates.map((upd) => [this.assembly.fieldDecls.get(upd[0]) as MIRFieldDecl, upd[1]]), resultAccessType);
            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(access));
        }
    }

    generateVFieldExtend(arg: MIRArgument, infertype: MIRType, merge: MIRArgument, infermerge: MIRType, fieldResolves: [string, MIRFieldDecl][], resultAccessType: MIRType): string {
        const upnames = fieldResolves.map((fr) => `${fr[0]}->${fr[1].fkey}`);
        const mname = `merge_${infertype.trkey}_${upnames.join("*")}_with_${infermerge.trkey}`;
        let decl = this.vobjmerges.find((lookup) => lookup.mname === mname);
        if(decl === undefined) {
            this.vobjmerges.push({ infertype: infertype, merge: merge, infermergetype: infermerge, fieldResolves: fieldResolves, resultAccessType: resultAccessType, mname: mname });
        }

        return `${this.typegen.mangleStringForSMT(mname)}(${this.argToSMT(arg, infertype)}, ${this.argToSMT(merge, infermerge)})`;
    }

    generateMIRStructuredExtendObject(op: MIRStructuredExtendObject, resultAccessType: MIRType): SMTExp {
        const inferargtype = this.typegen.getMIRType(op.argInferType);
        const mergeargtype = this.typegen.getMIRType(op.updateInferType);
        
        if (this.typegen.typecheckUEntity(inferargtype)) {
            const ekey = this.typegen.getEntityEKey(inferargtype);
            const utype = this.typegen.assembly.entityDecls.get(ekey) as MIREntityTypeDecl;
            let cvals: string[] = [];
            for (let i = 0; i < utype.fields.length; ++i) {
                const fdecl = utype.fields[i];
                const ftype = this.typegen.getMIRType(fdecl.declaredType);

                const fp = op.fieldResolves.find((tfp) => tfp[1] === fdecl.fkey);
                const faccess = `(${this.typegen.generateEntityAccessor(ekey, fdecl.fkey)} ${this.argToSMT(op.arg, inferargtype).emit()})`;
                if(fp === undefined) {
                    cvals.push(faccess);
                }
                else {
                    const hasp = this.typegen.recordHasField(mergeargtype, fp[0]);
                    if(hasp === "no") {
                        cvals.push(faccess);
                    }
                    else if (hasp === "yes") {
                        cvals.push(this.generateMIRAccessFromPropertyExpression(op.arg, fp[0], ftype).emit());
                    }
                    else {
                        let mvals = this.typegen.typecheckRecord(this.getArgType(op.update)) ? `(bsq_record_entries ${this.varToSMTName(op.update)})` : `(bsq_record_entries (bsqterm_record_value ${this.varToSMTName(op.update)}))`;
                        const check = new SMTValue(`(= (select ${mvals} "${fp[0]}") bsqterm@clear)`);

                        cvals.push(new SMTCond(check, new SMTValue(faccess), new SMTValue(`(select ${mvals} "${fp[0]}")`)).emit());
                    }
                }
            }

            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(${this.typegen.generateEntityConstructor(ekey)} ${cvals.join(" ")})`));
        }
        else {
            const access = this.generateVFieldExtend(op.arg, inferargtype, op.update, mergeargtype, op.fieldResolves.map((fr) => [fr[0], this.assembly.fieldDecls.get(fr[1]) as MIRFieldDecl]), resultAccessType);
            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(access));
        }
    }

    generateMIRLoadFromEpehmeralList(op: MIRLoadFromEpehmeralList): SMTExp {
        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(${this.typegen.generateEntityAccessor(op.argInferType, `entry_${op.idx}`)} ${this.varToSMTName(op.arg)})`));
    }

    generateMIRInvokeFixedFunction(ivop: MIRInvokeFixedFunction, gas: number | undefined): SMTExp {
        let vals: string[] = [];
        const idecl = (this.assembly.invokeDecls.get(ivop.mkey) || this.assembly.primitiveInvokeDecls.get(ivop.mkey)) as MIRInvokeDecl;

        for (let i = 0; i < ivop.args.length; ++i) {
            vals.push(this.argToSMT(ivop.args[i], this.assembly.typeMap.get(idecl.params[i].type) as MIRType).emit());
        }

        if(idecl.enclosingDecl === "NSCore::Regex" && ivop.args[0] instanceof MIRConstantRegex && (idecl.name === "s_accepts" || idecl.name === "s_match")) {
            return new SMTValue("[NOT IMPLEMENTED -- regex ops]");
        }
        else if (this.isSafeInvoke(idecl)) {
            assert(this.currentSCC === undefined || !this.currentSCC.has(ivop.mkey));
            const invokeexp = new SMTValue(vals.length !== 0 ? `(${this.invokenameToSMT(ivop.mkey)} ${vals.join(" ")})` : this.invokenameToSMT(ivop.mkey));
            return new SMTLet(this.varToSMTName(ivop.trgt), invokeexp);  
        }
        else {
            const tv = this.generateTempName();
            const ivrtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType((idecl as MIRInvokeDecl).resultType));
            const resulttype = this.typegen.getSMTTypeFor(this.currentRType);

            const checkerror = new SMTValue(`(is-result_error@${ivrtype} ${tv})`);
            const extracterror = (ivrtype !== resulttype) ? new SMTValue(`(result_error@${resulttype} (result_error_code@${ivrtype} ${tv}))`) : new SMTValue(tv);
            const normalassign = new SMTLet(this.varToSMTName(ivop.trgt), new SMTValue(`(result_success_value@${ivrtype} ${tv})`));

            if (this.currentSCC === undefined || !this.currentSCC.has(ivop.mkey)) {
                const invokeexp = new SMTValue(vals.length !== 0 ? `(${this.invokenameToSMT(ivop.mkey)} ${vals.join(" ")})` : this.invokenameToSMT(ivop.mkey));
                return new SMTLet(tv, invokeexp, new SMTCond(checkerror, extracterror, normalassign));
            }
            else {
                if (gas === 0) {
                    const invokeexp = this.generateBMCLimitCreate(ivop.mkey, ivrtype);
                    return new SMTLet(tv, invokeexp, new SMTCond(checkerror, extracterror, normalassign));
                }
                else {
                    const invokeexp = new SMTValue(vals.length !== 0 ? `(${this.invokenameToSMT(ivop.mkey)}@gas${gas} ${vals.join(" ")})` : this.invokenameToSMT(ivop.mkey));
                    return new SMTLet(tv, invokeexp, new SMTCond(checkerror, extracterror, normalassign));
                }
            }
        }
    }

    generateEquals(op: string, lhsinfertype: MIRType, lhs: MIRArgument, rhsinfertype: MIRType, rhs: MIRArgument, isstrict: boolean): string {
        let coreop = "";
        if (isstrict) {
            coreop = `(= ${this.argToSMT(lhs, lhsinfertype).emit()} ${this.argToSMT(rhs, rhsinfertype).emit()})`;
        }
        else {
            coreop = `(= ${this.argToSMT(lhs, this.typegen.keyType).emit()} ${this.argToSMT(rhs, this.typegen.keyType).emit()})`;
        }

        return op === "!=" ? `(not ${coreop})` : coreop;
    }

    generateLess(lhsinfertype: MIRType, lhs: MIRArgument, rhsinfertype: MIRType, rhs: MIRArgument, isstrict: boolean): string {
        if (isstrict) {
            const tt = lhsinfertype;
            const argl = this.argToSMT(lhs, lhsinfertype).emit();
            const argr = this.argToSMT(rhs, rhsinfertype).emit();

            if (this.typegen.typecheckIsName(tt, /^NSCore::Bool$/)) {
                return "false";
            }
            else if (this.typegen.typecheckIsName(tt, /^NSCore::Bool$/)) {
                return `(and (not ${argl}) ${argr})`;
            }
            else if (this.typegen.typecheckIsName(tt, /^NSCore::Int$/)) {
                return `(< ${argl} ${argr})`;
            }
            else if (this.typegen.typecheckIsName(tt, /^NSCore::BigInt$/)) {
                return `(< ${argl} ${argr})`;
            }
            else if (this.typegen.typecheckIsName(tt, /^NSCore::String$/)) {
                return `(str.< ${argl}${argr})`;
            }
            else if (this.typegen.typecheckIsName(tt, /^NSCore::SafeString<.*>$/)) {
                return `(str.< (bsq_safestring_value ${argl}) (bsq_safestring_value ${argr}))`;
            }
            else if (this.typegen.typecheckIsName(tt, /^NSCore::StringOf<.*>$/)) {
                return `(str.< (bsq_stringof_value ${argl}) (bsq_stringof_value ${argr}))`;
            }
            else if (this.typegen.typecheckIsName(tt, /^NSCore::UUID$/)) {
                return ` (str.< (bsq_uuid_value ${argl}) (bsq_uuid_value ${argr}))`;
            }
            else if (this.typegen.typecheckIsName(tt, /^NSCore::LogicalTime$/)) {
                return `(< (bsq_logicaltime_value ${argl}) (bsq_logicaltime_value ${argr}))`;
            }
            else if (this.typegen.typecheckIsName(tt, /^NSCore::CryptoHash$/)) {
                return `(str.< (bsq_cryptohash ${argl}) (bsq_cryptohash ${argr}))`;
            }
            else if (this.typegen.typecheckEntityAndProvidesName(tt, this.typegen.enumtype)) {
                return `(< (bsq_enum_value ${argl}) (bsq_enum_value ${argr}))`;
            }
            else {
                //TODO: this should turn into a gas driven generation
                return `(bsqkeyless_identity$${this.typegen.mangleStringForSMT(tt.trkey)} (bsq_idkey_value ${argl}) (bsq_idkey_value ${argr}))`;
            }
        }
        else {
            //TODO: this should turn into a gas driven generation
            return `(bsqkeyless ${this.argToSMT(lhs, this.typegen.keyType).emit()} ${this.argToSMT(rhs, this.typegen.keyType).emit()})`;
        }
    }

    generateCompare(op: string, lhsinfertype: MIRType, lhs: MIRArgument, rhsinfertype: MIRType, rhs: MIRArgument): string {
        if (op === "<") {
            return this.generateLess(lhsinfertype, lhs, rhsinfertype, rhs, true);
        }
        else if (op === "<=") {
            return `(or ${this.generateLess(lhsinfertype, lhs, rhsinfertype, rhs, true)} ${this.generateEquals("=", lhsinfertype, lhs, rhsinfertype, rhs, true)})`;
        }
        else if (op === ">") {
            return this.generateLess(rhsinfertype, rhs, lhsinfertype, lhs, true);
        }
        else {
            return `(or ${this.generateLess(rhsinfertype, rhs, lhsinfertype, lhs, true)} ${this.generateEquals("=", rhsinfertype, rhs, lhsinfertype, lhs, true)})`;
        }
    }

    generateSubtypeTupleCheck(argv: string, argtype: MIRType, oftype: MIRTupleType): string {
        const subtypesig = `subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)}_TTC ((atuple (Array Int BTerm))) Bool`;

        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let checks: string[] = [];

            //do all the checks that argtype satisfies all the requirements of oftype -- maybe a bit inefficiently
            for (let i = 0; i < oftype.entries.length; ++i) {
                const chk = this.generateTypeCheck(`(select atuple ${i})`, this.typegen.anyType, this.typegen.anyType, oftype.entries[i].type);

                if(oftype.entries[i].isOptional) {
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
                if(checks.length === 0) {
                    op = "true";
                }
                else if(checks.length === 1) {
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

        return `(subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)}_TTC ${argv})`;
    }

    generateTupleSpecialConceptCheck(argv: string, argtype: MIRType, oftype: MIRConceptType): string {
        const argrepr = this.typegen.getSMTTypeFor(argtype);
        const subtypesig = `subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)}_TSC ((arg ${argrepr})) Bool`;

        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let ttuple = "";
            if (this.typegen.typecheckTuple(argtype)) {
                ttuple = `(let ((tsi (bsq_tuple_concepts arg)))`;
            }
            else {
                ttuple = `(let ((tsi (bsq_tuple_concepts (bsqterm_tuple_value arg))))`;
            }

            const checks: string[] = [];
            if (oftype.ckeys.some((cc) => this.typegen.assembly.subtypeOf(this.typegen.parsableType, this.typegen.getMIRType(cc)))) {
                checks.push(`(StructuralSpecialTypeInfo$Parsable tsi)`);
            }

            if (oftype.ckeys.some((cc) => this.typegen.assembly.subtypeOf(this.typegen.podType, this.typegen.getMIRType(cc)))) {
                checks.push(`(StructuralSpecialTypeInfo$PODType tsi)`);
            }

            if (oftype.ckeys.some((cc) => this.typegen.assembly.subtypeOf(this.typegen.apiType, this.typegen.getMIRType(cc)))) {
                checks.push(`(StructuralSpecialTypeInfo$APIType tsi)`);
            }

            const decl = "(define-fun " + subtypesig
            + "\n  " + ttuple
            + "\n    " + (checks.length === 1) ? checks[0] : (`(and ${checks.join(" ")})`)
            + "))\n";

            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }

        return `(subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)}_TSC ${argv})`;
    }

    generateSubtypeRecordCheck(argv: string, argtype: MIRType, oftype: MIRRecordType): string {
        const subtypesig = `subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)}_TRC ((arecord (Array String BTerm))) Bool`;

        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let checks: string[] = [];

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
                    if(oftype.entries.find((entry) => entry.name === pname) === undefined) {
                        checks.push(`(= (select arecord "${pname}") bsqterm@clear)`);
                    }
                }
            }
            else {
                let nv = "bsqrecord_array_empty";
                for(let i = 0; i < oftype.entries.length; ++i) {
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
                if(checks.length === 0) {
                    op = "true";
                }
                else if(checks.length === 1) {
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

        return `(subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)}_TRC ${argv})`;
    }

    generateRecordSpecialConceptCheck(argv: string, argtype: MIRType, oftype: MIRConceptType): string {
        const argrepr = this.typegen.getSMTTypeFor(argtype);
        const subtypesig = `subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)}_RSC ((arg ${argrepr})) Bool`;

        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let ttuple = "";
            if (this.typegen.typecheckTuple(argtype)) {
                ttuple = `(let ((tsi (bsq_record_concepts arg)))`;
            }
            else {
                ttuple = `(let ((tsi (bsq_record_concepts (bsqterm_record_value arg))))`;
            }

            const checks: string[] = [];
            if (oftype.ckeys.some((cc) => this.typegen.assembly.subtypeOf(this.typegen.parsableType, this.typegen.getMIRType(cc)))) {
                checks.push(`(StructuralSpecialTypeInfo$Parsable tsi)`);
            }

            if (oftype.ckeys.some((cc) => this.typegen.assembly.subtypeOf(this.typegen.podType, this.typegen.getMIRType(cc)))) {
                checks.push(`(StructuralSpecialTypeInfo$PODType tsi)`);
            }

            if (oftype.ckeys.some((cc) => this.typegen.assembly.subtypeOf(this.typegen.apiType, this.typegen.getMIRType(cc)))) {
                checks.push(`(StructuralSpecialTypeInfo$APIType tsi)`);
            }

            const decl = "(define-fun " + subtypesig
            + "\n  " + ttuple
            + "\n    " + (checks.length === 1) ? checks[0] : (`(and ${checks.join(" ")})`)
            + "))\n";

            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }

        return `(subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)}_RSC ${argv})`;
    }

    generateFastTupleTypeCheck(arg: string, argtype: MIRType, inferargtype: MIRType, oftype: MIRTupleType): string {
        if (!inferargtype.options.some((opt) => opt instanceof MIRTupleType)) {
            return "false";
        }
        else {
            if (this.typegen.typecheckTuple(argtype)) {
                return this.generateSubtypeTupleCheck(`(bsq_tuple_entries ${arg})`, argtype, oftype);
            }
            else {
                const tsc = this.generateSubtypeTupleCheck(`(bsq_tuple_entries (bsqterm_tuple_value ${arg}))`, argtype, oftype);
                return `(and (is-bsqterm_tuple ${arg}) ${tsc})`
            }
        }
    }

    generateFastRecordTypeCheck(arg: string, argtype: MIRType, inferargtype: MIRType, oftype: MIRRecordType): string {
        if (!inferargtype.options.some((opt) => opt instanceof MIRRecordType)) {
            return "false";
        }
        else {
            if (this.typegen.typecheckRecord(argtype)) {
                return this.generateSubtypeRecordCheck(`(bsq_record_entries ${arg})`, argtype, oftype);
            }
            else {
                const tsc = this.generateSubtypeRecordCheck(`(bsq_record_entries (bsqterm_record_value ${arg}))`, argtype, oftype);
                return `(and (is-bsqterm_record ${arg}) ${tsc})`
            }
        }
    }

    generateSubtypeArrayLookup(access: string, oftype: MIRConceptType): string {
        this.checkedConcepts.add(oftype.trkey);
        return `(select MIRConceptSubtypeArray$${this.typegen.mangleStringForSMT(oftype.trkey)} ${access})`;
    }

    generateFastConceptTypeCheck(arg: string, argtype: MIRType, inferargtype: MIRType, oftype: MIRConceptType): string {
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
                if (this.typegen.typecheckAllKeys(argtype)) {
                    enumacc = `(bsqkey_get_nominal_type ${arg})`;
                }
                else {
                    enumacc = `(bsqterm_get_nominal_type ${arg})`;
                }
            }

            let ttest = "false";
            if (inferargtype.options.some((iopt) => iopt instanceof MIRTupleType)) {
                const tupmax = MIRType.createSingle(MIRConceptType.create([this.typegen.tupleType.trkey, this.typegen.podType.trkey, this.typegen.parsableType.trkey]));
                const maybespecial = this.typegen.assembly.subtypeOf(tupmax, this.typegen.getMIRType(oftype.trkey)); //if this isn't true then special subtype will never be true
                const trival = this.typegen.assembly.subtypeOf(this.typegen.tupleType, this.typegen.getMIRType(oftype.trkey)); //if this is true then the default subtypeArray is enough
                if (maybespecial && !trival) {
                    ttest = `(and (= enumacc MIRNominalTypeEnum_Tuple) ${this.generateTupleSpecialConceptCheck(arg, argtype, oftype)})`;
                }
            }

            let rtest = "false";
            if (inferargtype.options.some((iopt) => iopt instanceof MIRRecordType)) {
                const recmax = MIRType.createSingle(MIRConceptType.create([this.typegen.recordType.trkey, this.typegen.podType.trkey, this.typegen.parsableType.trkey]));
                const maybespecial = this.typegen.assembly.subtypeOf(recmax, this.typegen.getMIRType(oftype.trkey)); //if this isn't true then special subtype will never be true
                const trival = this.typegen.assembly.subtypeOf(this.typegen.recordType, this.typegen.getMIRType(oftype.trkey)); //if this is true then the default subtypeArray is enough
                if (maybespecial && !trival) {
                    rtest = `(and (enumacc == MIRNominalTypeEnum_Record) ${this.generateRecordSpecialConceptCheck(arg, argtype, oftype)})`;
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
                return `(${tests.join(" || ")})`
            }
        }
    }

    generateFastEntityTypeCheck(arg: string, argtype: MIRType, inferargtype: MIRType, oftype: MIREntityType): string {
        if (this.typegen.typecheckIsName(inferargtype, /^NSCore::None$/) || this.typegen.typecheckUEntity(inferargtype)) {
            return inferargtype.trkey == oftype.trkey ? "true" : "false";
        }
        else {
            if(this.typegen.typecheckAllKeys(argtype)) {
                return `(= (bsqkey_get_nominal_type ${arg}) MIRNominalTypeEnum_${this.typegen.mangleStringForSMT(oftype.ekey)})`;
            }
            else if (this.typegen.typecheckTuple(argtype) || this.typegen.typecheckRecord(argtype)) {
                return "false";
            }
            else {
                return `(= (bsqterm_get_nominal_type ${arg}) MIRNominalTypeEnum_${this.typegen.mangleStringForSMT(oftype.ekey)})`;
            }
        }
    }

    generateEphemeralTypeCheck(argv: string, argtype: MIRType, oftype: MIREphemeralListType): string {
        const argrepr = this.typegen.getSMTTypeFor(argtype);
        const subtypesig = `bool subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)}_EL(${argrepr} arg)`;

        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let checks: string[] = [];

            //do all the checks that argtype satisfies all the requirements of oftype 
            for (let i = 0; i < oftype.entries.length; ++i) {
                const etype = (argtype.options[0] as MIREphemeralListType).entries[i];
                checks.push(this.generateTypeCheck(this.typegen.generateEntityAccessor(argtype.trkey, `entry_${i}`), etype, etype, oftype.entries[i]));
            }

            let op = "";
            if (checks.includes("false")) {
                op = "false";
            }
            else {
                checks = checks.filter((chk) => chk !== "true");
                if(checks.length === 0) {
                    op = "true";
                }
                else if(checks.length === 1) {
                    op = checks[0];
                }
                else {
                    op = `(and ${checks.join(" ")})`;
                }
            }

            const decl = "(define-fun " + subtypesig
            + "\n    " + op
            + "))\n";

            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }

        return `(subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)}_EL ${argv})`;
    }

    generateTypeCheck(arg: string, argtype: MIRType, inferargtype: MIRType, oftype: MIRType): string {
        if(this.typegen.assembly.subtypeOf(inferargtype, oftype)) {
            //this case also include oftype == Any
            return "true";
        }

        if (oftype.trkey === "NSCore::Some") {
            if (!this.typegen.assembly.subtypeOf(this.typegen.noneType, inferargtype)) {
                return "true";
            }
            else {
                if (oftype.trkey === "NSCore::Some") {
                    if (this.typegen.typecheckAllKeys(argtype)) {
                        return `(not (= ${arg} bsqkey_none))`;
                    }
                    else {
                        return `(not (= ${arg} bsqterm_none))`;
                    }
                }
            }
        }

        const tests = oftype.options.map((topt) => {
            const mtype = this.typegen.getMIRType(topt.trkey);
            assert(mtype !== undefined, "We should generate all the component types by default??");

            if(topt instanceof MIREntityType) {
                return this.generateFastEntityTypeCheck(arg, argtype, inferargtype, topt);
            }
            else if (topt instanceof MIRConceptType) {
                return this.generateFastConceptTypeCheck(arg, argtype, inferargtype, topt);
            }
            else if (topt instanceof MIRTupleType) {
                return this.generateFastTupleTypeCheck(arg, argtype, inferargtype, topt);
            }
            else if (topt instanceof MIRRecordType) {
                return this.generateFastRecordTypeCheck(arg, argtype, inferargtype, topt);
            }
            else {
                assert(topt instanceof MIREphemeralListType);

                return this.generateEphemeralTypeCheck(arg, argtype, topt as MIREphemeralListType);
            }
        })
        .filter((test) => test !== "false");

        if(tests.length === 0) {
            return "false";
        }
        else if(tests.includes("true")) {
            return "true";
        }
        else if(tests.length === 1) {
            return tests[0];
        }
        else {
            return `(or ${tests.join(" ")})`
        }
    }

    generateMIRPackSlice(op: MIRPackSlice): SMTExp {
        const etype = this.typegen.getMIRType(op.sltype).options[0] as MIREphemeralListType;

        let args: string[] = [];
        for(let i = 0; i < etype.entries.length; ++i) {
            args.push(`(${this.typegen.generateEntityAccessor(etype.trkey, `entry_${i}`)} ${this.varToSMTName(op.src)})`);
        }

        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(${this.typegen.generateEntityConstructor(etype.trkey)} ${args.join(" ")})`));
    }

    generateMIRPackSliceExtend(op: MIRPackExtend): SMTExp {
        const fromtype = this.getArgType(op.basepack).options[0] as MIREphemeralListType;
        const etype = this.typegen.getMIRType(op.sltype).options[0] as MIREphemeralListType;

        let args: string[] = [];
        for(let i = 0; i < fromtype.entries.length; ++i) {
            args.push(`(${this.typegen.generateEntityAccessor(fromtype.trkey, `entry_${i}`)} ${this.varToSMTName(op.basepack)})`);
        }

        for(let i = 0; i < op.ext.length; ++i) {
            args.push(this.argToSMT(op.ext[i], etype.entries[fromtype.entries.length + i]).emit());
        }

        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(${this.typegen.generateEntityConstructor(etype.trkey)} ${args.join(" ")})`));
    }

    generateStmt(op: MIROp, fromblck: string, gas: number | undefined): SMTExp | undefined {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = op as MIRLoadConst;
                return new SMTLet(this.varToSMTName(lcv.trgt), this.generateConstantExp(lcv.src, this.getArgType(lcv.trgt)));
            }
            case MIROpTag.MIRLoadConstSafeString: {
                return this.generateLoadConstSafeString(op as MIRLoadConstSafeString);
            }
            case MIROpTag.MIRLoadConstTypedString:  {
                return this.generateLoadConstTypedString(op as MIRLoadConstTypedString);
            }
            case MIROpTag.MIRAccessConstantValue: {
                const acv = (op as MIRAccessConstantValue);
                return this.generateAccessConstantValue(acv);
            }
            case MIROpTag.MIRLoadFieldDefaultValue: {
                const ldv = (op as MIRLoadFieldDefaultValue);
                return this.generateLoadFieldDefaultValue(ldv);
            }
            case MIROpTag.MIRAccessArgVariable: {
                const lav = op as MIRAccessArgVariable;
                return new SMTLet(this.varToSMTName(lav.trgt), this.argToSMT(lav.name, this.getArgType(lav.trgt)));
            }
            case MIROpTag.MIRAccessLocalVariable: {
                const llv = op as MIRAccessLocalVariable;
                return new SMTLet(this.varToSMTName(llv.trgt), this.argToSMT(llv.name, this.getArgType(llv.trgt)));
            }
            case MIROpTag.MIRInvokeInvariantCheckDirect: {
                const icd = op as MIRInvokeInvariantCheckDirect;
                return this.generateMIRInvokeInvariantCheckDirect(icd);
            }
            case MIROpTag.MIRInvokeInvariantCheckVirtualTarget: {
                return NOT_IMPLEMENTED<SMTExp>("MIRInvokeInvariantCheckVirtualTarget");
            }
            case MIROpTag.MIRConstructorPrimary: {
                const cp = op as MIRConstructorPrimary;
                return this.generateMIRConstructorPrimary(cp);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
                const cpce = op as MIRConstructorPrimaryCollectionEmpty;
                return this.generateMIRConstructorPrimaryCollectionEmpty(cpce);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                const cpcs = op as MIRConstructorPrimaryCollectionSingletons;
                return this.generateMIRConstructorPrimaryCollectionSingletons(cpcs);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
                return NOT_IMPLEMENTED<SMTExp>("MIRConstructorPrimaryCollectionCopies");
            }
            case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                return NOT_IMPLEMENTED<SMTExp>("MIRConstructorPrimaryCollectionMixed");
            }
            case MIROpTag.MIRConstructorTuple: {
                const tc = op as MIRConstructorTuple;
                return this.generateMIRConstructorTuple(tc);
            }
            case MIROpTag.MIRConstructorRecord: {
                const tr = op as MIRConstructorRecord;
                return this.generateMIRConstructorRecord(tr);
            }
            case MIROpTag.MIRConstructorEphemeralValueList: {
                const te = op as MIRConstructorEphemeralValueList;
                return this.generateMIRConstructorEphemeralValueList(te);
            }
            case MIROpTag.MIRAccessFromIndex: {
                const ai = op as MIRAccessFromIndex;
                return new SMTLet(this.varToSMTName(ai.trgt), this.generateMIRAccessFromIndexExpression(ai.arg, ai.idx, this.typegen.getMIRType(ai.resultAccessType)));
            }
            case MIROpTag.MIRProjectFromIndecies: {
                const pi = op as MIRProjectFromIndecies;
                return this.generateMIRProjectFromIndecies(pi, this.typegen.getMIRType(pi.resultProjectType));
            }
            case MIROpTag.MIRAccessFromProperty: {
                const ap = op as MIRAccessFromProperty;
                return new SMTLet(this.varToSMTName(ap.trgt), this.generateMIRAccessFromPropertyExpression(ap.arg, ap.property, this.typegen.getMIRType(ap.resultAccessType)));
            }
            case MIROpTag.MIRProjectFromProperties: {
                const pp = op as MIRProjectFromProperties;
                return this.generateMIRProjectFromProperties(pp, this.typegen.getMIRType(pp.resultProjectType));
            }
            case MIROpTag.MIRAccessFromField: {
                const af = op as MIRAccessFromField;
                return new SMTLet(this.varToSMTName(af.trgt), this.generateMIRAccessFromFieldExpression(af.arg, this.typegen.getMIRType(af.argInferType), af.field, this.typegen.getMIRType(af.resultAccessType)));
            }
            case MIROpTag.MIRProjectFromFields: {
                const pf = op as MIRProjectFromFields;
                return this.generateMIRProjectFromFields(pf, this.typegen.getMIRType(pf.resultProjectType));
            }
            case MIROpTag.MIRProjectFromTypeTuple: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromTypeTuple");
            }
            case MIROpTag.MIRProjectFromTypeRecord: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromTypeRecord");
            }
            case MIROpTag.MIRProjectFromTypeNominal: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromTypeNominal");
            }
            case MIROpTag.MIRModifyWithIndecies: {
                const mi = op as MIRModifyWithIndecies;
                return this.generateMIRModifyWithIndecies(mi, this.typegen.getMIRType(mi.resultTupleType));
            }
            case MIROpTag.MIRModifyWithProperties: {
                const mp = op as MIRModifyWithProperties;
                return this.generateMIRModifyWithProperties(mp, this.typegen.getMIRType(mp.resultRecordType));
            }
            case MIROpTag.MIRModifyWithFields: {
                const mf = op as MIRModifyWithFields;
                return this.generateMIRModifyWithFields(mf, this.typegen.getMIRType(mf.resultNominalType));
            }
            case MIROpTag.MIRStructuredExtendTuple: {
                const si = op as MIRStructuredExtendTuple;
                return this.generateMIRStructuredExtendTuple(si, this.typegen.getMIRType(si.resultTupleType));
            }
            case MIROpTag.MIRStructuredExtendRecord: {
                const sp = op as MIRStructuredExtendRecord;
                return this.generateMIRStructuredExtendRecord(sp, this.typegen.getMIRType(sp.resultRecordType));
            }
            case MIROpTag.MIRStructuredExtendObject: {
                const so = op as MIRStructuredExtendObject;
                return this.generateMIRStructuredExtendObject(so, this.typegen.getMIRType(so.resultNominalType));
            }
            case MIROpTag.MIRLoadFromEpehmeralList: {
                const le = op as MIRLoadFromEpehmeralList;
                return this.generateMIRLoadFromEpehmeralList(le);
            }
            case MIROpTag.MIRInvokeFixedFunction: {
                const invk = op as MIRInvokeFixedFunction;
                return this.generateMIRInvokeFixedFunction(invk, gas);
            }
            case MIROpTag.MIRInvokeVirtualTarget: {
                return NOT_IMPLEMENTED<SMTExp>("MIRInvokeVirtualTarget");
            }
            case MIROpTag.MIRPrefixOp: {
                const pfx = op as MIRPrefixOp;
                if (pfx.op === "!") {
                    return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`(not ${this.argToSMT(pfx.arg, this.typegen.boolType).emit()})`));
                }
                else {
                    if (pfx.op === "-") {
                        if (pfx.arg instanceof MIRConstantInt) {
                            return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`-${(pfx.arg as MIRConstantInt).value}`));
                        }
                        else if (pfx.arg instanceof MIRConstantBigInt) {
                            return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`-${(pfx.arg as MIRConstantBigInt).digits()}`));
                        }
                        else if (pfx.arg instanceof MIRConstantFloat64) {
                            return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`-${(pfx.arg as MIRConstantFloat64).digits()}`));
                        }
                        else {
                            const opt = this.getArgType(pfx.trgt);
                            if (this.typegen.typecheckIsName(opt, /^NSCore::Int$/)) {
                                return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`(* -1 ${this.argToSMT(pfx.arg, this.typegen.intType).emit()})`));
                            }
                            else if (this.typegen.typecheckIsName(opt, /^NSCore::BigInt$/)) {
                                return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`(* -1 ${this.argToSMT(pfx.arg, this.typegen.bigIntType).emit()})`));
                            }
                            else {
                                return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`(* -1.0 ${this.argToSMT(pfx.arg, this.typegen.float64Type).emit()})`));
                            }
                        }
                    }
                    else {
                        return new SMTLet(this.varToSMTName(pfx.trgt), this.argToSMT(pfx.arg, this.getArgType(pfx.trgt)));
                    }
                }
            }
            case MIROpTag.MIRBinOp: {
                const bop = op as MIRBinOp;
                const opt = this.getArgType(bop.trgt);

                if (this.typegen.typecheckIsName(opt, /^NSCore::Int$/)) {
                    const chk = new SMTCond(new SMTValue(`(@int_unsafe ${this.varToSMTName(bop.trgt)})`), this.generateErrorCreate(bop.sinfo, this.typegen.getSMTTypeFor(this.currentRType)), SMTFreeVar.generate());
                    const opp = new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(`(${bop.op} ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`), chk);
                    if(bop.op !== "/") {
                        return opp;
                    }
                    else {
                        return new SMTCond(new SMTValue(`(= ${this.argToSMT(bop.rhs, this.typegen.intType).emit()} 0)`), this.generateErrorCreate(op.sinfo, this.typegen.getSMTTypeFor(this.currentRType)), opp);
                    }
                }
                else if (this.typegen.typecheckIsName(opt, /^NSCore::BigInt$/)) {
                    const opp = new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(`(${bop.op} ${this.argToSMT(bop.lhs, this.typegen.bigIntType).emit()} ${this.argToSMT(bop.rhs, this.typegen.bigIntType).emit()})`));
                    if(bop.op !== "/") {
                        return opp;
                    }
                    else {
                        return new SMTCond(new SMTValue(`(= ${this.argToSMT(bop.rhs, this.typegen.intType).emit()} 0)`), this.generateErrorCreate(op.sinfo, this.typegen.getSMTTypeFor(this.currentRType)), opp);
                    }
                }
                else {
                    return new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(`(${bop.op} ${this.argToSMT(bop.lhs, this.typegen.float64Type).emit()} ${this.argToSMT(bop.rhs, this.typegen.float64Type).emit()})`));
                }
            }
            case MIROpTag.MIRBinEq: {
                const beq = op as MIRBinEq;

                const lhvtypeinfer = this.typegen.getMIRType(beq.lhsInferType);
                const rhvtypeinfer = this.typegen.getMIRType(beq.rhsInferType);
                return new SMTLet(this.varToSMTName(beq.trgt), new SMTValue(this.generateEquals(beq.op, lhvtypeinfer, beq.lhs, rhvtypeinfer, beq.rhs, !beq.relaxed)));
            }
            case MIROpTag.MIRBinLess: {
                const blt = op as MIRBinLess;

                const lhvtypeinfer = this.typegen.getMIRType(blt.lhsInferType);
                const rhvtypeinfer = this.typegen.getMIRType(blt.rhsInferType);
                return new SMTLet(this.varToSMTName(blt.trgt), new SMTValue(this.generateLess(lhvtypeinfer, blt.lhs, rhvtypeinfer, blt.rhs, !blt.relaxed)));
            }
            case MIROpTag.MIRBinCmp: {
                const bcmp = op as MIRBinCmp;

                const lhvtypeinfer = this.typegen.getMIRType(bcmp.lhsInferType);
                const rhvtypeinfer = this.typegen.getMIRType(bcmp.rhsInferType);
                return new SMTLet(this.varToSMTName(bcmp.trgt), new SMTValue(this.generateCompare(bcmp.op, lhvtypeinfer, bcmp.lhs, rhvtypeinfer, bcmp.rhs)));
            }
            case MIROpTag.MIRIsTypeOfNone: {
                const ton = op as MIRIsTypeOfNone;
                return new SMTLet(this.varToSMTName(ton.trgt), this.generateNoneCheck(ton.arg));
            }
            case MIROpTag.MIRIsTypeOfSome: {
                const tos = op as MIRIsTypeOfSome;
                return new SMTLet(this.varToSMTName(tos.trgt), new SMTValue(`(not ${this.generateNoneCheck(tos.arg).emit()})`));
           }
            case MIROpTag.MIRIsTypeOf: {
                const top = op as MIRIsTypeOf;
                const oftype = this.typegen.getMIRType(top.oftype);
                const argtype = this.getArgType(top.arg);
                const infertype = this.typegen.getMIRType(top.argInferType);

                return new SMTLet(this.varToSMTName(top.trgt), new SMTValue(this.generateTypeCheck(this.argToSMT(top.arg, infertype).emit(), argtype, infertype, oftype)));
            }
            case MIROpTag.MIRRegAssign: {
                const regop = op as MIRRegAssign;
                return new SMTLet(this.varToSMTName(regop.trgt), this.argToSMT(regop.src, this.getArgType(regop.trgt)));
            }
            case MIROpTag.MIRTruthyConvert: {
                const tcop = op as MIRTruthyConvert;
                return new SMTLet(this.varToSMTName(tcop.trgt), this.generateTruthyConvert(tcop.src));
            }
            case MIROpTag.MIRVarStore: {
                const vsop = op as MIRVarStore;
                return new SMTLet(this.varToSMTName(vsop.name), this.argToSMT(vsop.src, this.getArgType(vsop.name)));
            }
            case MIROpTag.MIRPackSlice: {
                const vps = op as MIRPackSlice;
                return this.generateMIRPackSlice(vps);
            }
            case MIROpTag.MIRPackExtend: {
                const vpe = op as MIRPackExtend;
                return this.generateMIRPackSliceExtend(vpe);
            }
            case MIROpTag.MIRReturnAssign: {
                const raop = op as MIRReturnAssign;
                return new SMTLet(this.varToSMTName(raop.name), this.argToSMT(raop.src, this.getArgType(raop.name)));
            }
            case MIROpTag.MIRAbort: {
                const aop = (op as MIRAbort);
                return this.generateErrorCreate(aop.sinfo, this.typegen.getSMTTypeFor(this.currentRType));
            }
            case MIROpTag.MIRDebug: {
                return undefined;
            }
            case MIROpTag.MIRJump: {
                return undefined;
            }
            case MIROpTag.MIRJumpCond: {
                const cjop = op as MIRJumpCond;
                return new SMTCond(this.argToSMT(cjop.arg, this.typegen.boolType), SMTFreeVar.generate("#true_trgt#"), SMTFreeVar.generate("#false_trgt#"));
            }
            case MIROpTag.MIRJumpNone: {
                const njop = op as MIRJumpNone;
                return new SMTCond(this.generateNoneCheck(njop.arg), SMTFreeVar.generate("#true_trgt#"), SMTFreeVar.generate("#false_trgt#"));
            }
            case MIROpTag.MIRPhi: {
                const pop = op as MIRPhi;
                const uvar = pop.src.get(fromblck) as MIRRegisterArgument;

                return new SMTLet(this.varToSMTName(pop.trgt), this.argToSMT(uvar, this.getArgType(pop.trgt)));
            }
            case MIROpTag.MIRVarLifetimeStart:
            case MIROpTag.MIRVarLifetimeEnd: {
                return undefined;
            }
            default: {
                return NOT_IMPLEMENTED<SMTExp>(`Missing case ${op.tag}`);
            }
        }
    }

    generateBlockExps(issafe: boolean, block: MIRBasicBlock, fromblock: string, blocks: Map<string, MIRBasicBlock>, gas: number | undefined): SMTExp {
        const exps: SMTExp[] = [];
        for (let i = 0; i < block.ops.length; ++i) {
            const exp = this.generateStmt(block.ops[i], fromblock, gas);
            if (exp !== undefined) {
                exps.push(exp);
            }
        }

        if (block.label === "exit") {
            const resulttype = this.typegen.getSMTTypeFor(this.currentRType);
            let rexp = issafe ? new SMTValue("$$return") : new SMTValue(`(result_success@${resulttype} $$return)`) as SMTExp;
            for (let i = exps.length - 1; i >= 0; --i) {
                rexp = exps[i].bind(rexp, "#body#");
            }

            return rexp;
        }
        else {
            const jop = block.ops[block.ops.length - 1];
            if(jop.tag === MIROpTag.MIRAbort) {
                let rexp = exps[exps.length - 1];
                for (let i = exps.length - 2; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }

                return rexp;
            }
            else if (jop.tag === MIROpTag.MIRJump) {
                let rexp = this.generateBlockExps(issafe, blocks.get((jop as MIRJump).trgtblock) as MIRBasicBlock, block.label, blocks, gas);
                for (let i = exps.length - 1; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }

                return rexp;
            }
            else {
                assert(jop.tag === MIROpTag.MIRJumpCond || jop.tag === MIROpTag.MIRJumpNone);

                let tblock = ((jop.tag === MIROpTag.MIRJumpCond) ? blocks.get((jop as MIRJumpCond).trueblock) : blocks.get((jop as MIRJumpNone).noneblock)) as MIRBasicBlock;
                let texp = this.generateBlockExps(issafe, tblock, block.label, blocks, gas);

                let fblock = ((jop.tag === MIROpTag.MIRJumpCond) ? blocks.get((jop as MIRJumpCond).falseblock) : blocks.get((jop as MIRJumpNone).someblock)) as MIRBasicBlock;
                let fexp = this.generateBlockExps(issafe, fblock, block.label, blocks, gas);

                let rexp = exps[exps.length - 1].bind(texp, "#true_trgt#").bind(fexp, "#false_trgt#");
                for (let i = exps.length - 2; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }

                return rexp;
            }
        }
    }

    generateSMTInvoke(idecl: MIRInvokeDecl, cscc: Set<string>, gas: number | undefined, gasdown: number | undefined): string {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.getMIRType(idecl.resultType);
        this.currentSCC = cscc;

        let argvars = new Map<string, MIRType>();
        idecl.params.forEach((arg) => argvars.set(arg.name, this.assembly.typeMap.get(arg.type) as MIRType));

        const args = idecl.params.map((arg) => `(${this.varNameToSMTName(arg.name)} ${this.typegen.getSMTTypeFor(this.typegen.getMIRType(arg.type))})`);
        const restype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(idecl.resultType));

        const issafe = this.isSafeInvoke(idecl);

        const decl = issafe
            ? `(define-fun ${this.invokenameToSMT(idecl.key)} (${args.join(" ")}) ${restype}`
            : `(define-fun ${this.invokenameToSMT(idecl.key)}${gas !== undefined ? `@gas${gas}` : ""} (${args.join(" ")}) Result@${restype}`;

        if (idecl instanceof MIRInvokeBodyDecl) {
            this.vtypes = new Map<string, MIRType>();
            (idecl.body.vtypes as Map<string, string>).forEach((tkey, name) => {
                this.vtypes.set(name, this.typegen.getMIRType(tkey));
            });

            const blocks = (idecl as MIRInvokeBodyDecl).body.body;
            const body = this.generateBlockExps(issafe, blocks.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocks, gasdown);

            return `${decl} \n${body.emit("  ")})`;

        }
        else {
            assert(idecl instanceof MIRInvokePrimitiveDecl);

            const params = idecl.params.map((arg) => this.varNameToSMTName(arg.name));
            return `${decl} \n  ${this.generateBuiltinBody(issafe, idecl as MIRInvokePrimitiveDecl, params).emit("  ")}\n)`;
        }
    }

    generateBuiltinBody(issafe: boolean, idecl: MIRInvokePrimitiveDecl, params: string[]): SMTExp {
        const rtype = this.typegen.getMIRType(idecl.resultType);

        let bodyres: SMTExp | undefined = undefined;
        const enclkey = (idecl.enclosingDecl || "[NA]") as MIRNominalTypeKey
        switch (idecl.implkey) {
            case "validator_accepts": {
                const rs = this.assembly.literalRegexs.get(this.assembly.validatorRegexs.get(idecl.enclosingDecl as MIRNominalTypeKey) as string) as MIRRegex;
                bodyres = compileRegexSMTMatch(rs, params[0]);
                break;
            }
            case "enum_create": {
                bodyres = new SMTValue(`(bsq_enum@cons MIRNominalTypeEnum_${this.typegen.mangleStringForSMT(enclkey)} ${params[0]})`);
                break;
            }
            case "string_count": {
                bodyres = new SMTValue(`(str.len ${params[0]})`);
                break;
            }
            case "string_charat": {
                bodyres = new SMTValue(`(str.at ${params[0]} ${params[1]})`);
                break;
            }
            case "string_concat": {
                bodyres = new SMTValue(`(str.++ ${params[0]} ${params[1]})`);
                break;
            }
            case "string_substring": {
                bodyres = new SMTValue(`(str.substr ${params[0]} ${params[1]} ${params[2]})`);
                break;
            }
            case "safestring_string": {
                bodyres = new SMTValue(`(bsq_safestring_value ${params[0]})`);
                break;
            }
            case "safestring_unsafe_from": {
                bodyres = new SMTValue(`(bsq_safestring@cons MIRNominalTypeEnum_${this.typegen.mangleStringForSMT(enclkey)} ${params[0]})`);
                break;
            }
            case "stringof_string": {
                bodyres = new SMTValue(`(bsq_stringof_value ${params[0]})`);
                break;
            }
            case "stringof_unsafe_from": {
                bodyres = new SMTValue(`(bsq_stringof@cons MIRNominalTypeEnum_${this.typegen.mangleStringForSMT(enclkey)} ${params[0]})`);
                break;
            }
            case "list_size": {
                bodyres = this.typegen.generateSpecialTypeFieldAccessExp(enclkey, "size", params[0]);
                break;
            }
            case "list_unsafe_get": {
                bodyres = new SMTValue(`(select ${this.typegen.generateSpecialTypeFieldAccess(enclkey, "entries", params[0])} ${params[1]})`);
                break;
            }
            case "list_unsafe_push": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "entries", params[0]);
                const csize = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                bodyres = new SMTValue(`(${cons} (+ ${csize} 1) (store ${entries} ${csize} ${params[1]}))`);
                break;
            }
            case "list_unsafe_set": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "entries", params[0]);
                const csize = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                bodyres = new SMTValue(`(${cons} ${csize} (store ${entries} ${params[1]} ${params[2]}))`);
                break;
            }
            case "set_has_key": {
                bodyres = new SMTValue(`(select ${this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0])} ${params[1]})`)
                break;
            }
            /*
            case "list_size":
            case "set_size":
            case "map_size": {
                bodyres = this.typegen.generateSpecialTypeFieldAccessExp(enclkey, "size", params[0]);
                break;
            }
            case "list_unsafe_get": {
                bodyres = new SMTValue(`(select ${this.typegen.generateSpecialTypeFieldAccess(enclkey, "entries", params[0])} ${params[1]})`);
                break;
            }
            case "list_unsafe_add": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "entries", params[0]);
                const csize = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                bodyres = new SMTValue(`(${cons} (+ ${csize} 1) (store ${entries} ${csize} ${params[1]}))`);
                break;
            }
            case "list_unsafe_set": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "entries", params[0]);
                const csize = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                bodyres = new SMTValue(`(${cons} ${csize} (store ${entries} ${params[1]} ${params[2]}))`);
                break;
            }
            case "set_has_key":
            case "map_has_key": {
                bodyres = new SMTValue(`(select ${this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0])} ${params[1]})`)
                break;
            }
            case "map_at_key": {
                bodyres = new SMTValue(`(select ${this.typegen.generateSpecialTypeFieldAccess(enclkey, "keys", params[0])} ${params[1]})`)
                break;
            }
            case "set_at_val":
            case "map_at_val": {
                bodyres = new SMTValue(`(select ${this.typegen.generateSpecialTypeFieldAccess(enclkey, "values", params[0])} ${params[1]})`);
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
                const klctype = this.typegen.getKeyListTypeForSet(this.typegen.assembly.entityDecls.get(enclkey) as MIREntityTypeDecl);
                const kll = this.typegen.coerce(new SMTValue(params[2]), this.typegen.getMIRType(idecl.params[2].type), klctype);
                bodyres = new SMTValue(`(${cons} (- ${size} 1) (store ${has} ${params[1]} false) ${entries} ${kll.emit()})`);
                break;
            }
            case "map_clear_val": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const size = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                const has = this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0]);
                const keys = this.typegen.generateSpecialTypeFieldAccess(enclkey, "keys", params[0]);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "values", params[0]);
                const klctype = this.typegen.getKeyListTypeForMap(this.typegen.assembly.entityDecls.get(enclkey) as MIREntityTypeDecl);
                const kll = this.typegen.coerce(new SMTValue(params[2]), this.typegen.getMIRType(idecl.params[2].type), klctype);
                bodyres = new SMTValue(`(${cons} (- ${size} 1) (store ${has} ${params[1]} false) ${keys} ${entries} ${kll.emit()})`);
                break;
            }
            case "set_unsafe_update": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const size = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                const has = this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0]);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "values", params[0]);
                const kl = this.typegen.generateSpecialTypeFieldAccess(enclkey, "keylist", params[0]);
                bodyres = new SMTValue(`(${cons} ${size} ${has} (store ${entries} ${params[1]} ${params[2]}) ${kl})`);
                break;
            }
            case "map_unsafe_update": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const size = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                const has = this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0]);
                const keys = this.typegen.generateSpecialTypeFieldAccess(enclkey, "keys", params[0]);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "values", params[0]);
                const kl = this.typegen.generateSpecialTypeFieldAccess(enclkey, "keylist", params[0]);
                bodyres = new SMTValue(`(${cons} ${size} ${has} ${keys} (store ${entries} ${params[1]} ${params[3]}) ${kl})`);
                break;
            }
            case "set_unsafe_add":  {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const size = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                const has = this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0]);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "values", params[0]);
                const klctype = this.typegen.getKeyListTypeForSet(this.typegen.assembly.entityDecls.get(enclkey) as MIREntityTypeDecl);
                const kll = this.typegen.coerce(new SMTValue(params[3]), this.typegen.getMIRType(idecl.params[3].type), klctype);
                bodyres = new SMTValue(`(${cons} (+ ${size} 1) (store ${has} ${params[1]} true) (store ${entries} ${params[1]} ${params[2]}) ${kll.emit()})`);
                break;
            }
            case "map_unsafe_add": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const size = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                const has = this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0]);
                const keys = this.typegen.generateSpecialTypeFieldAccess(enclkey, "keys", params[0]);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "values", params[0]);
                const klctype = this.typegen.getKeyListTypeForMap(this.typegen.assembly.entityDecls.get(enclkey) as MIREntityTypeDecl);
                const kll = this.typegen.coerce(new SMTValue(params[4]), this.typegen.getMIRType(idecl.params[4].type), klctype);
                bodyres = new SMTValue(`(${cons} (+ ${size} 1) (store ${has} ${params[1]} true) (store ${keys} ${params[1]} ${params[2]}) (store ${entries} ${params[1]} ${params[3]}) ${kll.emit()})`);
                break;
            }
            */
            default: {
                bodyres = new SMTValue(`[Builtin not defined -- ${idecl.iname}]`);
                break;
            }
        }

        return issafe ? new SMTValue(bodyres.emit()) : new SMTValue(`(result_success@${this.typegen.getSMTTypeFor(rtype)} ${bodyres.emit()})`);
    }
}

export {
    SMTBodyEmitter
};
