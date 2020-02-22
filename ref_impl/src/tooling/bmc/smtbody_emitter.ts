//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIRInvokeDecl, MIRInvokeBodyDecl, MIRInvokePrimitiveDecl, MIRConstantDecl, MIRFieldDecl, MIREntityTypeDecl, MIREntityType, MIRTupleType, MIRRecordType, MIRConceptType, MIREphemeralListType } from "../../compiler/mir_assembly";
import { SMTTypeEmitter } from "./smttype_emitter";
import { MIRArgument, MIRRegisterArgument, MIRConstantNone, MIRConstantFalse, MIRConstantTrue, MIRConstantInt, MIRConstantArgument, MIRConstantString, MIROp, MIROpTag, MIRLoadConst, MIRAccessArgVariable, MIRAccessLocalVariable, MIRInvokeFixedFunction, MIRPrefixOp, MIRBinOp, MIRBinEq, MIRBinCmp, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRRegAssign, MIRTruthyConvert, MIRVarStore, MIRReturnAssign, MIRJumpCond, MIRJumpNone, MIRAbort, MIRPhi, MIRBasicBlock, MIRJump, MIRConstructorTuple, MIRConstructorRecord, MIRAccessFromIndex, MIRAccessFromProperty, MIRInvokeKey, MIRAccessConstantValue, MIRLoadFieldDefaultValue, MIRConstructorPrimary, MIRAccessFromField, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionSingletons, MIRIsTypeOf, MIRProjectFromIndecies, MIRModifyWithIndecies, MIRStructuredExtendTuple, MIRProjectFromProperties, MIRModifyWithProperties, MIRStructuredExtendRecord, MIRLoadConstTypedString, MIRConstructorEphemeralValueList, MIRProjectFromFields, MIRModifyWithFields, MIRStructuredExtendObject, MIRLoadConstSafeString, MIRInvokeInvariantCheckDirect, MIRLoadFromEpehmeralList, MIRPackStore, MIRLoadConstRegex, MIRNominalTypeKey } from "../../compiler/mir_ops";
import { SMTExp, SMTValue, SMTCond, SMTLet, SMTFreeVar } from "./smt_exp";
import { SourceInfo } from "../../ast/parser";

import * as assert from "assert";

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

    private currentFile: string = "[No File]";
    private currentRType: MIRType;
    private tmpvarctr = 0;
    private currentSCC = new Set<string>();

    private vtypes: Map<string, MIRType> = new Map<string, MIRType>();

    private subtypeOrderCtr = 0;
    subtypeFMap: Map<string, {order: number, decl: string}> = new Map<string, {order: number, decl: string}>();

    vfieldLookups: { infertype: MIRType, fdecl: MIRFieldDecl, lname: string }[] = [];
    vfieldProjects: { infertype: MIRType, fdecls: MIRFieldDecl[], pname: string }[] = [];
    vfieldUpdates: { infertype: MIRType, fupds: [MIRFieldDecl, MIRArgument][], uname: string }[] = [];
    vobjmerges: { infertype: MIRType, merge: MIRArgument, infermergetype: MIRType, fieldResolves: [string, MIRFieldDecl][], mname: string }[] = [];

    constructor(assembly: MIRAssembly, typegen: SMTTypeEmitter) {
        this.assembly = assembly;
        this.typegen = typegen;

        this.currentRType = typegen.noneType;
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

    varNameToSMTName(name: string): string {
        if (name === "_return_") {
            return "_return_";
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
            else {
                return this.typegen.stringType;
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
        else {
            assert(cval instanceof MIRConstantString);

            return this.typegen.coerce(new SMTValue((cval as MIRConstantString).value), this.typegen.stringType, into);
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
        if (op.vfunckey === undefined) {
            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_safestring@cons "${this.typegen.mangleStringForSMT(op.tskey)}" ${op.ivalue})`));
        }
        else {
            const pfunc = (this.assembly.invokeDecls.get(op.vfunckey) || this.assembly.primitiveInvokeDecls.get(op.vfunckey)) as MIRInvokeDecl;

            const rval = new SMTValue(`(bsq_safestring@cons "${this.typegen.mangleStringForSMT(op.tskey)}" ${op.ivalue})`);
            const tv = this.generateTempName();
            const ivrtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(pfunc.resultType));
            const resulttype = this.typegen.getSMTTypeFor(this.currentRType);
        
            const ichk = new SMTLet(tv, new SMTValue(`(${this.invokenameToSMT(op.vfunckey)} ${op.ivalue})`));
            const checkerror = new SMTValue(`(is-result_error@${ivrtype} ${tv})`);
            const extracterror = (ivrtype !== resulttype) ? new SMTValue(`(result_error@${this.typegen.getSMTTypeFor(this.currentRType)} (result_error_code@${ivrtype} ${tv}))`) : new SMTValue(tv);

            const resultv = ichk.bind(new SMTValue(`(result_success_value@${ivrtype} ${tv})`));
            const cond = new SMTValue(`(or ${checkerror} (= ${resultv} false))`)
            return new SMTLet(this.varToSMTName(op.trgt), new SMTCond(cond, extracterror, rval))
        }
    }

    generateLoadConstTypedString(op: MIRLoadConstTypedString): SMTExp {
        if (op.pfunckey === undefined) {
            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_stringof@cons "${this.typegen.mangleStringForSMT(op.tskey)}" ${op.ivalue})`));
        }
        else {
            const pfunc = (this.assembly.invokeDecls.get(op.pfunckey) || this.assembly.primitiveInvokeDecls.get(op.pfunckey)) as MIRInvokeDecl;

            const rval = new SMTValue(`(bsq_stringof@cons "${this.typegen.mangleStringForSMT(op.tskey)}" ${op.ivalue})`);
            const tv = this.generateTempName();
            const ivrtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(pfunc.resultType));
            const resulttype = this.typegen.getSMTTypeFor(this.currentRType);
        
            const ichk = new SMTLet(tv, new SMTValue(`(${this.invokenameToSMT(op.pfunckey)} ${op.ivalue})`));
            const checkerror = new SMTValue(`(is-result_error@${ivrtype} ${tv})`);
            const extracterror = (ivrtype !== resulttype) ? new SMTValue(`(result_error@${this.typegen.getSMTTypeFor(this.currentRType)} (result_error_code@${ivrtype} ${tv}))`) : new SMTValue(tv);

            const resultT = (this.typegen.assembly.conceptDecls.get(pfunc.resultType) as MIREntityTypeDecl).terms.get("T") as MIRType;
            const errtname = [...this.typegen.assembly.entityDecls].find((dcl) => dcl[0].startsWith("NSCore::Err<") && (dcl[1].terms.get("T") as MIRType).trkey === resultT.trkey) as [string, MIREntityTypeDecl];
            const successf = this.typegen.generateConstructorTest(errtname[0]);

            const resultv = ichk.bind(new SMTValue(`(result_success_value@${ivrtype} ${tv})`));
            const cond = new SMTValue(`(or ${checkerror} (${successf} ${resultv}))`)
            return new SMTLet(this.varToSMTName(op.trgt), new SMTCond(cond, extracterror, rval))
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
        let vals: string[] = fields.map((f) => `(${this.typegen.generateEntityAccessor(f.enclosingDecl, f.fkey)} ${this.argToSMT(ivop.rcvr, this.typegen.getMIRType(ivop.tkey)).emit()})`);
        
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
        else if(this.typegen.typecheckIsName(cpcetype, /NSCore::Set<.*>/)) {
            return new SMTLet(this.varToSMTName(cpce.trgt), new SMTValue(`(${smtctype} 0 ${this.typegen.generateEmptyHasArrayFor(cpce.tkey)} ${this.typegen.generateEmptyDataArrayFor(cpce.tkey)} bsqterm_none)`));
        }
        else {
           return new SMTLet(this.varToSMTName(cpce.trgt), new SMTValue(`(${smtctype} 0 ${this.typegen.generateEmptyHasArrayFor(cpce.tkey)} ${this.typegen.generateEmptyKeyArrayFor(cpce.tkey)} ${this.typegen.generateEmptyDataArrayFor(cpce.tkey)} bsqterm_none)`));
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
        else if(this.typegen.typecheckIsName(cpcstype, /NSCore::Set<.*>/)) {
            const oftype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("T") as MIRType;

            const realkeytype = this.typegen.getKeyProjectedTypeFrom(oftype);
            const kltype = [...this.typegen.assembly.entityDecls].find((edecl) => edecl[1].ns === "NSCore" && edecl[1].name === "KeyList" && (edecl[1].terms.get("K") as MIRType).trkey === realkeytype.trkey) as [string, MIREntityTypeDecl];
            const klcons = this.typegen.generateEntityConstructor(kltype[1].tkey);
            const klstore = this.typegen.getKeyListTypeForSet(this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl);

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
                const keyforce = this.typegen.coerce(new SMTValue(keycons), this.typegen.getMIRType(kltype[1].tkey), klstore).emit();
                const keyup = `(ite (select %HAS% ${key}) %KEY% ${keyforce})`;

                const body = consv.replace(/%CTR%/g, ctrvar).replace(/%HAS%/g, hasvar).replace(/%DATA%/g, datavar).replace(/%KEY%/g, keyvar);
                consv = `(let ((${ctrvar} ${ctrup}) (${hasvar} ${hasup}) (${datavar} ${dataup}) (${keyvar} ${keyup})) ${body})`
            }
            const key = this.typegen.getKeyFrom(this.argToSMT(cpcs.args[0], oftype).emit(), oftype);
            const val = this.argToSMT(cpcs.args[0], oftype).emit();
            const kl = new SMTValue(`(${klcons} ${key} bsqterm_none)`);
            const final = consv
                .replace(/%CTR%/g, "1")
                .replace(/%HAS%/g, `(store ${this.typegen.generateEmptyHasArrayFor(cpcs.tkey)} ${key} true)`)
                .replace(/%DATA%/g, `(store ${this.typegen.generateEmptyDataArrayFor(cpcs.tkey)} ${key} ${val})`)
                .replace(/%KEY%/g, this.typegen.coerce(kl, this.typegen.getMIRType(kltype[1].tkey), klstore).emit());

            return new SMTLet(this.varToSMTName(cpcs.trgt), new SMTValue(final));
        }
        else {
            const ktype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("K") as MIRType;
            const vtype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("V") as MIRType;
            const realkeytype = this.typegen.getKeyProjectedTypeFrom(ktype);

            const entrytype = [...this.typegen.assembly.entityDecls].find((edecl) => edecl[1].ns === "NSCore" && edecl[1].name === "MapEntry" && (edecl[1].terms.get("K") as MIRType).trkey === ktype.trkey && (edecl[1].terms.get("V") as MIRType).trkey === vtype.trkey) as [string, MIREntityTypeDecl];
            const entrykey = this.typegen.generateEntityAccessor(entrytype[1].tkey, (entrytype[1].fields.find((fd) => fd.name === "key") as MIRFieldDecl).fkey);
            const entryvalue = this.typegen.generateEntityAccessor(entrytype[1].tkey, (entrytype[1].fields.find((fd) => fd.name === "value") as MIRFieldDecl).fkey);

            const kltype = [...this.typegen.assembly.entityDecls].find((edecl) => edecl[1].ns === "NSCore" && edecl[1].name === "KeyList" && (edecl[1].terms.get("K") as MIRType).trkey === realkeytype.trkey) as [string, MIREntityTypeDecl];
            const klcons = this.typegen.generateEntityConstructor(kltype[1].tkey);
            const klstore = this.typegen.getKeyListTypeForMap(this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl);

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
                const keyforce = this.typegen.coerce(new SMTValue(keycons), this.typegen.getMIRType(kltype[1].tkey), klstore).emit();
                const keyup = `(ite (select %HAS% ${key}) %KEY% ${keyforce})`;

                const body = consv.replace(/%CTR%/g, ctrvar).replace(/%HAS%/g, hasvar).replace(/%ENTRYKEY%/g, entrykeyvar).replace(/%ENTRYDATA%/g, entrydatavar).replace(/%KEY%/g, keyvar);
                consv = `(let ((${ctrvar} ${ctrup}) (${hasvar} ${hasup}) (${entrykeyvar} ${entrykeyup}) (${entrydatavar} ${entrydataup})  (${keyvar} ${keyup})) ${body})`
            }
            const entrykeyexp0 = `(${entrykey} ${this.argToSMT(cpcs.args[0], this.typegen.getMIRType(entrytype[1].tkey)).emit()})`;
            const entryvalexp0 = `(${entryvalue} ${this.argToSMT(cpcs.args[0], this.typegen.getMIRType(entrytype[1].tkey)).emit()})`;

            const key = this.typegen.getKeyFrom(entrykeyexp0, ktype);
            const kl = new SMTValue(`(${klcons} ${key} bsqterm_none)`);
            const final = consv
                .replace(/%CTR%/g, "1")
                .replace(/%HAS%/g, `(store ${this.typegen.generateEmptyHasArrayFor(cpcs.tkey)} ${key} true)`)
                .replace(/%ENTRYKEY%/g, `(store ${this.typegen.generateEmptyKeyArrayFor(cpcs.tkey)} ${key} ${entrykeyexp0})`)
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
        let fvals = "3";
        let cvals = "bsqtuple_array_empty";
        for (let i = 0; i < op.args.length; ++i) {
            cvals = `(store ${cvals} ${i} ${this.argToSMT(op.args[i], this.typegen.anyType).emit()})`;
            fvals = `(@fj ${this.argToSMT(op.args[i], this.typegen.anyType)} ${fvals})`;
        }

        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_tuple@cons ${this.generateDataKindLoad(this.typegen.getMIRType(op.resultTupleType), fvals)} ${cvals})`));
    }

    generateMIRConstructorRecord(op: MIRConstructorRecord): SMTExp {
        let fvals = "3";
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
            let fvals = "3";
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
            let fvals = "3";
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
                cvals = `(store ${cvals} "${pname}" (select ${tc} "${pname}"))`
                fvals = `(@fj (select ${tc} "${pname}") ${fvals})`;
            }
        }

        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_record@cons ${this.generateDataKindLoad(this.typegen.getMIRType(op.resultRecordType), fvals)} ${cvals})`));
    }

    generateMIRStructuredExtendRecord(op: MIRStructuredExtendRecord, resultRecordType: MIRType): SMTExp {
        const argvals = this.typegen.typecheckRecord(this.getArgType(op.arg)) ? `(bsq_record_entries ${this.varToSMTName(op.arg)})` : `(bsq_record_entries (bsqterm_record_value ${this.varToSMTName(op.arg)}))`;
        let cvals = argvals;
        let fvals = "3";

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

    generateVFieldLookup(arg: MIRArgument, infertype: MIRType, fdecl: MIRFieldDecl): SMTExp {
        const lname = `resolve_${fdecl.fkey}_from_${infertype.trkey}`;
        let decl = this.vfieldLookups.find((lookup) => lookup.lname === lname);
        if(decl === undefined) {
            this.vfieldLookups.push({ infertype: infertype, fdecl: fdecl, lname: lname });
        }

        return new SMTValue(`(${this.typegen.mangleStringForSMT(lname)} ${this.argToSMT(arg, infertype).emit()})`);
    }

    generateMIRAccessFromField(op: MIRAccessFromField, resultAccessType: MIRType): SMTExp {
        const inferargtype = this.typegen.getMIRType(op.argInferType);
        const fdecl = this.assembly.fieldDecls.get(op.field) as MIRFieldDecl;
        const ftype = this.typegen.getMIRType(fdecl.declaredType);

        if (this.typegen.typecheckUEntity(inferargtype)) {
            const access = new SMTValue(`(${this.typegen.generateEntityAccessor(this.typegen.getEntityEKey(inferargtype), op.field)} ${this.argToSMT(op.arg, inferargtype).emit()})`);
            return new SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(access, ftype, resultAccessType));
        }
        else {
            const access = this.generateVFieldLookup(op.arg, inferargtype, fdecl);
            return new SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(access, ftype, resultAccessType));
        }
    }

    generateVFieldProject(arg: MIRArgument, infertype: MIRType, fdecls: MIRFieldDecl[]): SMTExp {
        const pname = `project_${fdecls.map((fd) => fd.fkey).sort().join("*")}_from_${infertype.trkey}`;
        let decl = this.vfieldProjects.find((lookup) => lookup.pname === pname);
        if(decl === undefined) {
            this.vfieldProjects.push({ infertype: infertype, fdecls: fdecls, pname: pname });
        }

        return new SMTValue(`(${this.typegen.mangleStringForSMT(pname)} ${this.argToSMT(arg, infertype)})`);
    }

    generateMIRProjectFromFields(op: MIRProjectFromFields): SMTExp {
        const inferargtype = this.typegen.getMIRType(op.argInferType);
        
        if (this.typegen.typecheckUEntity(inferargtype)) {
            let fvals = "3";
            let cvals = "bsqrecord_array_empty";
            for (let i = 0; i < op.fields.length; ++i) {
                const fdecl = this.assembly.fieldDecls.get(op.fields[i]) as MIRFieldDecl;
                const ftype = this.typegen.getMIRType(fdecl.declaredType);

                const access = new SMTValue(`(${this.typegen.generateEntityAccessor(this.typegen.getEntityEKey(inferargtype), op.fields[i])} ${this.argToSMT(op.arg, inferargtype).emit()})`);
                cvals = `(store ${cvals} "${fdecl.name}" ${this.typegen.coerce(access, ftype, this.typegen.anyType)})`;
                fvals = `(@fj ${this.typegen.coerce(access, ftype, this.typegen.anyType)} ${fvals})`;
            }

            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_record@cons ${this.generateDataKindLoad(this.typegen.getMIRType(op.resultProjectType), fvals)} ${cvals})`));
        }
        else {
            const access = this.generateVFieldProject(op.arg, inferargtype, op.fields.map((f) => this.assembly.fieldDecls.get(f) as MIRFieldDecl));
            return new SMTLet(this.varToSMTName(op.trgt), access);
        }
    }

    generateVFieldUpdates(arg: MIRArgument, infertype: MIRType, fupds: [MIRFieldDecl, MIRArgument][]): SMTExp {
        const upnames = fupds.map((fud) => `${fud[0].fkey}->${this.getArgType(fud[1])}`);
        const uname = `update_${upnames.sort().join("*")}_in_${infertype.trkey}`;
        let decl = this.vfieldUpdates.find((lookup) => lookup.uname === uname);
        if(decl === undefined) {
            this.vfieldUpdates.push({ infertype: infertype, fupds: fupds, uname: uname });
        }

        return new SMTValue(`(${this.typegen.mangleStringForSMT(uname)} ${this.argToSMT(arg, infertype)} ${fupds.map((upd) => this.argToSMT(upd[1], this.getArgType(upd[1])).emit()).join(" ")})`);
    }

    generateMIRModifyWithFields(op: MIRModifyWithFields): SMTExp {
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
            const access = this.generateVFieldUpdates(op.arg, inferargtype, op.updates.map((upd) => [this.assembly.fieldDecls.get(upd[0]) as MIRFieldDecl, upd[1]]));
            return new SMTLet(this.varToSMTName(op.trgt), access);
        }
    }
    
    generateVFieldExtend(arg: MIRArgument, infertype: MIRType, merge: MIRArgument, infermerge: MIRType, fieldResolves: [string, MIRFieldDecl][]): SMTExp {
        const upnames = fieldResolves.map((fr) => `${fr[0]}->${fr[1].fkey}`);
        const mname = `merge_${infertype.trkey}_${upnames.join("*")}_with_${infermerge.trkey}`;
        let decl = this.vobjmerges.find((lookup) => lookup.mname === mname);
        if(decl === undefined) {
            this.vobjmerges.push({ infertype: infertype, merge: merge, infermergetype: infermerge, fieldResolves: fieldResolves, mname: mname });
        }

        return new SMTValue(`(${this.typegen.mangleStringForSMT(mname)} ${this.argToSMT(arg, infertype)} ${this.argToSMT(merge, infermerge)})`);
    }

    generateMIRStructuredExtendObject(op: MIRStructuredExtendObject): SMTExp {
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
            const access = this.generateVFieldExtend(op.arg, inferargtype, op.update, mergeargtype, op.fieldResolves.map((fr) => [fr[0], this.assembly.fieldDecls.get(fr[1]) as MIRFieldDecl]));
            return new SMTLet(this.varToSMTName(op.trgt), access);
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

    generateCompare(op: string, lhsinfertype: MIRType, lhs: MIRArgument, rhsinfertype: MIRType, rhs: MIRArgument): string {
        return `(${op} ${this.argToSMT(lhs, lhsinfertype).emit()} ${this.argToSMT(rhs, rhsinfertype).emit()})`;
    }

    generateSubtypeTupleCheck(argv: string, argtype: MIRType, oftype: MIRTupleType): string {
        const subtypesig = `subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)} ((atuple (Array Int BTerm))) Bool`;

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

        return `(subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)} ${argv})`;
    }

    generateSubtypeRecordCheck(argv: string, argtype: MIRType, oftype: MIRRecordType): string {
        const subtypesig = `subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)} ((arecord (Array String BTerm))) Bool`;

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

        return `(subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)} ${argv})`;
    }

    generateSubtypeConceptCheck(argv: string, argtype: MIRType, oftype: MIRConceptType): string {
        const subtypesig = `subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)} ((val BTerm)) Bool`;

        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            const moftype = this.typegen.getMIRType(oftype.trkey);

            let getenum = new SMTLet("nenum", new SMTValue(`(bsqterm_get_nominal_type val)`));

            let fchk = this.generateConceptArrayLookup(`(bsqterm_get_nominal_type val)`, oftype);
            let chkrest = new SMTValue(fchk);

            let rchk = "[INVALID]";
            if(this.typegen.assembly.subtypeOf(this.typegen.recordType, moftype)) {
                rchk = "true";
            }
            else if (this.typegen.assembly.subtypeOf(moftype, this.typegen.apiType)) {
                rchk = `(not (= (bsqterm_record_flag val) 0))`;
            }
            else if(this.typegen.assembly.subtypeOf(moftype, this.typegen.podType)) {
                rchk = `(= (bsqterm_tuple_flag val) 0)`;
            }
            else {
                rchk = "false";
            }
            let chkrecord = new SMTCond(new SMTValue("(= nenum MIRNominalTypeEnum_Record)"), new SMTValue(rchk), chkrest);

            let tchk = "[INVALID]";
            if(this.typegen.assembly.subtypeOf(this.typegen.tupleType, moftype)) {
                tchk = "true";
            }
            else if (this.typegen.assembly.subtypeOf(moftype, this.typegen.apiType)) {
                tchk = `(not (= (bsqterm_tuple_flag val) 0))`;
            }
            else if(this.typegen.assembly.subtypeOf(moftype, this.typegen.podType)) {
                tchk = `(= (bsqterm_tuple_flag val) 3)`;
            }
            else {
                tchk = "false";
            }
            let chktuple = new SMTCond(new SMTValue("(= nenum MIRNominalTypeEnum_Tuple)"), new SMTValue(tchk), chkrecord)

            console.log(getenum.emit());
            console.log(chktuple.emit());

            const op = getenum.bind(chktuple);

            console.log(op.emit())

            const decl = "(define-fun " + subtypesig
            + "\n  " + op.emit("  ")
            + ")\n"; 

            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }

        return `(subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)} ${argv})`;
    }

    generateFastTupleTypeCheck(arg: string, argtype: MIRType, oftype: MIRTupleType): string {
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
            else if(this.typegen.typecheckUEntity(argtype)) {
                return "false";
            }
            else if (this.typegen.typecheckTuple(argtype)) {
                return this.generateSubtypeTupleCheck(`(bsq_tuple_entries ${arg})`, argtype, oftype);
            }
            else {
                const tsc = this.generateSubtypeTupleCheck(`(bsq_tuple_entries (bsqterm_tuple_value ${arg}))`, argtype, oftype);
                return `(and (is-bsqterm_tuple ${arg}) ${tsc})`
            }
        }
    }

    generateFastRecordTypeCheck(arg: string, argtype: MIRType, oftype: MIRRecordType): string {
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
            else if(this.typegen.typecheckUEntity(argtype)) {
                return "false";
            }
            else if (this.typegen.typecheckRecord(argtype)) {
                return this.generateSubtypeRecordCheck(`(bsq_record_entries ${arg})`, argtype, oftype);
            }
            else {
                const tsc = this.generateSubtypeRecordCheck(`(bsq_record_entries (bsqterm_record_value ${arg}))`, argtype, oftype);
                return `(and (is-bsqterm_record ${arg}) ${tsc})`
            }
        }
    }

    generateFastEntityTypeCheck(arg: string, argtype: MIRType, oftype: MIREntityType): string {
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
            if(this.typegen.typecheckAllKeys(argtype)) {
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
            else if(this.typegen.typecheckUEntity(argtype)) {
                return oftype.ekey === argtype.trkey ? "true" : "false";
            }
            else {
                return `(= (bsqterm_get_nominal_type ${arg}) "${this.typegen.mangleStringForSMT(oftype.ekey)}")`;
            }
        }
    }

    generateConceptArrayLookup(access: string, oftype: MIRConceptType): string {
        const lookups = oftype.ckeys.map((ckey) => {
            const sizestr = this.typegen.getSubtypesArrayCount(ckey);
            return  sizestr === 0 ? "false" : `(select MIRConceptSubtypeArray$${this.typegen.mangleStringForSMT(ckey)} ${access})`;
        });

        if(lookups.find((op) => op === "false")) {
            return "false";
        }
        else if(lookups.length === 1) {
            return lookups[0];
        }
        else {
            return `(and ${lookups.join(" ")})`;
        }
    }

    generateFastConceptTypeCheck(arg: string, argtype: MIRType, oftype: MIRConceptType): string {
        if(oftype.trkey === "NSCore::Any") {
            return "true";
        }

        if(oftype.trkey === "NSCore::Some") {
            if(!this.typegen.assembly.subtypeOf(this.typegen.noneType, argtype)) {
                return "true";
            }
            else {
                if(this.typegen.typecheckAllKeys(argtype)) {
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
            if(this.typegen.typecheckAllKeys(argtype)) {
                return this.generateConceptArrayLookup(`(bsqkey_get_nominal_type ${arg})`, oftype);
            }
            else if (this.typegen.typecheckIsName(argtype, /^NSCore::Buffer<.*>$/)) {
                return this.typegen.assembly.subtypeOf(argtype, moftype) ? "true" : "false";
            }
            else if (this.typegen.typecheckIsName(argtype, /^NSCore::ISOTime$/) || this.typegen.typecheckIsName(argtype, /^NSCore::Regex$/)) {
                return this.typegen.assembly.subtypeOf(argtype, moftype) ? "true" : "false";
            }
            else if (this.typegen.typecheckTuple(argtype)) {
                if(this.typegen.assembly.subtypeOf(this.typegen.tupleType, moftype)) {
                    return "true";
                }

                if(this.typegen.assembly.subtypeOf(moftype, this.typegen.apiType)) {
                    return `(not (= (bsqterm_tuple_flag ${arg}) 0))`;
                }

                if(this.typegen.assembly.subtypeOf(moftype, this.typegen.podType)) {
                    return `(= (bsqterm_tuple_flag ${arg}) 3)`;
                }

                return "false";
            }
            else if (this.typegen.typecheckRecord(argtype)) {
                if(this.typegen.assembly.subtypeOf(this.typegen.tupleType, moftype)) {
                    return "true";
                }

                if(this.typegen.assembly.subtypeOf(moftype, this.typegen.apiType)) {
                    return `(not (= (bsqterm_record_flag ${arg}) 0))`;
                }

                if(this.typegen.assembly.subtypeOf(moftype, this.typegen.podType)) {
                    return `(= (bsqterm_record_flag ${arg}) 3)`;
                }

                return "false";
            }
            else if(this.typegen.typecheckUEntity(argtype)) {
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

                if(simplenominalok) {
                    return this.generateConceptArrayLookup(`(bsqterm_get_nominal_type ${arg})`, oftype);
                }
                else {
                    return this.generateSubtypeConceptCheck(arg, argtype, oftype);
                }
            }
        }
    }

    generateTypeCheck(arg: string, argtype: MIRType, inferargtype: MIRType, oftype: MIRType): string {
        if(inferargtype.trkey !== argtype.trkey) {
            arg = this.typegen.coerce(new SMTValue(arg), argtype, inferargtype).emit();
        }

        if(this.typegen.assembly.subtypeOf(inferargtype, oftype)) {
            return "true";
        }

        const tests = oftype.options.map((topt) => {
            const mtype = this.typegen.getMIRType(topt.trkey);
            assert(mtype !== undefined, "We should generate all the component types by default??");

            if(topt instanceof MIREntityType) {
                return this.generateFastEntityTypeCheck(arg, inferargtype, topt);
            }
            else if (topt instanceof MIRConceptType) {
                return this.generateFastConceptTypeCheck(arg, inferargtype, topt);
            }
            else if (topt instanceof MIRTupleType) {
                return this.generateFastTupleTypeCheck(arg, inferargtype, topt);
            }
            else {
                assert(topt instanceof MIRRecordType);

                return this.generateFastRecordTypeCheck(arg, inferargtype, topt as MIRRecordType);
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

    generateMIRPackStore(op: MIRPackStore): SMTExp {
        if (Array.isArray(op.src)) {
            let ops: SMTExp = new SMTLet(this.varToSMTName(op.names[0]), this.argToSMT(op.src[0], this.getArgType(op.names[0])));
            for(let i = 1; i < op.src.length; ++i) {
                ops = ops.bind(new SMTLet(this.varToSMTName(op.names[i]), this.argToSMT(op.src[i], this.getArgType(op.names[i]))));
            }

            return ops;
        }
        else {
            const eltype = this.getArgType(op.src).options[0] as MIREphemeralListType;
            const tlist = eltype.entries;

            const getter0 = new SMTValue(`(${this.typegen.generateEntityAccessor(eltype.trkey, `entry_0`)} ${this.varToSMTName(op.src)})`);
            let ops: SMTExp = new SMTLet(this.varToSMTName(op.names[0]), getter0);
            for(let i = 1; i < tlist.length; ++i) {
                const getteri = new SMTValue(`(${this.typegen.generateEntityAccessor(eltype.trkey, `entry_${i}`)} ${this.varToSMTName(op.src)})`);
                ops = ops.bind(new SMTLet(this.varToSMTName(op.names[i]), getteri));
            }

            return ops;
        }
    }

    generateStmt(op: MIROp, fromblck: string, gas: number | undefined): SMTExp | undefined {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = op as MIRLoadConst;
                return new SMTLet(this.varToSMTName(lcv.trgt), this.generateConstantExp(lcv.src, this.getArgType(lcv.trgt)));
            }
            case MIROpTag.MIRLoadConstRegex: {
                const lcr = op as MIRLoadConstRegex;
                return new SMTLet(this.varToSMTName(lcr.trgt), new SMTValue(`(bsq_regex@cons "${lcr.restr}")`));
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
                return this.generateMIRAccessFromField(af, this.typegen.getMIRType(af.resultAccessType));
            }
            case MIROpTag.MIRProjectFromFields: {
                const pf = op as MIRProjectFromFields;
                return this.generateMIRProjectFromFields(pf);
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
                return this.generateMIRModifyWithFields(mf);
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
                return this.generateMIRStructuredExtendObject(so);
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
                    const tval = this.generateTruthyConvert(pfx.arg);
                    return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`(not ${tval.emit()})`));
                }
                else {
                    if (pfx.op === "-") {
                        if (pfx.arg instanceof MIRConstantInt) {
                            return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`-${(pfx.arg as MIRConstantInt).value}`));
                        }
                        else {
                            return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`(* -1 ${this.argToSMT(pfx.arg, this.typegen.intType).emit()})`));
                        }
                    }
                    else {
                        return new SMTLet(this.varToSMTName(pfx.trgt), this.argToSMT(pfx.arg, this.typegen.intType));
                    }
                }
            }
            case MIROpTag.MIRBinOp: {
                const bop = op as MIRBinOp;

                if (bop.op === "*") {
                    if(bop.rhs instanceof MIRConstantInt || bop.lhs instanceof MIRConstantInt) {
                        return new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(`(* ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                    }
                    else {
                        return new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(`(mult_op ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                    }
                }
                else if (bop.op === "/") {
                    if (bop.rhs instanceof MIRConstantInt || bop.lhs instanceof MIRConstantInt) {
                        const divres = new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(`(/ ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                        return new SMTCond(new SMTValue(`(= ${this.argToSMT(bop.rhs, this.typegen.intType).emit()} 0)`), this.generateErrorCreate(op.sinfo, this.typegen.getSMTTypeFor(this.currentRType)), divres);
                    }
                    else {
                        const divres = new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(`(div_op ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                        return new SMTCond(new SMTValue(`(= ${this.argToSMT(bop.rhs, this.typegen.intType).emit()} 0)`), this.generateErrorCreate(op.sinfo, this.typegen.getSMTTypeFor(this.currentRType)), divres);
                    }
                }
                else if (bop.op === "%") {
                    const modres = new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(`(mod_op ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                    return new SMTCond(new SMTValue(`(or (< ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} 0) (<= ${this.argToSMT(bop.rhs, this.typegen.intType).emit()} 0))`), this.generateErrorCreate(op.sinfo, this.typegen.getSMTTypeFor(this.currentRType)), modres);
                }
                else {
                    return new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(`(${bop.op} ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                }
            }
            case MIROpTag.MIRGetKey: {
                return NOT_IMPLEMENTED<SMTExp>("MIRGetKey");
            }
            case MIROpTag.MIRBinEq: {
                const beq = op as MIRBinEq;

                const lhvtypeinfer = this.typegen.getMIRType(beq.lhsInferType);
                const rhvtypeinfer = this.typegen.getMIRType(beq.rhsInferType);
                return new SMTLet(this.varToSMTName(beq.trgt), new SMTValue(this.generateEquals(beq.op, lhvtypeinfer, beq.lhs, rhvtypeinfer, beq.rhs, !beq.relaxed)));
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
            case MIROpTag.MIRPackStore: {
                const vps = op as MIRPackStore;
                return this.generateMIRPackStore(vps);
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
                const smttest = this.generateTruthyConvert(cjop.arg);
                return new SMTCond(smttest, SMTFreeVar.generate("#true_trgt#"), SMTFreeVar.generate("#false_trgt#"));
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

    generateBlockExps(block: MIRBasicBlock, fromblock: string, blocks: Map<string, MIRBasicBlock>, gas: number | undefined): SMTExp {
        const exps: SMTExp[] = [];
        for (let i = 0; i < block.ops.length; ++i) {
            const exp = this.generateStmt(block.ops[i], fromblock, gas);
            if (exp !== undefined) {
                exps.push(exp);
            }
        }

        if (block.label === "exit") {
            const resulttype = this.typegen.getSMTTypeFor(this.currentRType);
            let rexp = new SMTValue(`(result_success@${resulttype} _return_)`) as SMTExp;
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
                let rexp = this.generateBlockExps(blocks.get((jop as MIRJump).trgtblock) as MIRBasicBlock, block.label, blocks, gas);
                for (let i = exps.length - 1; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }

                return rexp;
            }
            else {
                assert(jop.tag === MIROpTag.MIRJumpCond || jop.tag === MIROpTag.MIRJumpNone);

                let tblock = ((jop.tag === MIROpTag.MIRJumpCond) ? blocks.get((jop as MIRJumpCond).trueblock) : blocks.get((jop as MIRJumpNone).noneblock)) as MIRBasicBlock;
                let texp = this.generateBlockExps(tblock, block.label, blocks, gas);

                let fblock = ((jop.tag === MIROpTag.MIRJumpCond) ? blocks.get((jop as MIRJumpCond).falseblock) : blocks.get((jop as MIRJumpNone).someblock)) as MIRBasicBlock;
                let fexp = this.generateBlockExps(fblock, block.label, blocks, gas);

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
        const decl = `(define-fun ${this.invokenameToSMT(idecl.key)}${gas !== undefined ? `@gas${gas}` : ""} (${args.join(" ")}) Result@${restype}`;

        if (idecl instanceof MIRInvokeBodyDecl) {
            this.vtypes = new Map<string, MIRType>();
            (idecl.body.vtypes as Map<string, string>).forEach((tkey, name) => {
                this.vtypes.set(name, this.typegen.getMIRType(tkey));
            });

            const blocks = (idecl as MIRInvokeBodyDecl).body.body;
            const body = this.generateBlockExps(blocks.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocks, gasdown);

            return `${decl} \n${body.emit("  ")})`;

        }
        else {
            assert(idecl instanceof MIRInvokePrimitiveDecl);

            const params = idecl.params.map((arg) => this.varNameToSMTName(arg.name));
            return `${decl} \n  ${this.generateBuiltinBody(idecl as MIRInvokePrimitiveDecl, params).emit("  ")}\n)`;
        }
    }

    generateBuiltinBody(idecl: MIRInvokePrimitiveDecl, params: string[]): SMTExp {
        const rtype = this.typegen.getMIRType(idecl.resultType);

        let bodyres: SMTExp | undefined = undefined;
        const enclkey = (idecl.enclosingDecl || "[NA]") as MIRNominalTypeKey
        switch (idecl.implkey) {
            case "list_size":
            case "set_size":
            case "map_size": {
                bodyres = this.typegen.generateSpecialTypeFieldAccessExp(enclkey, "size", params[0]);
                break;
            }
            case "list_unsafe_at": {
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
                const kll = this.typegen.coerce(new SMTValue(params[3]), this.typegen.getMIRType(idecl.params[3].type), klctype);
                bodyres = new SMTValue(`(${cons}(+ ${size} 1) (store ${has} ${params[1]} true) (store ${keys} ${params[1]} ${params[2]}) (store ${entries} ${params[1]} ${params[3]}) ${kll.emit()})`);
                break;
            }
            default: {
                bodyres = new SMTValue(`[Builtin not defined -- ${idecl.iname}]`);
                break;
            }
        }

        return new SMTValue(`(result_success@${this.typegen.getSMTTypeFor(rtype)} ${bodyres.emit()})`);
    }
}

export {
    SMTBodyEmitter
};
