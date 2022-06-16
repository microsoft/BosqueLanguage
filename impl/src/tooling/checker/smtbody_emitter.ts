//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRConceptType, MIRConstructableEntityTypeDecl, MIRDataBufferInternalEntityTypeDecl, MIRDataStringInternalEntityTypeDecl, MIREntityType, MIREntityTypeDecl, MIREnumEntityTypeDecl, MIREphemeralListType, MIRFieldDecl, MIRInvokeBodyDecl, MIRInvokeDecl, MIRInvokePrimitiveDecl, MIRObjectEntityTypeDecl, MIRPCode, MIRPrimitiveCollectionEntityTypeDecl, MIRPrimitiveInternalEntityTypeDecl, MIRPrimitiveListEntityTypeDecl, MIRPrimitiveMapEntityTypeDecl, MIRPrimitiveQueueEntityTypeDecl, MIRPrimitiveSetEntityTypeDecl, MIRPrimitiveStackEntityTypeDecl, MIRRecordType, MIRStringOfInternalEntityTypeDecl, MIRTupleType, MIRType } from "../../compiler/mir_assembly";
import { SMTTypeEmitter } from "./smttype_emitter";
import { MIRAbort, MIRArgGuard, MIRArgument, MIRAssertCheck, MIRBasicBlock, MIRBinKeyEq, MIRBinKeyLess, MIRConstantArgument, MIRConstantBigInt, MIRConstantBigNat, MIRConstantDataString, MIRConstantDecimal, MIRConstantFalse, MIRConstantFloat, MIRConstantInt, MIRConstantNat, MIRConstantNone, MIRConstantNothing, MIRConstantRational, MIRConstantRegex, MIRConstantString, MIRConstantStringOf, MIRConstantTrue, MIRConstantTypedNumber, MIRConstructorEntityDirect, MIRConstructorEphemeralList, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionMixed, MIRConstructorPrimaryCollectionSingletons, MIRConstructorRecord, MIRConstructorRecordFromEphemeralList, MIRConstructorTuple, MIRConstructorTupleFromEphemeralList, MIRConvertValue, MIRDeclareGuardFlagLocation, MIREntityProjectToEphemeral, MIREntityUpdate, MIREphemeralListExtend, MIRExtract, MIRFieldKey, MIRGlobalVariable, MIRGuard, MIRGuardedOptionInject, MIRInject, MIRInvokeFixedFunction, MIRInvokeKey, MIRInvokeVirtualFunction, MIRInvokeVirtualOperator, MIRIsTypeOf, MIRJump, MIRJumpCond, MIRJumpNone, MIRLoadConst, MIRLoadField, MIRLoadFromEpehmeralList, MIRLoadRecordProperty, MIRLoadRecordPropertySetGuard, MIRLoadTupleIndex, MIRLoadTupleIndexSetGuard, MIRLoadUnintVariableValue, MIRLogicAction, MIRMaskGuard, MIRMultiLoadFromEpehmeralList, MIROp, MIROpTag, MIRPhi, MIRPrefixNotOp, MIRRecordHasProperty, MIRRecordProjectToEphemeral, MIRRecordUpdate, MIRRegisterArgument, MIRRegisterAssign, MIRResolvedTypeKey, MIRReturnAssign, MIRReturnAssignOfCons, MIRSetConstantGuardFlag, MIRSliceEpehmeralList, MIRStatmentGuard, MIRStructuredAppendTuple, MIRStructuredJoinRecord, MIRTupleHasIndex, MIRTupleProjectToEphemeral, MIRTupleUpdate, MIRVirtualMethodKey } from "../../compiler/mir_ops";
import { SMTCallSimple, SMTCallGeneral, SMTCallGeneralWOptMask, SMTCond, SMTConst, SMTExp, SMTIf, SMTLet, SMTLetMulti, SMTMaskConstruct, SMTVar, SMTCallGeneralWPassThroughMask, SMTTypeInfo, VerifierOptions } from "./smt_exp";
import { SourceInfo } from "../../ast/parser";
import { SMTFunction } from "./smt_assembly";

import * as assert from "assert";
import { BSQRegex } from "../../ast/bsqregex";

function NOT_IMPLEMENTED(msg: string): SMTExp {
    throw new Error(`Not Implemented: ${msg}`);
}

class SMTBodyEmitter {
    readonly assembly: MIRAssembly;
    readonly typegen: SMTTypeEmitter;

    readonly callsafety: Map<MIRInvokeKey, { safe: boolean, trgt: boolean }>;

    readonly errorTrgtPos: { file: string, line: number, pos: number };
    readonly allErrors: { file: string, line: number, pos: number, msg: string }[];
    readonly vopts: VerifierOptions;

    private tmpvarctr = 0;

    currentFile: string = "[No File]";
    currentRType: MIRType;
    currentSCC = new Set<string>();

    private pendingMask: SMTMaskConstruct[] = [];
    requiredTypecheck: { inv: string, flowtype: MIRType, oftype: MIRType }[] = [];

    maskSizes: Set<number> = new Set<number>();

    //!!!
    //See the methods generateLoadTupleIndexVirtual, generateLoadTupleIndexVirtual, etc for processing the entries in these arrays
    //!!!

    requiredLoadVirtualTupleIndex: { inv: string, argflowtype: MIRType, idx: number, resulttype: MIRType, guard: MIRGuard | undefined }[] = [];
    requiredLoadVirtualRecordProperty: { inv: string, argflowtype: MIRType, pname: string, resulttype: MIRType, guard: MIRGuard | undefined }[] = [];
    requiredLoadVirtualEntityField: { inv: string, argflowtype: MIRType, field: MIRFieldDecl, resulttype: MIRType }[] = [];
    
    requiredProjectVirtualTupleIndex: { inv: string, argflowtype: MIRType, indecies: number[], resulttype: MIRType }[] = [];
    requiredProjectVirtualRecordProperty: { inv: string, argflowtype: MIRType, properties: string[], resulttype: MIRType }[] = [];
    requiredProjectVirtualEntityField: { inv: string, argflowtype: MIRType, fields: MIRFieldDecl[], resulttype: MIRType }[] = [];

    requiredUpdateVirtualTuple: { inv: string, argflowtype: MIRType, updates: [number, MIRResolvedTypeKey][], resulttype: MIRType }[] = [];
    requiredUpdateVirtualRecord: { inv: string, argflowtype: MIRType, updates: [string, MIRResolvedTypeKey][], resulttype: MIRType }[] = [];
    requiredUpdateVirtualEntity: { inv: string, argflowtype: MIRType, allsafe: boolean, updates: [MIRFieldKey, MIRResolvedTypeKey][], resulttype: MIRType }[] = [];

    requiredSingletonConstructorsList: { inv: string, argc: number, resulttype: MIRType }[] = [];
    requiredSingletonConstructorsMap: { srcFile: string, sinfo: SourceInfo, inv: string, argc: number, resulttype: MIRType }[] = [];

    requiredVirtualFunctionInvokes: { inv: string, allsafe: boolean, argflowtype: MIRType, vfname: MIRVirtualMethodKey, optmask: string | undefined, resulttype: MIRType }[] = [];
    requiredVirtualOperatorInvokes: { inv: string, argflowtype: MIRType, opname: MIRVirtualMethodKey, args: MIRResolvedTypeKey[], resulttype: MIRType }[] = [];

    requiredSubtypeTagChecks: {t: MIRType, oftype: MIRType}[] = [];
    requiredIndexTagChecks: {idx: number, oftype: MIRType}[] = [];
    requiredRecordTagChecks: {pname: string, oftype: MIRType}[] = [];

    requiredUFConsts: SMTTypeInfo[] = [];

    varStringToSMT(name: string): SMTVar {
        if (name === "$$return") {
            return new SMTVar("$$return");
        }
        else {
            return new SMTVar(name);
        }
    }

    varToSMTName(varg: MIRRegisterArgument): SMTVar {
        return this.varStringToSMT(varg.nameID);
    }

    globalToSMT(gval: MIRGlobalVariable): SMTConst {
        this.typegen.internGlobalName(gval.gkey, gval.shortname);
        return new SMTConst(this.typegen.lookupGlobalName(gval.gkey));
    }

    private processSubtypeTagCheck(t: MIRType, oftype: MIRType) {
        const stc = this.requiredSubtypeTagChecks.find((tc) => tc.t.typeID === t.typeID && tc.oftype.typeID === oftype.typeID);
        if (stc === undefined) {
            this.requiredSubtypeTagChecks.push({ t: t, oftype: oftype });
        }
    }

    private processIndexTagCheck(idx: number, oftype: MIRType) {
        const stc = this.requiredIndexTagChecks.find((tc) => tc.idx === idx && tc.oftype.typeID === oftype.typeID);
        if (stc === undefined) {
            this.requiredIndexTagChecks.push({ idx: idx, oftype: oftype });
        }
    }

    private processPropertyTagCheck(pname: string, oftype: MIRType) {
        const stc = this.requiredRecordTagChecks.find((tc) => tc.pname === pname && tc.oftype.typeID === oftype.typeID);
        if (stc === undefined) {
            this.requiredRecordTagChecks.push({ pname: pname, oftype: oftype });
        }
    }

    private generateTypeCheckName(argflowtype: MIRType, oftype: MIRType): string {
        return `$SubtypeCheck_${this.typegen.lookupTypeName(argflowtype.typeID)}_oftype_${this.typegen.lookupTypeName(oftype.typeID)}`;
    }

    private registerRequiredTypeCheck(argflowtype: MIRType, oftype: MIRType): string {
        const inv = this.generateTypeCheckName(argflowtype, oftype);
        if (this.requiredTypecheck.findIndex((rtc) => rtc.inv === inv) === -1) {
            this.requiredTypecheck.push({ inv: inv, flowtype: argflowtype, oftype: oftype });
        }

        return inv;
    }

    generateUFConstantForType(tt: MIRType): string {
        const ctype = this.typegen.getSMTTypeFor(tt);
        const ufcname = `${ctype.smttypename}@uicons_UF`;
        
        if(this.requiredUFConsts.find((cc) => cc.smttypename === ctype.smttypename) === undefined) {
            this.requiredUFConsts.push(ctype);
        }

        return ufcname;
    }

    private generateBoolForGuard(guard: MIRGuard): SMTExp {
        if(guard instanceof MIRMaskGuard) {
            return new SMTCallSimple(`$Mask_${guard.gsize}@${guard.gindex}`, [this.varStringToSMT(guard.gmask)]);
        }
        else {
            return this.argToSMT((guard as MIRArgGuard).greg);
        }
    }

    private generateAltForGuardStmt(arg: MIRArgument | undefined, oftype: MIRType): SMTExp {
        return arg !== undefined ? this.argToSMT(arg) : new SMTConst(this.generateUFConstantForType(oftype));
    }

    private generateGuardStmtCond(sguard: MIRStatmentGuard | undefined, gexp: SMTExp, rtype: MIRResolvedTypeKey): SMTExp {
        if(sguard === undefined) {
            return gexp;
        }
        else {
            const gcond = this.generateBoolForGuard(sguard.guard);
            const galt = this.generateAltForGuardStmt(sguard.defaultvar, this.typegen.getMIRType(rtype));
            if(sguard.usedefault === "defaultonfalse") {
                return new SMTIf(gcond, gexp, galt);
            }
            else {
                return new SMTIf(gcond, galt, gexp);
            }
        }
    }

    private generateGeneralCallValueProcessing(callertype: MIRType, calleetype: MIRType, gcall: SMTExp, trgt: MIRRegisterArgument, continuation: SMTExp): SMTLet {
        const cres = this.generateTempName();
        
        const callersmt = this.typegen.getSMTTypeFor(callertype);
        const calleesmt = this.typegen.getSMTTypeFor(calleetype);

        const okpath = new SMTLet(this.varToSMTName(trgt).vname, this.typegen.generateResultGetSuccess(calleetype, new SMTVar(cres)), continuation);
        const errpath = (callersmt.smttypename === calleesmt.smttypename) ? new SMTVar(cres) : this.typegen.generateResultTypeConstructorError(callertype, this.typegen.generateResultGetError(calleetype, new SMTVar(cres)));

        const icond = new SMTIf(this.typegen.generateResultIsErrorTest(calleetype, new SMTVar(cres)), errpath, okpath);
        return new SMTLet(cres, gcall, icond);
    }

    private generateLoadVirtualTupleInvName(argflowtype: MIRType, idx: number, resulttype: MIRType, guard: MIRGuard | undefined): string {
        const fullname = `$TupleLoad!${argflowtype.typeID}!${idx}!${resulttype.typeID}${guard !== undefined ? "_WG" : ""}`;
        const shortname = `$TupleLoad_${this.typegen.lookupTypeName(argflowtype.typeID)}@_${idx}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateLoadVirtualPropertyInvName(argflowtype: MIRType, pname: string, resulttype: MIRType, guard: MIRGuard | undefined): string {
        const fullname = `$RecordLoad!${argflowtype.typeID}!${pname}!${resulttype.typeID}${guard !== undefined ? "_WG" : ""}`;
        const shortname = `$RecordLoad_${this.typegen.lookupTypeName(argflowtype.typeID)}@_${pname}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateLoadVirtualFieldInvName(argflowtype: MIRType, fkey: MIRFieldKey, resulttype: MIRType): string {
        const fdecl = this.assembly.fieldDecls.get(fkey) as MIRFieldDecl;
        const fullname = `$EntityLoad!${argflowtype.typeID}!${fkey}!${resulttype.typeID}`;
        const shortname = `$EntityLoad_${this.typegen.lookupTypeName(argflowtype.typeID)}@_${fdecl.fname}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateProjectVirtualTupleInvName(argflowtype: MIRType, indecies: number[], resulttype: MIRType): string {
        const idxs = indecies.map((idx) => `${idx}`).join(",");
        const fullname = `$TupleProject!${argflowtype.typeID}[${idxs}]!${resulttype.typeID}`;
        const shortname = `$TupleProject_${this.typegen.lookupTypeName(argflowtype.typeID)}@_${idxs}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateProjectVirtualRecordInvName(argflowtype: MIRType, properties: string[], resulttype: MIRType): string {
        const pnames = properties.join(",");
        const fullname = `$RecordProject!${argflowtype.typeID}{${pnames}}${resulttype.typeID}`;
        const shortname = `$RecordProject_${this.typegen.lookupTypeName(argflowtype.typeID)}@_${pnames}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateProjectVirtualEntityInvName(argflowtype: MIRType, fields: MIRFieldKey[], resulttype: MIRType): string {
        const fkeys = fields.join(",");
        const shortkeys = fields.map((fn) => (this.assembly.fieldDecls.get(fn) as MIRFieldDecl).fname).join(",")
        const fullname = `$EntityProject!${argflowtype.typeID}!{${fkeys}}!${resulttype.typeID}`;
        const shortname = `$EntityProject_${this.typegen.lookupTypeName(argflowtype.typeID)}@_${shortkeys}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateUpdateVirtualTupleInvName(argflowtype: MIRType, indecies: [number, MIRResolvedTypeKey][], resulttype: MIRType): string {
        const idxs = indecies.map((idx) => `(${idx[0]} ${idx[1]})`).join(",");
        const shortidxs = indecies.map((idx) => idx[0]).join(",");
        const fullname = `$TupleUpdate!${argflowtype.typeID}![${idxs}]=!${resulttype.typeID}`;
        const shortname = `$TupleUpdate_${this.typegen.lookupTypeName(argflowtype.typeID)}@_${shortidxs}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateUpdateVirtualRecordInvName(argflowtype: MIRType, properties: [string, MIRResolvedTypeKey][], resulttype: MIRType): string {
        const pnames = properties.map((pname) => `(${pname[0]} ${pname[1]})`).join(",");
        const shortpnames = properties.map((pname) => pname[0]).join(",");
        const fullname = `$RecordUpdate!${argflowtype.typeID}!{${pnames}}=!${resulttype.typeID}`;
        const shortname = `$RecordUpdate_${this.typegen.lookupTypeName(argflowtype.typeID)}@_${shortpnames}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateUpdateVirtualEntityInvName(argflowtype: MIRType, fields: [MIRFieldKey, MIRResolvedTypeKey][], resulttype: MIRType): string {
        const fnames = fields.map((fname) => `(${fname[0]} ${fname[1]})`).join(",");
        const shortfnames = fields.map((fname) => (this.assembly.fieldDecls.get(fname[0]) as MIRFieldDecl).fname).join(",");
        const fullname = `$EntityUpdate!${argflowtype.typeID}!{${fnames}}=!${resulttype.typeID}`;
        const shortname = `$EntityUpdate_${argflowtype.typeID}@_${shortfnames}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateSingletonConstructorsList(argc: number, resulttype: MIRType): string {
        const fullname = `$ListSingletonCons!${argc}!${resulttype.typeID}`;
        const shortname = `$ListSingletonCons_${argc}_${resulttype.typeID}`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateSingletonConstructorsMap(argc: number, resulttype: MIRType): string {
        const fullname = `$MapSingletonCons!${argc}!${resulttype.typeID}`;
        const shortname = `$MapSingletonCons_${argc}_${resulttype.typeID}`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateVirtualInvokeFunctionName(argflowtype: MIRType, fname: MIRVirtualMethodKey, shortvname: string, optmask: boolean, resulttype: MIRType): string {
        const fullname = `$VirtualInvoke!${argflowtype.typeID}!${fname}${optmask ? "_WM_" : ""}!${resulttype.typeID}`;
        const shortname = `$VirtualInvoke_${this.typegen.lookupTypeName(argflowtype.typeID)}@_${shortvname}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateVirtualInvokeOperatorName(fname: MIRVirtualMethodKey, shortvname: string, rcvrtypes: MIRResolvedTypeKey[], resulttype: MIRType): string {
        const rnames = `(${rcvrtypes.join(",")})`;
        const shortrnames = `(${rcvrtypes.map((tt) => this.typegen.getMIRType(tt).typeID).join(",")})`;
        const fullname = `$VirtualOperator!${fname}${rnames}!${resulttype.typeID}`;
        const shortname = `$VirtualOperator_${shortvname}${shortrnames}`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    generateLoadTupleIndexVirtual(geninfo: { inv: string, argflowtype: MIRType, idx: number, resulttype: MIRType, guard: MIRGuard | undefined }): SMTFunction {
        const ttuples = [...this.assembly.tupleDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].typeID);
                return this.typegen.isUniqueTupleType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultType(geninfo.resulttype) : this.typegen.getSMTTypeFor(geninfo.resulttype);
        const ufcname = this.generateUFConstantForType(geninfo.resulttype);
        if(ttuples.length === 0) {
            const rbody = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, new SMTConst(ufcname), false) : new SMTConst(ufcname);
            return SMTFunction.create(this.typegen.lookupFunctionName(geninfo.inv), [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], rtype, rbody);
        }
        else {
            const ops = ttuples.map((tt) => {
                const mtt = this.typegen.getMIRType(tt.typeID);
                const test = new SMTCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

                const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
                const idxr = new SMTCallSimple(this.typegen.generateTupleIndexGetFunction(tt, geninfo.idx), [argpp]);
                const crt = this.typegen.coerce(idxr, (geninfo.argflowtype.options[0] as MIRTupleType).entries[geninfo.idx], geninfo.resulttype);
                const action = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, crt, true) : crt;

                return {test: test, result: action};
            });

            const orelse = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, new SMTConst(ufcname), false) : new SMTConst(ufcname);

            return SMTFunction.create(this.typegen.lookupFunctionName(geninfo.inv), [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], rtype, new SMTCond(ops, orelse));
        }
    }

    generateLoadRecordPropertyVirtual(geninfo: { inv: string, argflowtype: MIRType, pname: string, resulttype: MIRType, guard: MIRGuard | undefined }): SMTFunction {
        const trecords = [...this.assembly.recordDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].typeID);
                return this.typegen.isUniqueRecordType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultType(geninfo.resulttype) : this.typegen.getSMTTypeFor(geninfo.resulttype);
        const ufcname = this.generateUFConstantForType(geninfo.resulttype);
        if(trecords.length === 0) {
            const rbody = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, new SMTConst(ufcname), false) : new SMTConst(ufcname);
            return SMTFunction.create(this.typegen.lookupFunctionName(geninfo.inv), [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], rtype, rbody);
        }
        else {
            const ops = trecords.map((tt) => {
                const mtt = this.typegen.getMIRType(tt.typeID);
                const test = new SMTCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

                const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
                const idxr = new SMTCallSimple(this.typegen.generateRecordPropertyGetFunction(tt, geninfo.pname), [argpp]);
                const crt = this.typegen.coerce(idxr, ((geninfo.argflowtype.options[0] as MIRRecordType).entries.find((vv) => vv.pname === geninfo.pname) as {pname: string, ptype: MIRType}).ptype, geninfo.resulttype);
                const action = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, crt, true) : crt;

                return {test: test, result: action};
            });

            const orelse = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, new SMTConst(ufcname), false) : new SMTConst(ufcname);

            return SMTFunction.create(this.typegen.lookupFunctionName(geninfo.inv), [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], rtype, new SMTCond(ops, orelse));
        }
    }

    generateLoadEntityFieldVirtual(geninfo: { inv: string, argflowtype: MIRType, field: MIRFieldDecl, resulttype: MIRType }): SMTFunction {
        const tentities = [...this.assembly.entityDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].tkey);
                return this.typegen.isUniqueEntityType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getSMTTypeFor(geninfo.resulttype);
        let ops = tentities.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.tkey);
            const test = new SMTCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

            const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
            const action = new SMTCallSimple(this.typegen.generateEntityFieldGetFunction(tt, geninfo.field), [argpp]);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        return SMTFunction.create(this.typegen.lookupFunctionName(geninfo.inv), [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], rtype, new SMTCond(ops, orelse));
    }

    generateProjectTupleIndexVirtual(geninfo: { inv: string, argflowtype: MIRType, indecies: number[], resulttype: MIRType }): SMTFunction {
        const ttuples = [...this.assembly.tupleDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].typeID);
                return this.typegen.isUniqueTupleType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getSMTTypeFor(geninfo.resulttype);
        let ops = ttuples.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.typeID);
            const test = new SMTCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

            const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
            const pargs = geninfo.indecies.map((idx, i) => {
                const idxr = new SMTCallSimple(this.typegen.generateTupleIndexGetFunction(geninfo.argflowtype.options[0] as MIRTupleType, idx), [argpp]);
                return this.typegen.coerce(idxr, (geninfo.argflowtype.options[0] as MIRTupleType).entries[idx], (geninfo.resulttype.options[0] as MIREphemeralListType).entries[i]);
            });
            const action = new SMTCallSimple(this.typegen.getSMTConstructorName(geninfo.resulttype).cons, pargs);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);
            
        return SMTFunction.create(this.typegen.lookupFunctionName(geninfo.inv), [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], rtype, new SMTCond(ops, orelse));
    }

    generateProjectRecordPropertyVirtual(geninfo: { inv: string, argflowtype: MIRType, properties: string[], resulttype: MIRType }): SMTFunction {
        const trecords = [...this.assembly.recordDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].typeID);
                return this.typegen.isUniqueRecordType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getSMTTypeFor(geninfo.resulttype);
        let ops = trecords.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.typeID);
            const test = new SMTCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

            const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
            const pargs = geninfo.properties.map((pname, i) => {
                const idxr = new SMTCallSimple(this.typegen.generateRecordPropertyGetFunction(geninfo.argflowtype.options[0] as MIRRecordType, pname), [argpp]);
                return this.typegen.coerce(idxr, ((geninfo.argflowtype.options[0] as MIRRecordType).entries.find((vv) => vv.pname === pname) as {pname: string, ptype: MIRType}).ptype, (geninfo.resulttype.options[0] as MIREphemeralListType).entries[i]);
            });
            const action = new SMTCallSimple(this.typegen.getSMTConstructorName(geninfo.resulttype).cons, pargs);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        return SMTFunction.create(this.typegen.lookupFunctionName(geninfo.inv), [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], rtype, new SMTCond(ops, orelse));
    }

    generateProjectEntityFieldVirtual(geninfo: { inv: string, argflowtype: MIRType, fields: MIRFieldDecl[], resulttype: MIRType }): SMTFunction {
        const tentities = [...this.assembly.entityDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].tkey);
                return this.typegen.isUniqueEntityType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getSMTTypeFor(geninfo.resulttype);
        let ops = tentities.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.tkey);
            const test = new SMTCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

            const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
            const pargs = geninfo.fields.map((field, i) => {
                const idxr = new SMTCallSimple(this.typegen.generateEntityFieldGetFunction(tt, field), [argpp]);
                return this.typegen.coerce(idxr, this.typegen.getMIRType(field.declaredType), (geninfo.resulttype.options[0] as MIREphemeralListType).entries[i]);
            });
            const action = new SMTCallSimple(this.typegen.getSMTConstructorName(geninfo.resulttype).cons, pargs);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        return SMTFunction.create(this.typegen.lookupFunctionName(geninfo.inv), [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], rtype, new SMTCond(ops, orelse));
    }

    generateSingletonConstructorList(geninfo: { inv: string, argc: number, resulttype: MIRType }): SMTFunction {
        const ldecl = this.assembly.entityDecls.get(geninfo.resulttype.typeID) as MIRPrimitiveListEntityTypeDecl;
        const etype = ldecl.getTypeT();

        let args: { vname: string, vtype: SMTTypeInfo }[] = [];
        for(let j = 0; j < geninfo.argc; ++j) {
            args.push({ vname: `arg${j}`, vtype: this.typegen.getSMTTypeFor(etype) });
        }

        if(this.vopts.ARRAY_MODE === "Seq") {
            let largs: SMTExp[] = [];
            for(let i = 0; i < geninfo.argc; ++i) {
                largs.push(new SMTCallSimple("seq.unit", [new SMTVar(`arg${i}`)]));
            }

            const bbody = this.typegen.generateListTypeConstructorSeq(geninfo.resulttype, new SMTCallSimple("seq.++", largs));
            return SMTFunction.create(this.typegen.lookupFunctionName(geninfo.inv), args, this.typegen.getSMTTypeFor(geninfo.resulttype), bbody);
        }
        else {

            const larray = this.typegen.generateListTypeConstructorArrayElements(geninfo.resulttype, new SMTConst(`${geninfo.argc}`), args.map((arg) => new SMTVar(arg.vname)));
            const bbody = this.typegen.generateListTypeConstructorArray(geninfo.resulttype, new SMTConst(`${geninfo.argc}`), larray);
            return SMTFunction.create(this.typegen.lookupFunctionName(geninfo.inv), args, this.typegen.getSMTTypeFor(geninfo.resulttype), bbody);
        }
    }

    generateSingletonConstructorMap(geninfo: { srcFile: string, sinfo: SourceInfo, inv: string, argc: number, resulttype: MIRType }): SMTFunction {
        const ldecl = this.assembly.entityDecls.get(geninfo.resulttype.typeID) as MIRPrimitiveMapEntityTypeDecl;
        const etype = ldecl.tupentrytype;
        const etuple = this.typegen.getMIRType(etype).options[0] as MIRTupleType;
        const keytype = ldecl.getTypeK();

        let args: { vname: string, vtype: SMTTypeInfo }[] = [];
        for(let j = 0; j < geninfo.argc; ++j) {
            args.push({ vname: `arg${j}`, vtype: this.typegen.getSMTTypeFor(this.typegen.getMIRType(etype)) });
        }
        
        const entrytype = this.typegen.generateMapEntryType(geninfo.resulttype);
        const entryinfo = this.typegen.generateMapEntryTypeConsInfo(geninfo.resulttype);

            let keys: SMTExp[] = [];
            let array: SMTExp = new SMTConst(`((as const (Array ${this.typegen.getSMTTypeFor(keytype).smttypename} ${entrytype.smttypename})) ${entryinfo.empty})`);
            for(let i = 0; i < geninfo.argc; ++i) {
                const ekey = new SMTCallSimple(this.typegen.generateTupleIndexGetFunction(etuple, 0), [new SMTVar(`arg${i}`)]);

                keys.push(ekey);
                array = new SMTCallSimple("store", [array, ekey, this.typegen.generateMapEntryTypeConstructorValid(geninfo.resulttype, ekey, new SMTVar(`arg${i}`))]);
            }

            let distinct = new SMTCallSimple("distinct", keys);
            let ccons = this.typegen.generateMapTypeConstructor(geninfo.resulttype, new SMTConst(`${geninfo.argc}`), array);
            
            const bbody = new SMTIf(distinct,
                this.typegen.generateResultTypeConstructorSuccess(geninfo.resulttype, ccons),
                this.typegen.generateResultTypeConstructorError(geninfo.resulttype, this.generateErrorCreateWithFile(geninfo.srcFile, geninfo.sinfo, geninfo.resulttype, "Duplicate keys in map constructor"))
            );

        return SMTFunction.create(this.typegen.lookupFunctionName(geninfo.inv), args, this.typegen.generateResultType(geninfo.resulttype), bbody);
    }

    generateUpdateTupleIndexVirtual(geninfo: { inv: string, argflowtype: MIRType, updates: [number, MIRResolvedTypeKey][], resulttype: MIRType }): SMTFunction {
        const ttuples = [...this.assembly.tupleDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].typeID);
                return this.typegen.isUniqueTupleType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getSMTTypeFor(geninfo.resulttype);
        let ops = ttuples.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.typeID);
            const test = new SMTCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

            const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
            let cargs: SMTExp[] = [];
            for (let i = 0; i < tt.entries.length; ++i) {
                const upd = geninfo.updates.findIndex((vv) => vv[0] === i);
                if(upd === undefined) {
                    cargs.push(new SMTCallSimple(this.typegen.generateTupleIndexGetFunction(tt, i), [argpp]));
                }
                else {
                    cargs.push(new SMTVar(`arg_${i}`));
                }
            }

            const action = new SMTCallSimple(this.typegen.getSMTConstructorName(geninfo.resulttype).cons, cargs);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        const fargs = [
            { vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) },
            ...geninfo.updates.map((upd, i) => {
                return { vname: `arg_${i}`, vtype: this.typegen.getSMTTypeFor(this.typegen.getMIRType(upd[1])) };
            })
        ];
        return SMTFunction.create(this.typegen.lookupFunctionName(geninfo.inv), fargs, rtype, new SMTCond(ops, orelse));
    }

    generateUpdateRecordPropertyVirtual(geninfo: { inv: string, argflowtype: MIRType, updates: [string, MIRResolvedTypeKey][], resulttype: MIRType }): SMTFunction {
        const trecords = [...this.assembly.recordDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].typeID);
                return this.typegen.isUniqueRecordType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getSMTTypeFor(geninfo.resulttype);
        let ops = trecords.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.typeID);
            const test = new SMTCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

            const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
            let cargs: SMTExp[] = [];
            for (let i = 0; i < tt.entries.length; ++i) {
                const upd = geninfo.updates.find((vv) => vv[0] === tt.entries[i].pname);
                if(upd === undefined) {
                    cargs.push(new SMTCallSimple(this.typegen.generateRecordPropertyGetFunction(tt, tt.entries[i].pname), [argpp]));
                }
                else {
                    cargs.push(new SMTVar(`arg_${i}`));
                }
            }
            const action = new SMTCallSimple(this.typegen.getSMTConstructorName(geninfo.resulttype).cons, cargs);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        const fargs = [
            { vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) },
            ...geninfo.updates.map((upd, i) => {
                return { vname: `arg_${i}`, vtype: this.typegen.getSMTTypeFor(this.typegen.getMIRType(upd[1])) };
            })
        ];
        return SMTFunction.create(this.typegen.lookupFunctionName(geninfo.inv), fargs, rtype, new SMTCond(ops, orelse));
    }

    generateUpdateEntityFieldVirtual(geninfo: { inv: string, argflowtype: MIRType, allsafe: boolean, updates: [MIRFieldKey, MIRResolvedTypeKey][], resulttype: MIRType }): SMTFunction {
        const tentities = [...this.assembly.entityDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].tkey);
                return this.typegen.isUniqueEntityType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getSMTTypeFor(geninfo.resulttype);
        let ops = tentities.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.tkey);
            const consfields = (this.assembly.entityDecls.get(tt.tkey) as MIRObjectEntityTypeDecl).consfuncfields.map((ccf) => this.assembly.fieldDecls.get(ccf.cfkey) as MIRFieldDecl);

            const test = new SMTCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

            const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
           
            let cargs: SMTExp[] = [];
            for (let i = 0; i < consfields.length; ++i) {
                const upd = geninfo.updates.find((vv) => vv[0] === consfields[i].fname);
                if(upd === undefined) {
                    cargs.push(new SMTCallSimple(this.typegen.generateEntityFieldGetFunction(tt, consfields[i]), [argpp]));
                }
                else {
                    cargs.push(new SMTVar(`arg_${i}`));
                }
            }
            
            let action: SMTExp = new SMTConst("[NOT SET]"); 
            if (this.isSafeConstructorInvoke(mtt) && geninfo.allsafe) {
                const ccall = new SMTCallSimple(this.typegen.getSMTConstructorName(mtt).cons, cargs);
                action = this.typegen.coerce(ccall, mtt, geninfo.resulttype);
            }
            else {
                if(this.isSafeConstructorInvoke(mtt)) {
                    const ccall = new SMTCallSimple(this.typegen.getSMTConstructorName(mtt).cons, cargs);
                    action = this.typegen.generateResultTypeConstructorSuccess(geninfo.resulttype, this.typegen.coerce(ccall, mtt, geninfo.resulttype));
                }
                else {
                    const consfunc = (this.assembly.entityDecls.get(tt.tkey) as MIRObjectEntityTypeDecl).consfunc;
                    const ccall = new SMTCallGeneral(this.typegen.lookupFunctionName(consfunc as MIRInvokeKey), cargs);
                    if(mtt.typeID === geninfo.resulttype.typeID) {
                        action = ccall;
                    }
                    else {
                        const tres = this.generateTempName();
                        const cond = this.typegen.generateResultIsSuccessTest(mtt, new SMTVar(tres));
                        const erropt = this.typegen.generateResultTypeConstructorError(geninfo.resulttype, this.typegen.generateResultGetError(mtt, new SMTVar(tres)));
                        const okopt =  this.typegen.generateResultTypeConstructorSuccess(geninfo.resulttype, this.typegen.coerce(this.typegen.generateResultGetSuccess(mtt, new SMTVar(tres)), mtt, geninfo.resulttype));

                        action = new SMTLet(tres, ccall, new SMTIf(cond, okopt, erropt));
                    } 
                }
            }

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        const fargs = [
            { vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) },
            ...geninfo.updates.map((upd, i) => {
                return { vname: `arg_${i}`, vtype: this.typegen.getSMTTypeFor(this.typegen.getMIRType(upd[1])) };
            })
        ];
        return SMTFunction.create(this.typegen.lookupFunctionName(geninfo.inv), fargs, rtype, new SMTCond(ops, orelse));
    }

    generateVirtualFunctionInvoke(geninfo: { inv: string, allsafe: boolean, argflowtype: MIRType, vfname: MIRVirtualMethodKey, optmask: string | undefined, resulttype: MIRType }): SMTFunction {
        const tentities = [...this.assembly.entityDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].tkey);
                return this.typegen.isUniqueEntityType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getSMTTypeFor(geninfo.resulttype);
        let ops = tentities.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.tkey);
            const vfunc = (this.assembly.entityDecls.get(tt.tkey) as MIRObjectEntityTypeDecl).vcallMap.get(geninfo.vfname) as MIRInvokeKey;
            
            const test = new SMTCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

            const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
            const invk = this.assembly.invokeDecls.get(vfunc) as MIRInvokeBodyDecl;
            const atype = this.typegen.getMIRType(invk.resultType);

            const cargs = [argpp, ...invk.params.slice(1).map((p, i) =>new SMTVar(`arg_${i}`))];

            const gcall = geninfo.optmask !== undefined ? new SMTCallGeneralWPassThroughMask(this.typegen.lookupFunctionName(vfunc), cargs, geninfo.optmask) : new SMTCallGeneral(this.typegen.lookupFunctionName(vfunc), cargs);
                
            let action: SMTExp = new SMTConst("[NOT SET]"); 
            if (this.isSafeInvoke(vfunc) && geninfo.allsafe) {
                action = this.typegen.coerce(gcall, atype, geninfo.resulttype);
            }
            else {
                if(this.isSafeInvoke(vfunc)) {
                    action = this.typegen.generateResultTypeConstructorSuccess(geninfo.resulttype, this.typegen.coerce(gcall, atype, geninfo.resulttype));
                }
                else {
                    const smtaatype = this.typegen.getSMTTypeFor(atype);
                    const smtgresult = this.typegen.getSMTTypeFor(geninfo.resulttype);
                    if(smtaatype.smttypename === smtgresult.smttypename) {
                        action = gcall;
                    }
                    else {
                        const tres = this.generateTempName();
                        const cond = this.typegen.generateResultIsSuccessTest(atype, new SMTVar(tres));
                        const erropt = this.typegen.generateResultTypeConstructorError(geninfo.resulttype, this.typegen.generateResultGetError(atype, new SMTVar(tres)));
                        const okopt =  this.typegen.generateResultTypeConstructorSuccess(geninfo.resulttype, this.typegen.coerce(this.typegen.generateResultGetSuccess(atype, new SMTVar(tres)), atype, geninfo.resulttype));

                        action = new SMTLet(tres, gcall, new SMTIf(cond, okopt, erropt));
                    } 
                }
            }

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        const sinvk = this.assembly.invokeDecls.get((this.assembly.entityDecls.get(tentities[0].tkey) as MIRObjectEntityTypeDecl).vcallMap.get(geninfo.vfname) as MIRInvokeKey) as MIRInvokeBodyDecl;
        const argtypes = sinvk.params.slice(1).map((p) => this.typegen.getSMTTypeFor(this.typegen.getMIRType(p.type)));

        const fargs = [
            { vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) },
            ...argtypes.map((vv, i) => {
                return { vname: `arg_${i}`, vtype: vv };
            })
        ];
        return SMTFunction.create(this.typegen.lookupFunctionName(geninfo.inv), fargs, rtype, new SMTCond(ops, orelse));
    }

    generateVirtualOperatorInvoke(geninfo: { inv: string, argflowtype: MIRType, opname: MIRVirtualMethodKey, args: MIRResolvedTypeKey[], resulttype: MIRType }): SMTFunction {
        //const otrgts = this.assembly.virtualOperatorDecls.get(geninfo.opname) as MIRInvokeKey[];

        return SMTFunction.create("NOT_IMPLEMENTED", [], this.typegen.getSMTTypeFor(geninfo.resulttype), NOT_IMPLEMENTED("generateVirtualOperatorInvoke"));
    }

    private generateSubtypeCheckEntity(arg: MIRArgument, layout: MIRType, flow: MIRType, ofentity: MIRType): SMTExp {
        if(flow.options.every((opt) => (opt instanceof MIRTupleType) || (opt instanceof MIRRecordType))) {
            return new SMTConst("false");
        }

        if (this.typegen.isUniqueEntityType(flow)) {
            return new SMTConst(flow.typeID === ofentity.typeID ? "true" : "false");
        }
        else {
            const smtlayout = this.typegen.getSMTTypeFor(layout);

            let consaccess: SMTExp = new SMTConst("[UNDEF]");
            if(smtlayout.isGeneralTermType()) {
                const boxcons = this.typegen.getSMTConstructorName(ofentity).box;
                consaccess = new SMTCallSimple("BTerm_termvalue", [this.argToSMT(arg)]);
                return new SMTCallSimple(`(_ is ${boxcons})`, [consaccess]);
            }
            else {
                const accessTypeTag = new SMTCallSimple("GetTypeTag@BKey", [this.argToSMT(arg)]);
                return SMTCallSimple.makeEq(accessTypeTag, new SMTConst(`TypeTag_${this.typegen.lookupTypeName(ofentity.typeID)}`));
            }
        }
    }

    private generateSubtypeCheckConcept(arg: MIRArgument, layout: MIRType, flow: MIRType, ofconcept: MIRType): SMTExp {
        if (this.typegen.isUniqueEntityType(flow) || this.typegen.isUniqueTupleType(flow) || this.typegen.isUniqueRecordType(flow)) {
            return new SMTConst(this.assembly.subtypeOf(flow, ofconcept) ? "true" : "false");
        }
        else {
            const accessTypeTag = this.typegen.getSMTTypeFor(layout).isGeneralTermType() ? new SMTCallSimple("GetTypeTag@BTerm", [this.argToSMT(arg)]) : new SMTCallSimple("GetTypeTag@BKey", [this.argToSMT(arg)]);
            
            const occ = ofconcept.options[0] as MIRConceptType;
            let tests: SMTExp[] = [];
            for(let i = 0; i < occ.ckeys.length; ++i) {
                this.processSubtypeTagCheck(flow, ofconcept);
                tests.push(new SMTCallSimple("SubtypeOf@", [accessTypeTag, new SMTConst(`AbstractTypeTag_${this.typegen.lookupTypeName(occ.ckeys[i])}`)]));
            }

            if(tests.length === 1) {
                return tests[0];
            }
            else {
                return SMTCallSimple.makeAndOf(...tests);
            }
        }
    }

    private generateSubtypeCheckTuple(arg: MIRArgument, layout: MIRType, flow: MIRType, oftuple: MIRType): SMTExp {
        if(flow.options.every((opt) => (opt instanceof MIREntityType) || (opt instanceof MIRRecordType))) {
            return new SMTConst("false");
        }

        if (this.typegen.isUniqueTupleType(flow)) {
            return new SMTConst(this.assembly.subtypeOf(flow, oftuple) ? "true" : "false");
        }
        else {
            const boxcons = this.typegen.getSMTConstructorName(oftuple).box;
            const consaccess = new SMTCallSimple("BTerm_termvalue", [this.argToSMT(arg)]);
            return new SMTCallSimple(`(_ is ${boxcons})`, [consaccess]);
        }
    }

    private generateSubtypeCheckRecord(arg: MIRArgument, layout: MIRType, flow: MIRType, ofrecord: MIRType): SMTExp {
        if(flow.options.every((opt) => (opt instanceof MIREntityType) || (opt instanceof MIRTupleType))) {
            return new SMTConst("false");
        }

        if (this.typegen.isUniqueRecordType(flow)) {
            return new SMTConst(this.assembly.subtypeOf(flow, ofrecord) ? "true" : "false");
        }
        else {
            const boxcons = this.typegen.getSMTConstructorName(ofrecord).box;
            const consaccess = new SMTCallSimple("BTerm_termvalue", [this.argToSMT(arg)]);
            return new SMTCallSimple(`(_ is ${boxcons})`, [consaccess]);
        }
    }

    constructor(assembly: MIRAssembly, typegen: SMTTypeEmitter, vopts: VerifierOptions, callsafety: Map<MIRInvokeKey, { safe: boolean, trgt: boolean }>, errorTrgtPos: { file: string, line: number, pos: number }) {
        this.assembly = assembly;
        this.typegen = typegen;
        this.callsafety = callsafety;

        this.errorTrgtPos = errorTrgtPos;
        this.allErrors = [];
        this.vopts = vopts;

        this.currentRType = typegen.getMIRType("None");

        const safecalls = new Set<MIRInvokeKey>();
        callsafety.forEach((pv, inv) => {
            if(pv.safe) {
                safecalls.add(inv);
            }
        });
    }

    generateTempName(): string {
        return `_@tmpvar@${this.tmpvarctr++}`;
    }

    generateErrorCreate(sinfo: SourceInfo, rtype: MIRType, msg: string): SMTExp {
        if (this.allErrors.find((vv) => this.currentFile === vv.file && sinfo.pos === vv.pos) === undefined) {
            this.allErrors.push({ file: this.currentFile, line: sinfo.line, pos: sinfo.pos, msg: msg });
        }

        if(this.currentFile === this.errorTrgtPos.file && sinfo.pos === this.errorTrgtPos.pos) {
            return this.typegen.generateResultTypeConstructorError(rtype, new SMTConst("ErrorID_Target"));
        }
        else {
            return this.typegen.generateResultTypeConstructorError(rtype, new SMTConst("ErrorID_AssumeCheck"));
        }
    }

    generateErrorCreateWithFile(srcFile: string, sinfo: SourceInfo, rtype: MIRType, msg: string): SMTExp {
        if (this.allErrors.find((vv) => srcFile === vv.file && sinfo.pos === vv.pos) === undefined) {
            this.allErrors.push({ file: srcFile, line: sinfo.line, pos: sinfo.pos, msg: msg });
        }

        if(srcFile === this.errorTrgtPos.file && sinfo.pos === this.errorTrgtPos.pos) {
            return this.typegen.generateResultTypeConstructorError(rtype, new SMTConst("ErrorID_Target"));
        }
        else {
            return this.typegen.generateResultTypeConstructorError(rtype, new SMTConst("ErrorID_AssumeCheck"));
        }
    }

    isSafeInvoke(mkey: MIRInvokeKey): boolean {
        const idecl = (this.assembly.invokeDecls.get(mkey) || this.assembly.primitiveInvokeDecls.get(mkey)) as MIRInvokeDecl;
        if(idecl.attributes.includes("__safe") || idecl.attributes.includes("__assume_safe")) {
            return true;
        }
        else {
            const csi = this.callsafety.get(mkey);
            return csi !== undefined && csi.safe;
        }
    }

    isSafeVirtualInvoke(vkey: MIRVirtualMethodKey, rcvrtype: MIRType): boolean {
        return [...this.assembly.entityDecls]
        .filter((tt) => {
            const mtt = this.typegen.getMIRType(tt[1].tkey);
            return this.typegen.isUniqueEntityType(mtt) && this.assembly.subtypeOf(mtt, rcvrtype);
        })
        .every((edcl) => {
            return this.isSafeInvoke((this.assembly.entityDecls.get(edcl[1].tkey) as MIRObjectEntityTypeDecl).vcallMap.get(vkey) as MIRInvokeKey);
        });
    }

    isSafeConstructorInvoke(oftype: MIRType): boolean {
        const edecl = this.assembly.entityDecls.get(oftype.typeID) as MIREntityTypeDecl;
        if(edecl instanceof MIRConstructableEntityTypeDecl) {
            const cname = edecl.usingcons as MIRInvokeKey;
            return this.isSafeInvoke(cname);
        }
        else {
            const cname = (edecl as MIRObjectEntityTypeDecl).consfunc as MIRInvokeKey;
            return this.isSafeInvoke(cname);
        }
    }

    isSafeVirtualConstructorInvoke(oftypes: MIRType): boolean {
        return [...this.assembly.entityDecls]
        .filter((tt) => {
            const mtt = this.typegen.getMIRType(tt[1].tkey);
            return this.typegen.isUniqueEntityType(mtt) && this.assembly.subtypeOf(mtt, oftypes);
        })
        .every((edcl) => {
            return this.isSafeConstructorInvoke(this.typegen.getMIRType(edcl[0]));
        });
    }

    constantToSMT(cval: MIRConstantArgument): SMTExp {
        if (cval instanceof MIRConstantNone) {
            return new SMTConst("bsq_none@literal");
        }
        else if (cval instanceof MIRConstantNothing) {
            return new SMTConst("bsq_nothing@literal");
        }
        else if (cval instanceof MIRConstantTrue) {
            return new SMTConst("true");
        }
        else if (cval instanceof MIRConstantFalse) {
            return new SMTConst("false");
        }
        else if (cval instanceof MIRConstantInt) {
            return new SMTConst(cval.value.slice(0, cval.value.length - 1));
        }
        else if (cval instanceof MIRConstantNat) {
            return new SMTConst(cval.value.slice(0, cval.value.length - 1));
        }
        else if (cval instanceof MIRConstantBigInt) {
            return new SMTConst(cval.value.slice(0, cval.value.length - 1));
        }
        else if (cval instanceof MIRConstantBigNat) {
            return new SMTConst(cval.value.slice(0, cval.value.length - 1));
        }
        else if (cval instanceof MIRConstantRational) {
            if(/^0\/[0-9]+R$/.test(cval.value)) {
                return new SMTConst("BRational@zero");
            }
            else if(/^1\/1R$/.test(cval.value)) {
                return new SMTConst("BRational@one");
            }
            else {
                return NOT_IMPLEMENTED("BRational mixed");
            }
        }
        else if (cval instanceof MIRConstantFloat) {
            if(/^0([.]0+)?f$/.test(cval.value)) {
                return new SMTConst("BFloat@zero");
            }
            else if(/^1([.]0+)?f$/.test(cval.value)) {
                return new SMTConst("BFloat@one");
            }
            else {
                const fval = cval.value.slice(0, cval.value.length - 1);
                return new SMTConst(fval.includes(".") ? fval : (fval + ".0"));
            }
        }
        else if (cval instanceof MIRConstantDecimal) {
            if(/^0([.]0+)?d$/.test(cval.value)) {
                return new SMTConst("BDecimal@zero");
            }
            else if(/^1([.]0+)?d$/.test(cval.value)) {
                return new SMTConst("BDecimal@one");
            }
            else {
                const dval = cval.value.slice(0, cval.value.length - 1);
                return new SMTConst(dval.includes(".") ? dval : (dval + ".0"));
            }
        }
        else if (cval instanceof MIRConstantString) {
            return new SMTConst(cval.value);
        }
        else if (cval instanceof MIRConstantTypedNumber) {
            return this.constantToSMT(cval.value);
        }
        else if (cval instanceof MIRConstantStringOf) {
            return new SMTConst("\"" + cval.value.slice(1, cval.value.length - 1) + "\"");
        }
        else if (cval instanceof MIRConstantDataString) {
            return new SMTConst("\"" + cval.value.slice(1, cval.value.length - 1) + "\"");
        }
        else {
            assert(cval instanceof MIRConstantRegex);

            const rval = (cval as MIRConstantRegex).value;
            const ere = this.assembly.literalRegexs.findIndex((re) => re.restr === rval.restr);

            return new SMTCallSimple("bsq_regex@cons", [new SMTConst(`${ere}`)]);
        }
    }

    argToSMT(arg: MIRArgument): SMTExp {
        if (arg instanceof MIRRegisterArgument) {
            return this.varToSMTName(arg);
        }
        else if(arg instanceof MIRGlobalVariable) {
            return this.globalToSMT(arg);
        }
        else {
            return this.constantToSMT(arg as MIRConstantArgument);
        }
    }

    generateNoneCheck(arg: MIRArgument, argtype: MIRType): SMTExp {
        if (this.typegen.isType(argtype, "None")) {
            return new SMTConst("true");
        }
        else if (!this.assembly.subtypeOf(this.typegen.getMIRType("None"), argtype)) {
            return new SMTConst("false");
        }
        else {
            const trepr = this.typegen.getSMTTypeFor(argtype);
            if(trepr.isGeneralKeyType()) {
                return SMTCallSimple.makeEq(this.argToSMT(arg), new SMTConst("BKey@none"));
            }
            else {
                return SMTCallSimple.makeEq(this.argToSMT(arg), new SMTConst("BTerm@none"));
            }
        }
    }

    generateSomeCheck(arg: MIRArgument, argtype: MIRType): SMTExp {
        if (this.typegen.isType(argtype, "None")) {
            return new SMTConst("false");
        }
        else if (!this.assembly.subtypeOf(this.typegen.getMIRType("None"), argtype)) {
            return new SMTConst("true");
        }
        else {
            const trepr = this.typegen.getSMTTypeFor(argtype);
            if(trepr.isGeneralKeyType()) {
                return SMTCallSimple.makeNotEq(this.argToSMT(arg), new SMTConst("BKey@none"));
            }
            else {
                return SMTCallSimple.makeNotEq(this.argToSMT(arg), new SMTConst("BTerm@none"));
            }
        }
    }
    
    generateNothingCheck(arg: MIRArgument, argtype: MIRType): SMTExp {
        if (this.typegen.isType(argtype, "Nothing")) {
            return new SMTConst("true");
        }
        else if (!this.assembly.subtypeOf(this.typegen.getMIRType("Nothing"), argtype)) {
            return new SMTConst("false");
        }
        else {
            const trepr = this.typegen.getSMTTypeFor(argtype);
            if(trepr.isGeneralKeyType()) {
                return SMTCallSimple.makeEq(this.argToSMT(arg), new SMTConst("BKey@nothing"));
            }
            else {
                return SMTCallSimple.makeEq(this.argToSMT(arg), new SMTConst("BTerm@nothing"));
            }
        }
    }

    processAbort(op: MIRAbort): SMTExp {
        return this.generateErrorCreate(op.sinfo, this.currentRType, op.info);
    }

    processAssertCheck(op: MIRAssertCheck, continuation: SMTExp): SMTExp {
        const chkval = this.argToSMT(op.arg);
        const errorval = this.generateErrorCreate(op.sinfo, this.currentRType, op.info);
        
        return new SMTIf(chkval, continuation, errorval);
    }

    processLoadUnintVariableValue(op: MIRLoadUnintVariableValue, continuation: SMTExp): SMTExp {
        const ufcname = this.generateUFConstantForType(this.typegen.getMIRType(op.oftype));

        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTConst(ufcname), continuation);
    }

    processDeclareGuardFlagLocation(op: MIRDeclareGuardFlagLocation) {
        this.maskSizes.add(op.count);
        this.pendingMask = this.pendingMask.filter((pm) => pm.maskname !== op.name);
    }

    processSetConstantGuardFlag(op: MIRSetConstantGuardFlag) {
        const pm = this.pendingMask.find((mm) => mm.maskname === op.name) as SMTMaskConstruct;
        pm.entries[op.position] = new SMTConst(op.flag ? "true" : "false");
    }

    processConvertValue(op: MIRConvertValue, continuation: SMTExp): SMTExp {
        const conv = this.typegen.coerce(this.argToSMT(op.src), this.typegen.getMIRType(op.srctypelayout), this.typegen.getMIRType(op.intotype));
        const call = this.generateGuardStmtCond(op.sguard, conv, op.intotype);

        return new SMTLet(this.varToSMTName(op.trgt).vname, call, continuation);
    }

    processInject(op: MIRInject, continuation: SMTExp): SMTExp {
        return new SMTLet(this.varToSMTName(op.trgt).vname, this.argToSMT(op.src), continuation);
    }

    processGuardedOptionInject(op: MIRGuardedOptionInject, continuation: SMTExp): SMTExp {
        const conv = this.typegen.coerce(this.argToSMT(op.src), this.typegen.getMIRType(op.somethingtype), this.typegen.getMIRType(op.optiontype));
        const call = this.generateGuardStmtCond(op.sguard, conv, op.optiontype);

        return new SMTLet(this.varToSMTName(op.trgt).vname, call, continuation);
    }

    processExtract(op: MIRExtract, continuation: SMTExp): SMTExp {
        return new SMTLet(this.varToSMTName(op.trgt).vname, this.argToSMT(op.src), continuation);
    }

    processLoadConst(op: MIRLoadConst, continuation: SMTExp): SMTExp {
        return new SMTLet(this.varToSMTName(op.trgt).vname, this.argToSMT(op.src), continuation);
    }

    processTupleHasIndex(op: MIRTupleHasIndex, continuation: SMTExp): SMTExp {
        const argtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(op.arglayouttype));

        this.processIndexTagCheck(op.idx, this.typegen.getMIRType(op.argflowtype));
        const accessTypeTag = argtype.isGeneralTermType() ? new SMTCallSimple("GetTypeTag@BTerm", [this.argToSMT(op.arg)]) : new SMTCallSimple("GetTypeTag@BKey", [this.argToSMT(op.arg)]);
        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple("HasIndex@", [accessTypeTag, new SMTConst(`TupleIndexTag_${op.idx}`)]), continuation);
    }

    processRecordHasProperty(op: MIRRecordHasProperty, continuation: SMTExp): SMTExp {
        const argtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(op.arglayouttype));

        this.processPropertyTagCheck(op.pname, this.typegen.getMIRType(op.argflowtype));
        const accessTypeTag = argtype.isGeneralTermType() ? new SMTCallSimple("GetTypeTag@BTerm", [this.argToSMT(op.arg)]) : new SMTCallSimple("GetTypeTag@BKey", [this.argToSMT(op.arg)]);
        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple("HasProperty@", [accessTypeTag, new SMTConst(`RecordPropertyTag_${op.pname}`)]), continuation);
    }

    processLoadTupleIndex(op: MIRLoadTupleIndex, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateLoadVirtualTupleInvName(this.typegen.getMIRType(op.argflowtype), op.idx, this.typegen.getMIRType(op.resulttype), undefined);
            if(this.requiredLoadVirtualTupleIndex.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), idx: op.idx, resulttype: this.typegen.getMIRType(op.resulttype), guard: undefined };
                this.requiredLoadVirtualTupleIndex.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.lookupFunctionName(icall), [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const idxr = new SMTCallSimple(this.typegen.generateTupleIndexGetFunction(argflowtype.options[0] as MIRTupleType, op.idx), [argpp]);
            return new SMTLet(this.varToSMTName(op.trgt).vname, idxr, continuation);
        }
    }

    processLoadTupleIndexSetGuard(op: MIRLoadTupleIndexSetGuard, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateLoadVirtualTupleInvName(this.typegen.getMIRType(op.argflowtype), op.idx, this.typegen.getMIRType(op.resulttype), op.guard);
            if(this.requiredLoadVirtualTupleIndex.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), idx: op.idx, resulttype: this.typegen.getMIRType(op.resulttype), guard: op.guard };
                this.requiredLoadVirtualTupleIndex.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const cc = new SMTCallSimple(this.typegen.lookupFunctionName(icall), [argpp]);

            const callbind = this.generateTempName();
            const smtcallvar = new SMTVar(callbind);
            let ncont: SMTExp = new SMTConst("[UNDEF]");

            if(op.guard instanceof MIRMaskGuard) {
                const pm = this.pendingMask.find((mm) => mm.maskname === (op.guard as MIRMaskGuard).gmask) as SMTMaskConstruct;
                pm.entries[(op.guard as MIRMaskGuard).gindex] = this.typegen.generateAccessWithSetGuardResultGetFlag(this.typegen.getMIRType(op.resulttype), smtcallvar);

                ncont = new SMTLet(this.varToSMTName(op.trgt).vname, this.typegen.generateAccessWithSetGuardResultGetValue(this.typegen.getMIRType(op.resulttype), smtcallvar), continuation);
            }
            else {
                ncont = new SMTLetMulti([
                    { vname: this.varToSMTName((op.guard as MIRArgGuard).greg as MIRRegisterArgument).vname, value: this.typegen.generateAccessWithSetGuardResultGetFlag(this.typegen.getMIRType(op.resulttype), smtcallvar) },
                    { vname: this.varToSMTName(op.trgt).vname, value: this.typegen.generateAccessWithSetGuardResultGetValue(this.typegen.getMIRType(op.resulttype), smtcallvar) }
                ], continuation);
            }

            return new SMTLet(callbind, cc, ncont);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const idxr = new SMTCallSimple(this.typegen.generateTupleIndexGetFunction(argflowtype.options[0] as MIRTupleType, op.idx), [argpp]);

            if(op.guard instanceof MIRMaskGuard) {
                const pm = this.pendingMask.find((mm) => mm.maskname === (op.guard as MIRMaskGuard).gmask) as SMTMaskConstruct;
                pm.entries[(op.guard as MIRMaskGuard).gindex] = new SMTConst("true");

                return new SMTLet(this.varToSMTName(op.trgt).vname, idxr, continuation);
            }
            else {
                return new SMTLetMulti([
                    { vname: this.varToSMTName((op.guard as MIRArgGuard).greg as MIRRegisterArgument).vname, value: new SMTConst("true") },
                    { vname: this.varToSMTName(op.trgt).vname, value: idxr }
                ], continuation);
            }
        }
    }

    processLoadRecordProperty(op: MIRLoadRecordProperty, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateLoadVirtualPropertyInvName(this.typegen.getMIRType(op.argflowtype), op.pname, this.typegen.getMIRType(op.resulttype), undefined);
            if(this.requiredLoadVirtualRecordProperty.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), pname: op.pname, resulttype: this.typegen.getMIRType(op.resulttype), guard: undefined };
                this.requiredLoadVirtualRecordProperty.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.lookupFunctionName(icall), [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const idxr = new SMTCallSimple(this.typegen.generateRecordPropertyGetFunction(argflowtype.options[0] as MIRRecordType, op.pname), [argpp]);
            return new SMTLet(this.varToSMTName(op.trgt).vname, idxr, continuation);
        }
    }

    processLoadRecordPropertySetGuard(op: MIRLoadRecordPropertySetGuard, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateLoadVirtualPropertyInvName(this.typegen.getMIRType(op.argflowtype), op.pname, this.typegen.getMIRType(op.resulttype), op.guard);
            if(this.requiredLoadVirtualRecordProperty.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), pname: op.pname, resulttype: this.typegen.getMIRType(op.resulttype), guard: op.guard };
                this.requiredLoadVirtualRecordProperty.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const cc = new SMTCallSimple(this.typegen.lookupFunctionName(icall), [argpp]);

            const callbind = this.generateTempName();
            const smtcallvar = new SMTVar(callbind);
            let ncont: SMTExp = new SMTConst("[UNDEF]");

            if(op.guard instanceof MIRMaskGuard) {
                const pm = this.pendingMask.find((mm) => mm.maskname === (op.guard as MIRMaskGuard).gmask) as SMTMaskConstruct;
                pm.entries[(op.guard as MIRMaskGuard).gindex] = this.typegen.generateAccessWithSetGuardResultGetFlag(this.typegen.getMIRType(op.resulttype), smtcallvar);

                ncont = new SMTLet(this.varToSMTName(op.trgt).vname, this.typegen.generateAccessWithSetGuardResultGetValue(this.typegen.getMIRType(op.resulttype), smtcallvar), continuation);
            }
            else {
                ncont = new SMTLetMulti([
                    { vname: this.varToSMTName((op.guard as MIRArgGuard).greg as MIRRegisterArgument).vname, value: this.typegen.generateAccessWithSetGuardResultGetFlag(this.typegen.getMIRType(op.resulttype), smtcallvar) },
                    { vname: this.varToSMTName(op.trgt).vname, value: this.typegen.generateAccessWithSetGuardResultGetValue(this.typegen.getMIRType(op.resulttype), smtcallvar) }
                ], continuation);
            }

            return new SMTLet(callbind, cc, ncont);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const idxr = new SMTCallSimple(this.typegen.generateRecordPropertyGetFunction(argflowtype.options[0] as MIRRecordType, op.pname), [argpp]);
            
            if(op.guard instanceof MIRMaskGuard) {
                const pm = this.pendingMask.find((mm) => mm.maskname === (op.guard as MIRMaskGuard).gmask) as SMTMaskConstruct;
                pm.entries[(op.guard as MIRMaskGuard).gindex] = new SMTConst("true");

                return new SMTLet(this.varToSMTName(op.trgt).vname, idxr, continuation);
            }
            else {
                return new SMTLetMulti([
                    { vname: this.varToSMTName((op.guard as MIRArgGuard).greg as MIRRegisterArgument).vname, value: new SMTConst("true") },
                    { vname: this.varToSMTName(op.trgt).vname, value: idxr }
                ], continuation);
            }
        }
    }

    processLoadField(op: MIRLoadField, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateLoadVirtualFieldInvName(this.typegen.getMIRType(op.argflowtype), op.field, this.typegen.getMIRType(op.resulttype));
            if(this.requiredLoadVirtualEntityField.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), field: this.assembly.fieldDecls.get(op.field) as MIRFieldDecl, resulttype: this.typegen.getMIRType(op.resulttype) };
                this.requiredLoadVirtualEntityField.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.lookupFunctionName(icall), [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const fdecl = this.assembly.fieldDecls.get(op.field) as MIRFieldDecl;
            const idxr = new SMTCallSimple(this.typegen.generateEntityFieldGetFunction(this.assembly.entityDecls.get(argflowtype.typeID) as MIREntityTypeDecl, fdecl), [argpp]);
            return new SMTLet(this.varToSMTName(op.trgt).vname, idxr, continuation);
        }
    }

    processTupleProjectToEphemeral(op: MIRTupleProjectToEphemeral, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.epht);

        if(op.isvirtual) {
            const icall = this.generateProjectVirtualTupleInvName(this.typegen.getMIRType(op.argflowtype), op.indecies, resulttype);
            if(this.requiredProjectVirtualTupleIndex.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), indecies: op.indecies, resulttype: resulttype };
                this.requiredProjectVirtualTupleIndex.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.lookupFunctionName(icall), [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const pargs = op.indecies.map((idx, i) => {
                const idxr = new SMTCallSimple(this.typegen.generateTupleIndexGetFunction(argflowtype.options[0] as MIRTupleType, idx), [argpp]);
                return this.typegen.coerce(idxr, (argflowtype.options[0] as MIRTupleType).entries[idx], (resulttype.options[0] as MIREphemeralListType).entries[i]);
            });

            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.getSMTConstructorName(resulttype).cons, pargs), continuation);
        }
    }

    processRecordProjectToEphemeral(op: MIRRecordProjectToEphemeral, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.epht);

        if(op.isvirtual) {
            const icall = this.generateProjectVirtualRecordInvName(this.typegen.getMIRType(op.argflowtype), op.properties, resulttype);
            if(this.requiredProjectVirtualRecordProperty.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), properties: op.properties, resulttype: resulttype };
                this.requiredProjectVirtualRecordProperty.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.lookupFunctionName(icall), [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const pargs = op.properties.map((pname, i) => {
                const idxr = new SMTCallSimple(this.typegen.generateRecordPropertyGetFunction(argflowtype.options[0] as MIRRecordType, pname), [argpp]);
                return this.typegen.coerce(idxr, ((argflowtype.options[0] as MIRRecordType).entries.find((vv) => vv.pname === pname) as {pname: string, ptype: MIRType}).ptype, (resulttype.options[0] as MIREphemeralListType).entries[i]);
            });

            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.getSMTConstructorName(resulttype).cons, pargs), continuation);
        }
    }

    processEntityProjectToEphemeral(op: MIREntityProjectToEphemeral, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.epht);

        if(op.isvirtual) {
            const icall = this.generateProjectVirtualEntityInvName(this.typegen.getMIRType(op.argflowtype), op.fields, resulttype);
            if(this.requiredProjectVirtualEntityField.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), fields: op.fields.map((fkey) => this.assembly.fieldDecls.get(fkey) as MIRFieldDecl), resulttype: resulttype };
                this.requiredProjectVirtualEntityField.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.lookupFunctionName(icall), [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const pargs = op.fields.map((fkey, i) => {
                const fdecl = this.assembly.fieldDecls.get(fkey) as MIRFieldDecl;
                const idxr = new SMTCallSimple(this.typegen.generateEntityFieldGetFunction(this.assembly.entityDecls.get(argflowtype.typeID) as MIREntityTypeDecl, fdecl), [argpp]);
                return this.typegen.coerce(idxr, this.typegen.getMIRType((this.assembly.fieldDecls.get(fkey) as MIRFieldDecl).declaredType), (resulttype.options[0] as MIREphemeralListType).entries[i]);
            });

            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.getSMTConstructorName(resulttype).cons, pargs), continuation);
        }
    }

    processTupleUpdate(op: MIRTupleUpdate, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateUpdateVirtualTupleInvName(this.typegen.getMIRType(op.argflowtype), op.updates.map((upd) => [upd[0], upd[2]]), resulttype);
            if(this.requiredUpdateVirtualTuple.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), updates: op.updates.map((upd) => [upd[0], upd[2]] as [number, MIRResolvedTypeKey]), resulttype: resulttype };
                this.requiredUpdateVirtualTuple.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.lookupFunctionName(icall), [argpp]), continuation);
        }
        else {
            const ttype = argflowtype.options[0] as MIRTupleType;

            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            let cargs: SMTExp[] = [];
            for (let i = 0; i < ttype.entries.length; ++i) {
                const upd = op.updates.find((vv) => vv[0] === i);
                if(upd === undefined) {
                    cargs.push(new SMTCallSimple(this.typegen.generateTupleIndexGetFunction(ttype, i), [argpp]));
                }
                else {
                    cargs.push(this.argToSMT(upd[1]));
                }
            }

            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.getSMTConstructorName(resulttype).cons, cargs), continuation);
        }
    }

    processRecordUpdate(op: MIRRecordUpdate, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateUpdateVirtualRecordInvName(this.typegen.getMIRType(op.argflowtype), op.updates.map((upd) => [upd[0], upd[2]]), resulttype);
            if(this.requiredUpdateVirtualRecord.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), updates: op.updates.map((upd) => [upd[0], upd[2]] as [string, MIRResolvedTypeKey]), resulttype: resulttype };
                this.requiredUpdateVirtualRecord.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.lookupFunctionName(icall), [argpp]), continuation);
        }
        else {
            const ttype = argflowtype.options[0] as MIRRecordType;

            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            let cargs: SMTExp[] = [];
            for (let i = 0; i < ttype.entries.length; ++i) {
                const upd = op.updates.find((vv) => vv[0] === ttype.entries[i].pname);
                if(upd === undefined) {
                    cargs.push(new SMTCallSimple(this.typegen.generateRecordPropertyGetFunction(ttype, ttype.entries[i].pname), [argpp]));
                }
                else {
                    cargs.push(this.argToSMT(upd[1]));
                }
            }

            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.getSMTConstructorName(resulttype).cons, cargs), continuation);
        }
    }

    processEntityUpdate(op: MIREntityUpdate, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.argflowtype);

        if (op.isvirtual) {
            const allsafe = this.isSafeVirtualConstructorInvoke(argflowtype);
            const icall = this.generateUpdateVirtualEntityInvName(this.typegen.getMIRType(op.argflowtype), op.updates.map((upd) => [upd[0], upd[2]]), resulttype);

            if (this.requiredUpdateVirtualEntity.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), allsafe: allsafe, updates: op.updates.map((upd) => [upd[0], upd[2]] as [MIRFieldKey, MIRResolvedTypeKey]), resulttype: resulttype };
                this.requiredUpdateVirtualEntity.push(geninfo);
            }

            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            if (allsafe) {
                return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.lookupFunctionName(icall), [argpp]), continuation);
            }
            else {
                return this.generateGeneralCallValueProcessing(this.currentRType, resulttype, new SMTCallGeneral(this.typegen.lookupFunctionName(icall), [argpp]), op.trgt, continuation);
            }
        }
        else {
            const ttype = argflowtype.options[0] as MIREntityType;
            const ttdecl = this.assembly.entityDecls.get(ttype.typeID) as MIRObjectEntityTypeDecl;
            const consfunc = ttdecl.consfunc;
            const consfields = ttdecl.consfuncfields.map((ccf) => this.assembly.fieldDecls.get(ccf.cfkey) as MIRFieldDecl);

            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            let cargs: SMTExp[] = [];
            for (let i = 0; i < consfields.length; ++i) {
                const upd = op.updates.find((vv) => vv[0] === consfields[i].fkey);
                if (upd === undefined) {
                    cargs.push(new SMTCallSimple(this.typegen.generateEntityFieldGetFunction(ttdecl, consfields[i]), [argpp]));
                }
                else {
                    cargs.push(this.argToSMT(upd[1]));
                }
            }

            if (this.isSafeConstructorInvoke(argflowtype)) {
                const ccall = new SMTCallSimple(this.typegen.getSMTConstructorName(argflowtype).cons, cargs);
                return new SMTLet(this.varToSMTName(op.trgt).vname, ccall, continuation);
            }
            else {
                const ccall = new SMTCallGeneral(this.typegen.lookupFunctionName(consfunc as MIRInvokeKey), cargs);
                return this.generateGeneralCallValueProcessing(this.currentRType, resulttype, ccall, op.trgt, continuation);
            }
        }
    }

    processLoadFromEpehmeralList(op: MIRLoadFromEpehmeralList, continuation: SMTExp): SMTExp {
        const argtype = this.typegen.getMIRType(op.argtype);

        const idxr = new SMTCallSimple(this.typegen.generateEphemeralListGetFunction(argtype.options[0] as MIREphemeralListType, op.idx), [this.argToSMT(op.arg)]);
        return new SMTLet(this.varToSMTName(op.trgt).vname, idxr, continuation);
    }

    processMultiLoadFromEpehmeralList(op: MIRMultiLoadFromEpehmeralList, continuation: SMTExp): SMTExp {
        const eltype = this.typegen.getMIRType(op.argtype).options[0] as MIREphemeralListType;

        const assigns = op.trgts.map((asgn) => {
            const idxr = new SMTCallSimple(this.typegen.generateEphemeralListGetFunction(eltype, asgn.pos), [this.argToSMT(op.arg)]);
            return { vname: this.varToSMTName(asgn.into).vname, value: idxr };
        });

        return new SMTLetMulti(assigns, continuation);
    }

    processSliceEpehmeralList(op: MIRSliceEpehmeralList, continuation: SMTExp): SMTExp {
        const eltype = this.typegen.getMIRType(op.argtype).options[0] as MIREphemeralListType;
        const sltype = this.typegen.getMIRType(op.sltype).options[0] as MIREphemeralListType;

        const pargs = sltype.entries.map((sle, i) => new SMTCallSimple(this.typegen.generateEphemeralListGetFunction(eltype, i), [this.argToSMT(op.arg)]));
        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.sltype)).cons, pargs), continuation);
    }

    processInvokeFixedFunction(op: MIRInvokeFixedFunction, continuation: SMTExp): SMTExp {
        const invk = (this.assembly.invokeDecls.get(op.mkey) || this.assembly.primitiveInvokeDecls.get(op.mkey)) as MIRInvokeDecl;
        const rtype = this.typegen.getMIRType(invk.resultType);

        if(invk instanceof MIRInvokePrimitiveDecl && invk.implkey === "default") {
            assert(op.sguard === undefined && op.optmask === undefined);

            const args = op.args.map((arg) => this.argToSMT(arg));
            return this.processDefaultOperatorInvokePrimitiveType(op.sinfo, op.trgt, op.mkey, args, continuation);
        }
        else {
            let mask: SMTMaskConstruct | undefined = undefined;
            if (op.optmask !== undefined) {
                mask = new SMTMaskConstruct(op.optmask);
                this.pendingMask.push(mask);
            }

            const args = op.args.map((arg) => this.argToSMT(arg));
            const call = mask !== undefined ? new SMTCallGeneralWOptMask(this.typegen.lookupFunctionName(op.mkey), args, mask) : new SMTCallGeneral(this.typegen.lookupFunctionName(op.mkey), args);
            const gcall = this.generateGuardStmtCond(op.sguard, call, invk.resultType);

            if (this.isSafeInvoke(op.mkey)) {
                return new SMTLet(this.varToSMTName(op.trgt).vname, gcall, continuation);
            }
            else {
                return this.generateGeneralCallValueProcessing(this.currentRType, rtype, gcall, op.trgt, continuation);
            }
        }
    }

    processInvokeVirtualFunction(op: MIRInvokeVirtualFunction, continuation: SMTExp): SMTExp {
        const rcvrlayouttype = this.typegen.getMIRType(op.rcvrlayouttype);
        const rcvrflowtype = this.typegen.getMIRType(op.rcvrflowtype);
        const resulttype = this.typegen.getMIRType(op.resultType);

        const allsafe = this.isSafeVirtualInvoke(op.vresolve, rcvrflowtype);
        const icall = this.generateVirtualInvokeFunctionName(rcvrflowtype, op.vresolve, op.shortname, op.optmask !== undefined, resulttype);
        if(this.requiredVirtualFunctionInvokes.findIndex((vv) => vv.inv === icall) === -1) {
            const geninfo = { inv: icall, allsafe: allsafe, argflowtype: rcvrflowtype, vfname: op.vresolve, optmask: op.optmask, resulttype: resulttype };
            this.requiredVirtualFunctionInvokes.push(geninfo);
        }

        let mask: SMTMaskConstruct | undefined = undefined;
        if (op.optmask !== undefined) {
            mask = new SMTMaskConstruct(op.optmask);
            this.pendingMask.push(mask);
        }
            
        const argpp = this.typegen.coerce(this.argToSMT(op.args[0]), rcvrlayouttype, rcvrflowtype);
        const args = [argpp, ...op.args.slice(1).map((arg) => this.argToSMT(arg))];
        const call = mask !== undefined ? new SMTCallGeneralWOptMask(this.typegen.lookupFunctionName(icall), args, mask) : new SMTCallGeneral(this.typegen.lookupFunctionName(icall), args);    

        if(allsafe) {
            return new SMTLet(this.varToSMTName(op.trgt).vname, call, continuation);
        }
        else {
            return this.generateGeneralCallValueProcessing(this.currentRType, resulttype, call, op.trgt, continuation);
        }
    }

    processInvokeVirtualOperator(op: MIRInvokeVirtualOperator, continuation: SMTExp): SMTExp {
        const resulttype = this.typegen.getMIRType(op.resultType);

        //TODO: also need all operator safe here 
        const iop = this.generateVirtualInvokeOperatorName(op.vresolve, op.shortname, op.args.map((arg) => arg.argflowtype), resulttype);
        if(this.requiredVirtualOperatorInvokes.findIndex((vv) => vv.inv === iop) === -1) {
            assert(false);
        }

        return NOT_IMPLEMENTED("processInvokeVirtualOperator");
    }

    processConstructorTuple(op: MIRConstructorTuple, continuation: SMTExp): SMTExp {
        const args = op.args.map((arg) => this.argToSMT(arg));

        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultTupleType)).cons, args), continuation);
    }

    processConstructorTupleFromEphemeralList(op: MIRConstructorTupleFromEphemeralList, continuation: SMTExp): SMTExp {
        const elt = this.typegen.getMIRType(op.elistType).options[0] as MIREphemeralListType;
        const args = elt.entries.map((tt, i) => new SMTCallSimple(this.typegen.generateEphemeralListGetFunction(elt, i), [this.argToSMT(op.arg)]));

        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultTupleType)).cons, args), continuation);
    }

    processConstructorRecord(op: MIRConstructorRecord, continuation: SMTExp): SMTExp {
        const args = op.args.map((arg) => this.argToSMT(arg[1]));

        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultRecordType)).cons, args), continuation);
    }

    processConstructorRecordFromEphemeralList(op: MIRConstructorRecordFromEphemeralList, continuation: SMTExp): SMTExp {
        const elt = this.typegen.getMIRType(op.elistType).options[0] as MIREphemeralListType;
        const eargs = elt.entries.map((tt, i) => new SMTCallSimple(this.typegen.generateEphemeralListGetFunction(elt, i), [this.argToSMT(op.arg)]));

        const rtype = this.typegen.getMIRType(op.resultRecordType).options[0] as MIRRecordType;
        const args = rtype.entries.map((rentry) => {
            const eidx = op.propertyPositions.indexOf(rentry.pname);
            return eargs[eidx];
        });

        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultRecordType)).cons, args), continuation);
    }

    processStructuredAppendTuple(op: MIRStructuredAppendTuple, continuation: SMTExp): SMTExp {
        let args: SMTExp[] = [];
        for (let i = 0; i < op.args.length; ++i) {
            const tt = this.typegen.getMIRType(op.ttypes[i].flow).options[0] as MIRTupleType;
            const argi = this.argToSMT(op.args[i]);

            for (let j = 0; j < tt.entries.length; ++j) {
                args.push(new SMTCallSimple(this.typegen.generateTupleIndexGetFunction(tt, j), [argi]));
            }
        }

        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultTupleType)).cons, args), continuation);
    }

    processStructuredJoinRecord(op: MIRStructuredJoinRecord, continuation: SMTExp): SMTExp {
        const rtype = this.typegen.getMIRType(op.resultRecordType).options[0] as MIRRecordType;

        let args: SMTExp[] = [];
        for (let i = 0; i < op.args.length; ++i) {
            const tt = this.typegen.getMIRType(op.ttypes[i].flow).options[0] as MIRRecordType;
            const argi = this.argToSMT(op.args[i]);

            for (let j = 0; j < tt.entries.length; ++j) {
                const ppidx = rtype.entries.findIndex((ee) => ee.pname === tt.entries[j].pname);
                args[ppidx] = new SMTCallSimple(this.typegen.generateRecordPropertyGetFunction(tt, tt.entries[j].pname), [argi]);
            }
        }

        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultRecordType)).cons, args), continuation);
    }

    processConstructorEphemeralList(op: MIRConstructorEphemeralList, continuation: SMTExp): SMTExp {
        const args = op.args.map((arg) => this.argToSMT(arg));

        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultEphemeralListType)).cons, args), continuation);
    }

    processConstructorEntityDirect(op: MIRConstructorEntityDirect, continuation: SMTExp): SMTExp {
        const args = op.args.map((arg) => this.argToSMT(arg));

        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.entityType)).cons, args), continuation);
    }

    processEphemeralListExtend(op: MIREphemeralListExtend, continuation: SMTExp): SMTExp {
        const ietype = this.typegen.getMIRType(op.argtype).options[0] as MIREphemeralListType;
        const iargs = ietype.entries.map((ee, i) => new SMTCallSimple(this.typegen.generateEphemeralListGetFunction(ietype, i), [this.argToSMT(op.arg)]));

        const eargs = op.ext.map((arg) => this.argToSMT(arg));

        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultType)).cons, [...iargs, ...eargs]), continuation);
    }

    processConstructorPrimaryCollectionEmpty(op: MIRConstructorPrimaryCollectionEmpty, continuation: SMTExp): SMTExp {
        const emptyconst = this.typegen.getSMTTypeFor(this.typegen.getMIRType(op.tkey)).smttypename + "@@empty";
        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTConst(emptyconst), continuation);
    }

    processConstructorPrimaryCollectionSingletons_ListHelper(ltype: MIRPrimitiveListEntityTypeDecl, exps: SMTExp[]): SMTExp {
        const icall = this.generateSingletonConstructorsList(exps.length, this.typegen.getMIRType(ltype.tkey));
        if(this.requiredSingletonConstructorsList.findIndex((vv) => vv.inv === icall) === -1) {
            const geninfo = { inv: icall, argc: exps.length, resulttype: this.typegen.getMIRType(ltype.tkey) };
            this.requiredSingletonConstructorsList.push(geninfo);
        }

        return new SMTCallSimple(this.typegen.lookupFunctionName(icall), exps);
    }

    processConstructorPrimaryCollectionSingletons_MapHelper(sinfo: SourceInfo, ltype: MIRPrimitiveMapEntityTypeDecl, exps: SMTExp[]): SMTExp {
        const icall = this.generateSingletonConstructorsMap(exps.length, this.typegen.getMIRType(ltype.tkey));
        if(this.requiredSingletonConstructorsMap.findIndex((vv) => vv.inv === icall) === -1) {
            const geninfo = { srcFile: this.currentFile, sinfo: sinfo, inv: icall, argc: exps.length, resulttype: this.typegen.getMIRType(ltype.tkey) };
            this.requiredSingletonConstructorsMap.push(geninfo);
        }

        return new SMTCallGeneral(this.typegen.lookupFunctionName(icall), exps);
    }

    processConstructorPrimaryCollectionSingletons(op: MIRConstructorPrimaryCollectionSingletons, continuation: SMTExp): SMTExp {
        const constype = this.assembly.entityDecls.get(op.tkey) as MIRPrimitiveCollectionEntityTypeDecl;
        const args = op.args.map((arg) => this.argToSMT(arg[1]));

        if(constype instanceof MIRPrimitiveListEntityTypeDecl) {
            const consexp = this.processConstructorPrimaryCollectionSingletons_ListHelper(constype, args);
            return new SMTLet(this.varToSMTName(op.trgt).vname, consexp, continuation);
        }
        else if (constype instanceof MIRPrimitiveStackEntityTypeDecl) {
            return NOT_IMPLEMENTED("MIRPrimitiveStackEntityTypeDecl@cons");
        }
        else if (constype instanceof MIRPrimitiveQueueEntityTypeDecl) {
            return NOT_IMPLEMENTED("MIRPrimitiveQueueEntityTypeDecl@cons");
        }
        else if (constype instanceof MIRPrimitiveSetEntityTypeDecl) {
            return NOT_IMPLEMENTED("MIRPrimitiveSetEntityTypeDecl@cons");
        }
        else {
            assert(constype instanceof MIRPrimitiveMapEntityTypeDecl);
            const mapconstype = constype as MIRPrimitiveMapEntityTypeDecl;

            const consexp = this.processConstructorPrimaryCollectionSingletons_MapHelper(op.sinfo, mapconstype, args);

            const cvar = this.generateTempName();
            return new SMTLet(cvar, consexp,
                new SMTIf(this.typegen.generateResultIsErrorTest(this.typegen.getMIRType(constype.tkey), new SMTVar(cvar)),
                    this.generateErrorCreate(op.sinfo, this.typegen.getMIRType(op.tkey), "Key collision in Map constructor"),
                    new SMTLet(this.varToSMTName(op.trgt).vname, this.typegen.generateResultGetSuccess(this.typegen.getMIRType(constype.tkey), new SMTVar(cvar)), continuation)
                )
            );
        }
    }

    processConstructorPrimaryCollectionCopies(op: MIRConstructorPrimaryCollectionCopies, continuation: SMTExp): SMTExp {
        return NOT_IMPLEMENTED("processConstructorPrimaryCollectionCopies");
    }

    processConstructorPrimaryCollectionMixed(op: MIRConstructorPrimaryCollectionMixed, continuation: SMTExp): SMTExp {
        return NOT_IMPLEMENTED("processConstructorPrimaryCollectionMixed");
    }

    processBinKeyEq(op: MIRBinKeyEq, continuation: SMTExp): SMTExp {
        const mirlhslayout = this.typegen.getMIRType(op.lhslayouttype);
        const mirrhslayout = this.typegen.getMIRType(op.rhslayouttype);

        let eqcmp: SMTExp = new SMTConst("false");
        if(mirlhslayout.typeID === mirrhslayout.typeID && this.typegen.isUniqueType(mirlhslayout) && this.typegen.isUniqueType(mirrhslayout)) {
            eqcmp = SMTCallSimple.makeEq(this.argToSMT(op.lhs), this.argToSMT(op.rhs));
        }
        else {
            const lhs = this.typegen.coerceToKey(this.argToSMT(op.lhs), mirlhslayout);
            const rhs = this.typegen.coerceToKey(this.argToSMT(op.rhs), mirrhslayout);

            eqcmp = SMTCallSimple.makeEq(lhs, rhs);
        }

        const gop = this.generateGuardStmtCond(op.sguard, eqcmp, "Bool");
        return new SMTLet(this.varToSMTName(op.trgt).vname, gop, continuation);
    }

    generateBinKeyCmpFor(cmptype: MIRType, lhstype: MIRType, lhsexp: SMTExp, rhstype: MIRType, rhsexp: SMTExp): SMTExp {
        if(lhstype.typeID === cmptype.typeID && rhstype.typeID === cmptype.typeID && this.typegen.isUniqueType(cmptype)) {
            const etype = this.typegen.assembly.entityDecls.get(cmptype.typeID) as MIREntityTypeDecl;

            if(etype instanceof MIRPrimitiveInternalEntityTypeDecl) {
                const oftype = this.typegen.getSMTTypeFor(cmptype);
                return new SMTCallSimple(`${oftype.smttypename}@less`, [lhsexp, rhsexp]);
            }
            else if(etype instanceof MIRStringOfInternalEntityTypeDecl) {
                const oftype = this.typegen.getSMTTypeFor(this.typegen.getMIRType("String"));
                return new SMTCallSimple(`${oftype.smttypename}@less`, [lhsexp, rhsexp]);
            }
            else if(etype instanceof MIRDataStringInternalEntityTypeDecl) {
                const oftype = this.typegen.getSMTTypeFor(this.typegen.getMIRType("String"));
                return new SMTCallSimple(`${oftype.smttypename}@less`, [lhsexp, rhsexp]);
            }
            xxxx;
            else if(etype instanceof MIRDataBufferInternalEntityTypeDecl) {
                const oftype = this.typegen.getSMTTypeFor(this.typegen.getMIRType("String"));
                return new SMTCallSimple(`${oftype.smttypename}@less`, [lhsexp, rhsexp]);
            }
            else if(etype instanceof MIREnumEntityTypeDecl) {
                const oftype = this.typegen.getSMTTypeFor(this.typegen.getMIRType("Nat"));
                return new SMTCallSimple(`${oftype.smttypename}@less`, [lhsexp, rhsexp]);
            }
            else {
                const ttval = etype as MIRConstructableEntityTypeDecl;

                const oftype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(ttval.fromtype));
                return new SMTCallSimple(`${oftype.smttypename}@less`, [lhsexp, rhsexp]);
            }
        }
        else {
            const lhs = this.typegen.coerceToKey(lhsexp, lhstype);
            const rhs = this.typegen.coerceToKey(rhsexp, rhstype);

            return new SMTCallSimple("BKey@less", [lhs, rhs]);
        }
    }

    processBinKeyLess(op: MIRBinKeyLess, continuation: SMTExp): SMTExp {
        const mirlhslayout = this.typegen.getMIRType(op.lhslayouttype);
        const mirrhslayout = this.typegen.getMIRType(op.rhslayouttype);

        const ltcmp = this.generateBinKeyCmpFor(this.typegen.getMIRType(op.cmptype), mirlhslayout, this.argToSMT(op.lhs), mirrhslayout, this.argToSMT(op.rhs));
        return new SMTLet(this.varToSMTName(op.trgt).vname, ltcmp, continuation);
    }

    processPrefixNotOp(op: MIRPrefixNotOp, continuation: SMTExp): SMTExp {
        return new SMTLet(this.varToSMTName(op.trgt).vname, SMTCallSimple.makeNot(this.argToSMT(op.arg)), continuation);
    }

    processLogicAction(op: MIRLogicAction, continuation: SMTExp): SMTExp {
        assert(op.args.length !== 0, "Should not be empty logic argument list");

        if(op.args.length === 1) {
            return new SMTLet(this.varToSMTName(op.trgt).vname, this.argToSMT(op.args[0]), continuation);
        }
        else {
            if (op.opkind === "/\\") {
                return new SMTLet(this.varToSMTName(op.trgt).vname, SMTCallSimple.makeAndOf(...op.args.map((arg) => this.argToSMT(arg))), continuation);
            }
            else {
                return new SMTLet(this.varToSMTName(op.trgt).vname, SMTCallSimple.makeOrOf(...op.args.map((arg) => this.argToSMT(arg))), continuation);
            }
        }
    }

    processIsTypeOf(op: MIRIsTypeOf, continuation: SMTExp): SMTExp {
        const layout = this.typegen.getMIRType(op.srclayouttype);
        const flow = this.typegen.getMIRType(op.srcflowtype);
        const oftype = this.typegen.getMIRType(op.chktype);

        let ttop: SMTExp = new SMTConst("false");
        if(this.assembly.subtypeOf(flow, oftype)) {
            //also handles the oftype is Any case
            ttop = new SMTConst("true");
        }
        else if(this.typegen.isType(oftype, "None")) {
            ttop = this.generateNoneCheck(op.arg, layout);
        }
        else if (this.typegen.isType(oftype, "Some")) {
            ttop = this.generateSomeCheck(op.arg, layout);
        }
        else if(this.typegen.isType(oftype, "Nothing")) {
            ttop = this.generateNothingCheck(op.arg, layout);
        }
        else {
            const tests = oftype.options.map((topt) => {
                const mtype = this.typegen.getMIRType(topt.typeID);
                assert(mtype !== undefined, "We should generate all the component types by default??");
    
                if(topt instanceof MIREntityType) {
                    return this.generateSubtypeCheckEntity(op.arg, layout, flow, mtype);
                }
                else if (topt instanceof MIRConceptType) {
                    return this.generateSubtypeCheckConcept(op.arg, layout, flow, mtype);
                }
                else if (topt instanceof MIRTupleType) {
                    return this.generateSubtypeCheckTuple(op.arg, layout, flow, mtype);
                }
                else {
                    assert(topt instanceof MIRRecordType, "All other cases should be handled previously (e.g. dynamic subtype of ephemeral or literal types is not good here)");

                    return this.generateSubtypeCheckRecord(op.arg, layout, flow, mtype);
                }
            })
            .filter((test) => !(test instanceof SMTConst) || test.cname !== "false");
    
            if(tests.length === 0) {
                ttop = new SMTConst("false");
            }
            else if(tests.findIndex((test) => (test instanceof SMTConst) && test.cname === "true") !== -1) {
                ttop = new SMTConst("true");
            }
            else if(tests.length === 1) {
                ttop = tests[0];
            }
            else {
                ttop = SMTCallSimple.makeOrOf(...tests);
            }
        }

        const gop = this.generateGuardStmtCond(op.sguard, ttop, "Bool");
        return new SMTLet(this.varToSMTName(op.trgt).vname, gop, continuation);
    }

    processRegisterAssign(op: MIRRegisterAssign, continuation: SMTExp): SMTExp {
        if(op.sguard === undefined) {
            return new SMTLet(this.varToSMTName(op.trgt).vname, this.argToSMT(op.src), continuation);
        }
        else {
            const cassign = this.generateGuardStmtCond(op.sguard, this.argToSMT(op.src), op.layouttype);
            return new SMTLet(this.varToSMTName(op.trgt).vname, cassign, continuation);
        }
    }

    processReturnAssign(op: MIRReturnAssign, continuation: SMTExp): SMTExp {
        return new SMTLet(this.varToSMTName(op.name).vname, this.argToSMT(op.src), continuation);
    }

    processReturnAssignOfCons(op: MIRReturnAssignOfCons, continuation: SMTExp): SMTExp {
        const conscall = new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.oftype)).cons, op.args.map((arg) => this.argToSMT(arg)));
        return new SMTLet(this.varToSMTName(op.name).vname, conscall, continuation);
    }

    processOp(op: MIROp, continuation: SMTExp): SMTExp | undefined {
        switch (op.tag) {
            case MIROpTag.MIRNop:
            case MIROpTag.MIRDebug:
            case MIROpTag.MIRJump:
            case MIROpTag.MIRJumpCond:
            case MIROpTag.MIRJumpNone:
            case MIROpTag.MIRVarLifetimeStart:
            case MIROpTag.MIRVarLifetimeEnd: {
                return undefined;
            }
            case MIROpTag.MIRAbort: {
                return this.processAbort(op as MIRAbort);
            }
            case MIROpTag.MIRAssertCheck: {
                return this.processAssertCheck(op as MIRAssertCheck, continuation);
            }
            case MIROpTag.MIRLoadUnintVariableValue: {
                return this.processLoadUnintVariableValue(op as MIRLoadUnintVariableValue, continuation);
            }
            case MIROpTag.MIRDeclareGuardFlagLocation: {
                this.processDeclareGuardFlagLocation(op as MIRDeclareGuardFlagLocation);
                return undefined;
            }
            case MIROpTag.MIRSetConstantGuardFlag: {
                this.processSetConstantGuardFlag(op as MIRSetConstantGuardFlag);
                return undefined;
            }
            case MIROpTag.MIRConvertValue: {
                return this.processConvertValue(op as MIRConvertValue, continuation);
            }
            case MIROpTag.MIRInject: {
                return this.processInject(op as MIRInject, continuation);
            }
            case MIROpTag.MIRGuardedOptionInject: {
                return this.processGuardedOptionInject(op as MIRGuardedOptionInject, continuation);
            }
            case MIROpTag.MIRExtract: {
                return this.processExtract(op as MIRExtract, continuation);
            }
            case MIROpTag.MIRLoadConst: {
                return this.processLoadConst(op as MIRLoadConst, continuation);
            }
            case MIROpTag.MIRTupleHasIndex: {
                return this.processTupleHasIndex(op as MIRTupleHasIndex, continuation);
            }
            case MIROpTag.MIRRecordHasProperty: {
                return this.processRecordHasProperty(op as MIRRecordHasProperty, continuation);
            }
            case MIROpTag.MIRLoadTupleIndex: {
                return this.processLoadTupleIndex(op as MIRLoadTupleIndex, continuation);
            }
            case MIROpTag.MIRLoadTupleIndexSetGuard: {
                return this.processLoadTupleIndexSetGuard(op as MIRLoadTupleIndexSetGuard, continuation);
            }
            case MIROpTag.MIRLoadRecordProperty: {
                return this.processLoadRecordProperty(op as MIRLoadRecordProperty, continuation);
            }
            case MIROpTag.MIRLoadRecordPropertySetGuard: {
                return this.processLoadRecordPropertySetGuard(op as MIRLoadRecordPropertySetGuard, continuation);
            }
            case MIROpTag.MIRLoadField: {
                return this.processLoadField(op as MIRLoadField, continuation);
            }
            case MIROpTag.MIRTupleProjectToEphemeral: {
                return this.processTupleProjectToEphemeral(op as MIRTupleProjectToEphemeral, continuation);
            }
            case MIROpTag.MIRRecordProjectToEphemeral: {
                return this.processRecordProjectToEphemeral(op as MIRRecordProjectToEphemeral, continuation);
            }
            case MIROpTag.MIREntityProjectToEphemeral: {
                return this.processEntityProjectToEphemeral(op as MIREntityProjectToEphemeral, continuation);
            }
            case MIROpTag.MIRTupleUpdate: {
                return this.processTupleUpdate(op as MIRTupleUpdate, continuation);
            }
            case MIROpTag.MIRRecordUpdate: {
                return this.processRecordUpdate(op as MIRRecordUpdate, continuation);
            }
            case MIROpTag.MIREntityUpdate: {
                return this.processEntityUpdate(op as MIREntityUpdate, continuation);
            }
            case MIROpTag.MIRLoadFromEpehmeralList: {
                return this.processLoadFromEpehmeralList(op as MIRLoadFromEpehmeralList, continuation);
            }
            case MIROpTag.MIRMultiLoadFromEpehmeralList: {
                return this.processMultiLoadFromEpehmeralList(op as MIRMultiLoadFromEpehmeralList, continuation);
            }
            case MIROpTag.MIRSliceEpehmeralList: {
                return this.processSliceEpehmeralList(op as MIRSliceEpehmeralList, continuation);
            }
            case MIROpTag.MIRInvokeFixedFunction: {
                return this.processInvokeFixedFunction(op as MIRInvokeFixedFunction, continuation);
            }
            case MIROpTag.MIRInvokeVirtualFunction: {
                return this.processInvokeVirtualFunction(op as MIRInvokeVirtualFunction, continuation);
            }
            case MIROpTag.MIRInvokeVirtualOperator: {
                return this.processInvokeVirtualOperator(op as MIRInvokeVirtualOperator, continuation);
            }
            case MIROpTag.MIRConstructorTuple: {
                return this.processConstructorTuple(op as MIRConstructorTuple, continuation);
            }
            case MIROpTag.MIRConstructorTupleFromEphemeralList: {
                return this.processConstructorTupleFromEphemeralList(op as MIRConstructorTupleFromEphemeralList, continuation);
            }
            case MIROpTag.MIRConstructorRecord: {
                return this.processConstructorRecord(op as MIRConstructorRecord, continuation);
            }
            case MIROpTag.MIRConstructorRecordFromEphemeralList: {
                return this.processConstructorRecordFromEphemeralList(op as MIRConstructorRecordFromEphemeralList, continuation);
            }
            case MIROpTag.MIRStructuredAppendTuple: {
                return this.processStructuredAppendTuple(op as MIRStructuredAppendTuple, continuation);
            }
            case MIROpTag.MIRStructuredJoinRecord: {
                return this.processStructuredJoinRecord(op as MIRStructuredJoinRecord, continuation);
            }
            case MIROpTag.MIRConstructorEphemeralList: {
                return this.processConstructorEphemeralList(op as MIRConstructorEphemeralList, continuation);
            }
            case MIROpTag.MIRConstructorEntityDirect: {
                return this.processConstructorEntityDirect(op as MIRConstructorEntityDirect, continuation);
            }
            case MIROpTag.MIREphemeralListExtend: {
                return this.processEphemeralListExtend(op as MIREphemeralListExtend, continuation);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
                return this.processConstructorPrimaryCollectionEmpty(op as MIRConstructorPrimaryCollectionEmpty, continuation);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                return this.processConstructorPrimaryCollectionSingletons(op as MIRConstructorPrimaryCollectionSingletons, continuation);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
                return this.processConstructorPrimaryCollectionCopies(op as MIRConstructorPrimaryCollectionCopies, continuation);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                return this.processConstructorPrimaryCollectionMixed(op as MIRConstructorPrimaryCollectionMixed, continuation);
            }
            case MIROpTag.MIRBinKeyEq: {
                return this.processBinKeyEq(op as MIRBinKeyEq, continuation);
            }
            case MIROpTag.MIRBinKeyLess: {
                return this.processBinKeyLess(op as MIRBinKeyLess, continuation);
            }
            case MIROpTag.MIRPrefixNotOp: {
                return this.processPrefixNotOp(op as MIRPrefixNotOp, continuation);
            }
            case MIROpTag.MIRLogicAction: {
                return this.processLogicAction(op as MIRLogicAction, continuation);
            }
            case MIROpTag.MIRIsTypeOf: {
                return this.processIsTypeOf(op as MIRIsTypeOf, continuation);
            }
            case MIROpTag.MIRRegisterAssign: {
                return this.processRegisterAssign(op as MIRRegisterAssign, continuation);
            }
            case MIROpTag.MIRReturnAssign: {
                return this.processReturnAssign(op as MIRReturnAssign, continuation);
            }
            case MIROpTag.MIRReturnAssignOfCons: {
                return this.processReturnAssignOfCons(op as MIRReturnAssignOfCons, continuation);
            }
            case MIROpTag.MIRDeadFlow:
            case MIROpTag.MIRPhi: {
                assert(false, "Should be eliminated in cleanup");
                return undefined;
            }
        }
    }

    processGenerateResultUnderflowCheck(sinfo: SourceInfo, arg0: SMTExp, arg1: SMTExp , oftype: MIRType, val: SMTExp): SMTExp {
        return new SMTIf(new SMTCallSimple("<", [arg1, arg0]), this.generateErrorCreate(sinfo, oftype, "Unsigned Underflow"), this.typegen.generateResultTypeConstructorSuccess(oftype, val));
    }

    processGenerateResultWithZeroArgCheck(sinfo: SourceInfo, zero: SMTConst, not0arg: SMTExp, oftype: MIRType, val: SMTExp): SMTExp {
        const chkzero = SMTCallSimple.makeEq(zero, not0arg);
        return new SMTIf(chkzero, this.generateErrorCreate(sinfo, oftype, "Div by 0"), this.typegen.generateResultTypeConstructorSuccess(oftype, val));
    }

    processDefaultOperatorInvokePrimitiveType(sinfo: SourceInfo, trgt: MIRRegisterArgument, op: MIRInvokeKey, args: SMTExp[], continuation: SMTExp): SMTExp {
        let smte: SMTExp = new SMTConst("[INVALID]");
        let erropt = false;
        let rtype = this.typegen.getMIRType("Bool"); //default for all the compare ops

        switch (op) {
            //op unary +
            case "__i__Core::+=prefix=(Int)": {
                rtype = this.typegen.getMIRType("Int");
                smte = args[0];
                break;
            }
            case "__i__Core::+=prefix=(Nat)": {
                rtype = this.typegen.getMIRType("Nat");
                smte = args[0];
                break;
            }
            case "__i__Core::+=prefix=(BigInt)": {
                rtype = this.typegen.getMIRType("BigInt");
                smte = args[0];
                break;
            }
            case "__i__Core::+=prefix=(BigNat)": {
                rtype = this.typegen.getMIRType("BigNat");
                smte = args[0];
                break;
            }
            case "__i__Core::+=prefix=(Rational)": {
                rtype = this.typegen.getMIRType("Rational");
                smte = args[0];
                break;
            }
            case "__i__Core::+=prefix=(Float)": {
                rtype = this.typegen.getMIRType("Float");
                smte = args[0];
                break;
            }
            case "__i__Core::+=prefix=(Decimal)": {
                rtype = this.typegen.getMIRType("Decimal");
                smte = args[0];
                break;
            }
            //op unary -
            case "__i__Core::-=prefix=(Int)": {
                rtype = this.typegen.getMIRType("Int");
                smte = new SMTCallSimple("*", [args[0], new SMTConst("-1")]);
                break;
            }
            case "__i__Core::-=prefix=(BigInt)": {
                rtype = this.typegen.getMIRType("BigInt");
                smte = new SMTCallSimple("*", [args[0], new SMTConst("-1")]);
                break;
            }
            case "__i__Core::-=prefix=(Rational)": {
                rtype = this.typegen.getMIRType("Rational");
                smte = new SMTCallSimple("-", args);
                break;
            }
            case "__i__Core::-=prefix=(Float)": {
                rtype = this.typegen.getMIRType("Float");
                smte = new SMTCallSimple("-", args);
                break;
            }
            case "__i__Core::-=prefix=(Decimal)": {
                rtype = this.typegen.getMIRType("Decimal");
                smte = new SMTCallSimple("-", args);
                break;
            }
            //op infix +
            case "__i__Core::+=infix=(Int, Int)": {
                rtype = this.typegen.getMIRType("Int");
                smte = new SMTCallSimple("+", args);
                break;
            }
            case "__i__Core::+=infix=(Nat, Nat)": {
                rtype = this.typegen.getMIRType("Nat");
                smte = new SMTCallSimple("+", args);
                break;
            }
            case "__i__Core::+=infix=(BigInt, BigInt)": {
                rtype = this.typegen.getMIRType("BigInt");
                smte = new SMTCallSimple("+", args);
                break;
            }
            case "__i__Core::+=infix=(BigNat, BigNat)": {
                rtype = this.typegen.getMIRType("BigNat");
                smte = new SMTCallSimple("+", args);
                break;
            }
            case "__i__Core::+=infix=(Rational, Rational)": {
                rtype = this.typegen.getMIRType("Rational");
                smte = new SMTCallSimple("+", args);
                break;
            }
            case "__i__Core::+=infix=(Float, Float)": {
                rtype = this.typegen.getMIRType("Float");
                smte = new SMTCallSimple("+", args);
                break;
            }
            case "__i__Core::+=infix=(Decimal, Decimal)": {
                rtype = this.typegen.getMIRType("Decmial");
                smte = new SMTCallSimple("+", args);
                break;
            }
            //op infix -
            case "__i__Core::-=infix=(Int, Int)": {
                rtype = this.typegen.getMIRType("Int");
                smte = new SMTCallSimple("-", args);
                break;
            }
            case "__i__Core::-=infix=(Nat, Nat)": {
                rtype = this.typegen.getMIRType("Nat");
                smte = this.processGenerateResultUnderflowCheck(sinfo, args[0], args[1], rtype, new SMTCallSimple("-", args));
                erropt = true;
                break;
            }
            case "__i__Core::-=infix=(BigInt, BigInt)": {
                rtype = this.typegen.getMIRType("BigInt");
                smte = new SMTCallSimple("-", args);
                break;
            }
            case "__i__Core::-=infix=(BigNat, BigNat)": {
                rtype = this.typegen.getMIRType("BigNat");
                smte = this.processGenerateResultUnderflowCheck(sinfo, args[0], args[1], rtype, new SMTCallSimple("-", args));
                erropt = true;
                break
            }
            case "__i__Core::-=infix=(Rational, Rational)": {
                rtype = this.typegen.getMIRType("Rational");
                smte = new SMTCallSimple("-", args);
                break;
            }
            case "__i__Core::-=infix=(Float, Float)": {
                rtype = this.typegen.getMIRType("Float");
                smte = new SMTCallSimple("-", args);
                break;
            }
            case "__i__Core::-=infix=(Decimal, Decimal)": {
                rtype = this.typegen.getMIRType("Decmial");
                smte = new SMTCallSimple("-", args);
                break;
            }
            //op infix *
            case "__i__Core::*=infix=(Int, Int)": {
                rtype = this.typegen.getMIRType("Int");
                smte = new SMTCallSimple("*", args);
                break;
            }
            case "__i__Core::*=infix=(Nat, Nat)": {
                rtype = this.typegen.getMIRType("Nat");
                smte = new SMTCallSimple("*", args);
                break;
            }
            case "__i__Core::*=infix=(BigInt, BigInt)": {
                rtype = this.typegen.getMIRType("BigInt");
                smte = new SMTCallSimple("*", args);
                break;
            }
            case "__i__Core::*=infix=(BigNat, BigNat)": {
                rtype = this.typegen.getMIRType("BigNat");
                smte = new SMTCallSimple("*", args);
                break;
            }
            case "__i__Core::*=infix=(Rational, Rational)": {
                rtype = this.typegen.getMIRType("Rational");
                smte = new SMTCallSimple("*", args);
                break;
            }
            case "__i__Core::*=infix=(Float, Float)": {
                rtype = this.typegen.getMIRType("Float");
                smte = new SMTCallSimple("*", args);
                break;
            }
            case "__i__Core::*=infix=(Decimal, Decimal)": {
                rtype = this.typegen.getMIRType("Decmial");
                smte = new SMTCallSimple("*", args);
                break;
            }
            //op infix /
            case "__i__Core::/=infix=(Int, Int)": {
                rtype = this.typegen.getMIRType("Int");
                smte = this.processGenerateResultWithZeroArgCheck(sinfo, new SMTConst("BInt@zero"), args[1], rtype, new SMTCallSimple("/", args));
                erropt = true;
                break;
            }
            case "__i__Core::/=infix=(Nat, Nat)": {
                rtype = this.typegen.getMIRType("Nat");
                smte = this.processGenerateResultWithZeroArgCheck(sinfo, new SMTConst("BNat@zero"), args[1], rtype, new SMTCallSimple("/", args));
                erropt = true;
                break;
            }
            case "__i__Core::/=infix=(BigInt, BigInt)": {
                rtype = this.typegen.getMIRType("BigInt");
                smte = this.processGenerateResultWithZeroArgCheck(sinfo, new SMTConst("BBigInt@zero"), args[1], rtype, new SMTCallSimple("/", args));
                erropt = true;
                break;
            }
            case "__i__Core::/=infix=(BigNat, BigNat)": {
                rtype = this.typegen.getMIRType("BigNat");
                smte = this.processGenerateResultWithZeroArgCheck(sinfo, new SMTConst("BBigNat@zero"), args[1], rtype, new SMTCallSimple("/", args));
                erropt = true;
                break
            }
            case "__i__Core::/=infix=(Rational, Rational)": {
                rtype = this.typegen.getMIRType("Rational");
                smte = this.processGenerateResultWithZeroArgCheck(sinfo, new SMTConst("BRational@zero"), args[1], rtype, new SMTCallSimple("/", args));
                erropt = true;
                break;
            }
            case "__i__Core::/=infix=(Float, Float)": {
                rtype = this.typegen.getMIRType("Float");
                smte = this.processGenerateResultWithZeroArgCheck(sinfo, new SMTConst("BFloat@zero"), args[1], rtype, new SMTCallSimple("/", args));
                erropt = true;
                break;
            }
            case "__i__Core::/=infix=(Decimal, Decimal)": {
                rtype = this.typegen.getMIRType("Decimal");
                smte = this.processGenerateResultWithZeroArgCheck(sinfo, new SMTConst("BDecimal@zero"), args[1], rtype, new SMTCallSimple("/", args));
                erropt = true;
                break;
            }
            //op infix ==
            case "__i__Core::===infix=(Int, Int)":
            case "__i__Core::===infix=(Nat, Nat)":
            case "__i__Core::===infix=(BigInt, BigInt)":
            case "__i__Core::===infix=(BigNat, BigNat)":
            case "__i__Core::===infix=(Rational, Rational)":
            case "__i__Core::===infix=(Float, Float)":
            case "__i__Core::===infix=(Decimal, Decimal)": {
                smte = SMTCallSimple.makeEq(args[0], args[1]);
                break;
            }
            //op infix !=
            case "__i__Core::!==infix=(Int, Int)":
            case "__i__Core::!==infix=(Nat, Nat)":
            case "__i__Core::!==infix=(BigInt, BigInt)":
            case "__i__Core::!==infix=(BigNat, BigNat)":
            case "__i__Core::!==infix=(Rational, Rational)":
            case "__i__Core::!==infix=(Float, Float)":
            case "__i__Core::!==infix=(Decimal, Decimal)": {
                smte = SMTCallSimple.makeNotEq(args[0], args[1]);
                break;
            }
            //op infix <
            case "__i__Core::<=infix=(Int, Int)": {
                smte = new SMTCallSimple("<", args);
                break;
            }
            case "__i__Core::<=infix=(Nat, Nat)": {
                smte = new SMTCallSimple("<", args);
                break;
            }
            case "__i__Core::<=infix=(BigInt, BigInt)": {
                smte = new SMTCallSimple("<", args);
                break;
            }
            case "__i__Core::<=infix=(BigNat, BigNat)": {
                smte = new SMTCallSimple("<", args);
                break;
            }
            case "__i__Core::<=infix=(Rational, Rational)": {
                smte = new SMTCallSimple("<", args);
                break;
            }
            case "__i__Core::<=infix=(Float, Float)": {
                smte = new SMTCallSimple("<", args);
                break;
            }
            case "__i__Core::<=infix=(Decimal, Decimal)": {
                smte = new SMTCallSimple("<", args);
                break;
            }
            //op infix >
            case "__i__Core::>=infix=(Int, Int)": {
                smte = new SMTCallSimple(">", args);
                break;
            }
            case "__i__Core::>=infix=(Nat, Nat)": {
                smte = new SMTCallSimple(">", args);
                break;
            }
            case "__i__Core::>=infix=(BigInt, BigInt)": {
                smte = new SMTCallSimple(">", args);
                break;
            }
            case "__i__Core::>=infix=(BigNat, BigNat)": {
                smte = new SMTCallSimple(">", args);
                break;
            }
            case "__i__Core::>=infix=(Rational, Rational)": {
                smte = new SMTCallSimple(">", args);
                break;
            }
            case "__i__Core::>=infix=(Float, Float)": {
                smte = new SMTCallSimple(">", args);
                break;
            }
            case "__i__Core::>=infix=(Decimal, Decimal)": {
                smte = new SMTCallSimple(">", args);
                break;
            }
            //op infix <=
            case "__i__Core::<==infix=(Int, Int)": {
                smte = new SMTCallSimple("<=", args);
                break;
            }
            case "__i__Core::<==infix=(Nat, Nat)": {
                smte = new SMTCallSimple("<=", args);
                break;
            }
            case "__i__Core::<==infix=(BigInt, BigInt)":  {
                smte = new SMTCallSimple("<=", args);
                break;
            }
            case "__i__Core::<==infix=(BigNat, BigNat)": {
                smte = new SMTCallSimple("<=", args);
                break;
            }
            case "__i__Core::<==infix=(Rational, Rational)": {
                smte = new SMTCallSimple("<=", args);
                break;
            }
            case "__i__Core::<==infix=(Float, Float)": {
                smte = new SMTCallSimple("<=", args);
                break;
            }
            case "__i__Core::<==infix=(Decimal, Decimal)": {
                smte = new SMTCallSimple("<=", args);
                break;
            }
            //op infix >=
            case "__i__Core::>==infix=(Int, Int)": {
                smte = new SMTCallSimple(">=", args);
                break;
            }
            case "__i__Core::>==infix=(Nat, Nat)": {
                smte = new SMTCallSimple(">=", args);
                break;
            }
            case "__i__Core::>==infix=(BigInt, BigInt)": {
                smte = new SMTCallSimple(">=", args);
                break;
            }
            case "__i__Core::>==infix=(BigNat, BigNat)": {
                smte = new SMTCallSimple(">=", args);
                break;
            }
            case "__i__Core::>==infix=(Rational, Rational)":{
                smte = new SMTCallSimple(">=", args);
                break;
            }
            case "__i__Core::>==infix=(Float, Float)":{
                smte = new SMTCallSimple(">=", args);
                break;
            }
            case "__i__Core::>==infix=(Decimal, Decimal)":{
                smte = new SMTCallSimple(">=", args);
                break;
            }
            default: {
                assert(false);
            }
        }

        if (!erropt) {
            return new SMTLet(this.varToSMTName(trgt).vname, smte, continuation);
        }
        else {
            const cres = this.generateTempName();

            const okpath = new SMTLet(this.varToSMTName(trgt).vname, this.typegen.generateResultGetSuccess(rtype, new SMTVar(cres)), continuation);
            const smtrtype = this.typegen.getSMTTypeFor(rtype);
            const smtcurrenttype = this.typegen.getSMTTypeFor(this.currentRType);
            const errpath = (smtrtype.smttypename === smtcurrenttype.smttypename) ? new SMTVar(cres) : this.typegen.generateResultTypeConstructorError(this.currentRType, this.typegen.generateResultGetError(rtype, new SMTVar(cres)));

            const icond = new SMTIf(this.typegen.generateResultIsErrorTest(rtype, new SMTVar(cres)), errpath, okpath);
            return new SMTLet(cres, smte, icond);
        }
    }

    getReadyBlock(blocks: Map<string, MIRBasicBlock>, done: Map<string, SMTExp>): MIRBasicBlock | undefined {
        return [...blocks].map((bb) => bb[1]).find((bb) => {
            if(done.has(bb.label)) {
                return false;
            }

            const jop = bb.ops[bb.ops.length - 1];
            if(jop.tag === MIROpTag.MIRAbort) {
               return true;
            }
            else if (jop.tag === MIROpTag.MIRJump) {
               return done.has((jop as MIRJump).trgtblock);
            }
            else {
                assert(jop.tag === MIROpTag.MIRJumpCond || jop.tag === MIROpTag.MIRJumpNone);

                let tdone = (jop.tag === MIROpTag.MIRJumpCond) ? done.has((jop as MIRJumpCond).trueblock) : done.has((jop as MIRJumpNone).noneblock);
                let fdone = (jop.tag === MIROpTag.MIRJumpCond) ? done.has((jop as MIRJumpCond).falseblock) : done.has((jop as MIRJumpNone).someblock);
                
                return tdone && fdone;
            }
        });
    }

    getNextBlockExp(blocks: Map<string, MIRBasicBlock>, smtexps: Map<string, SMTExp>, from: string, trgt: string): SMTExp {
        if(trgt !== "returnassign") {
            return smtexps.get(trgt) as SMTExp;
        }
        else {
            const eblock = blocks.get("returnassign") as MIRBasicBlock;
            let rexp: SMTExp = smtexps.get("exit") as SMTExp;

            const nomrmalidx = eblock.ops.findIndex((op) => !(op instanceof MIRPhi));
            for (let i = eblock.ops.length - 1; i >= nomrmalidx; --i) {
                const texp = this.processOp(eblock.ops[i], rexp);
                if(texp !== undefined) {
                    rexp = texp;
                }
            }

            if(nomrmalidx === 0) {
                return rexp;
            }
            else {
                const phis = eblock.ops.slice(0, nomrmalidx) as MIRPhi[];
                
                const assigns = phis.map((phi) => {
                    return {
                        vname: this.varToSMTName(phi.trgt).vname,
                        value: this.varToSMTName(phi.src.get(from) as MIRRegisterArgument)
                    }
                });

                return new SMTLetMulti(assigns, rexp);
            }
        }
    }

    generateBlockExps(issafe: boolean, blocks: Map<string, MIRBasicBlock>): SMTExp {
        let smtexps = new Map<string, SMTExp>();

        const eblock = blocks.get("exit") as MIRBasicBlock;
        let rexp: SMTExp = issafe ? new SMTVar("$$return") : this.typegen.generateResultTypeConstructorSuccess(this.currentRType, new SMTVar("$$return"));
        for (let i = eblock.ops.length - 1; i >= 0; --i) {
            const texp = this.processOp(eblock.ops[i], rexp);
            if(texp !== undefined) {
                rexp = texp;
            }
        }
        smtexps.set("exit", rexp);
        smtexps.set("returnassign", new SMTConst("[DUMMY RETURN ASSIGN]"));

        let bb = this.getReadyBlock(blocks, smtexps);
        while(bb !== undefined) {
           const jop = bb.ops[bb.ops.length - 1];

            let rexp: SMTExp = new SMTConst("[UNITIALIZED FLOW]");
            if(jop.tag === MIROpTag.MIRAbort) {
                ; //No continuation so just leave uninit
            }
            else if (jop.tag === MIROpTag.MIRJump) {
                rexp = this.getNextBlockExp(blocks, smtexps, bb.label, (jop as MIRJump).trgtblock);
            }
            else if (jop.tag === MIROpTag.MIRJumpCond) {
                const smtcond = this.argToSMT((jop as MIRJumpCond).arg);
                const texp = this.getNextBlockExp(blocks, smtexps, bb.label, (jop as MIRJumpCond).trueblock);
                const fexp = this.getNextBlockExp(blocks, smtexps, bb.label, (jop as MIRJumpCond).falseblock);
                
                rexp = new SMTIf(smtcond, texp, fexp);
            }
            else {
                assert(jop.tag === MIROpTag.MIRJumpNone);

                const smtcond = this.generateNoneCheck((jop as MIRJumpNone).arg, this.typegen.getMIRType((jop as MIRJumpNone).arglayouttype));
                const nexp = this.getNextBlockExp(blocks, smtexps, bb.label, (jop as MIRJumpNone).noneblock);
                const sexp = this.getNextBlockExp(blocks, smtexps, bb.label, (jop as MIRJumpNone).someblock);
                
                rexp = new SMTIf(smtcond, nexp, sexp);
            }

            for (let i = bb.ops.length - 1; i >= 0; --i) {
                const texp = this.processOp(bb.ops[i], rexp);
                if(texp !== undefined) {
                    rexp = texp;
                }
            }

            smtexps.set(bb.label, rexp);
            bb = this.getReadyBlock(blocks, smtexps);
        }

        return smtexps.get("entry") as SMTExp;
    }

    generateSMTInvoke(idecl: MIRInvokeDecl): SMTFunction | undefined {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.getMIRType(idecl.resultType);

        const args = idecl.params.map((arg) => {
            return { vname: this.varStringToSMT(arg.name).vname, vtype: this.typegen.getSMTTypeFor(this.typegen.getMIRType(arg.type)) };
        });

        const issafe = this.isSafeInvoke(idecl.ikey);
        const restype = issafe ? this.typegen.getSMTTypeFor(this.typegen.getMIRType(idecl.resultType)) : this.typegen.generateResultType(this.typegen.getMIRType(idecl.resultType));

        if (idecl instanceof MIRInvokeBodyDecl) {
            const body = this.generateBlockExps(issafe, (idecl as MIRInvokeBodyDecl).body.body);

            if (idecl.masksize === 0) {
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, restype, body);
            }
            else {
                return SMTFunction.createWithMask(this.typegen.lookupFunctionName(idecl.ikey), args, "@maskparam@", idecl.masksize, restype, body);
            }
        }
        else {
            assert(idecl instanceof MIRInvokePrimitiveDecl);

            return this.generateBuiltinFunction(idecl as MIRInvokePrimitiveDecl);
        }
    }

    generateBuiltinFunction(idecl: MIRInvokePrimitiveDecl): SMTFunction | undefined {
        const args = idecl.params.map((arg) => {
            return { vname: this.varStringToSMT(arg.name).vname, vtype: this.typegen.getSMTTypeFor(this.typegen.getMIRType(arg.type)) };
        });

        const issafe = this.isSafeInvoke(idecl.ikey);

        const mirrestype = this.typegen.getMIRType(idecl.resultType);
        const smtrestype = this.typegen.getSMTTypeFor(mirrestype);

        const chkrestype = issafe ? smtrestype : this.typegen.generateResultType(mirrestype);

        switch(idecl.implkey) {
            case "default": 
            case "special_extract": {
                return undefined;
            }
            case "special_inject": {
                return undefined;
            }
            case "validator_accepts": {
                const bsqre = this.assembly.validatorRegexs.get(idecl.enclosingDecl as MIRResolvedTypeKey) as BSQRegex;
                const lre = bsqre.compileToPatternToSMT(true);

                let accept = new SMTCallSimple("str.in.re", [new SMTVar(args[0].vname), new SMTConst(lre)]);
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, accept);
            }
            case "number_nattoint": {
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new SMTVar(args[0].vname));
            }
            case "number_inttonat": {
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new SMTVar(args[0].vname));
            }
            case "number_nattobignat": {
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new SMTVar(args[0].vname));
            }
            case "number_inttobigint": {
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new SMTVar(args[0].vname));
            }
            case "number_bignattonat": {
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new SMTVar(args[0].vname));
            }
            case "number_biginttoint": {
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new SMTVar(args[0].vname)); 
            }
            case "number_bignattobigint": {
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new SMTVar(args[0].vname));
            }
            case "number_biginttobignat": {
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new SMTVar(args[0].vname));
            }
            case "number_bignattofloat":
            case "number_bignattodecimal":
            case "number_bignattorational":
            case "number_biginttofloat":
            case "number_biginttodecimal":
            case "number_biginttorational": {
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new SMTCallSimple("to_real", [new SMTVar(args[0].vname)]));
            }
            case "number_floattobigint":
            case "number_decimaltobigint": 
            case "number_rationaltobigint": {
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new SMTCallSimple("to_int", [new SMTVar(args[0].vname)]));
            }
            case "number_floattodecimal":
            case "number_floattorational":
            case "number_decimaltofloat":
            case "number_decimaltorational":
            case "number_rationaltofloat":
            case "number_rationaltodecimal": {
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new SMTVar(args[0].vname));
            }
            case "float_floor":
            case "decimal_floor": {
                const floor = new SMTIf(
                    new SMTCallSimple("<=", [new SMTVar("vvround"), new SMTVar(args[0].vname)]),
                    new SMTCallSimple("to_int", [new SMTVar(args[0].vname)]),
                    new SMTCallSimple("-", [new SMTCallSimple("to_int", [new SMTVar(args[0].vname)]), new SMTConst("1")])
                );
                const vvround = new SMTLet("vvround", new SMTCallSimple("to_real", [new SMTCallSimple("to_int", [new SMTVar(args[0].vname)])]), new SMTCallSimple("to_real", [floor]));
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, vvround);
            }
            case "float_ceil":
            case "decimal_ceil": {
                const ceil = new SMTIf(
                    new SMTCallSimple(">=", [new SMTVar("vvround"), new SMTVar(args[0].vname)]),
                    new SMTCallSimple("to_int", [new SMTVar(args[0].vname)]),
                    new SMTCallSimple("+", [new SMTCallSimple("to_int", [new SMTVar(args[0].vname)]), new SMTConst("1")])
                );
                const vvround = new SMTLet("vvround", new SMTCallSimple("to_real", [new SMTCallSimple("to_int", [new SMTVar(args[0].vname)])]), new SMTCallSimple("to_real", [ceil]));
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, vvround);
            }
            case "float_truncate":
            case "decimal_truncate":  {
                const truncate = new SMTIf(
                    new SMTCallSimple(">=", [new SMTVar(args[0].vname), new SMTConst("0.0")]),
                    new SMTCallSimple("to_int", [new SMTVar(args[0].vname)]),
                    new SMTCallSimple("-", [new SMTCallSimple("to_int", [new SMTCallSimple("-", [new SMTVar(args[0].vname)])])])
                );
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, truncate);
            }
            case "float_power":
            case "decimal_power": {
                const rr = new SMTCallSimple("^", [new SMTVar(args[0].vname), new SMTVar(args[0].vname)]);
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, rr);
            }
            case "string_empty": {
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, SMTCallSimple.makeEq(new SMTCallSimple("str.len", [new SMTVar(args[0].vname)]), new SMTConst("0")));
            }
            case "string_append": {
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new SMTCallSimple("str.++", [new SMTVar(args[0].vname), new SMTVar(args[1].vname)]));
            }
            case "bytebuffer_getformat": {
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new SMTCallSimple("BByteBuffer@format", [new SMTVar(args[0].vname)]));
            }
            case "bytebuffer_getcompression": {
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new SMTCallSimple("BByteBuffer@compress", [new SMTVar(args[0].vname)]));
            }
            case "datetime_create": {
                const dd = new SMTCallSimple("BDateTime@cons", args.map((arg) => new SMTVar(arg.vname)));
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "s_list_index": {
                const genlist = new SMTCallSimple("@@SortedIntSeq@@Create", args.map((arg) => new SMTVar(arg.vname)));
                const chklist = SMTCallSimple.makeAndOf(
                    new SMTCallSimple("@@CheckIntSeqLen", [new SMTVar("seq"), new SMTVar(args[2].vname)]),
                    new SMTCallSimple("@@CheckIntSeqSorted", [new SMTVar("seq"), new SMTVar(args[0].vname), new SMTVar(args[2].vname)])
                );

                const cbody = new SMTLet("seq", genlist, 
                    new SMTIf(chklist,
                        this.typegen.generateResultTypeConstructorSuccess(mirrestype, this.typegen.generateListTypeConstructorSeq(mirrestype, new SMTVar("seq"))),
                        this.typegen.generateErrorResultAssert(mirrestype)
                    )
                );

                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_empty": {
                const lt = this.typegen.getMIRType(idecl.params[0].type);
                const emptyconst = this.typegen.getSMTTypeFor(lt).smttypename + "@@empty";
                const cbody = SMTCallSimple.makeEq(new SMTVar(args[0].vname), new SMTConst(emptyconst));
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_size": {
                const lt = this.typegen.getMIRType(idecl.params[0].type);
                const cbody = this.typegen.generateListTypeGetLength(lt, new SMTVar(args[0].vname));
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            } 
            case "s_list_append": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = this.typegen.generateListTypeConstructorSeq(mirrestype, new SMTCallSimple("seq.++", [
                        this.typegen.generateListTypeGetData(mirrestype, new SMTVar(args[0].vname)),
                        this.typegen.generateListTypeGetData(mirrestype, new SMTVar(args[1].vname))
                    ]));
                }
                else {
                    cbody = NOT_IMPLEMENTED("s_list_append array");
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_slice_front": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(mirrestype, new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = this.typegen.generateListTypeConstructorSeq(mirrestype, new SMTCallSimple("seq.extract", [
                        sval,
                        new SMTVar(args[1].vname),
                        new SMTCallSimple("-", [this.typegen.generateListTypeGetLength(mirrestype, sval), new SMTVar(args[1].vname)])
                    ]));
                }
                else {
                    cbody = NOT_IMPLEMENTED("s_list_slice_front array");
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_slice_end": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(mirrestype, new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = this.typegen.generateListTypeConstructorSeq(mirrestype, new SMTCallSimple("seq.extract", [
                        sval,
                        new SMTConst("0"),
                        new SMTVar(args[1].vname)
                    ]));
                }
                else {
                    cbody = NOT_IMPLEMENTED("s_list_slice_end array");
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_slice": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(mirrestype, new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = this.typegen.generateListTypeConstructorSeq(mirrestype, new SMTCallSimple("seq.extract", [
                        sval,
                        new SMTVar(args[1].vname),
                        new SMTVar(args[2].vname)
                    ]));
                }
                else {
                    cbody = NOT_IMPLEMENTED("s_list_slice array");
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_get": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(this.typegen.getMIRType(idecl.params[0].type), new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = new SMTCallSimple("seq.nth", [sval, new SMTVar(args[1].vname)]);
                }
                else {
                    cbody = this.typegen.generateArrayEntryTypeGetValue(this.typegen.getMIRType(idecl.params[0].type), new SMTCallSimple("select", [sval, new SMTVar(args[1].vname)]));
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_get_back": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(this.typegen.getMIRType(idecl.params[0].type), new SMTVar(args[0].vname));
                const idx = this.typegen.generateListTypeSeq_GetLengthMinus1(this.typegen.getMIRType(idecl.params[0].type), new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = new SMTCallSimple("seq.nth", [sval, idx]);
                }
                else {
                    cbody = this.typegen.generateArrayEntryTypeGetValue(this.typegen.getMIRType(idecl.params[0].type), new SMTCallSimple("select", [sval, idx]));
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_get_front": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(this.typegen.getMIRType(idecl.params[0].type), new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = new SMTCallSimple("seq.nth", [sval, new SMTConst("0")]);
                }
                else {
                    cbody = this.typegen.generateArrayEntryTypeGetValue(this.typegen.getMIRType(idecl.params[0].type), new SMTCallSimple("select", [sval, new SMTConst("0")]));
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_set": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(mirrestype, new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = new SMTLet("sval", sval, this.typegen.generateListTypeConstructorSeq(mirrestype, new SMTCallSimple("seq.++", [
                        new SMTCallSimple("seq.extract", [new SMTVar("sval"), new SMTConst("0"), new SMTVar(args[1].vname)]),
                        new SMTCallSimple("seq.unit", [new SMTVar(args[2].vname)]),
                        new SMTCallSimple("seq.extract", [new SMTVar("sval"),
                        new SMTCallSimple("+", [new SMTVar(args[1].vname), new SMTConst("1")]),
                        new SMTCallSimple("-", [this.typegen.generateListTypeGetLength(mirrestype, new SMTVar(args[0].vname)), new SMTCallSimple("+", [new SMTVar(args[1].vname), new SMTConst("1")])
                        ])])
                    ])));
                }
                else {
                    cbody = this.typegen.generateListTypeConstructorArray(mirrestype, 
                        this.typegen.generateListTypeGetLength(mirrestype, new SMTVar(args[0].vname)), 
                        new SMTCallSimple("store", [sval, new SMTVar(args[1].vname), this.typegen.generateArrayEntryTypeConstructorValid(mirrestype, new SMTVar(args[1].vname), new SMTVar(args[2].vname))])
                    );
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_push_back": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(mirrestype, new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = this.typegen.generateListTypeConstructorSeq(mirrestype, new SMTCallSimple("seq.++", [
                        sval,
                        new SMTCallSimple("seq.unit", [new SMTVar(args[1].vname)])
                    ]));
                }
                else {
                    cbody = this.typegen.generateListTypeConstructorArray(mirrestype, 
                        new SMTCallSimple("+", [this.typegen.generateListTypeGetLength(mirrestype, new SMTVar(args[0].vname)), new SMTConst("1")]), 
                        new SMTCallSimple("store", [sval, this.typegen.generateListTypeSeq_GetLengthMinus1(mirrestype, new SMTVar(args[0].vname)), this.typegen.generateArrayEntryTypeConstructorValid(mirrestype, this.typegen.generateListTypeSeq_GetLengthMinus1(mirrestype, new SMTVar(args[0].vname)), new SMTVar(args[2].vname))])
                    );
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_push_front": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(mirrestype, new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = this.typegen.generateListTypeConstructorSeq(mirrestype, new SMTCallSimple("seq.++", [
                        new SMTCallSimple("seq.unit", [new SMTVar(args[1].vname)]),
                        sval
                    ]));
                }
                else {
                    cbody = NOT_IMPLEMENTED("s_list_push_front array");
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_remove": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(mirrestype, new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = new SMTLet("sval", sval, this.typegen.generateListTypeConstructorSeq(mirrestype, new SMTCallSimple("seq.++", [
                        new SMTCallSimple("seq.extract", [new SMTVar("sval"), new SMTConst("0"), new SMTVar(args[1].vname)]),
                        new SMTCallSimple("seq.extract", [new SMTVar("sval"),
                        new SMTCallSimple("+", [new SMTVar(args[1].vname), new SMTConst("1")]),
                        new SMTCallSimple("-", [this.typegen.generateListTypeGetLength(mirrestype, new SMTVar(args[0].vname)), new SMTCallSimple("+", [new SMTVar(args[1].vname), new SMTConst("1")])
                        ])])
                    ])));
                }
                else {
                    cbody = NOT_IMPLEMENTED("s_list_remove array");
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_pop_back": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(mirrestype, new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = this.typegen.generateListTypeConstructorSeq(mirrestype, new SMTCallSimple("seq.extract", [
                        sval,
                        new SMTConst("0"),
                        this.typegen.generateListTypeSeq_GetLengthMinus1(mirrestype, new SMTVar(args[0].vname))
                    ]));
                }
                else {
                    cbody = this.typegen.generateListTypeConstructorArray(mirrestype, 
                        this.typegen.generateListTypeSeq_GetLengthMinus1(mirrestype, new SMTVar(args[0].vname)), 
                        new SMTCallSimple("store", [sval, this.typegen.generateListTypeSeq_GetLengthMinus1(mirrestype, new SMTVar(args[0].vname)), this.typegen.generateArrayEntryTypeConstructorEmpty(mirrestype)])
                    );
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            } 
            case "s_list_pop_front": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(mirrestype, new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = this.typegen.generateListTypeConstructorSeq(mirrestype, new SMTCallSimple("seq.extract", [
                        sval,
                        new SMTConst("1"),
                        this.typegen.generateListTypeSeq_GetLengthMinus1(mirrestype, new SMTVar(args[0].vname))
                    ]));
                }
                else {
                    cbody = NOT_IMPLEMENTED("s_list_pop_front array");
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_map_pred": {
                const lt = this.typegen.getMIRType(idecl.params[0].type);
                const sval = this.typegen.generateListTypeGetData(lt, new SMTVar(args[0].vname));

                const pc = idecl.pcodes.get("p") as MIRPCode;
                const pcdcl = this.typegen.assembly.invokeDecls.get(pc.code) as MIRInvokeDecl;
                const argtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(pcdcl.params[0].type));
                const pcfn = this.typegen.lookupFunctionName(pc.code);
                const captured = pc.cargs.map((carg) => carg.cname);

                const implicitlambdas = [pcfn];

                if (this.vopts.ARRAY_MODE === "Seq") {
                    const maparray = new SMTCallSimple("seq.map", [
                        new SMTConst(`(lambda ((@@x ${argtype.smttypename})) (${pcfn} @@x${captured.length !== 0 ? (" " + captured.join(" ")) : ""}))`),
                        sval
                    ]);

                    if (this.isSafeInvoke(pc.code)) {
                        return SMTFunction.createWithImplicitLambdas(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, this.typegen.generateListTypeConstructorSeq(mirrestype, maparray), implicitlambdas);
                    }
                    else {
                        const trgterr = new SMTCallSimple("seq.unit", [this.typegen.generateResultTypeConstructorError(this.typegen.getMIRType("Bool"), new SMTConst("ErrorID_Target"))]);
                        const trgtresulterr = this.typegen.generateResultTypeConstructorError(mirrestype, new SMTConst("ErrorID_Target"));
                        const othererr = new SMTCallSimple("seq.unit", [this.typegen.generateResultTypeConstructorError(this.typegen.getMIRType("Bool"), new SMTConst("ErrorID_AssumeCheck"))]);
                        const otherresulterr = this.typegen.generateResultTypeConstructorError(mirrestype, new SMTConst("ErrorID_AssumeCheck"));

                        const values = new SMTCallSimple("seq.map", [
                            new SMTConst(`(lambda ((@@r ${this.typegen.generateResultType(this.typegen.getMIRType("Bool")).smttypename})) ${this.typegen.generateResultGetSuccess(this.typegen.getMIRType("Bool"), new SMTVar("@@r")).emitSMT2(undefined)})`),
                            new SMTVar("@maparray")
                        ]);

                        const cbody = new SMTLet("@maparray", maparray,
                            new SMTLetMulti([{ vname: "@trgterr", value: new SMTCallSimple("seq.contains", [new SMTVar("@maparray"), trgterr]) }, { vname: "@othererr", value: new SMTCallSimple("seq.contains", [new SMTVar("@maparray"), othererr]) }],
                                new SMTIf(new SMTVar("@trgterr"),
                                    trgtresulterr,
                                    new SMTIf(new SMTVar("@othererr"),
                                        otherresulterr,
                                        this.typegen.generateResultTypeConstructorSuccess(mirrestype, this.typegen.generateListTypeConstructorSeq(mirrestype, values))
                                    )
                                )
                            )
                        );

                        return SMTFunction.createWithImplicitLambdas(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody, implicitlambdas);
                    }
                }
                else {
                    const cbody = NOT_IMPLEMENTED("s_list_map_pred array");
                    return SMTFunction.createWithImplicitLambdas(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody, implicitlambdas);
                }
            }
            case "s_llist_map_pred_idx": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
            }
            case "s_list_map_fn": {
                const lt = this.typegen.getMIRType(idecl.params[0].type);
                const sval = this.typegen.generateListTypeGetData(lt, new SMTVar(args[0].vname));

                const pc = idecl.pcodes.get("f") as MIRPCode;
                const pcdcl = this.typegen.assembly.invokeDecls.get(pc.code) as MIRInvokeDecl;
                const argtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(pcdcl.params[0].type));
                const pcfn = this.typegen.lookupFunctionName(pc.code);
                const captured = pc.cargs.map((carg) => carg.cname);

                const implicitlambdas = [pcfn];

                if (this.vopts.ARRAY_MODE === "Seq") {
                    const maparray = new SMTCallSimple("seq.map", [
                        new SMTConst(`(lambda ((@@x ${argtype.smttypename})) (${pcfn} @@x${captured.length !== 0 ? (" " + captured.join(" ")) : ""}))`),
                        sval
                    ]);

                    if (this.isSafeInvoke(pc.code)) {
                        return SMTFunction.createWithImplicitLambdas(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, this.typegen.generateListTypeConstructorSeq(mirrestype, maparray), implicitlambdas);
                    }
                    else {
                        const mirresult_T = (this.typegen.assembly.entityDecls.get(mirrestype.typeID) as MIRPrimitiveInternalEntityTypeDecl).terms.get("T") as MIRType;

                        const trgterr = new SMTCallSimple("seq.unit", [this.typegen.generateResultTypeConstructorError(mirresult_T, new SMTConst("ErrorID_Target"))]);
                        const trgtresulterr = this.typegen.generateResultTypeConstructorError(mirrestype, new SMTConst("ErrorID_Target"));
                        const othererr = new SMTCallSimple("seq.unit", [this.typegen.generateResultTypeConstructorError(mirresult_T, new SMTConst("ErrorID_AssumeCheck"))]);
                        const otherresulterr = this.typegen.generateResultTypeConstructorError(mirrestype, new SMTConst("ErrorID_AssumeCheck"));

                        const values = new SMTCallSimple("seq.map", [
                            new SMTConst(`(lambda ((@@r ${this.typegen.generateResultType(mirresult_T).smttypename})) ${this.typegen.generateResultGetSuccess(mirresult_T, new SMTVar("@@r")).emitSMT2(undefined)})`),
                            new SMTVar("@maparray")
                        ]);

                        const cbody = new SMTLet("@maparray", maparray,
                            new SMTLetMulti([{ vname: "@trgterr", value: new SMTCallSimple("seq.contains", [new SMTVar("@maparray"), trgterr]) }, { vname: "@othererr", value: new SMTCallSimple("seq.contains", [new SMTVar("@maparray"), othererr]) }],
                                new SMTIf(new SMTVar("@trgterr"),
                                    trgtresulterr,
                                    new SMTIf(new SMTVar("@othererr"),
                                        otherresulterr,
                                        this.typegen.generateResultTypeConstructorSuccess(mirrestype, this.typegen.generateListTypeConstructorSeq(mirrestype, values))
                                    )
                                )
                            )
                        );

                        return SMTFunction.createWithImplicitLambdas(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody, implicitlambdas);
                    }
                }
                else {
                    const cbody = NOT_IMPLEMENTED("s_list_map_fn array");
                    return SMTFunction.createWithImplicitLambdas(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody, implicitlambdas);
                }
            }
            case "s_list_map_fn_idx": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
            }
            case "s_list_has": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(this.typegen.getMIRType(idecl.params[0].type), new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = new SMTCallSimple("seq.contains", [sval, new SMTCallSimple("seq.unit", [new SMTVar(args[1].vname)])]);
                }
                else {
                    cbody = NOT_IMPLEMENTED("s_list_has array");
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_indexof": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(this.typegen.getMIRType(idecl.params[0].type), new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = new SMTCallSimple("seq.indexof", [sval, new SMTCallSimple("seq.unit", [new SMTVar(args[1].vname)])]);
                }
                else {
                    cbody = NOT_IMPLEMENTED("s_list_indexof array");
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_last_indexof": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(this.typegen.getMIRType(idecl.params[0].type), new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = new SMTCallSimple("seq.last_indexof", [sval, new SMTCallSimple("seq.unit", [new SMTVar(args[1].vname)])]);
                }
                else {
                    cbody = NOT_IMPLEMENTED("s_list_last_indexof array");
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_has_true": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(this.typegen.getMIRType(idecl.params[0].type), new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = new SMTCallSimple("seq.contains", [sval, new SMTCallSimple("seq.unit", [new SMTConst("true")])]);
                }
                else {
                    cbody = NOT_IMPLEMENTED("s_list_has_true array");
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_has_false": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(this.typegen.getMIRType(idecl.params[0].type), new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = new SMTCallSimple("seq.contains", [sval, new SMTCallSimple("seq.unit", [new SMTConst("false")])]);
                }
                else {
                    cbody = NOT_IMPLEMENTED("s_list_has_false array");
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_single_true": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(this.typegen.getMIRType(idecl.params[0].type), new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    const call_left = new SMTCallSimple("seq.indexof", [sval, new SMTCallSimple("seq.unit", [new SMTConst("true")])]);
                    const call_right = new SMTCallSimple("seq.last_indexof", [sval, new SMTCallSimple("seq.unit", [new SMTConst("true")])]);

                    cbody = new SMTLet("lidx", call_left, 
                        new SMTIf(SMTCallSimple.makeEq(new SMTVar("lidx"), new SMTConst("-1")),
                            new SMTConst("false"),
                            new SMTLet("ridx", call_right, 
                                SMTCallSimple.makeEq(new SMTVar("lidx"), new SMTVar("ridx"))
                            )
                        )
                    );
                }
                else {
                    cbody = NOT_IMPLEMENTED("s_list_indexof_true array");
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_single_indexof_true": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(this.typegen.getMIRType(idecl.params[0].type), new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    const call_left = new SMTCallSimple("seq.indexof", [sval, new SMTCallSimple("seq.unit", [new SMTConst("true")])]);
                    const call_right = new SMTCallSimple("seq.last_indexof", [sval, new SMTCallSimple("seq.unit", [new SMTConst("true")])]);

                    cbody = new SMTLet("lidx", call_left, 
                        new SMTIf(SMTCallSimple.makeEq(new SMTVar("lidx"), new SMTConst("-1")),
                            new SMTConst("-1"),
                            new SMTLet("ridx", call_right, 
                                new SMTIf(SMTCallSimple.makeEq(new SMTVar("lidx"), new SMTVar("ridx")),
                                    new SMTVar("lidx"),
                                    new SMTConst("-1")
                                )
                            )
                        )
                    );
                }
                else {
                    cbody = NOT_IMPLEMENTED("s_list_indexof_true array");
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_indexof_true": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(this.typegen.getMIRType(idecl.params[0].type), new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = new SMTCallSimple("seq.indexof", [sval, new SMTCallSimple("seq.unit", [new SMTConst("true")])]);
                }
                else {
                    cbody = NOT_IMPLEMENTED("s_list_indexof_true array");
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_last_indexof_true": {
                let cbody: SMTExp = new SMTConst("[UNDEF]");
                const sval = this.typegen.generateListTypeGetData(this.typegen.getMIRType(idecl.params[0].type), new SMTVar(args[0].vname));
                if (this.vopts.ARRAY_MODE === "Seq") {
                    cbody = new SMTCallSimple("seq.last_indexof", [sval, new SMTCallSimple("seq.unit", [new SMTConst("true")])]);
                }
                else {
                    cbody = NOT_IMPLEMENTED("s_list_last_indexof_true array");
                }
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_list_reduce": {
                const lt = this.typegen.getMIRType(idecl.params[0].type);
                const sval = this.typegen.generateListTypeGetData(lt, new SMTVar(args[0].vname));

                const pc = idecl.pcodes.get("f") as MIRPCode;
                const pcdcl = this.typegen.assembly.invokeDecls.get(pc.code) as MIRInvokeDecl;
                const argtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(pcdcl.params[0].type));
                const pcfn = this.typegen.lookupFunctionName(pc.code);
                const captured = pc.cargs.map((carg) => carg.cname);

                const implicitlambdas = [pcfn];

                if (this.vopts.ARRAY_MODE === "Seq") {
                    if (this.isSafeInvoke(pc.code)) {
                        const foldcall = new SMTCallSimple("seq.foldl", [
                            new SMTConst(`(lambda ((@@acc ${this.typegen.getSMTTypeFor(mirrestype).smttypename}) (@@x ${argtype.smttypename})) (${pcfn} @@acc @@x${captured.length !== 0 ? (" " + captured.join(" ")) : ""}))`),
                            new SMTVar(args[1].vname),
                            sval
                        ]);

                        return SMTFunction.createWithImplicitLambdas(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, foldcall, implicitlambdas);
                    }
                    else {
                        const resultsmtu = this.typegen.generateResultType(mirrestype);
                        const foldcall = new SMTCallSimple("seq.foldl", [
                            new SMTConst(`(lambda ((@@acc ${resultsmtu.smttypename}) (@@x ${argtype.smttypename})) (ite (${this.typegen.generateResultIsErrorTest(mirrestype, new SMTVar("@@acc"))}) @acc (${pcfn} ${this.typegen.generateResultGetSuccess(mirrestype, new SMTVar("@@acc")).emitSMT2(undefined)} @@x${captured.length !== 0 ? (" " + captured.join(" ")) : ""})))`),
                            this.typegen.generateResultTypeConstructorSuccess(mirrestype, new SMTVar(args[1].vname)),
                            sval
                        ]);

                        return SMTFunction.createWithImplicitLambdas(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, foldcall, implicitlambdas);
                    }
                }
                else {
                    const cbody = NOT_IMPLEMENTED("s_list_reduce array");
                    return SMTFunction.createWithImplicitLambdas(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody, implicitlambdas);
                }
            }
            case "s_map_empty": {
                const mt = this.typegen.getMIRType(idecl.params[0].type);
                const emptyconst = this.typegen.getSMTTypeFor(mt).smttypename + "@@empty";
                const cbody = SMTCallSimple.makeEq(new SMTVar(args[0].vname), new SMTConst(emptyconst));
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_map_count": {
                const mt = this.typegen.getMIRType(idecl.params[0].type);
                const cbody = this.typegen.generateMapTypeGetLength(mt, new SMTVar(args[0].vname));
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_map_has": {
                const mt = this.typegen.getMIRType(idecl.params[0].type);
                const cbody = SMTCallSimple.makeNotEq(
                    this.typegen.generateMapEntryTypeConstructorEmpty(mt),
                    new SMTCallSimple("select", [this.typegen.generateMapTypeGetArray(mt, new SMTVar(args[0].vname)), new SMTVar(args[1].vname)])
                );
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_map_get": {
                const mt = this.typegen.getMIRType(idecl.params[0].type);
                const cbody = this.typegen.generateMapEntryTypeGetValueTuple(mt, new SMTCallSimple("select", [this.typegen.generateMapTypeGetArray(mt, new SMTVar(args[0].vname)), new SMTVar(args[1].vname)]));
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_map_disjoint": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
            }
            case "s_map_union": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
            }
            case "s_map_add": {
                const cbody = this.typegen.generateMapTypeConstructor(mirrestype, 
                    new SMTCallSimple("+", [this.typegen.generateMapTypeGetLength(mirrestype, new SMTVar(args[0].vname)), new SMTConst("1")]),
                    new SMTCallSimple("store", [
                        this.typegen.generateMapTypeGetArray(mirrestype, new SMTVar(args[0].vname)), 
                        new SMTVar(args[1].vname),
                        new SMTVar(args[2].vname)
                    ])
                );
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_map_set": {
                const cbody = this.typegen.generateMapTypeConstructor(mirrestype, 
                    this.typegen.generateMapTypeGetLength(mirrestype, new SMTVar(args[0].vname)),
                    new SMTCallSimple("store", [
                        this.typegen.generateMapTypeGetArray(mirrestype, new SMTVar(args[0].vname)), 
                        new SMTVar(args[1].vname),
                        this.typegen.generateMapEntryTypeConstructorEmpty(mirrestype)
                    ])
                );
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_map_remove": {
                const cbody = this.typegen.generateMapTypeConstructor(mirrestype, 
                    new SMTCallSimple("-", [this.typegen.generateMapTypeGetLength(mirrestype, new SMTVar(args[0].vname)), new SMTConst("1")]),
                    new SMTCallSimple("store", [
                        this.typegen.generateMapTypeGetArray(mirrestype, new SMTVar(args[0].vname)), 
                        new SMTVar(args[1].vname),
                        this.typegen.generateMapEntryTypeConstructorEmpty(mirrestype)
                    ])
                );
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, cbody);
            }
            case "s_blockingfailure": {
                return SMTFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, this.typegen.generateErrorResultAssert(mirrestype));
            }
            default: {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
                return undefined;
            }
        }
    }
}

export {
     SMTBodyEmitter
};
