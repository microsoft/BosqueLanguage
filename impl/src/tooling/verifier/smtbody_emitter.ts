//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRConceptType, MIREntityType, MIREntityTypeDecl, MIREphemeralListType, MIRFieldDecl, MIRInvokeBodyDecl, MIRInvokeDecl, MIRInvokePrimitiveDecl, MIRPCode, MIRRecordType, MIRRecordTypeEntry, MIRTupleType, MIRType } from "../../compiler/mir_assembly";
import { SMTTypeEmitter } from "./smttype_emitter";
import { MIRAbort, MIRAllTrue, MIRArgGuard, MIRArgument, MIRAssertCheck, MIRBasicBlock, MIRBinKeyEq, MIRBinKeyLess, MIRConstantArgument, MIRConstantBigInt, MIRConstantBigNat, MIRConstantDataString, MIRConstantDecimal, MIRConstantFalse, MIRConstantFloat, MIRConstantInt, MIRConstantNat, MIRConstantNone, MIRConstantRational, MIRConstantRegex, MIRConstantString, MIRConstantStringOf, MIRConstantTrue, MIRConstantTypedNumber, MIRConstructorEphemeralList, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionMixed, MIRConstructorPrimaryCollectionSingletons, MIRConstructorRecord, MIRConstructorRecordFromEphemeralList, MIRConstructorTuple, MIRConstructorTupleFromEphemeralList, MIRConvertValue, MIRDeclareGuardFlagLocation, MIREntityProjectToEphemeral, MIREntityUpdate, MIREphemeralListExtend, MIRFieldKey, MIRGlobalVariable, MIRGuard, MIRInvokeFixedFunction, MIRInvokeKey, MIRInvokeVirtualFunction, MIRInvokeVirtualOperator, MIRIsTypeOf, MIRJump, MIRJumpCond, MIRJumpNone, MIRLoadConst, MIRLoadField, MIRLoadFromEpehmeralList, MIRLoadRecordProperty, MIRLoadRecordPropertySetGuard, MIRLoadTupleIndex, MIRLoadTupleIndexSetGuard, MIRLoadUnintVariableValue, MIRMaskGuard, MIRMultiLoadFromEpehmeralList, MIROp, MIROpTag, MIRPrefixNotOp, MIRRecordHasProperty, MIRRecordProjectToEphemeral, MIRRecordUpdate, MIRRegisterArgument, MIRRegisterAssign, MIRResolvedTypeKey, MIRReturnAssign, MIRReturnAssignOfCons, MIRSetConstantGuardFlag, MIRSliceEpehmeralList, MIRStructuredAppendTuple, MIRStructuredJoinRecord, MIRTupleHasIndex, MIRTupleProjectToEphemeral, MIRTupleUpdate, MIRVerifierAssume, MIRVirtualMethodKey } from "../../compiler/mir_ops";
import { SMTCallSimple, SMTCallGeneral, SMTCallGeneralWOptMask, SMTCond, SMTConst, SMTExp, SMTIf, SMTLet, SMTLetMulti, SMTMaskConstruct, SMTVar, SMTCallGeneralWPassThroughMask, SMTType, VerifierOptions } from "./smt_exp";
import { SourceInfo } from "../../ast/parser";
import { SMTFunction, SMTFunctionUninterpreted } from "./smt_assembly";

import * as assert from "assert";

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

    requiredCollectionConstructors_Literal: { cname: MIRInvokeKey, oftype: MIRResolvedTypeKey, argc: number }[] = []; //base constructors of known size of literal arguments (empty and literal)
    requiredCollectionConstructors_Combine: { cname: MIRInvokeKey, oftype: MIRResolvedTypeKey, argc: number }[] = []; //base constructors of append or union (copy and mixed)
    requiredCollectionConstructors_Structured: { cname: MIRInvokeKey, oftype: MIRResolvedTypeKey, argc: number }[] = []; //operations which structurally build lists (append, zip, unzipt, etc.)
    requiredCollectionConstructors_Computational: { cname: MIRInvokeKey, oftype: MIRResolvedTypeKey, argc: number }[] = []; //operations which computationally build lists (map, filter, join, etc.)

    requiredCollectionDestructorsPrimitive_Bool: { cname: MIRInvokeKey, oftype: MIRResolvedTypeKey, argc: number }[] = []; //operations which extract bools using primitive operations (find, etc.)
    requiredCollectionDestructorsComputational_Bool: { cname: MIRInvokeKey, oftype: MIRResolvedTypeKey, argc: number }[] = []; //operations which computationally extract bools using functors (allof, etc.)
    requiredCollectionDestructors_PrimitiveNat: { cname: MIRInvokeKey, oftype: MIRResolvedTypeKey, argc: number }[] = []; //operations which extract bools using primitive operations (count, indexof, etc.)
    requiredCollectionDestructorsComputational_Nat: { cname: MIRInvokeKey, oftype: MIRResolvedTypeKey, argc: number }[] = []; //operations which computationally extract bools using functors (countif, allof, etc.)
    //always implicit get operator too!!!

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
    requiredUpdateVirtualEntity: { inv: string, argflowtype: MIRType,  allsafe: boolean, updates: [MIRFieldKey, MIRResolvedTypeKey][], resulttype: MIRType }[] = [];

    requiredVirtualFunctionInvokes: { inv: string, allsafe: boolean, argflowtype: MIRType, vfname: MIRVirtualMethodKey, optmask: string | undefined, resulttype: MIRType }[] = [];
    requiredVirtualOperatorInvokes: { inv: string, argflowtype: MIRType, opname: MIRVirtualMethodKey, args: MIRResolvedTypeKey[], resulttype: MIRType }[] = [];

    requiredSubtypeTagChecks: {t: MIRType, oftype: MIRType}[] = [];
    requiredIndexTagChecks: {idx: number, oftype: MIRType}[] = [];
    requiredRecordTagChecks: {pname: string, oftype: MIRType}[] = [];

    private processSubtypeTagCheck(t: MIRType, oftype: MIRType) {
        const stc = this.requiredSubtypeTagChecks.find((tc) => tc.t.trkey === t.trkey && tc.oftype.trkey === oftype.trkey);
        if (stc === undefined) {
            this.requiredSubtypeTagChecks.push({ t: t, oftype: oftype });
        }
    }

    private processIndexTagCheck(idx: number, oftype: MIRType) {
        const stc = this.requiredIndexTagChecks.find((tc) => tc.idx === idx && tc.oftype.trkey === oftype.trkey);
        if (stc === undefined) {
            this.requiredIndexTagChecks.push({ idx: idx, oftype: oftype });
        }
    }

    private processPropertyTagCheck(pname: string, oftype: MIRType) {
        const stc = this.requiredRecordTagChecks.find((tc) => tc.pname === pname && tc.oftype.trkey === oftype.trkey);
        if (stc === undefined) {
            this.requiredRecordTagChecks.push({ pname: pname, oftype: oftype });
        }
    }

    private generateTypeCheckName(argflowtype: MIRType, oftype: MIRType): string {
        return `$SubtypeCheck_${this.typegen.mangle(argflowtype.trkey)}_oftype_${this.typegen.mangle(oftype.trkey)}`;
    }

    private registerRequiredTypeCheck(argflowtype: MIRType, oftype: MIRType): string {
        const inv = this.generateTypeCheckName(argflowtype, oftype);
        if (this.requiredTypecheck.findIndex((rtc) => rtc.inv === inv) === -1) {
            this.requiredTypecheck.push({ inv: inv, flowtype: argflowtype, oftype: oftype });
        }

        return inv;
    }

    private generateConstructorOfSizeName(oftype: MIRResolvedTypeKey, argc: number): string {
        return `@@cons_${this.typegen.mangle(oftype)}_k_${argc}`;
    }

    private generateUFConstantForType(tt: MIRType): string {
        const ctype = this.typegen.getSMTTypeFor(tt);
        const ufcname = `${ctype}@uicons_UF`;
        
        return ufcname;
    }

    private generateBoolForGuard(guard: MIRGuard): SMTExp {
        if(guard instanceof MIRMaskGuard) {
            return new SMTCallSimple(`$Mask_${guard.gsize}@${guard.gindex}`, [new SMTVar(this.typegen.mangle(guard.gmask))]);
        }
        else {
            return this.argToSMT((guard as MIRArgGuard).greg);
        }
    }

    private generateAltForGuardStmt(arg: MIRArgument | undefined, oftype: MIRType): SMTExp {
        return arg !== undefined ? this.argToSMT(arg) : new SMTConst(this.generateUFConstantForType(oftype));
    }

    private generateGeneralCallValueProcessing(callerrtype: MIRType, calleertype: MIRType, gcall: SMTExp, trgt: MIRRegisterArgument, continuation: SMTExp): SMTLet {
        const cres = this.generateTempName();
        
        const okpath = new SMTLet(this.varToSMTName(trgt).vname, this.typegen.generateResultGetSuccess(calleertype, new SMTVar(cres)), continuation);
        const errpath = (callerrtype.trkey === calleertype.trkey) ? new SMTVar(cres) : this.typegen.generateResultTypeConstructorError(calleertype, this.typegen.generateResultGetError(calleertype, new SMTVar(cres)));

        const icond = new SMTIf(this.typegen.generateResultIsErrorTest(calleertype, new SMTVar(cres)), errpath, okpath);
        return new SMTLet(cres, gcall, icond);
    }

    private generateLoadVirtualTupleInvName(argflowtype: MIRType, idx: number, resulttype: MIRType, guard: MIRGuard | undefined): string {
        return `$TupleLoad_${this.typegen.mangle(argflowtype.trkey)}_${idx}_${this.typegen.mangle(resulttype.trkey)}${guard !== undefined ? "_WG" : ""}`;
    }

    private generateLoadVirtualPropertyInvName(argflowtype: MIRType, pname: string, resulttype: MIRType, guard: MIRGuard | undefined): string {
        return `$RecordLoad_${this.typegen.mangle(argflowtype.trkey)}_${pname}_${this.typegen.mangle(resulttype.trkey)}${guard !== undefined ? "_WG" : ""}`;
    }

    private generateLoadVirtualFieldInvName(argflowtype: MIRType, fkey: MIRFieldKey, resulttype: MIRType): string {
        return `$EntityLoad_${this.typegen.mangle(argflowtype.trkey)}_${this.typegen.mangle(fkey)}_${this.typegen.mangle(resulttype.trkey)}`;
    }

    private generateProjectVirtualTupleInvName(argflowtype: MIRType, indecies: number[], resulttype: MIRType): string {
        const idxs = this.typegen.mangle(indecies.map((idx) => `${idx}`).join(","));
        return `$TupleProject_${this.typegen.mangle(argflowtype.trkey)}_${idxs}_${this.typegen.mangle(resulttype.trkey)}`;
    }

    private generateProjectVirtualRecordInvName(argflowtype: MIRType, properties: string[], resulttype: MIRType): string {
        const pnames = this.typegen.mangle(properties.join(","));
        return `$RecordProject_${this.typegen.mangle(argflowtype.trkey)}_${pnames}_${this.typegen.mangle(resulttype.trkey)}`;
    }

    private generateProjectVirtualEntityInvName(argflowtype: MIRType, fields: MIRFieldKey[], resulttype: MIRType): string {
        const fkeys = this.typegen.mangle(fields.join(","));
        return `$EntityProject_${this.typegen.mangle(argflowtype.trkey)}_${fkeys}_${this.typegen.mangle(resulttype.trkey)}`;
    }

    private generateUpdateVirtualTupleInvName(argflowtype: MIRType, indecies: [number, MIRResolvedTypeKey][], resulttype: MIRType): string {
        const idxs = this.typegen.mangle(indecies.map((idx) => `(${idx[0]} ${idx[1]})`).join(","));
        return `$TupleUpdate_${this.typegen.mangle(argflowtype.trkey)}_${idxs}_${this.typegen.mangle(resulttype.trkey)}`;
    }

    private generateUpdateVirtualRecordInvName(argflowtype: MIRType, properties: [string, MIRResolvedTypeKey][], resulttype: MIRType): string {
        const pnames = this.typegen.mangle(properties.map((pname) => `(${pname[0]} ${pname[1]})`).join(","));
        return `$RecordUpdate_${this.typegen.mangle(argflowtype.trkey)}_${pnames}_${this.typegen.mangle(resulttype.trkey)}`;
    }

    private generateUpdateVirtualEntityInvName(argflowtype: MIRType, fields: [MIRFieldKey, MIRResolvedTypeKey][], resulttype: MIRType): string {
        const fnames = this.typegen.mangle(fields.map((fname) => `(${fname[0]} ${fname[1]})`).join(","));
        return `$EntityUpdate_${this.typegen.mangle(argflowtype.trkey)}_${fnames}_${this.typegen.mangle(resulttype.trkey)}`;
    }

    private generateVirtualInvokeFunctionName(argflowtype: MIRType, fname: MIRVirtualMethodKey, optmask: boolean, resulttype: MIRType): string {
        const rname = this.typegen.mangle(fname);
        return `$VirtualInvoke_${this.typegen.mangle(argflowtype.trkey)}_${rname}${optmask ? "_WM_" : ""}_${this.typegen.mangle(resulttype.trkey)}`;
    }

    private generateVirtualInvokeOperatorName(fname: MIRVirtualMethodKey, rcvrtypes: MIRResolvedTypeKey[], resulttype: MIRType): string {
        const rnames = this.typegen.mangle(`${fname}::(${rcvrtypes.join(",")})`);
        return `$VirtualOperator_${rnames}_${this.typegen.mangle(resulttype.trkey)}`;
    }

    private generateLoadTupleIndexVirtual(geninfo: { inv: string, argflowtype: MIRType, idx: number, resulttype: MIRType, guard: MIRGuard | undefined }): SMTFunction {
        const ttuples = [...this.assembly.tupleDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].trkey);
                return this.typegen.isUniqueTupleType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultType(geninfo.resulttype) : this.typegen.getSMTTypeFor(geninfo.resulttype);
        const ufcname = this.generateUFConstantForType(geninfo.resulttype);
        if(ttuples.length === 0) {
            const rbody = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, new SMTConst(ufcname), false) : new SMTConst(ufcname);
            return new SMTFunction(geninfo.inv, [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], undefined, rtype, rbody);
        }
        else {
            const ops = ttuples.map((tt) => {
                const mtt = this.typegen.getMIRType(tt.trkey);
                const test = new SMTCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

                const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
                const idxr = new SMTCallSimple(this.typegen.generateTupleIndexGetFunction(tt, geninfo.idx), [argpp]);
                const crt = this.typegen.coerce(idxr, (geninfo.argflowtype.options[0] as MIRTupleType).entries[geninfo.idx].type, geninfo.resulttype);
                const action = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, crt, true) : crt;

                return {test: test, result: action};
            });

            const orelse = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, new SMTConst(ufcname), false) : new SMTConst(ufcname);

            return new SMTFunction(geninfo.inv, [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], undefined, rtype, new SMTCond(ops, orelse));
        }
    }

    private generateLoadRecordPropertyVirtual(geninfo: { inv: string, argflowtype: MIRType, pname: string, resulttype: MIRType, guard: MIRGuard | undefined }): SMTFunction {
        const trecords = [...this.assembly.recordDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].trkey);
                return this.typegen.isUniqueRecordType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultType(geninfo.resulttype) : this.typegen.getSMTTypeFor(geninfo.resulttype);
        const ufcname = this.generateUFConstantForType(geninfo.resulttype);
        if(trecords.length === 0) {
            const rbody = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, new SMTConst(ufcname), false) : new SMTConst(ufcname);
            return new SMTFunction(geninfo.inv, [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], undefined, rtype, rbody);
        }
        else {
            const ops = trecords.map((tt) => {
                const mtt = this.typegen.getMIRType(tt.trkey);
                const test = new SMTCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

                const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
                const idxr = new SMTCallSimple(this.typegen.generateRecordPropertyGetFunction(tt, geninfo.pname), [argpp]);
                const crt = this.typegen.coerce(idxr, ((geninfo.argflowtype.options[0] as MIRRecordType).entries.find((vv) => vv.name === geninfo.pname) as MIRRecordTypeEntry).type, geninfo.resulttype);
                const action = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, crt, true) : crt;

                return {test: test, result: action};
            });

            const orelse = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, new SMTConst(ufcname), false) : new SMTConst(ufcname);

            return new SMTFunction(geninfo.inv, [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], undefined, rtype, new SMTCond(ops, orelse));
        }
    }

    private generateLoadEntityFieldVirtual(geninfo: { inv: string, argflowtype: MIRType, field: MIRFieldDecl, resulttype: MIRType }): SMTFunction {
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
            const action = new SMTCallSimple(this.typegen.generateEntityFieldGetFunction(tt, geninfo.field.fkey), [argpp]);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        return new SMTFunction(geninfo.inv, [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], undefined, rtype, new SMTCond(ops, orelse));
    }

    private generateProjectTupleIndexVirtual(geninfo: { inv: string, argflowtype: MIRType, indecies: number[], resulttype: MIRType }): SMTFunction {
        const ttuples = [...this.assembly.tupleDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].trkey);
                return this.typegen.isUniqueTupleType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getSMTTypeFor(geninfo.resulttype);
        let ops = ttuples.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.trkey);
            const test = new SMTCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

            const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
            const pargs = geninfo.indecies.map((idx, i) => {
                const idxr = new SMTCallSimple(this.typegen.generateTupleIndexGetFunction(geninfo.argflowtype.options[0] as MIRTupleType, idx), [argpp]);
                return this.typegen.coerce(idxr, (geninfo.argflowtype.options[0] as MIRTupleType).entries[idx].type, (geninfo.resulttype.options[0] as MIREphemeralListType).entries[i]);
            });
            const action = new SMTCallSimple(this.typegen.getSMTConstructorName(geninfo.resulttype).cons, pargs);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);
            
        return new SMTFunction(geninfo.inv, [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], undefined, rtype, new SMTCond(ops, orelse));
    }

    private generateProjectRecordPropertyVirtual(geninfo: { inv: string, argflowtype: MIRType, properties: string[], resulttype: MIRType }): SMTFunction {
        const trecords = [...this.assembly.recordDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].trkey);
                return this.typegen.isUniqueRecordType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getSMTTypeFor(geninfo.resulttype);
        let ops = trecords.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.trkey);
            const test = new SMTCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

            const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
            const pargs = geninfo.properties.map((pname, i) => {
                const idxr = new SMTCallSimple(this.typegen.generateRecordPropertyGetFunction(geninfo.argflowtype.options[0] as MIRRecordType, pname), [argpp]);
                return this.typegen.coerce(idxr, ((geninfo.argflowtype.options[0] as MIRRecordType).entries.find((vv) => vv.name === pname) as MIRRecordTypeEntry).type, (geninfo.resulttype.options[0] as MIREphemeralListType).entries[i]);
            });
            const action = new SMTCallSimple(this.typegen.getSMTConstructorName(geninfo.resulttype).cons, pargs);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        return new SMTFunction(geninfo.inv, [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], undefined, rtype, new SMTCond(ops, orelse));
    }

    private generateProjectEntityFieldVirtual(geninfo: { inv: string, argflowtype: MIRType, fields: MIRFieldDecl[], resulttype: MIRType }): SMTFunction {
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
                const idxr = new SMTCallSimple(this.typegen.generateEntityFieldGetFunction(tt, field.fkey), [argpp]);
                return this.typegen.coerce(idxr, this.typegen.getMIRType(field.declaredType), (geninfo.resulttype.options[0] as MIREphemeralListType).entries[i]);
            });
            const action = new SMTCallSimple(this.typegen.getSMTConstructorName(geninfo.resulttype).cons, pargs);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        return new SMTFunction(geninfo.inv, [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], undefined, rtype, new SMTCond(ops, orelse));
    }

    private generateUpdateTupleIndexVirtual(geninfo: { inv: string, argflowtype: MIRType, updates: [number, MIRResolvedTypeKey][], resulttype: MIRType }): SMTFunction {
        const ttuples = [...this.assembly.tupleDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].trkey);
                return this.typegen.isUniqueTupleType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getSMTTypeFor(geninfo.resulttype);
        let ops = ttuples.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.trkey);
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
        return new SMTFunction(geninfo.inv, fargs, undefined, rtype, new SMTCond(ops, orelse));
    }

    private generateUpdateRecordPropertyVirtual(geninfo: { inv: string, argflowtype: MIRType, updates: [string, MIRResolvedTypeKey][], resulttype: MIRType }): SMTFunction {
        const trecords = [...this.assembly.recordDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].trkey);
                return this.typegen.isUniqueRecordType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getSMTTypeFor(geninfo.resulttype);
        let ops = trecords.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.trkey);
            const test = new SMTCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

            const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
            let cargs: SMTExp[] = [];
            for (let i = 0; i < tt.entries.length; ++i) {
                const upd = geninfo.updates.find((vv) => vv[0] === tt.entries[i].name);
                if(upd === undefined) {
                    cargs.push(new SMTCallSimple(this.typegen.generateRecordPropertyGetFunction(tt, tt.entries[i].name), [argpp]));
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
        return new SMTFunction(geninfo.inv, fargs, undefined, rtype, new SMTCond(ops, orelse));
    }

    private generateUpdateEntityFieldVirtual(geninfo: { inv: string, argflowtype: MIRType, allsafe: boolean, updates: [MIRFieldKey, MIRResolvedTypeKey][], resulttype: MIRType }): SMTFunction {
        const tentities = [...this.assembly.entityDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].tkey);
                return this.typegen.isUniqueEntityType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getSMTTypeFor(geninfo.resulttype);
        let ops = tentities.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.tkey);
            const consfunc = (this.assembly.entityDecls.get(tt.tkey) as MIREntityTypeDecl).consfunc;
            const consfields = (this.assembly.entityDecls.get(tt.tkey) as MIREntityTypeDecl).consfuncfields.map((ccf) => this.assembly.fieldDecls.get(ccf) as MIRFieldDecl);

            const test = new SMTCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

            const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
           
            let cargs: SMTExp[] = [];
            for (let i = 0; i < consfields.length; ++i) {
                const upd = geninfo.updates.find((vv) => vv[0] === consfields[i].name);
                if(upd === undefined) {
                    cargs.push(new SMTCallSimple(this.typegen.generateEntityFieldGetFunction(tt, consfields[i].name), [argpp]));
                }
                else {
                    cargs.push(new SMTVar(`arg_${i}`));
                }
            }
            
            const ccall = new SMTCallGeneral(this.typegen.mangle(consfunc), cargs);

            let action: SMTExp = new SMTConst("[NOT SET]"); 
            if (this.isSafeConstructorInvoke(mtt) && geninfo.allsafe) {
                action = this.typegen.coerce(ccall, mtt, geninfo.resulttype);
            }
            else {
                if(this.isSafeConstructorInvoke(mtt)) {
                    action = this.typegen.generateResultTypeConstructorSuccess(geninfo.resulttype, this.typegen.coerce(ccall, mtt, geninfo.resulttype));
                }
                else {
                    if(mtt.trkey === geninfo.resulttype.trkey) {
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
        return new SMTFunction(geninfo.inv, fargs, undefined, rtype, new SMTCond(ops, orelse));
    }

    private generateVirtualFunctionInvoke(geninfo: { inv: string, allsafe: boolean, argflowtype: MIRType, vfname: MIRVirtualMethodKey, optmask: string | undefined, resulttype: MIRType }): SMTFunction {
        const tentities = [...this.assembly.entityDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].tkey);
                return this.typegen.isUniqueEntityType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getSMTTypeFor(geninfo.resulttype);
        let ops = tentities.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.tkey);
            const vfunc = (this.assembly.entityDecls.get(tt.tkey) as MIREntityTypeDecl).vcallMap.get(geninfo.vfname) as MIRInvokeKey;
            
            const test = new SMTCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

            const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
            const invk = this.assembly.invokeDecls.get(vfunc) as MIRInvokeBodyDecl;
            const atype = this.typegen.getMIRType(invk.resultType);

            const cargs = [argpp, ...invk.params.slice(1).map((p, i) =>new SMTVar(`arg_${i}`))];

            const gcall = geninfo.optmask !== undefined ? new SMTCallGeneralWPassThroughMask(this.typegen.mangle(vfunc), cargs, geninfo.optmask) : new SMTCallGeneral(this.typegen.mangle(vfunc), cargs);
                
            let action: SMTExp = new SMTConst("[NOT SET]"); 
            if (this.isSafeInvoke(vfunc) && geninfo.allsafe) {
                action = this.typegen.coerce(gcall, atype, geninfo.resulttype);
            }
            else {
                if(this.isSafeInvoke(vfunc)) {
                    action = this.typegen.generateResultTypeConstructorSuccess(geninfo.resulttype, this.typegen.coerce(gcall, atype, geninfo.resulttype));
                }
                else {
                    if(atype.trkey === geninfo.resulttype.trkey) {
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

        const sinvk = this.assembly.invokeDecls.get((this.assembly.entityDecls.get(tentities[0].tkey) as MIREntityTypeDecl).vcallMap.get(geninfo.vfname) as MIRInvokeKey) as MIRInvokeBodyDecl;
        const argtypes = sinvk.params.slice(1).map((p) => this.typegen.getSMTTypeFor(this.typegen.getMIRType(p.type)));

        const fargs = [
            { vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) },
            ...argtypes.map((vv, i) => {
                return { vname: `arg_${i}`, vtype: vv };
            })
        ];
        return new SMTFunction(geninfo.inv, fargs, undefined, rtype, new SMTCond(ops, orelse));
    }

    private generateVirtualOperatorInvoke(geninfo: { inv: string, argflowtype: MIRType, opname: MIRVirtualMethodKey, args: MIRResolvedTypeKey[], resulttype: MIRType }): SMTFunction {
        //const otrgts = this.assembly.virtualOperatorDecls.get(geninfo.opname) as MIRInvokeKey[];

        return new SMTFunction("NOT_IMPLEMENTED", [], undefined, this.typegen.getSMTTypeFor(geninfo.resulttype), NOT_IMPLEMENTED("generateVirtualOperatorInvoke"));
    }

    private generateSubtypeCheckEntity(arg: MIRArgument, layout: MIRType, flow: MIRType, ofentity: MIRType): SMTExp {
        if(flow.options.every((opt) => (opt instanceof MIRTupleType) || (opt instanceof MIRRecordType))) {
            return new SMTConst("false");
        }

        if (this.typegen.isUniqueEntityType(flow)) {
            return new SMTConst(flow.trkey === ofentity.trkey ? "true" : "false");
        }
        else {
            const accessTypeTag = this.typegen.getSMTTypeFor(layout).isGeneralTermType() ? new SMTCallSimple("GetTypeTag@BTerm", [this.argToSMT(arg)]) : new SMTCallSimple("GetTypeTag@BKey", [this.argToSMT(arg)]);
            return new SMTCallSimple("=", [accessTypeTag, new SMTConst(`TypeTag_${this.typegen.mangle(ofentity.trkey)}`)]);
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
                tests.push(new SMTCallSimple("SubtypeOf@", [accessTypeTag, new SMTConst(`AbstractTypeTag_${this.typegen.mangle(occ.ckeys[i])}`)]));
            }

            if(tests.length === 1) {
                return tests[0];
            }
            else {
                return new SMTCallSimple("and", tests);
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
            const accessTypeTag = this.typegen.getSMTTypeFor(layout).isGeneralTermType() ? new SMTCallSimple("GetTypeTag@BTerm", [this.argToSMT(arg)]) : new SMTCallSimple("GetTypeTag@BKey", [this.argToSMT(arg)]);

            if ((oftuple.options[0] as MIRTupleType).entries.every((entry) => !entry.isOptional)) {
                return new SMTCallSimple("=", [accessTypeTag, new SMTConst(`TypeTag_${this.typegen.mangle(oftuple.trkey)}`)]);
            }
            else {
                this.processSubtypeTagCheck(flow, oftuple);
                return new SMTCallSimple("SubtypeOf@", [accessTypeTag, new SMTConst(`AbstractTypeTag_${this.typegen.mangle(oftuple.trkey)}`)]);
            }
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
            const accessTypeTag = this.typegen.getSMTTypeFor(layout).isGeneralTermType() ? new SMTCallSimple("GetTypeTag@BTerm", [this.argToSMT(arg)]) : new SMTCallSimple("GetTypeTag@BKey", [this.argToSMT(arg)]);

            if ((ofrecord.options[0] as MIRRecordType).entries.every((entry) => !entry.isOptional)) {
                return new SMTCallSimple("=", [accessTypeTag, new SMTConst(`TypeTag_${this.typegen.mangle(ofrecord.trkey)}`)]);
            }
            else {
                this.processSubtypeTagCheck(flow, ofrecord);
                return new SMTCallSimple("SubtypeOf@", [accessTypeTag, new SMTConst(`AbstractTypeTag_${this.typegen.mangle(ofrecord.trkey)}`)]);
            }
        }
    }

    constructor(assembly: MIRAssembly, typegen: SMTTypeEmitter, vopts: VerifierOptions, callsafety: Map<MIRInvokeKey, { safe: boolean, trgt: boolean }>, errorTrgtPos: { file: string, line: number, pos: number }) {
        this.assembly = assembly;
        this.typegen = typegen;
        this.callsafety = callsafety;

        this.errorTrgtPos = errorTrgtPos;
        this.allErrors = [];
        this.vopts = vopts;

        this.currentRType = typegen.getMIRType("NSCore::None");
    }

    generateTempName(): string {
        return `@tmpvar@${this.tmpvarctr++}`;
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

    generateErrorExpandLimit(rtype: MIRType): SMTExp {
        if(this.errorTrgtPos.file === "[ExpandLimit]") {
            return this.typegen.generateResultTypeConstructorError(rtype, new SMTConst("ErrorID_Target"));
        }
        else {
            return this.typegen.generateResultTypeConstructorError(rtype, new SMTConst("ErrorID_AssumeCheck"));
        }
    }

    isSafeInvoke(mkey: MIRInvokeKey): boolean {
        return (this.callsafety.get(mkey) as { safe: boolean, trgt: boolean }).safe;
    }

    isSafeVirtualInvoke(vkey: MIRVirtualMethodKey, rcvrtype: MIRType): boolean {
        return [...this.assembly.entityDecls]
        .filter((tt) => {
            const mtt = this.typegen.getMIRType(tt[1].tkey);
            return this.typegen.isUniqueEntityType(mtt) && this.assembly.subtypeOf(mtt, rcvrtype);
        })
        .every((edcl) => {
            return this.isSafeInvoke((this.assembly.entityDecls.get(edcl[1].tkey) as MIREntityTypeDecl).vcallMap.get(vkey) as MIRInvokeKey);
        });
    }

    isSafeConstructorInvoke(oftype: MIRType): boolean {
        const cname = `${oftype.trkey}@@constructor`
        const idecl = this.assembly.invokeDecls.get(cname) as MIRInvokeDecl;
        return idecl.attributes.includes("__safe") || idecl.attributes.includes("__assume_safe");
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

    varStringToSMT(name: string): SMTVar {
        if (name === "$$return") {
            return new SMTVar("$$return");
        }
        else {
            return new SMTVar(this.typegen.mangle(name));
        }
    }

    varToSMTName(varg: MIRRegisterArgument): SMTVar {
        return this.varStringToSMT(varg.nameID);
    }

    globalToSMT(gval: MIRGlobalVariable): SMTConst {
        return new SMTConst(this.typegen.mangle(gval.gkey));
    }

    constantToSMT(cval: MIRConstantArgument): SMTExp {
        if (cval instanceof MIRConstantNone) {
            return new SMTConst("bsq_none@literal");
        }
        else if (cval instanceof MIRConstantTrue) {
            return new SMTConst("true");
        }
        else if (cval instanceof MIRConstantFalse) {
            return new SMTConst("false");
        }
        else if (cval instanceof MIRConstantInt) {
            if(!cval.value.startsWith("-")) {
                return new SMTConst(`(_ bv${cval.value.slice(0, cval.value.length - 1)} ${this.vopts.ISize})`);
            }
            else {
                return new SMTCallSimple("bvnot", [ new SMTConst(`(_ bv${cval.value.slice(0, cval.value.length - 1)} ${this.vopts.ISize})`)]);
            }
        }
        else if (cval instanceof MIRConstantNat) {
            return new SMTConst(`(_ bv${cval.value.slice(0, cval.value.length - 1)} ${this.vopts.ISize})`);
        }
        else if (cval instanceof MIRConstantBigInt) {
            return new SMTConst(cval.value.slice(0, cval.value.length - 1));
        }
        else if (cval instanceof MIRConstantBigNat) {
            return new SMTConst(cval.value.slice(0, cval.value.length - 1));
        }
        else if (cval instanceof MIRConstantRational) {
            if(this.vopts.FPOpt === "UF") {
                return new SMTCallSimple("BRationalUnary_UF", [new SMTConst("@cons"), new SMTConst("\"" + cval.value + "\"")]);
            }
            else {
                const spos = cval.value.indexOf("/");
                const num = new SMTConst(cval.value.slice(0, spos) + ".0");
                const denom = new SMTConst(cval.value.slice(spos + 1, cval.value.length - 1) + ".0");
                return new SMTCallSimple("/", [num, denom]);
            }
        }
        else if (cval instanceof MIRConstantFloat) {
            if(this.vopts.FPOpt === "UF" || (cval.value.includes("e") || cval.value.includes("E"))) {
                return new SMTCallSimple("BFloatUnary_UF", [new SMTConst("@cons"), new SMTConst("\"" + cval.value + "\"")]);
            }
            else {
                const sv = cval.value.includes(".") ? cval.value.slice(0, cval.value.length - 1) : (cval.value.slice(0, cval.value.length - 1) + ".0");
                return new SMTConst(sv);
            }
        }
        else if (cval instanceof MIRConstantTypedNumber) {
            const sctype = this.typegen.getMIRType(cval.tnkey);
            return new SMTCallSimple(this.typegen.getSMTConstructorName(sctype).cons, [this.constantToSMT(cval.value)]);
        }
        else if (cval instanceof MIRConstantDecimal) {
            if(this.vopts.FPOpt === "UF" || (cval.value.includes("e") || cval.value.includes("E"))) {
                return new SMTCallSimple("BDecimalUnary_UF", [new SMTConst("@cons"), new SMTConst("\"" + cval.value + "\"")]);
            }
            else {
                const sv = cval.value.includes(".") ? cval.value.slice(0, cval.value.length - 1) : (cval.value.slice(0, cval.value.length - 1) + ".0");
                return new SMTConst(sv);
            }
        }
        else if (cval instanceof MIRConstantString) {
            assert(this.vopts.StringOpt === "ASCII", "We need to UNICODE!!!🦄🚀✨");
            
            return new SMTConst(cval.value);
        }
        else if (cval instanceof MIRConstantStringOf) {
            assert(this.vopts.StringOpt === "ASCII", "We need to UNICODE!!!🦄🚀✨");

            const sctype = this.typegen.getMIRType(cval.tskey);
            return new SMTCallSimple(this.typegen.getSMTConstructorName(sctype).cons, [new SMTConst(cval.value)]);
        }
        else if (cval instanceof MIRConstantDataString) {
            assert(this.vopts.StringOpt === "ASCII", "We need to UNICODE!!!🦄🚀✨");

            const sctype = this.typegen.getMIRType(cval.tskey);
            return new SMTCallSimple(this.typegen.getSMTConstructorName(sctype).cons, [new SMTConst(cval.value)]);
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
        if (this.typegen.isType(argtype, "NSCore::None")) {
            return new SMTConst("true");
        }
        else if (!this.assembly.subtypeOf(this.typegen.getMIRType("NScore::None"), argtype)) {
            return new SMTConst("false");
        }
        else {
            const trepr = this.typegen.getSMTTypeFor(argtype);
            if(trepr.isGeneralKeyType()) {
                return new SMTCallSimple("=", [this.argToSMT(arg), new SMTConst("BKey@none")]);
            }
            else {
                return new SMTCallSimple("=", [this.argToSMT(arg), new SMTConst("BTerm@none")]);
            }
        }
    }

    generateSomeCheck(arg: MIRArgument, argtype: MIRType): SMTExp {
        if (this.typegen.isType(argtype, "NSCore::None")) {
            return new SMTConst("false");
        }
        else if (!this.assembly.subtypeOf(this.typegen.getMIRType("NScore::None"), argtype)) {
            return new SMTConst("true");
        }
        else {
            const trepr = this.typegen.getSMTTypeFor(argtype);
            if(trepr.isGeneralKeyType()) {
                return new SMTCallSimple("not", [new SMTCallSimple("=", [this.argToSMT(arg), new SMTConst("BKey@none")])]);
            }
            else {
                return new SMTCallSimple("not", [new SMTCallSimple("=", [this.argToSMT(arg), new SMTConst("BTerm@none")])]);
            }
        }
    }
    
    processAbort(op: MIRAbort): SMTExp {
        return this.generateErrorCreate(op.sinfo, this.currentRType, op.info);
    }

    processVerifierAssume(op: MIRVerifierAssume, continuation: SMTExp): SMTExp {
        const chkval = this.argToSMT(op.arg);
        const errorval = this.typegen.generateResultTypeConstructorError(this.currentRType, new SMTConst("ErrorID_AssumeCheck"));
        
        return new SMTIf(chkval, continuation, errorval);
    }

    processAssertCheck(op: MIRAssertCheck, continuation: SMTExp): SMTExp {
        const chkval = this.argToSMT(op.arg);
        const errorval = this.generateErrorCreate(op.sinfo, this.currentRType, op.info);
        
        return new SMTIf(chkval, continuation, errorval);
    }

    processLoadUnintVariableValue(op: MIRLoadUnintVariableValue, continuation: SMTExp): SMTExp {
        const ufcname = this.generateUFConstantForType(this.typegen.getMIRType(op.oftype));

        return new SMTConst(ufcname);
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
        const call = op.guard !== undefined ? new SMTIf(this.generateBoolForGuard(op.guard.guard), conv, this.generateAltForGuardStmt(op.guard.altvalue, this.typegen.getMIRType(op.intotype))) : conv;

        return new SMTLet(this.varToSMTName(op.trgt).vname, call, continuation);
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
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(icall, [argpp]), continuation);
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
            const cc = new SMTCallSimple(icall, [argpp]);

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
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(icall, [argpp]), continuation);
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
            const cc = new SMTCallSimple(icall, [argpp]);

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
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(icall, [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const idxr = new SMTCallSimple(this.typegen.generateEntityFieldGetFunction(this.assembly.entityDecls.get(arglayouttype.trkey) as MIREntityTypeDecl, op.field), [argpp]);
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
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(icall, [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const pargs = op.indecies.map((idx, i) => {
                const idxr = new SMTCallSimple(this.typegen.generateTupleIndexGetFunction(argflowtype.options[0] as MIRTupleType, idx), [argpp]);
                return this.typegen.coerce(idxr, (argflowtype.options[0] as MIRTupleType).entries[idx].type, (resulttype.options[0] as MIREphemeralListType).entries[i]);
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
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(icall, [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const pargs = op.properties.map((pname, i) => {
                const idxr = new SMTCallSimple(this.typegen.generateRecordPropertyGetFunction(argflowtype.options[0] as MIRRecordType, pname), [argpp]);
                return this.typegen.coerce(idxr, ((argflowtype.options[0] as MIRRecordType).entries.find((vv) => vv.name === pname) as MIRRecordTypeEntry).type, (resulttype.options[0] as MIREphemeralListType).entries[i]);
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
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(icall, [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const pargs = op.fields.map((fkey, i) => {
                const idxr = new SMTCallSimple(this.typegen.generateEntityFieldGetFunction(this.assembly.entityDecls.get(argflowtype.trkey) as MIREntityTypeDecl, fkey), [argpp]);
                return this.typegen.coerce(idxr, this.typegen.getMIRType((this.assembly.fieldDecls.get(fkey) as MIRFieldDecl).declaredType), (resulttype.options[0] as MIREphemeralListType).entries[i]);
            });

            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(this.typegen.getSMTConstructorName(resulttype).cons, pargs), continuation);
        }
    }

    processTupleUpdate(op: MIRTupleUpdate, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.arglayouttype);

        if(op.isvirtual) {
            const icall = this.generateUpdateVirtualTupleInvName(this.typegen.getMIRType(op.argflowtype), op.updates.map((upd) => [upd[0], upd[2]]), resulttype);
            if(this.requiredUpdateVirtualTuple.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), updates: op.updates.map((upd) => [upd[0], upd[2]] as [number, MIRResolvedTypeKey]), resulttype: resulttype };
                this.requiredUpdateVirtualTuple.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(icall, [argpp]), continuation);
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
        const resulttype = this.typegen.getMIRType(op.arglayouttype);

        if(op.isvirtual) {
            const icall = this.generateUpdateVirtualRecordInvName(this.typegen.getMIRType(op.argflowtype), op.updates.map((upd) => [upd[0], upd[2]]), resulttype);
            if(this.requiredUpdateVirtualRecord.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), updates: op.updates.map((upd) => [upd[0], upd[2]] as [string, MIRResolvedTypeKey]), resulttype: resulttype };
                this.requiredUpdateVirtualRecord.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(icall, [argpp]), continuation);
        }
        else {
            const ttype = argflowtype.options[0] as MIRRecordType;

            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            let cargs: SMTExp[] = [];
            for (let i = 0; i < ttype.entries.length; ++i) {
                const upd = op.updates.find((vv) => vv[0] === ttype.entries[i].name);
                if(upd === undefined) {
                    cargs.push(new SMTCallSimple(this.typegen.generateRecordPropertyGetFunction(ttype, ttype.entries[i].name), [argpp]));
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
        const resulttype = this.typegen.getMIRType(op.arglayouttype);

        if (op.isvirtual) {
            const allsafe = this.isSafeVirtualConstructorInvoke(argflowtype);
            const icall = this.generateUpdateVirtualEntityInvName(this.typegen.getMIRType(op.argflowtype), op.updates.map((upd) => [upd[0], upd[2]]), resulttype);

            if (this.requiredUpdateVirtualEntity.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), allsafe: allsafe, updates: op.updates.map((upd) => [upd[0], upd[2]] as [MIRFieldKey, MIRResolvedTypeKey]), resulttype: resulttype };
                this.requiredUpdateVirtualEntity.push(geninfo);
            }

            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const ccall = new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallGeneral(icall, [argpp]), continuation);

            if (allsafe) {
                return new SMTLet(this.varToSMTName(op.trgt).vname, ccall, continuation);
            }
            else {
                return this.generateGeneralCallValueProcessing(this.currentRType, resulttype, ccall, op.trgt, continuation);
            }
        }
        else {
            const ttype = argflowtype.options[0] as MIREntityType;
            const ttdecl = this.assembly.entityDecls.get(ttype.trkey) as MIREntityTypeDecl;
            const consfunc = ttdecl.consfunc;
            const consfields = ttdecl.consfuncfields.map((ccf) => this.assembly.fieldDecls.get(ccf) as MIRFieldDecl);

            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            let cargs: SMTExp[] = [];
            for (let i = 0; i < consfields.length; ++i) {
                const upd = op.updates.find((vv) => vv[0] === consfields[i].name);
                if (upd === undefined) {
                    cargs.push(new SMTCallSimple(this.typegen.generateEntityFieldGetFunction(ttdecl, consfields[i].name), [argpp]));
                }
                else {
                    cargs.push(this.argToSMT(upd[1]));
                }
            }

            const ccall = new SMTCallGeneral(this.typegen.mangle(consfunc), cargs);
            if (this.isSafeConstructorInvoke(argflowtype)) {
                return new SMTLet(this.varToSMTName(op.trgt).vname, ccall, continuation);
            }
            else {
                return this.generateGeneralCallValueProcessing(this.currentRType, resulttype, ccall, op.trgt, continuation);
            }
        }
    }

    processLoadFromEpehmeralList(op: MIRLoadFromEpehmeralList, continuation: SMTExp): SMTExp {
        const argtype = this.typegen.getMIRType(op.argtype);
        const resulttype = this.typegen.getMIRType(op.resulttype);

        const idxr = new SMTCallSimple(this.typegen.generateEphemeralListGetFunction(argtype.options[0] as MIREphemeralListType, op.idx), [this.argToSMT(op.arg)]);
        return new SMTLet(this.varToSMTName(op.trgt).vname, this.typegen.coerce(idxr, (argtype.options[0] as MIREphemeralListType).entries[op.idx], resulttype), continuation);
    }

    processMultiLoadFromEpehmeralList(op: MIRMultiLoadFromEpehmeralList, continuation: SMTExp): SMTExp {
        const eltype = this.typegen.getMIRType(op.argtype).options[0] as MIREphemeralListType;

        const assigns = op.trgts.map((asgn) => {
            const idxr = new SMTCallSimple(this.typegen.generateEphemeralListGetFunction(eltype, asgn.pos), [this.argToSMT(op.arg)]);
            const cexp = this.typegen.coerce(idxr, eltype.entries[asgn.pos], this.typegen.getMIRType(asgn.oftype));

            return { vname: this.varToSMTName(asgn.into).vname, value: cexp };
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
            assert(op.guard === undefined && op.optmask === undefined);

            const args = op.args.map((arg) => this.argToSMT(arg));
            return this.processDefaultOperatorInvokePrimitiveType(op.sinfo, op.trgt, invk.implkey, args, continuation);
        }
        if(invk instanceof MIRInvokePrimitiveDecl && invk.implkey.startsWith("verifier_")) {
            assert(op.guard === undefined && op.optmask === undefined);

            const args = op.args.map((arg) => this.argToSMT(arg));
            return this.generateVerifierExp(op.trgt, invk.implkey, args, continuation);
        }
        else {
            let mask: SMTMaskConstruct | undefined = undefined;
            if (op.optmask !== undefined) {
                mask = new SMTMaskConstruct(op.optmask);
                this.pendingMask.push(mask);
            }

            const args = op.args.map((arg) => this.argToSMT(arg));
            const call = mask !== undefined ? new SMTCallGeneralWOptMask(this.typegen.mangle(op.mkey), args, mask) : new SMTCallGeneral(this.typegen.mangle(op.mkey), args);
            const gcall = op.guard !== undefined ? new SMTIf(this.generateBoolForGuard(op.guard.guard), call, this.generateAltForGuardStmt(op.guard.altvalue, rtype)) : call;
                
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
        const icall = this.generateVirtualInvokeFunctionName(rcvrflowtype, op.vresolve, op.optmask !== undefined, resulttype);
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
        const call = mask !== undefined ? new SMTCallGeneralWOptMask(icall, args, mask) : new SMTCallGeneral(icall, args);    

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
        const iop = this.generateVirtualInvokeOperatorName(op.vresolve, op.args.map((arg) => arg.argflowtype), resulttype);
        if(this.requiredVirtualOperatorInvokes.findIndex((vv) => vv.inv === iop) === -1) {
            assert(true);
        }

        return NOT_IMPLEMENTED("processInvokeVirtualOperator");
    }

    processConstructorTuple(op: MIRConstructorTuple, continuation: SMTExp): SMTExp {
        const args = op.args.map((arg) => this.argToSMT(arg));

        return new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultTupleType)).cons, args);
    }

    processConstructorTupleFromEphemeralList(op: MIRConstructorTupleFromEphemeralList, continuation: SMTExp): SMTExp {
        const elt = this.typegen.getMIRType(op.elistType).options[0] as MIREphemeralListType;
        const args = elt.entries.map((tt, i) => new SMTCallSimple(this.typegen.generateEphemeralListGetFunction(elt, i), [this.argToSMT(op.arg)]));

        return new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultTupleType)).cons, args);
    }

    processConstructorRecord(op: MIRConstructorRecord, continuation: SMTExp): SMTExp {
        const args = op.args.map((arg) => this.argToSMT(arg[1]));

        return new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultRecordType)).cons, args);
    }

    processConstructorRecordFromEphemeralList(op: MIRConstructorRecordFromEphemeralList, continuation: SMTExp): SMTExp {
        const elt = this.typegen.getMIRType(op.elistType).options[0] as MIREphemeralListType;
        const eargs = elt.entries.map((tt, i) => new SMTCallSimple(this.typegen.generateEphemeralListGetFunction(elt, i), [this.argToSMT(op.arg)]));

        const rtype = this.typegen.getMIRType(op.resultRecordType).options[0] as MIRRecordType;
        const args = rtype.entries.map((rentry) => {
            const eidx = op.propertyPositions.indexOf(rentry.name);
            return eargs[eidx];
        });

        return new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultRecordType)).cons, args);
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

        return new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultTupleType)).cons, args);
    }

    processStructuredJoinRecord(op: MIRStructuredJoinRecord, continuation: SMTExp): SMTExp {
        const rtype = this.typegen.getMIRType(op.resultRecordType).options[0] as MIRRecordType;

        let args: SMTExp[] = [];
        for (let i = 0; i < op.args.length; ++i) {
            const tt = this.typegen.getMIRType(op.ttypes[i].flow).options[0] as MIRRecordType;
            const argi = this.argToSMT(op.args[i]);

            for (let j = 0; j < tt.entries.length; ++j) {
                const ppidx = rtype.entries.findIndex((ee) => ee.name === tt.entries[j].name);
                args[ppidx] = new SMTCallSimple(this.typegen.generateRecordPropertyGetFunction(tt, tt.entries[j].name), [argi]);
            }
        }

        return new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultRecordType)).cons, args);
    }

    processConstructorEphemeralList(op: MIRConstructorEphemeralList, continuation: SMTExp): SMTExp {
        const args = op.args.map((arg) => this.argToSMT(arg));

        return new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultEphemeralListType)).cons, args);
    }

    processEphemeralListExtend(op: MIREphemeralListExtend, continuation: SMTExp): SMTExp {
        const ietype = this.typegen.getMIRType(op.argtype).options[0] as MIREphemeralListType;
        const iargs = ietype.entries.map((ee, i) => new SMTCallSimple(this.typegen.generateEphemeralListGetFunction(ietype, i), [this.argToSMT(op.arg)]));

        const eargs = op.ext.map((arg) => this.argToSMT(arg));

        return new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultType)).cons, [...iargs, ...eargs]);
    }

    processConstructorPrimaryCollectionEmpty(op: MIRConstructorPrimaryCollectionEmpty, continuation: SMTExp): SMTExp {
        const consf = this.generateConstructorOfSizeName(op.tkey, 0);
        if (this.requiredCollectionOfConstructors.find((ee) => ee.cname === consf) === undefined) {
            this.requiredCollectionOfConstructors.push({ cname: consf, oftype: op.tkey, argc: 0 });
        }

        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(consf, []), continuation);
    }

    processConstructorPrimaryCollectionSingletons(op: MIRConstructorPrimaryCollectionSingletons, continuation: SMTExp): SMTExp {
        const consf = this.generateConstructorOfSizeName(op.tkey, op.args.length);
        if (this.requiredCollectionOfConstructors.find((ee) => ee.cname === consf) === undefined) {
            this.requiredCollectionOfConstructors.push({ cname: consf, oftype: op.tkey, argc: op.args.length });
        }

        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple(consf, op.args.map((arg) => this.argToSMT(arg[1]))), continuation);
    }

    processConstructorPrimaryCollectionCopies(op: MIRConstructorPrimaryCollectionCopies, continuation: SMTExp): SMTExp {
        return NOT_IMPLEMENTED("processConstructorPrimaryCollectionCopies");
    }

    processConstructorPrimaryCollectionMixed(op: MIRConstructorPrimaryCollectionMixed, continuation: SMTExp): SMTExp {
        return NOT_IMPLEMENTED("processConstructorPrimaryCollectionMixed");
    }

    processBinKeyEq(op: MIRBinKeyEq, continuation: SMTExp): SMTExp {
        const lhs = this.typegen.coerceToKey(this.argToSMT(op.lhs), this.typegen.getMIRType(op.lhslayouttype));
        const rhs = this.typegen.coerceToKey(this.argToSMT(op.rhs), this.typegen.getMIRType(op.rhslayouttype));

        const eqcmp = new SMTCallSimple("=", [lhs, rhs]);
        return new SMTLet(this.varToSMTName(op.trgt).vname, eqcmp, continuation);
    }

    processBinKeyLess(op: MIRBinKeyLess, continuation: SMTExp): SMTExp {
        return NOT_IMPLEMENTED("processBinKeyLess");
    }

    processPrefixNotOp(op: MIRPrefixNotOp, continuation: SMTExp): SMTExp {
        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple("not", [this.argToSMT(op.arg)]), continuation);
    }

    processAllTrue(op: MIRAllTrue, continuation: SMTExp): SMTExp {
        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCallSimple("and", op.args.map((arg) => this.argToSMT(arg))), continuation);
    }

    processIsTypeOf(op: MIRIsTypeOf, continuation: SMTExp): SMTExp {
        const layout = this.typegen.getMIRType(op.srclayouttype);
        const flow = this.typegen.getMIRType(op.srcflowtype);
        const oftype = this.typegen.getMIRType(op.chktype);

        if(this.assembly.subtypeOf(flow, oftype)) {
            //also handles the oftype is Any case
            return new SMTConst("true");
        }
        else if(this.typegen.isType(oftype, "NSCore::None")) {
            return this.generateNoneCheck(op.arg, layout);
        }
        else if (this.typegen.isType(oftype, "NSCore::Some")) {
            return this.generateSomeCheck(op.arg, layout);
        }
        else {
            const tests = oftype.options.map((topt) => {
                const mtype = this.typegen.getMIRType(topt.trkey);
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
                return new SMTConst("false");
            }
            else if(tests.findIndex((test) => (test instanceof SMTConst) && test.cname === "true") !== -1) {
                return new SMTConst("true");
            }
            else if(tests.length === 1) {
                return tests[0];
            }
            else {
                return new SMTCallSimple("or", tests);
            }
        }
    }

    processRegisterAssign(op: MIRRegisterAssign, continuation: SMTExp): SMTExp {
        if(op.guard === undefined) {
            return new SMTLet(this.varToSMTName(op.trgt).vname, this.argToSMT(op.src), continuation);
        }
        else {
            const cassign = new SMTIf(this.generateBoolForGuard(op.guard.guard), this.argToSMT(op.src), this.generateAltForGuardStmt(op.guard.altvalue, this.typegen.getMIRType(op.layouttype)));
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
            case MIROpTag.MIRVerifierAssume: {
                return this.processVerifierAssume(op as MIRAssertCheck, continuation);
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
            case MIROpTag.MIRAllTrue: {
                return this.processAllTrue(op as MIRAllTrue, continuation);
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

    processGenerateResultWithZeroArgCheck(sinfo: SourceInfo, not0arg: SMTExp, oftype: MIRType, val: SMTExp): SMTExp {
        const chkzero = new SMTCallSimple("==", [new SMTConst("0"), not0arg]);
        return new SMTIf(chkzero, this.generateErrorCreate(sinfo, oftype, "Div by 0"), this.typegen.generateResultTypeConstructorSuccess(oftype, val));
    }

    processGenerateResultWithBounds(sinfo: SourceInfo, op: string, args: SMTExp[], oftype: MIRType): SMTExp {
        if(!this.vopts.OverflowEnabled) {
            const opbvbasic = { "+": "bvadd", "-": "bvsub", "*": "bvmul" }[op as "+" | "-" | "*"];

            if(op === "-" && (oftype.trkey === "NSCore::Nat" || oftype.trkey === "NSCore::BigNat")) {
                const vtmp = this.generateTempName();
                const val = new SMTVar(vtmp);

                const chkbounds = new SMTCallSimple("bvult", args);
                const bop = new SMTIf(chkbounds, this.generateErrorCreate(sinfo, oftype, "Unsigned subtract underflow"), this.typegen.generateResultTypeConstructorSuccess(oftype, val));

                return new SMTLet(vtmp, new SMTCallSimple(op, args), bop);
            }
            else {
                return new SMTCallSimple(opbvbasic, args);
            }
        }
        else {
            //TODO: See following links
            //https://github.com/Z3Prover/z3/blob/master/src/api/api_bv.cpp
            //https://github.com/Z3Prover/z3/issues/574
            //https://github.com/Z3Prover/z3/blob/518296dbc10267d4a4b8589212feaeefca800022/src/ast/bv_decl_plugin.cpp

            return NOT_IMPLEMENTED("Overflow Checked Arith");
        }
    }

    processDefaultOperatorInvokePrimitiveType(sinfo: SourceInfo, trgt: MIRRegisterArgument, op: MIRInvokeKey, args: SMTExp[], continuation: SMTExp): SMTExp {
        let smte: SMTExp = new SMTConst("[INVALID]");
        let erropt = false;
        let rtype = this.typegen.getMIRType("NSCore::None");

        switch (op) {
            //op unary +
            case "NSCore::+=prefix=(NSCore::Int)":
            case "NSCore::+=prefix=(NSCore::Nat)":
            case "NSCore::+=prefix=(NSCore::BigInt)":
            case "NSCore::+=prefix=(NSCore::BigNat)":
            case "NSCore::+=prefix=(NSCore::Rational)":
            case "NSCore::+=prefix=(NSCore::Float)":
            case "NSCore::+=prefix=(NSCore::Decimal)": {
                smte = args[0];
                break;
            }
            //op unary -
            case "NSCore::-=prefix=(NSCore::Int)": {
                smte = new SMTCallSimple("bvnot", args);
                break;
            }
            case "NSCore::-=prefix=(NSCore::BigInt)": {
                smte = new SMTCallSimple("-", args);
                break;
            }
            case "NSCore::-=prefix=(NSCore::Rational)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BRationalUnary_UF", [new SMTConst("op_unary_negate"), ...args]) : new SMTCallSimple("-", args);
                break;
            }
            case "NSCore::-=prefix=(NSCore::Float)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BFloatUnary_UF", [new SMTConst("op_unary_negate"), ...args]) : new SMTCallSimple("-", args);
                break;
            }
            case "NSCore::-=prefix=(NSCore::Decimal)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BDecimalUnary_UF", [new SMTConst("op_unary_negate"), ...args]) : new SMTCallSimple("-", args);
                break;
            }
            //op infix +
            case "NSCore::+=infix=(NSCore::Int, NSCore::Int)": {
                rtype = this.typegen.getMIRType("NSCore::Int");
                smte = this.processGenerateResultWithBounds(sinfo, "+", args, rtype);
                erropt = true;
            }
            case "NSCore::+=infix=(NSCore::Nat, NSCore::Nat)": {
                rtype = this.typegen.getMIRType("NSCore::Nat");
                smte = this.processGenerateResultWithBounds(sinfo, "+", args, rtype);
                erropt = true;
            }
            case "NSCore::+=infix=(NSCore::BigInt, NSCore::BigInt)": {
                rtype = this.typegen.getMIRType("NSCore::BigInt");
                smte = this.processGenerateResultWithBounds(sinfo, "+", args, rtype);
                erropt = true;
            }
            case "NSCore::+=infix=(NSCore::BigNat, NSCore::BigNat)": {
                rtype = this.typegen.getMIRType("NSCore::BigNat");
                smte = this.processGenerateResultWithBounds(sinfo, "+", args, rtype);
                erropt = true;
                break
            }
            case "NSCore::+=infix=(NSCore::Rational, NSCore::Rational)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BRationalBinary_UF", [new SMTConst("op_binary_plus"), ...args]) : new SMTCallSimple("+", args);
                break;
            }
            case "NSCore::+=infix=(NSCore::Float, NSCore::Float)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BFloatBinary_UF", [new SMTConst("op_binary_plus"), ...args]) : new SMTCallSimple("+", args);
                break;
            }
            case "NSCore::+=infix=(NSCore::Decimal, NSCore::Decimal)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BDecimalBinary_UF", [new SMTConst("op_binary_plus"), ...args]) : new SMTCallSimple("+", args);
                break;
            }
            //op infix -
            case "NSCore::-=infix=(NSCore::Int, NSCore::Int)": {
                rtype = this.typegen.getMIRType("NSCore::Int");
                smte = this.processGenerateResultWithBounds(sinfo, "-", args, rtype);
                erropt = true;
            }
            case "NSCore::-=infix=(NSCore::Nat, NSCore::Nat)": {
                rtype = this.typegen.getMIRType("NSCore::Nat");
                smte = this.processGenerateResultWithBounds(sinfo, "-", args, rtype);
                erropt = true;
            }
            case "NSCore::-=infix=(NSCore::BigInt, NSCore::BigInt)": {
                rtype = this.typegen.getMIRType("NSCore::BigInt");
                smte = this.processGenerateResultWithBounds(sinfo, "-", args, rtype);
                erropt = true;
            }
            case "NSCore::-=infix=(NSCore::BigNat, NSCore::BigNat)": {
                rtype = this.typegen.getMIRType("NSCore::BigNat");
                smte = this.processGenerateResultWithBounds(sinfo, "-", args, rtype);
                erropt = true;
                break
            }
            case "NSCore::-=infix=(NSCore::Rational, NSCore::Rational)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BRationalBinary_UF", [new SMTConst("op_binary_minus"), ...args]) : new SMTCallSimple("-", args);
                break;
            }
            case "NSCore::-=infix=(NSCore::Float, NSCore::Float)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BFloatBinary_UF", [new SMTConst("op_binary_minus"), ...args]) : new SMTCallSimple("-", args);
                break;
            }
            case "NSCore::-=infix=(NSCore::Decimal, NSCore::Decimal)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BDecimalBinary_UF", [new SMTConst("op_binary_minus"), ...args]) : new SMTCallSimple("-", args);
                break;
            }
            //op infix *
            case "NSCore::*=infix=(NSCore::Int, NSCore::Int)": {
                rtype = this.typegen.getMIRType("NSCore::Int");
                smte = this.processGenerateResultWithBounds(sinfo, "*", args, rtype);
                erropt = true;
            }
            case "NSCore::*=infix=(NSCore::Nat, NSCore::Nat)": {
                rtype = this.typegen.getMIRType("NSCore::Nat");
                smte = this.processGenerateResultWithBounds(sinfo, "*", args, rtype);
                erropt = true;
            }
            case "NSCore::*=infix=(NSCore::BigInt, NSCore::BigInt)": {
                rtype = this.typegen.getMIRType("NSCore::BigInt");
                smte = this.processGenerateResultWithBounds(sinfo, "*", args, rtype);
                erropt = true;
            }
            case "NSCore::*=infix=(NSCore::BigNat, NSCore::BigNat)": {
                rtype = this.typegen.getMIRType("NSCore::BigNat");
                smte = this.processGenerateResultWithBounds(sinfo, "*", args, rtype);
                erropt = true;
                break
            }
            case "NSCore::*=infix=(NSCore::Rational, NSCore::Rational)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BRationalBinary_UF", [new SMTConst("op_binary_mult"), ...args]) : new SMTCallSimple("*", args);
                break;
            }
            case "NSCore::*=infix=(NSCore::Float, NSCore::Float)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BFloatBinary_UF", [new SMTConst("op_binary_mult"), ...args]) : new SMTCallSimple("*", args);
                break;
            }
            case "NSCore::*=infix=(NSCore::Decimal, NSCore::Decimal)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BDecimalBinary_UF", [new SMTConst("op_binary_mult"), ...args]) : new SMTCallSimple("*", args);
                break;
            }
            //op infix /
            case "NSCore::/=infix=(NSCore::Int, NSCore::Int)": {
                rtype = this.typegen.getMIRType("NSCore::Int");
                smte = this.processGenerateResultWithZeroArgCheck(sinfo, args[1], rtype, new SMTCallSimple("/", args));
                erropt = true;
            }
            case "NSCore::/=infix=(NSCore::Nat, NSCore::Nat)": {
                rtype = this.typegen.getMIRType("NSCore::Nat");
                smte = this.processGenerateResultWithZeroArgCheck(sinfo, args[1], rtype, new SMTCallSimple("/", args));
                erropt = true;
            }
            case "NSCore::/=infix=(NSCore::BigInt, NSCore::BigInt)": {
                rtype = this.typegen.getMIRType("NSCore::BigInt");
                smte = this.processGenerateResultWithZeroArgCheck(sinfo, args[1], rtype, new SMTCallSimple("/", args));
                erropt = true;
            }
            case "NSCore::/=infix=(NSCore::BigNat, NSCore::BigNat)": {
                rtype = this.typegen.getMIRType("NSCore::BigNat");
                smte = this.processGenerateResultWithZeroArgCheck(sinfo, args[1], rtype, new SMTCallSimple("/", args));
                erropt = true;
                break
            }
            case "NSCore::/=infix=(NSCore::Rational, NSCore::Rational)": {
                rtype = this.typegen.getMIRType("NSCore::Rational");
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BRationalBinary_UF", [new SMTConst("op_binary_div"), ...args]) : this.processGenerateResultWithZeroArgCheck(sinfo, args[1], rtype, new SMTCallSimple("/", args));
                erropt = true;
                break;
            }
            case "NSCore::/=infix=(NSCore::Float, NSCore::Float)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BFloatBinary_UF", [new SMTConst("op_binary_div"), ...args]) : new SMTCallSimple("/", args);
                break;
            }
            case "NSCore::/=infix=(NSCore::Decimal, NSCore::Decimal)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BDecimalBinary_UF", [new SMTConst("op_binary_div"), ...args]) : new SMTCallSimple("/", args);
                break;
            }
            //op infix ==
            case "NSCore::===infix=(NSCore::Int, NSCore::Int)":
            case "NSCore::===infix=(NSCore::Nat, NSCore::Nat)":
            case "NSCore::===infix=(NSCore::BigInt, NSCore::BigInt)":
            case "NSCore::===infix=(NSCore::BigNat, NSCore::BigNat)":
            case "NSCore::===infix=(NSCore::Rational, NSCore::Rational)": {
                smte = new SMTCallSimple("=", args);
                break;
            }
            //op infix !=
            case "NSCore::===infix=(NSCore::Int, NSCore::Int)":
            case "NSCore::===infix=(NSCore::Nat, NSCore::Nat)":
            case "NSCore::===infix=(NSCore::BigInt, NSCore::BigInt)":
            case "NSCore::===infix=(NSCore::BigNat, NSCore::BigNat)":
            case "NSCore::===infix=(NSCore::Rational, NSCore::Rational)": {
                smte = new SMTCallSimple("not", [new SMTCallSimple("=", args)]);
                break;
            }
            //op infix <
            case "NSCore::<=infix=(NSCore::Int, NSCore::Int)":
            case "NSCore::<=infix=(NSCore::Nat, NSCore::Nat)":
            case "NSCore::<=infix=(NSCore::BigInt, NSCore::BigInt)":
            case "NSCore::<=infix=(NSCore::BigNat, NSCore::BigNat)":
            case "NSCore::<=infix=(NSCore::Rational, NSCore::Rational)":
            case "NSCore::<=infix=(NSCore::Float, NSCore::Float)":
            case "NSCore::<=infix=(NSCore::Decimal, NSCore::Decimal)": {
                smte = new SMTCallSimple("<", args);
                break;
            }
            //op infix >
            case "NSCore::>=infix=(NSCore::Int, NSCore::Int)":
            case "NSCore::>=infix=(NSCore::Nat, NSCore::Nat)":
            case "NSCore::>=infix=(NSCore::BigInt, NSCore::BigInt)":
            case "NSCore::>=infix=(NSCore::BigNat, NSCore::BigNat)":
            case "NSCore::>=infix=(NSCore::Rational, NSCore::Rational)":
            case "NSCore::>=infix=(NSCore::Float, NSCore::Float)":
            case "NSCore::>=infix=(NSCore::Decimal, NSCore::Decimal)": {
                smte = new SMTCallSimple(">", args);
                break;
            }
            //op infix <=
            case "NSCore::<==infix=(NSCore::Int, NSCore::Int)":
            case "NSCore::<==infix=(NSCore::Nat, NSCore::Nat)":
            case "NSCore::<==infix=(NSCore::BigInt, NSCore::BigInt)":
            case "NSCore::<==infix=(NSCore::BigNat, NSCore::BigNat)":
            case "NSCore::<==infix=(NSCore::Rational, NSCore::Rational)": {
                smte = new SMTCallSimple("<=", args);
                break;
            }
            //op infix >=
            case "NSCore::>==infix=(NSCore::Int, NSCore::Int)":
            case "NSCore::>==infix=(NSCore::Nat, NSCore::Nat)":
            case "NSCore::>==infix=(NSCore::BigInt, NSCore::BigInt)":
            case "NSCore::>==infix=(NSCore::BigNat, NSCore::BigNat)":
            case "NSCore::>==infix=(NSCore::Rational, NSCore::Rational)": {
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
            const errpath = (rtype.trkey === this.currentRType.trkey) ? new SMTVar(cres) : this.typegen.generateResultTypeConstructorError(this.currentRType, this.typegen.generateResultGetError(rtype, new SMTVar(cres)));

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

        let bb = this.getReadyBlock(blocks, smtexps);
        while(bb !== undefined) {
            const jop = bb.ops[bb.ops.length - 1];

            let rexp: SMTExp = new SMTConst("[UNITIALIZED FLOW]");
            if(jop.tag === MIROpTag.MIRAbort) {
                ; //No continuation so just leave uninit
            }
            else if (jop.tag === MIROpTag.MIRJump) {
                rexp = smtexps.get((jop as MIRJump).trgtblock) as SMTExp;
            }
            else if (jop.tag === MIROpTag.MIRJumpCond) {
                const smtcond = this.argToSMT((jop as MIRJumpCond).arg);
                const texp = smtexps.get((jop as MIRJumpCond).trueblock) as SMTExp;
                const fexp = smtexps.get((jop as MIRJumpCond).falseblock) as SMTExp;
                
                rexp = new SMTIf(smtcond, texp, fexp);
            }
            else {
                assert(jop.tag === MIROpTag.MIRJumpNone);

                const smtcond = this.generateNoneCheck((jop as MIRJumpNone).arg, this.typegen.getMIRType((jop as MIRJumpNone).arglayouttype));
                const nexp = smtexps.get((jop as MIRJumpNone).noneblock) as SMTExp;
                const sexp = smtexps.get((jop as MIRJumpNone).someblock) as SMTExp;
                
                rexp = new SMTIf(smtcond, nexp, sexp);
            }

            for (let i = eblock.ops.length - 1; i >= 0; --i) {
                const texp = this.processOp(eblock.ops[i], rexp);
                if(texp !== undefined) {
                    rexp = texp;
                }
            }

            bb = this.getReadyBlock(blocks, smtexps);
        }

        return smtexps.get("entry") as SMTExp;
    }

    generateSMTInvoke(idecl: MIRInvokeDecl, cscc: Set<string>): SMTFunction | SMTFunctionUninterpreted | undefined {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.getMIRType(idecl.resultType);
        this.currentSCC = cscc;

        const args = idecl.params.map((arg) => {
            return { vname: this.varStringToSMT(arg.name).vname, vtype: this.typegen.getSMTTypeFor(this.typegen.getMIRType(arg.type)) };
        });

        const issafe = this.isSafeInvoke(idecl.key);
        const restype = issafe ? this.typegen.getSMTTypeFor(this.typegen.getMIRType(idecl.resultType)) : this.typegen.generateResultType(this.typegen.getMIRType(idecl.resultType));

        //
        //TODO: if cscc is not empty then we should handle it
        //
        assert(this.currentSCC.size === 0);

        if (idecl instanceof MIRInvokeBodyDecl) {
            const body = this.generateBlockExps(issafe, (idecl as MIRInvokeBodyDecl).body.body);

            return new SMTFunction(this.typegen.mangle(idecl.key), args, idecl.takesmask ? "#maskparam#" : undefined, restype, body);
        }
        else {
            assert(idecl instanceof MIRInvokePrimitiveDecl);

            return this.generateBuiltinFunction(idecl as MIRInvokePrimitiveDecl);
        }
    }

    generateVerifierExp(trgt: MIRRegisterArgument, op: string, args: SMTExp[], continuation: SMTExp): SMTExp {
        switch(op) {
            case "verifier_termeq": {
                return new SMTLet(this.varToSMTName(trgt).vname, new SMTCallSimple("=", args), continuation);
            }
            case "verifier_lnot": {
                return new SMTLet(this.varToSMTName(trgt).vname, new SMTCallSimple("not", args), continuation);
            }
            case "verifier_land": {
                return new SMTLet(this.varToSMTName(trgt).vname, new SMTCallSimple("and", args), continuation);
            }
            case "verifier_lor": {
                return new SMTLet(this.varToSMTName(trgt).vname, new SMTCallSimple("or", args), continuation);
            }
            case "verifier_limplies": {
                return new SMTLet(this.varToSMTName(trgt).vname, new SMTCallSimple("=>", args), continuation);
            }
            default: {
                assert(false);
                return new SMTConst("[MISSING VERIFIER CASE]");
            }
        }

    }

    generateBuiltinFunction(idecl: MIRInvokePrimitiveDecl): SMTFunction | SMTFunctionUninterpreted | undefined {
        const args = idecl.params.map((arg) => {
            return { vname: this.varStringToSMT(arg.name).vname, vtype: this.typegen.getSMTTypeFor(this.typegen.getMIRType(arg.type)) };
        });

        const issafe = this.isSafeInvoke(idecl.key);
        const restype = issafe ? this.typegen.getSMTTypeFor(this.typegen.getMIRType(idecl.resultType)) : this.typegen.generateResultType(this.typegen.getMIRType(idecl.resultType));

        switch(idecl.implkey) {
            case "string_count": {
                return new SMTFunction(this.typegen.mangle(idecl.key), args, undefined, restype, new SMTCallSimple("str.len", [new SMTVar(args[0].vname)]));
            }
            case "string_charat": {
                return new SMTFunction(this.typegen.mangle(idecl.key), args, undefined, restype, new SMTCallSimple("str.at", [new SMTVar(args[0].vname)]));
            }
            default: {
                return undefined;
            }
        }
    }

    generateListBoundsGuard(ltype: SMTType, l: SMTVar, n: SMTVar): SMTExp {
        return new SMTCallSimple("and", [new SMTCallSimple("<=", [new SMTConst("0"), n]), new SMTCallSimple("<", [n, new SMTCallSimple(`${ltype.name}@size`, [l])])]);
    }

    createLambdaGuards(pc: MIRPCode): { vname: string, vtype: SMTType }[] {
        const lc = (this.assembly.invokeDecls.get(pc.code) || this.assembly.primitiveInvokeDecls.get(pc.code)) as MIRInvokeDecl;

        return pc.cargs.map((ca, i) => {
            return { vname: this.typegen.mangle(ca), vtype: this.typegen.getSMTTypeFor(this.typegen.getMIRType(lc.params[i].type)) };
        });
    }

    isLambdaSafe(pc: MIRPCode): boolean {
        return this.isSafeInvoke(pc.code);
    }

    generateSafeLambdaPredCall(pc: MIRPCode, ...args: SMTExp[]): SMTExp {
        const cargs = pc.cargs.map((ca) => new SMTVar(this.typegen.mangle(ca)));
        return new SMTCallSimple(this.typegen.mangle(pc.code), [...args, ...cargs]);
    }

    generateCallGeneralLambdaPrediate(pc: MIRPCode, ...args: SMTExp[]): SMTExp {
        const cargs = pc.cargs.map((ca) => new SMTVar(this.typegen.mangle(ca)));
        return new SMTCallSimple(this.typegen.mangle(pc.code), [...args, ...cargs]);
    }

    generateIsErrorLambdaPrediate(pc: MIRPCode, ...args: SMTExp[]): SMTExp {
        return this.typegen.generateResultIsErrorTest(this.typegen.getMIRType("NSCore::Bool"), this.generateCallGeneralLambdaPrediate(pc, ...args));
    }

    generateIsSuccessLambdaPredicate(pc: MIRPCode, ofvalue: boolean, ...args: SMTExp[]): SMTExp {
        const call = this.generateCallGeneralLambdaPrediate(pc, ...args)
        const rvalue = this.typegen.generateResultTypeConstructorSuccess(this.typegen.getMIRType("NSCore::Bool"), new SMTConst(ofvalue ? "true" : "false"));

        return new SMTCallSimple("=", [call, rvalue]);
    }
}

export {
     SMTBodyEmitter
};
