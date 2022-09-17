//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRConceptType, MIRConstructableEntityTypeDecl, MIREntityType, MIREntityTypeDecl, MIREphemeralListType, MIRFieldDecl, MIRInvokeBodyDecl, MIRInvokeDecl, MIRInvokePrimitiveDecl, MIRObjectEntityTypeDecl, MIRPCode, MIRPrimitiveCollectionEntityTypeDecl, MIRPrimitiveListEntityTypeDecl, MIRPrimitiveMapEntityTypeDecl, MIRPrimitiveQueueEntityTypeDecl, MIRPrimitiveSetEntityTypeDecl, MIRPrimitiveStackEntityTypeDecl, MIRRecordType, MIRTupleType, MIRType } from "../../../compiler/mir_assembly";
import { MorphirTypeEmitter } from "./morphirtype_emitter";
import { MIRAbort, MIRArgGuard, MIRArgument, MIRAssertCheck, MIRBasicBlock, MIRBinKeyEq, MIRBinKeyLess, MIRConstantArgument, MIRConstantBigInt, MIRConstantBigNat, MIRConstantDataString, MIRConstantDecimal, MIRConstantFalse, MIRConstantFloat, MIRConstantInt, MIRConstantNat, MIRConstantNone, MIRConstantNothing, MIRConstantRational, MIRConstantRegex, MIRConstantString, MIRConstantStringOf, MIRConstantTrue, MIRConstantTypedNumber, MIRConstructorEntityDirect, MIRConstructorEphemeralList, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionOneElement, MIRConstructorPrimaryCollectionSingletons, MIRConstructorRecord, MIRConstructorRecordFromEphemeralList, MIRConstructorTuple, MIRConstructorTupleFromEphemeralList, MIRConvertValue, MIRDeclareGuardFlagLocation, MIREntityProjectToEphemeral, MIREntityUpdate, MIREphemeralListExtend, MIRExtract, MIRFieldKey, MIRGlobalVariable, MIRGuard, MIRGuardedOptionInject, MIRInject, MIRInvokeFixedFunction, MIRInvokeKey, MIRInvokeVirtualFunction, MIRInvokeVirtualOperator, MIRIsTypeOf, MIRJump, MIRJumpCond, MIRJumpNone, MIRLoadConst, MIRLoadField, MIRLoadFromEpehmeralList, MIRLoadRecordProperty, MIRLoadRecordPropertySetGuard, MIRLoadTupleIndex, MIRLoadTupleIndexSetGuard, MIRLoadUnintVariableValue, MIRLogicAction, MIRMaskGuard, MIRMultiLoadFromEpehmeralList, MIROp, MIROpTag, MIRPhi, MIRPrefixNotOp, MIRRecordHasProperty, MIRRecordProjectToEphemeral, MIRRecordUpdate, MIRRegisterArgument, MIRRegisterAssign, MIRResolvedTypeKey, MIRReturnAssign, MIRReturnAssignOfCons, MIRSetConstantGuardFlag, MIRSliceEpehmeralList, MIRStatmentGuard, MIRStructuredAppendTuple, MIRStructuredJoinRecord, MIRTupleHasIndex, MIRTupleProjectToEphemeral, MIRTupleUpdate, MIRVirtualMethodKey } from "../../../compiler/mir_ops";
import { MorphirCallSimple, MorphirCallGeneral, MorphirCallGeneralWOptMask, MorphirCond, MorphirConst, MorphirExp, MorphirIf, MorphirLet, MorphirLetMulti, MorphirMaskConstruct, MorphirVar, MorphirCallGeneralWPassThroughMask, MorphirTypeInfo } from "./morphir_exp";
import { SourceInfo } from "../../../ast/parser";
import { MorphirFunction } from "./morphir_assembly";

import * as assert from "assert";
import { BSQRegex } from "../../../ast/bsqregex";

function NOT_IMPLEMENTED(msg: string): MorphirExp {
    throw new Error(`Not Implemented: ${msg}`);
}

class MorphirBodyEmitter {
    readonly assembly: MIRAssembly;
    readonly typegen: MorphirTypeEmitter;

    readonly callsafety: Map<MIRInvokeKey, { safe: boolean, trgt: boolean }>;

    private tmpvarctr = 0;

    currentFile: string = "[No File]";
    currentRType: MIRType;
    currentSCC = new Set<string>();

    private pendingMask: MorphirMaskConstruct[] = [];
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

    requiredVirtualFunctionInvokes: { inv: string, allsafe: boolean, argflowtype: MIRType, vfname: MIRVirtualMethodKey, optmask: string | undefined, resulttype: MIRType }[] = [];
    requiredVirtualOperatorInvokes: { inv: string, argflowtype: MIRType, opname: MIRVirtualMethodKey, args: MIRResolvedTypeKey[], resulttype: MIRType }[] = [];

    requiredSubtypeTagChecks: {t: MIRType, oftype: MIRType}[] = [];
    requiredIndexTagChecks: {idx: number, oftype: MIRType}[] = [];
    requiredRecordTagChecks: {pname: string, oftype: MIRType}[] = [];

    requiredUFConsts: MorphirTypeInfo[] = [];

    varStringToMorphir(name: string): MorphirVar {
        if (name === "$$return") {
            return new MorphirVar("$$return");
        }
        else {
            return new MorphirVar(name);
        }
    }

    varToMorphirName(varg: MIRRegisterArgument): MorphirVar {
        return this.varStringToMorphir(varg.nameID);
    }

    globalToMorphir(gval: MIRGlobalVariable): MorphirConst {
        this.typegen.internGlobalName(gval.gkey, gval.shortname);
        return new MorphirConst(this.typegen.lookupGlobalName(gval.gkey));
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
        return `subtype_check_${this.typegen.lookupTypeName(argflowtype.typeID)}_oftype_${this.typegen.lookupTypeName(oftype.typeID)}`;
    }

    private registerRequiredTypeCheck(argflowtype: MIRType, oftype: MIRType): string {
        const inv = this.generateTypeCheckName(argflowtype, oftype);
        if (this.requiredTypecheck.findIndex((rtc) => rtc.inv === inv) === -1) {
            this.requiredTypecheck.push({ inv: inv, flowtype: argflowtype, oftype: oftype });
        }

        return inv;
    }

    generateUFConstantForType(tt: MIRType): string {
        const ctype = this.typegen.getMorphirTypeFor(tt);
        const ufcname = `bsq${ctype.morphirtypename.toLowerCase()}_default`;
        
        if(this.requiredUFConsts.find((cc) => cc.morphirtypename === ctype.morphirtypename) === undefined) {
            this.requiredUFConsts.push(ctype);
        }

        return ufcname;
    }

    private generateBoolForGuard(guard: MIRGuard): MorphirExp {
        if(guard instanceof MIRMaskGuard) {
            return new MorphirCallSimple(`mask_${guard.gsize}_${guard.gindex}`, [this.varStringToMorphir(guard.gmask)]);
        }
        else {
            return this.argToMorphir((guard as MIRArgGuard).greg);
        }
    }

    private generateAltForGuardStmt(arg: MIRArgument | undefined, oftype: MIRType): MorphirExp {
        return arg !== undefined ? this.argToMorphir(arg) : new MorphirConst(this.generateUFConstantForType(oftype));
    }

    private generateGuardStmtCond(sguard: MIRStatmentGuard | undefined, gexp: MorphirExp, rtype: MIRResolvedTypeKey): MorphirExp {
        if(sguard === undefined) {
            return gexp;
        }
        else {
            const gcond = this.generateBoolForGuard(sguard.guard);
            const galt = this.generateAltForGuardStmt(sguard.defaultvar, this.typegen.getMIRType(rtype));
            if(sguard.usedefault === "defaultonfalse") {
                return new MorphirIf(gcond, gexp, galt);
            }
            else {
                return new MorphirIf(gcond, galt, gexp);
            }
        }
    }

    private generateGeneralCallValueProcessing(callertype: MIRType, calleetype: MIRType, gcall: MorphirExp, trgt: MIRRegisterArgument, continuation: MorphirExp): MorphirLet {
        const cres = this.generateTempName();
        
        const callermph = this.typegen.getMorphirTypeFor(callertype);
        const calleemph = this.typegen.getMorphirTypeFor(calleetype);

        const okpath = new MorphirLet(this.varToMorphirName(trgt).vname, this.typegen.generateResultGetSuccess(calleetype, new MorphirVar(cres)), continuation);
        const errpath = (callermph.morphirtypename === calleemph.morphirtypename) ? new MorphirVar(cres) : this.typegen.generateResultTypeConstructorError(callertype, this.typegen.generateResultGetError(calleetype, new MorphirVar(cres)));

        const icond = new MorphirIf(this.typegen.generateResultIsErrorTest(calleetype, new MorphirVar(cres)), errpath, okpath);
        return new MorphirLet(cres, gcall, icond);
    }

    private generateLoadVirtualTupleInvName(argflowtype: MIRType, idx: number, resulttype: MIRType, guard: MIRGuard | undefined): string {
        const fullname = `$TupleLoad!${argflowtype.typeID}!${idx}!${resulttype.typeID}${guard !== undefined ? "_WG" : ""}`;
        const shortname = `tuple_load_${this.typegen.lookupTypeName(argflowtype.typeID)}__${idx}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateLoadVirtualPropertyInvName(argflowtype: MIRType, pname: string, resulttype: MIRType, guard: MIRGuard | undefined): string {
        const fullname = `$RecordLoad!${argflowtype.typeID}!${pname}!${resulttype.typeID}${guard !== undefined ? "_WG" : ""}`;
        const shortname = `record_load_${this.typegen.lookupTypeName(argflowtype.typeID)}__${pname}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateLoadVirtualFieldInvName(argflowtype: MIRType, fkey: MIRFieldKey, resulttype: MIRType): string {
        const fdecl = this.assembly.fieldDecls.get(fkey) as MIRFieldDecl;
        const fullname = `$EntityLoad!${argflowtype.typeID}!${fkey}!${resulttype.typeID}`;
        const shortname = `entity_load_${this.typegen.lookupTypeName(argflowtype.typeID)}__${fdecl.fname}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateProjectVirtualTupleInvName(argflowtype: MIRType, indecies: number[], resulttype: MIRType): string {
        const idxs = indecies.map((idx) => `${idx}`).join(",");
        const fullname = `$TupleProject!${argflowtype.typeID}[${idxs}]!${resulttype.typeID}`;
        const shortname = `tuple_project_${this.typegen.lookupTypeName(argflowtype.typeID)}__${idxs}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateProjectVirtualRecordInvName(argflowtype: MIRType, properties: string[], resulttype: MIRType): string {
        const pnames = properties.join(",");
        const fullname = `$RecordProject!${argflowtype.typeID}{${pnames}}${resulttype.typeID}`;
        const shortname = `record_project_${this.typegen.lookupTypeName(argflowtype.typeID)}__${pnames}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateProjectVirtualEntityInvName(argflowtype: MIRType, fields: MIRFieldKey[], resulttype: MIRType): string {
        const fkeys = fields.join(",");
        const shortkeys = fields.map((fn) => (this.assembly.fieldDecls.get(fn) as MIRFieldDecl).fname).join(",")
        const fullname = `$EntityProject!${argflowtype.typeID}!{${fkeys}}!${resulttype.typeID}`;
        const shortname = `entity_project_${this.typegen.lookupTypeName(argflowtype.typeID)}__${shortkeys}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateUpdateVirtualTupleInvName(argflowtype: MIRType, indecies: [number, MIRResolvedTypeKey][], resulttype: MIRType): string {
        const idxs = indecies.map((idx) => `(${idx[0]} ${idx[1]})`).join(",");
        const shortidxs = indecies.map((idx) => idx[0]).join(",");
        const fullname = `$TupleUpdate!${argflowtype.typeID}![${idxs}]=!${resulttype.typeID}`;
        const shortname = `tuple_update_${this.typegen.lookupTypeName(argflowtype.typeID)}__${shortidxs}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateUpdateVirtualRecordInvName(argflowtype: MIRType, properties: [string, MIRResolvedTypeKey][], resulttype: MIRType): string {
        const pnames = properties.map((pname) => `(${pname[0]} ${pname[1]})`).join(",");
        const shortpnames = properties.map((pname) => pname[0]).join(",");
        const fullname = `$RecordUpdate!${argflowtype.typeID}!{${pnames}}=!${resulttype.typeID}`;
        const shortname = `record_update_${this.typegen.lookupTypeName(argflowtype.typeID)}__${shortpnames}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateUpdateVirtualEntityInvName(argflowtype: MIRType, fields: [MIRFieldKey, MIRResolvedTypeKey][], resulttype: MIRType): string {
        const fnames = fields.map((fname) => `(${fname[0]} ${fname[1]})`).join(",");
        const shortfnames = fields.map((fname) => (this.assembly.fieldDecls.get(fname[0]) as MIRFieldDecl).fname).join(",");
        const fullname = `$EntityUpdate!${argflowtype.typeID}!{${fnames}}=!${resulttype.typeID}`;
        const shortname = `entity_update_${argflowtype.typeID}__${shortfnames}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateVirtualInvokeFunctionName(argflowtype: MIRType, fname: MIRVirtualMethodKey, shortvname: string, optmask: boolean, resulttype: MIRType): string {
        const fullname = `$VirtualInvoke!${argflowtype.typeID}!${fname}${optmask ? "_WM_" : ""}!${resulttype.typeID}`;
        const shortname = `virtual_invoke_${this.typegen.lookupTypeName(argflowtype.typeID)}__${shortvname}_`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    private generateVirtualInvokeOperatorName(fname: MIRVirtualMethodKey, shortvname: string, rcvrtypes: MIRResolvedTypeKey[], resulttype: MIRType): string {
        const rnames = `(${rcvrtypes.join(",")})`;
        const shortrnames = `(${rcvrtypes.map((tt) => this.typegen.getMIRType(tt).typeID).join(",")})`;
        const fullname = `$VirtualOperator!${fname}${rnames}!${resulttype.typeID}`;
        const shortname = `virtual_operator_${shortvname}${shortrnames}`;

        this.typegen.internFunctionName(fullname, shortname);
        return fullname;
    }

    generateLoadTupleIndexVirtual(geninfo: { inv: string, argflowtype: MIRType, idx: number, resulttype: MIRType, guard: MIRGuard | undefined }): MorphirFunction {
        const ttuples = [...this.assembly.tupleDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].typeID);
                return this.typegen.isUniqueTupleType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultType(geninfo.resulttype) : this.typegen.getMorphirTypeFor(geninfo.resulttype);
        const ufcname = this.generateUFConstantForType(geninfo.resulttype);
        if(ttuples.length === 0) {
            const rbody = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, new MorphirConst(ufcname), false) : new MorphirConst(ufcname);
            return MorphirFunction.create(this.typegen.lookupFunctionName(geninfo.inv), [{ vname: "arg", vtype: this.typegen.getMorphirTypeFor(geninfo.argflowtype) }], rtype, rbody);
        }
        else {
            const ops = ttuples.map((tt) => {
                const mtt = this.typegen.getMIRType(tt.typeID);
                const test = new MorphirCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new MorphirVar("arg")]);

                const argpp = this.typegen.coerce(new MorphirVar("arg"), geninfo.argflowtype, mtt);
                const idxr = this.typegen.generateTupleIndexGet(tt, geninfo.idx, argpp);
                const crt = this.typegen.coerce(idxr, (geninfo.argflowtype.options[0] as MIRTupleType).entries[geninfo.idx], geninfo.resulttype);
                const action = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, crt, true) : crt;

                return {test: test, result: action};
            });

            const orelse = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, new MorphirConst(ufcname), false) : new MorphirConst(ufcname);

            return MorphirFunction.create(this.typegen.lookupFunctionName(geninfo.inv), [{ vname: "arg", vtype: this.typegen.getMorphirTypeFor(geninfo.argflowtype) }], rtype, new MorphirCond(ops, orelse));
        }
    }

    generateLoadRecordPropertyVirtual(geninfo: { inv: string, argflowtype: MIRType, pname: string, resulttype: MIRType, guard: MIRGuard | undefined }): MorphirFunction {
        const trecords = [...this.assembly.recordDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].typeID);
                return this.typegen.isUniqueRecordType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultType(geninfo.resulttype) : this.typegen.getMorphirTypeFor(geninfo.resulttype);
        const ufcname = this.generateUFConstantForType(geninfo.resulttype);
        if(trecords.length === 0) {
            const rbody = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, new MorphirConst(ufcname), false) : new MorphirConst(ufcname);
            return MorphirFunction.create(this.typegen.lookupFunctionName(geninfo.inv), [{ vname: "arg", vtype: this.typegen.getMorphirTypeFor(geninfo.argflowtype) }], rtype, rbody);
        }
        else {
            const ops = trecords.map((tt) => {
                const mtt = this.typegen.getMIRType(tt.typeID);
                const test = new MorphirCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new MorphirVar("arg")]);

                const argpp = this.typegen.coerce(new MorphirVar("arg"), geninfo.argflowtype, mtt);
                const idxr = this.typegen.generateRecordPropertyGet(tt, geninfo.pname, argpp);
                const crt = this.typegen.coerce(idxr, ((geninfo.argflowtype.options[0] as MIRRecordType).entries.find((vv) => vv.pname === geninfo.pname) as {pname: string, ptype: MIRType}).ptype, geninfo.resulttype);
                const action = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, crt, true) : crt;

                return {test: test, result: action};
            });

            const orelse = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, new MorphirConst(ufcname), false) : new MorphirConst(ufcname);

            return MorphirFunction.create(this.typegen.lookupFunctionName(geninfo.inv), [{ vname: "arg", vtype: this.typegen.getMorphirTypeFor(geninfo.argflowtype) }], rtype, new MorphirCond(ops, orelse));
        }
    }

    generateLoadEntityFieldVirtual(geninfo: { inv: string, argflowtype: MIRType, field: MIRFieldDecl, resulttype: MIRType }): MorphirFunction {
        const tentities = [...this.assembly.entityDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].tkey);
                return this.typegen.isUniqueEntityType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getMorphirTypeFor(geninfo.resulttype);
        let ops = tentities.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.tkey);
            const test = new MorphirCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new MorphirVar("arg")]);

            const argpp = this.typegen.coerce(new MorphirVar("arg"), geninfo.argflowtype, mtt);
            const action = this.typegen.generateEntityFieldGet(tt, geninfo.field, argpp);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        return MorphirFunction.create(this.typegen.lookupFunctionName(geninfo.inv), [{ vname: "arg", vtype: this.typegen.getMorphirTypeFor(geninfo.argflowtype) }], rtype, new MorphirCond(ops, orelse));
    }

    generateProjectTupleIndexVirtual(geninfo: { inv: string, argflowtype: MIRType, indecies: number[], resulttype: MIRType }): MorphirFunction {
        const ttuples = [...this.assembly.tupleDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].typeID);
                return this.typegen.isUniqueTupleType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getMorphirTypeFor(geninfo.resulttype);
        let ops = ttuples.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.typeID);
            const test = new MorphirCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new MorphirVar("arg")]);

            const argpp = this.typegen.coerce(new MorphirVar("arg"), geninfo.argflowtype, mtt);
            const pargs = geninfo.indecies.map((idx, i) => {
                const idxr = this.typegen.generateTupleIndexGet(geninfo.argflowtype.options[0] as MIRTupleType, idx, argpp);
                return this.typegen.coerce(idxr, (geninfo.argflowtype.options[0] as MIRTupleType).entries[idx], (geninfo.resulttype.options[0] as MIREphemeralListType).entries[i]);
            });
            const action = new MorphirCallSimple(this.typegen.getMorphirConstructorName(geninfo.resulttype).cons, pargs);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);
            
        return MorphirFunction.create(this.typegen.lookupFunctionName(geninfo.inv), [{ vname: "arg", vtype: this.typegen.getMorphirTypeFor(geninfo.argflowtype) }], rtype, new MorphirCond(ops, orelse));
    }

    generateProjectRecordPropertyVirtual(geninfo: { inv: string, argflowtype: MIRType, properties: string[], resulttype: MIRType }): MorphirFunction {
        const trecords = [...this.assembly.recordDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].typeID);
                return this.typegen.isUniqueRecordType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getMorphirTypeFor(geninfo.resulttype);
        let ops = trecords.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.typeID);
            const test = new MorphirCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new MorphirVar("arg")]);

            const argpp = this.typegen.coerce(new MorphirVar("arg"), geninfo.argflowtype, mtt);
            const pargs = geninfo.properties.map((pname, i) => {
                const idxr = this.typegen.generateRecordPropertyGet(geninfo.argflowtype.options[0] as MIRRecordType, pname, argpp);
                return this.typegen.coerce(idxr, ((geninfo.argflowtype.options[0] as MIRRecordType).entries.find((vv) => vv.pname === pname) as {pname: string, ptype: MIRType}).ptype, (geninfo.resulttype.options[0] as MIREphemeralListType).entries[i]);
            });
            const action = new MorphirCallSimple(this.typegen.getMorphirConstructorName(geninfo.resulttype).cons, pargs);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        return MorphirFunction.create(this.typegen.lookupFunctionName(geninfo.inv), [{ vname: "arg", vtype: this.typegen.getMorphirTypeFor(geninfo.argflowtype) }], rtype, new MorphirCond(ops, orelse));
    }

    generateProjectEntityFieldVirtual(geninfo: { inv: string, argflowtype: MIRType, fields: MIRFieldDecl[], resulttype: MIRType }): MorphirFunction {
        const tentities = [...this.assembly.entityDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].tkey);
                return this.typegen.isUniqueEntityType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getMorphirTypeFor(geninfo.resulttype);
        let ops = tentities.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.tkey);
            const test = new MorphirCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new MorphirVar("arg")]);

            const argpp = this.typegen.coerce(new MorphirVar("arg"), geninfo.argflowtype, mtt);
            const pargs = geninfo.fields.map((field, i) => {
                const idxr = this.typegen.generateEntityFieldGet(tt, field, argpp);
                return this.typegen.coerce(idxr, this.typegen.getMIRType(field.declaredType), (geninfo.resulttype.options[0] as MIREphemeralListType).entries[i]);
            });
            const action = new MorphirCallSimple(this.typegen.getMorphirConstructorName(geninfo.resulttype).cons, pargs);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        return MorphirFunction.create(this.typegen.lookupFunctionName(geninfo.inv), [{ vname: "arg", vtype: this.typegen.getMorphirTypeFor(geninfo.argflowtype) }], rtype, new MorphirCond(ops, orelse));
    }

    generateSingletonConstructorList(geninfo: { inv: string, argc: number, resulttype: MIRType }): MorphirFunction {
        const ldecl = this.assembly.entityDecls.get(geninfo.resulttype.typeID) as MIRPrimitiveListEntityTypeDecl;
        const etype = ldecl.getTypeT();

        let args: { vname: string, vtype: MorphirTypeInfo }[] = [];
        for(let j = 0; j < geninfo.argc; ++j) {
            args.push({ vname: `arg${j}`, vtype: this.typegen.getMorphirTypeFor(etype) });
        }

        let largs: string[] = [];
        for (let i = 0; i < geninfo.argc; ++i) {
            largs.push(`arg${i}`);
        }

        const bbody = new MorphirConst(`[${largs.join(", ")}]`);
        return MorphirFunction.create(this.typegen.lookupFunctionName(geninfo.inv), args, this.typegen.getMorphirTypeFor(geninfo.resulttype), bbody);
    }

    generateSingletonConstructorMap(geninfo: { srcFile: string, sinfo: SourceInfo, inv: string, argc: number, argtupletype: MIRTupleType, resulttype: MIRType }): MorphirFunction {
        let args: { vname: string, vtype: MorphirTypeInfo }[] = [];
        for(let j = 0; j < geninfo.argc; ++j) {
            args.push({ vname: `arg${j}`, vtype: this.typegen.getMorphirTypeFor(this.typegen.getMIRType(geninfo.argtupletype.typeID)) });
        }
        
        if(geninfo.argc === 1) {
            const vkey = this.typegen.generateTupleIndexGet(geninfo.argtupletype, 0, new MorphirVar("arg0"));
            const vval = this.typegen.generateTupleIndexGet(geninfo.argtupletype, 1, new MorphirVar("arg0"));
            const consexp = new MorphirConst(`[MapEntry ${vkey.emitMorphir(undefined)} ${vval.emitMorphir(undefined)}]`);
            
            return MorphirFunction.create(this.typegen.lookupFunctionName(geninfo.inv), args, this.typegen.getMorphirTypeFor(geninfo.resulttype), consexp);
        }
        else {
            //TODO: here or course
            assert(false);
            return (undefined as any) as MorphirFunction;
        }
    }

    generateUpdateTupleIndexVirtual(geninfo: { inv: string, argflowtype: MIRType, updates: [number, MIRResolvedTypeKey][], resulttype: MIRType }): MorphirFunction {
        const ttuples = [...this.assembly.tupleDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].typeID);
                return this.typegen.isUniqueTupleType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getMorphirTypeFor(geninfo.resulttype);
        let ops = ttuples.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.typeID);
            const test = new MorphirCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new MorphirVar("arg")]);

            const argpp = this.typegen.coerce(new MorphirVar("arg"), geninfo.argflowtype, mtt);
            let cargs: MorphirExp[] = [];
            for (let i = 0; i < tt.entries.length; ++i) {
                const upd = geninfo.updates.findIndex((vv) => vv[0] === i);
                if(upd === undefined) {
                    cargs.push(this.typegen.generateTupleIndexGet(tt, i, argpp));
                }
                else {
                    cargs.push(new MorphirVar(`arg_${i}`));
                }
            }

            const action = new MorphirCallSimple(this.typegen.getMorphirConstructorName(geninfo.resulttype).cons, cargs);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        const fargs = [
            { vname: "arg", vtype: this.typegen.getMorphirTypeFor(geninfo.argflowtype) },
            ...geninfo.updates.map((upd, i) => {
                return { vname: `arg_${i}`, vtype: this.typegen.getMorphirTypeFor(this.typegen.getMIRType(upd[1])) };
            })
        ];
        return MorphirFunction.create(this.typegen.lookupFunctionName(geninfo.inv), fargs, rtype, new MorphirCond(ops, orelse));
    }

    generateUpdateRecordPropertyVirtual(geninfo: { inv: string, argflowtype: MIRType, updates: [string, MIRResolvedTypeKey][], resulttype: MIRType }): MorphirFunction {
        const trecords = [...this.assembly.recordDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].typeID);
                return this.typegen.isUniqueRecordType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getMorphirTypeFor(geninfo.resulttype);
        let ops = trecords.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.typeID);
            const test = new MorphirCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new MorphirVar("arg")]);

            const argpp = this.typegen.coerce(new MorphirVar("arg"), geninfo.argflowtype, mtt);
            let cargs: MorphirExp[] = [];
            for (let i = 0; i < tt.entries.length; ++i) {
                const upd = geninfo.updates.find((vv) => vv[0] === tt.entries[i].pname);
                if(upd === undefined) {
                    cargs.push(this.typegen.generateRecordPropertyGet(tt, tt.entries[i].pname, argpp));
                }
                else {
                    cargs.push(new MorphirVar(`arg_${i}`));
                }
            }
            const action = new MorphirCallSimple(this.typegen.getMorphirConstructorName(geninfo.resulttype).cons, cargs);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        const fargs = [
            { vname: "arg", vtype: this.typegen.getMorphirTypeFor(geninfo.argflowtype) },
            ...geninfo.updates.map((upd, i) => {
                return { vname: `arg_${i}`, vtype: this.typegen.getMorphirTypeFor(this.typegen.getMIRType(upd[1])) };
            })
        ];
        return MorphirFunction.create(this.typegen.lookupFunctionName(geninfo.inv), fargs, rtype, new MorphirCond(ops, orelse));
    }

    generateUpdateEntityFieldVirtual(geninfo: { inv: string, argflowtype: MIRType, allsafe: boolean, updates: [MIRFieldKey, MIRResolvedTypeKey][], resulttype: MIRType }): MorphirFunction {
        const tentities = [...this.assembly.entityDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].tkey);
                return this.typegen.isUniqueEntityType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getMorphirTypeFor(geninfo.resulttype);
        let ops = tentities.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.tkey);
            const consfields = (this.assembly.entityDecls.get(tt.tkey) as MIRObjectEntityTypeDecl).consfuncfields.map((ccf) => this.assembly.fieldDecls.get(ccf.cfkey) as MIRFieldDecl);

            const test = new MorphirCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new MorphirVar("arg")]);

            const argpp = this.typegen.coerce(new MorphirVar("arg"), geninfo.argflowtype, mtt);
           
            let cargs: MorphirExp[] = [];
            for (let i = 0; i < consfields.length; ++i) {
                const upd = geninfo.updates.find((vv) => vv[0] === consfields[i].fname);
                if(upd === undefined) {
                    cargs.push(this.typegen.generateEntityFieldGet(tt, consfields[i], argpp));
                }
                else {
                    cargs.push(new MorphirVar(`arg_${i}`));
                }
            }
            
            let action: MorphirExp = new MorphirConst("[NOT SET]"); 
            if (this.isSafeConstructorInvoke(mtt) && geninfo.allsafe) {
                const ccall = new MorphirCallSimple(this.typegen.getMorphirConstructorName(mtt).cons, cargs);
                action = this.typegen.coerce(ccall, mtt, geninfo.resulttype);
            }
            else {
                if(this.isSafeConstructorInvoke(mtt)) {
                    const ccall = new MorphirCallSimple(this.typegen.getMorphirConstructorName(mtt).cons, cargs);
                    action = this.typegen.coerce(ccall, mtt, geninfo.resulttype);
                }
                else {
                    const consfunc = (this.assembly.entityDecls.get(tt.tkey) as MIRObjectEntityTypeDecl).consfunc;
                    const ccall = new MorphirCallGeneral(this.typegen.lookupFunctionName(consfunc as MIRInvokeKey), cargs);
                    if(mtt.typeID === geninfo.resulttype.typeID) {
                        action = ccall;
                    }
                    else {
                        const tres = this.generateTempName();
                        const cond = this.typegen.generateResultIsSuccessTest(mtt, new MorphirVar(tres));
                        const erropt = this.typegen.generateResultTypeConstructorError(geninfo.resulttype, this.typegen.generateResultGetError(mtt, new MorphirVar(tres)));
                        const okopt =  this.typegen.generateResultTypeConstructorSuccess(geninfo.resulttype, this.typegen.coerce(this.typegen.generateResultGetSuccess(mtt, new MorphirVar(tres)), mtt, geninfo.resulttype));

                        action = new MorphirLet(tres, ccall, new MorphirIf(cond, okopt, erropt));
                    } 
                }
            }

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        const fargs = [
            { vname: "arg", vtype: this.typegen.getMorphirTypeFor(geninfo.argflowtype) },
            ...geninfo.updates.map((upd, i) => {
                return { vname: `arg_${i}`, vtype: this.typegen.getMorphirTypeFor(this.typegen.getMIRType(upd[1])) };
            })
        ];
        return MorphirFunction.create(this.typegen.lookupFunctionName(geninfo.inv), fargs, rtype, new MorphirCond(ops, orelse));
    }

    generateVirtualFunctionInvoke(geninfo: { inv: string, allsafe: boolean, argflowtype: MIRType, vfname: MIRVirtualMethodKey, optmask: string | undefined, resulttype: MIRType }): MorphirFunction {
        const tentities = [...this.assembly.entityDecls]
            .filter((tt) => {
                const mtt = this.typegen.getMIRType(tt[1].tkey);
                return this.typegen.isUniqueEntityType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getMorphirTypeFor(geninfo.resulttype);
        let ops = tentities.map((tt) => {
            const mtt = this.typegen.getMIRType(tt.tkey);
            const vfunc = (this.assembly.entityDecls.get(tt.tkey) as MIRObjectEntityTypeDecl).vcallMap.get(geninfo.vfname) as MIRInvokeKey;
            
            const test = new MorphirCallSimple(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new MorphirVar("arg")]);

            const argpp = this.typegen.coerce(new MorphirVar("arg"), geninfo.argflowtype, mtt);
            const invk = this.assembly.invokeDecls.get(vfunc) as MIRInvokeBodyDecl;
            const atype = this.typegen.getMIRType(invk.resultType);

            const cargs = [argpp, ...invk.params.slice(1).map((p, i) =>new MorphirVar(`arg_${i}`))];

            const gcall = geninfo.optmask !== undefined ? new MorphirCallGeneralWPassThroughMask(this.typegen.lookupFunctionName(vfunc), cargs, geninfo.optmask) : new MorphirCallGeneral(this.typegen.lookupFunctionName(vfunc), cargs);
                
            let action: MorphirExp = new MorphirConst("[NOT SET]"); 
            if (this.isSafeInvoke(vfunc) && geninfo.allsafe) {
                action = this.typegen.coerce(gcall, atype, geninfo.resulttype);
            }
            else {
                if(this.isSafeInvoke(vfunc)) {
                    action = this.typegen.generateResultTypeConstructorSuccess(geninfo.resulttype, this.typegen.coerce(gcall, atype, geninfo.resulttype));
                }
                else {
                    const mphaatype = this.typegen.getMorphirTypeFor(atype);
                    const mphgresult = this.typegen.getMorphirTypeFor(geninfo.resulttype);
                    if(mphaatype.morphirtypename === mphgresult.morphirtypename) {
                        action = gcall;
                    }
                    else {
                        const tres = this.generateTempName();
                        const cond = this.typegen.generateResultIsSuccessTest(atype, new MorphirVar(tres));
                        const erropt = this.typegen.generateResultTypeConstructorError(geninfo.resulttype, this.typegen.generateResultGetError(atype, new MorphirVar(tres)));
                        const okopt =  this.typegen.generateResultTypeConstructorSuccess(geninfo.resulttype, this.typegen.coerce(this.typegen.generateResultGetSuccess(atype, new MorphirVar(tres)), atype, geninfo.resulttype));

                        action = new MorphirLet(tres, gcall, new MorphirIf(cond, okopt, erropt));
                    } 
                }
            }

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        const sinvk = this.assembly.invokeDecls.get((this.assembly.entityDecls.get(tentities[0].tkey) as MIRObjectEntityTypeDecl).vcallMap.get(geninfo.vfname) as MIRInvokeKey) as MIRInvokeBodyDecl;
        const argtypes = sinvk.params.slice(1).map((p) => this.typegen.getMorphirTypeFor(this.typegen.getMIRType(p.type)));

        const fargs = [
            { vname: "arg", vtype: this.typegen.getMorphirTypeFor(geninfo.argflowtype) },
            ...argtypes.map((vv, i) => {
                return { vname: `arg_${i}`, vtype: vv };
            })
        ];
        return MorphirFunction.create(this.typegen.lookupFunctionName(geninfo.inv), fargs, rtype, new MorphirCond(ops, orelse));
    }

    generateVirtualOperatorInvoke(geninfo: { inv: string, argflowtype: MIRType, opname: MIRVirtualMethodKey, args: MIRResolvedTypeKey[], resulttype: MIRType }): MorphirFunction {
        //const otrgts = this.assembly.virtualOperatorDecls.get(geninfo.opname) as MIRInvokeKey[];

        return MorphirFunction.create("NOT_IMPLEMENTED", [], this.typegen.getMorphirTypeFor(geninfo.resulttype), NOT_IMPLEMENTED("generateVirtualOperatorInvoke"));
    }

    private generateSubtypeCheckEntity(arg: MIRArgument, layout: MIRType, flow: MIRType, ofentity: MIRType): MorphirExp {
        if(flow.options.every((opt) => (opt instanceof MIRTupleType) || (opt instanceof MIRRecordType))) {
            return new MorphirConst("False");
        }

        if (this.typegen.isUniqueEntityType(flow)) {
            return new MorphirConst(flow.typeID === ofentity.typeID ? "True" : "False");
        }
        else {
            const accessTypeTag = this.typegen.getMorphirTypeFor(layout).isGeneralTermType() ? new MorphirCallSimple("getTypeTag_BTerm", [this.argToMorphir(arg)]) : new MorphirCallSimple("getTypeTag_BKey", [this.argToMorphir(arg)]);
            return MorphirCallSimple.makeEq(accessTypeTag, new MorphirConst(`TypeTag_${this.typegen.lookupTypeName(ofentity.typeID)}`));
        }
    }

    private generateSubtypeCheckConcept(arg: MIRArgument, layout: MIRType, flow: MIRType, ofconcept: MIRType): MorphirExp {
        if (this.typegen.isUniqueEntityType(flow) || this.typegen.isUniqueTupleType(flow) || this.typegen.isUniqueRecordType(flow)) {
            return new MorphirConst(this.assembly.subtypeOf(flow, ofconcept) ? "True" : "False");
        }
        else {
            const accessTypeTag = this.typegen.getMorphirTypeFor(layout).isGeneralTermType() ? new MorphirCallSimple("getTypeTag_BTerm", [this.argToMorphir(arg)]) : new MorphirCallSimple("getTypeTag_BKey", [this.argToMorphir(arg)]);
            
            const occ = ofconcept.options[0] as MIRConceptType;
            let tests: MorphirExp[] = [];
            for(let i = 0; i < occ.ckeys.length; ++i) {
                this.processSubtypeTagCheck(flow, ofconcept);
                tests.push(new MorphirCallSimple("subtypeOf", [accessTypeTag, new MorphirConst(`AbstractTypeTag_${this.typegen.lookupTypeName(occ.ckeys[i])}`)]));
            }

            if(tests.length === 1) {
                return tests[0];
            }
            else {
                return MorphirCallSimple.makeAndOf(...tests);
            }
        }
    }

    private generateSubtypeCheckTuple(arg: MIRArgument, layout: MIRType, flow: MIRType, oftuple: MIRType): MorphirExp {
        if(flow.options.every((opt) => (opt instanceof MIREntityType) || (opt instanceof MIRRecordType))) {
            return new MorphirConst("False");
        }

        if (this.typegen.isUniqueTupleType(flow)) {
            return new MorphirConst(this.assembly.subtypeOf(flow, oftuple) ? "True" : "False");
        }
        else {
            const accessTypeTag = new MorphirCallSimple("getTypeTag_BTerm", [this.argToMorphir(arg)]);
            return MorphirCallSimple.makeEq(accessTypeTag, new MorphirConst(`TypeTag_${this.typegen.lookupTypeName(oftuple.typeID)}`));
        }
    }

    private generateSubtypeCheckRecord(arg: MIRArgument, layout: MIRType, flow: MIRType, ofrecord: MIRType): MorphirExp {
        if(flow.options.every((opt) => (opt instanceof MIREntityType) || (opt instanceof MIRTupleType))) {
            return new MorphirConst("False");
        }

        if (this.typegen.isUniqueRecordType(flow)) {
            return new MorphirConst(this.assembly.subtypeOf(flow, ofrecord) ? "True" : "False");
        }
        else {
            const accessTypeTag = new MorphirCallSimple("getTypeTag_BTerm", [this.argToMorphir(arg)]);
            return MorphirCallSimple.makeEq(accessTypeTag, new MorphirConst(`TypeTag_${this.typegen.lookupTypeName(ofrecord.typeID)}`));
        }
    }

    constructor(assembly: MIRAssembly, typegen: MorphirTypeEmitter, callsafety: Map<MIRInvokeKey, { safe: boolean, trgt: boolean }>) {
        this.assembly = assembly;
        this.typegen = typegen;
        this.callsafety = callsafety;

        this.currentRType = typegen.getMIRType("None");

        const safecalls = new Set<MIRInvokeKey>();
        callsafety.forEach((pv, inv) => {
            if(pv.safe) {
                safecalls.add(inv);
            }
        });
    }

    generateTempName(): string {
        return `tmp_var_${this.tmpvarctr++}`;
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

    constantToMorphir(cval: MIRConstantArgument): MorphirExp {
        if (cval instanceof MIRConstantNone) {
            return new MorphirConst("bsqnone_literal");
        }
        else if (cval instanceof MIRConstantNothing) {
            return new MorphirConst("bsqnothing_literal");
        }
        else if (cval instanceof MIRConstantTrue) {
            return new MorphirConst("True");
        }
        else if (cval instanceof MIRConstantFalse) {
            return new MorphirConst("False");
        }
        else if (cval instanceof MIRConstantInt) {
            return new MorphirConst(cval.value.slice(0, cval.value.length - 1));
        }
        else if (cval instanceof MIRConstantNat) {
            return new MorphirConst(cval.value.slice(0, cval.value.length - 1));
        }
        else if (cval instanceof MIRConstantBigInt) {
            return new MorphirConst(cval.value.slice(0, cval.value.length - 1));
        }
        else if (cval instanceof MIRConstantBigNat) {
            return new MorphirConst(cval.value.slice(0, cval.value.length - 1));
        }
        else if (cval instanceof MIRConstantRational) {
            if(/^0\/[0-9]+R$/.test(cval.value)) {
                return new MorphirConst("bRational_zero");
            }
            else if(/^1\/1R$/.test(cval.value)) {
                return new MorphirConst("bRational_one");
            }
            else {
                return NOT_IMPLEMENTED("BRational mixed");
            }
        }
        else if (cval instanceof MIRConstantFloat) {
            if(/^0([.]0+)?f$/.test(cval.value)) {
                return new MorphirConst("bFloat_zero");
            }
            else if(/^1([.]0+)?f$/.test(cval.value)) {
                return new MorphirConst("bFloat_one");
            }
            else {
                const fval = cval.value.slice(0, cval.value.length - 1);
                return new MorphirConst(fval.includes(".") ? fval : (fval + ".0"));
            }
        }
        else if (cval instanceof MIRConstantDecimal) {
            if(/^0([.]0+)?d$/.test(cval.value)) {
                return new MorphirConst("bDecimal_zero");
            }
            else if(/^1([.]0+)?d$/.test(cval.value)) {
                return new MorphirConst("bDecimal_one");
            }
            else {
                const dval = cval.value.slice(0, cval.value.length - 1);
                return new MorphirConst(dval.includes(".") ? dval : (dval + ".0"));
            }
        }
        else if (cval instanceof MIRConstantString) {
            return new MorphirConst(cval.value);
        }
        else if (cval instanceof MIRConstantTypedNumber) {
            return this.constantToMorphir(cval.value);
        }
        else if (cval instanceof MIRConstantStringOf) {
            return new MorphirConst("\"" + cval.value.slice(1, cval.value.length - 1) + "\"");
        }
        else if (cval instanceof MIRConstantDataString) {
            return new MorphirConst("\"" + cval.value.slice(1, cval.value.length - 1) + "\"");
        }
        else {
            assert(cval instanceof MIRConstantRegex);

            const rval = (cval as MIRConstantRegex).value;
            const ere = this.assembly.literalRegexs.findIndex((re) => re.restr === rval.restr);
            const mre = this.assembly.literalRegexs[ere].compileToJS();

            return new MorphirConst(mre);
        }
    }

    argToMorphir(arg: MIRArgument): MorphirExp {
        if (arg instanceof MIRRegisterArgument) {
            return this.varToMorphirName(arg);
        }
        else if(arg instanceof MIRGlobalVariable) {
            return this.globalToMorphir(arg);
        }
        else {
            return this.constantToMorphir(arg as MIRConstantArgument);
        }
    }

    generateNoneCheck(arg: MIRArgument, argtype: MIRType): MorphirExp {
        if (this.typegen.isType(argtype, "None")) {
            return new MorphirConst("True");
        }
        else if (!this.assembly.subtypeOf(this.typegen.getMIRType("None"), argtype)) {
            return new MorphirConst("False");
        }
        else {
            const trepr = this.typegen.getMorphirTypeFor(argtype);
            if(trepr.isGeneralKeyType()) {
                return new MorphirCallSimple("isBKeyNone", [this.argToMorphir(arg)]);
            }
            else {
                return new MorphirCallSimple("isBTermNone", [this.argToMorphir(arg)]);
            }
        }
    }

    generateSomeCheck(arg: MIRArgument, argtype: MIRType): MorphirExp {
        if (this.typegen.isType(argtype, "None")) {
            return new MorphirConst("False");
        }
        else if (!this.assembly.subtypeOf(this.typegen.getMIRType("None"), argtype)) {
            return new MorphirConst("True");
        }
        else {
            const trepr = this.typegen.getMorphirTypeFor(argtype);
            if(trepr.isGeneralKeyType()) {
                return new MorphirCallSimple("isBKeySome", [this.argToMorphir(arg)]);
            }
            else {
                return new MorphirCallSimple("isBTermSome", [this.argToMorphir(arg)]);
            }
        }
    }
    
    generateNothingCheck(arg: MIRArgument, argtype: MIRType): MorphirExp {
        if (this.typegen.isType(argtype, "Nothing")) {
            return new MorphirConst("True");
        }
        else if (!this.assembly.subtypeOf(this.typegen.getMIRType("Nothing"), argtype)) {
            return new MorphirConst("False");
        }
        else {
            return new MorphirCallSimple("isBTermNothing", [this.argToMorphir(arg)]);
        }
    }

    processAbort(op: MIRAbort): MorphirExp {
        return this.typegen.generateErrorResultAssert(this.currentRType, this.currentFile, op.sinfo);
    }

    processAssertCheck(op: MIRAssertCheck, continuation: MorphirExp): MorphirExp {
        const chkval = this.argToMorphir(op.arg);
        const errorval = this.typegen.generateErrorResultAssert(this.currentRType, this.currentFile, op.sinfo);
        
        return new MorphirIf(chkval, continuation, errorval);
    }

    processLoadUnintVariableValue(op: MIRLoadUnintVariableValue, continuation: MorphirExp): MorphirExp {
        const ufcname = this.generateUFConstantForType(this.typegen.getMIRType(op.oftype));

        return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirConst(ufcname), continuation);
    }

    processDeclareGuardFlagLocation(op: MIRDeclareGuardFlagLocation) {
        this.maskSizes.add(op.count);
        this.pendingMask = this.pendingMask.filter((pm) => pm.maskname !== op.name);
    }

    processSetConstantGuardFlag(op: MIRSetConstantGuardFlag) {
        const pm = this.pendingMask.find((mm) => mm.maskname === op.name) as MorphirMaskConstruct;
        pm.entries[op.position] = new MorphirConst(op.flag ? "True" : "False");
    }

    processConvertValue(op: MIRConvertValue, continuation: MorphirExp): MorphirExp {
        const conv = this.typegen.coerce(this.argToMorphir(op.src), this.typegen.getMIRType(op.srctypelayout), this.typegen.getMIRType(op.intotype));
        const call = this.generateGuardStmtCond(op.sguard, conv, op.intotype);

        return new MorphirLet(this.varToMorphirName(op.trgt).vname, call, continuation);
    }

    processInject(op: MIRInject, continuation: MorphirExp): MorphirExp {
        return new MorphirLet(this.varToMorphirName(op.trgt).vname, this.argToMorphir(op.src), continuation);
    }

    processGuardedOptionInject(op: MIRGuardedOptionInject, continuation: MorphirExp): MorphirExp {
        const conv = this.typegen.coerce(this.argToMorphir(op.src), this.typegen.getMIRType(op.somethingtype), this.typegen.getMIRType(op.optiontype));
        const call = this.generateGuardStmtCond(op.sguard, conv, op.optiontype);

        return new MorphirLet(this.varToMorphirName(op.trgt).vname, call, continuation);
    }

    processExtract(op: MIRExtract, continuation: MorphirExp): MorphirExp {
        return new MorphirLet(this.varToMorphirName(op.trgt).vname, this.argToMorphir(op.src), continuation);
    }

    processLoadConst(op: MIRLoadConst, continuation: MorphirExp): MorphirExp {
        return new MorphirLet(this.varToMorphirName(op.trgt).vname, this.argToMorphir(op.src), continuation);
    }

    processTupleHasIndex(op: MIRTupleHasIndex, continuation: MorphirExp): MorphirExp {
        const argtype = this.typegen.getMorphirTypeFor(this.typegen.getMIRType(op.arglayouttype));

        this.processIndexTagCheck(op.idx, this.typegen.getMIRType(op.argflowtype));
        const accessTypeTag = argtype.isGeneralTermType() ? new MorphirCallSimple("getTypeTag_BTerm", [this.argToMorphir(op.arg)]) : new MorphirCallSimple("getTypeTag_BKey", [this.argToMorphir(op.arg)]);
        return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple("hasIndex", [accessTypeTag, new MorphirConst(`TupleIndexTag_${op.idx}`)]), continuation);
    }

    processRecordHasProperty(op: MIRRecordHasProperty, continuation: MorphirExp): MorphirExp {
        const argtype = this.typegen.getMorphirTypeFor(this.typegen.getMIRType(op.arglayouttype));

        this.processPropertyTagCheck(op.pname, this.typegen.getMIRType(op.argflowtype));
        const accessTypeTag = argtype.isGeneralTermType() ? new MorphirCallSimple("getTypeTag_BTerm", [this.argToMorphir(op.arg)]) : new MorphirCallSimple("getTypeTag_BKey", [this.argToMorphir(op.arg)]);
        return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple("hasProperty", [accessTypeTag, new MorphirConst(`RecordPropertyTag_${op.pname}`)]), continuation);
    }

    processLoadTupleIndex(op: MIRLoadTupleIndex, continuation: MorphirExp): MorphirExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateLoadVirtualTupleInvName(this.typegen.getMIRType(op.argflowtype), op.idx, this.typegen.getMIRType(op.resulttype), undefined);
            if(this.requiredLoadVirtualTupleIndex.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), idx: op.idx, resulttype: this.typegen.getMIRType(op.resulttype), guard: undefined };
                this.requiredLoadVirtualTupleIndex.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.lookupFunctionName(icall), [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            const idxr = this.typegen.generateTupleIndexGet(argflowtype.options[0] as MIRTupleType, op.idx, argpp);
            return new MorphirLet(this.varToMorphirName(op.trgt).vname, idxr, continuation);
        }
    }

    processLoadTupleIndexSetGuard(op: MIRLoadTupleIndexSetGuard, continuation: MorphirExp): MorphirExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateLoadVirtualTupleInvName(this.typegen.getMIRType(op.argflowtype), op.idx, this.typegen.getMIRType(op.resulttype), op.guard);
            if(this.requiredLoadVirtualTupleIndex.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), idx: op.idx, resulttype: this.typegen.getMIRType(op.resulttype), guard: op.guard };
                this.requiredLoadVirtualTupleIndex.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            const cc = new MorphirCallSimple(this.typegen.lookupFunctionName(icall), [argpp]);

            const callbind = this.generateTempName();
            const mphcallvar = new MorphirVar(callbind);
            let ncont: MorphirExp = new MorphirConst("[UNDEF]");

            if(op.guard instanceof MIRMaskGuard) {
                const pm = this.pendingMask.find((mm) => mm.maskname === (op.guard as MIRMaskGuard).gmask) as MorphirMaskConstruct;
                pm.entries[(op.guard as MIRMaskGuard).gindex] = this.typegen.generateAccessWithSetGuardResultGetFlag(this.typegen.getMIRType(op.resulttype), mphcallvar);

                ncont = new MorphirLet(this.varToMorphirName(op.trgt).vname, this.typegen.generateAccessWithSetGuardResultGetValue(this.typegen.getMIRType(op.resulttype), mphcallvar), continuation);
            }
            else {
                ncont = new MorphirLetMulti([
                    { vname: this.varToMorphirName((op.guard as MIRArgGuard).greg as MIRRegisterArgument).vname, value: this.typegen.generateAccessWithSetGuardResultGetFlag(this.typegen.getMIRType(op.resulttype), mphcallvar) },
                    { vname: this.varToMorphirName(op.trgt).vname, value: this.typegen.generateAccessWithSetGuardResultGetValue(this.typegen.getMIRType(op.resulttype), mphcallvar) }
                ], continuation);
            }

            return new MorphirLet(callbind, cc, ncont);
        }
        else {
            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            const idxr = this.typegen.generateTupleIndexGet(argflowtype.options[0] as MIRTupleType, op.idx, argpp);

            if(op.guard instanceof MIRMaskGuard) {
                const pm = this.pendingMask.find((mm) => mm.maskname === (op.guard as MIRMaskGuard).gmask) as MorphirMaskConstruct;
                pm.entries[(op.guard as MIRMaskGuard).gindex] = new MorphirConst("True");

                return new MorphirLet(this.varToMorphirName(op.trgt).vname, idxr, continuation);
            }
            else {
                return new MorphirLetMulti([
                    { vname: this.varToMorphirName((op.guard as MIRArgGuard).greg as MIRRegisterArgument).vname, value: new MorphirConst("True") },
                    { vname: this.varToMorphirName(op.trgt).vname, value: idxr }
                ], continuation);
            }
        }
    }

    processLoadRecordProperty(op: MIRLoadRecordProperty, continuation: MorphirExp): MorphirExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateLoadVirtualPropertyInvName(this.typegen.getMIRType(op.argflowtype), op.pname, this.typegen.getMIRType(op.resulttype), undefined);
            if(this.requiredLoadVirtualRecordProperty.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), pname: op.pname, resulttype: this.typegen.getMIRType(op.resulttype), guard: undefined };
                this.requiredLoadVirtualRecordProperty.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.lookupFunctionName(icall), [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            const idxr = this.typegen.generateRecordPropertyGet(argflowtype.options[0] as MIRRecordType, op.pname, argpp);
            return new MorphirLet(this.varToMorphirName(op.trgt).vname, idxr, continuation);
        }
    }

    processLoadRecordPropertySetGuard(op: MIRLoadRecordPropertySetGuard, continuation: MorphirExp): MorphirExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateLoadVirtualPropertyInvName(this.typegen.getMIRType(op.argflowtype), op.pname, this.typegen.getMIRType(op.resulttype), op.guard);
            if(this.requiredLoadVirtualRecordProperty.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), pname: op.pname, resulttype: this.typegen.getMIRType(op.resulttype), guard: op.guard };
                this.requiredLoadVirtualRecordProperty.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            const cc = new MorphirCallSimple(this.typegen.lookupFunctionName(icall), [argpp]);

            const callbind = this.generateTempName();
            const mphcallvar = new MorphirVar(callbind);
            let ncont: MorphirExp = new MorphirConst("[UNDEF]");

            if(op.guard instanceof MIRMaskGuard) {
                const pm = this.pendingMask.find((mm) => mm.maskname === (op.guard as MIRMaskGuard).gmask) as MorphirMaskConstruct;
                pm.entries[(op.guard as MIRMaskGuard).gindex] = this.typegen.generateAccessWithSetGuardResultGetFlag(this.typegen.getMIRType(op.resulttype), mphcallvar);

                ncont = new MorphirLet(this.varToMorphirName(op.trgt).vname, this.typegen.generateAccessWithSetGuardResultGetValue(this.typegen.getMIRType(op.resulttype), mphcallvar), continuation);
            }
            else {
                ncont = new MorphirLetMulti([
                    { vname: this.varToMorphirName((op.guard as MIRArgGuard).greg as MIRRegisterArgument).vname, value: this.typegen.generateAccessWithSetGuardResultGetFlag(this.typegen.getMIRType(op.resulttype), mphcallvar) },
                    { vname: this.varToMorphirName(op.trgt).vname, value: this.typegen.generateAccessWithSetGuardResultGetValue(this.typegen.getMIRType(op.resulttype), mphcallvar) }
                ], continuation);
            }

            return new MorphirLet(callbind, cc, ncont);
        }
        else {
            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            const idxr = this.typegen.generateRecordPropertyGet(argflowtype.options[0] as MIRRecordType, op.pname, argpp);
            
            if(op.guard instanceof MIRMaskGuard) {
                const pm = this.pendingMask.find((mm) => mm.maskname === (op.guard as MIRMaskGuard).gmask) as MorphirMaskConstruct;
                pm.entries[(op.guard as MIRMaskGuard).gindex] = new MorphirConst("True");

                return new MorphirLet(this.varToMorphirName(op.trgt).vname, idxr, continuation);
            }
            else {
                return new MorphirLetMulti([
                    { vname: this.varToMorphirName((op.guard as MIRArgGuard).greg as MIRRegisterArgument).vname, value: new MorphirConst("True") },
                    { vname: this.varToMorphirName(op.trgt).vname, value: idxr }
                ], continuation);
            }
        }
    }

    processLoadField(op: MIRLoadField, continuation: MorphirExp): MorphirExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateLoadVirtualFieldInvName(this.typegen.getMIRType(op.argflowtype), op.field, this.typegen.getMIRType(op.resulttype));
            if(this.requiredLoadVirtualEntityField.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), field: this.assembly.fieldDecls.get(op.field) as MIRFieldDecl, resulttype: this.typegen.getMIRType(op.resulttype) };
                this.requiredLoadVirtualEntityField.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.lookupFunctionName(icall), [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            const fdecl = this.assembly.fieldDecls.get(op.field) as MIRFieldDecl;
            const idxr = this.typegen.generateEntityFieldGet(this.assembly.entityDecls.get(argflowtype.typeID) as MIREntityTypeDecl, fdecl, argpp);
            return new MorphirLet(this.varToMorphirName(op.trgt).vname, idxr, continuation);
        }
    }

    processTupleProjectToEphemeral(op: MIRTupleProjectToEphemeral, continuation: MorphirExp): MorphirExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.epht);

        if(op.isvirtual) {
            const icall = this.generateProjectVirtualTupleInvName(this.typegen.getMIRType(op.argflowtype), op.indecies, resulttype);
            if(this.requiredProjectVirtualTupleIndex.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), indecies: op.indecies, resulttype: resulttype };
                this.requiredProjectVirtualTupleIndex.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.lookupFunctionName(icall), [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            const pargs = op.indecies.map((idx, i) => {
                const idxr = this.typegen.generateTupleIndexGet(argflowtype.options[0] as MIRTupleType, idx, argpp);
                return this.typegen.coerce(idxr, (argflowtype.options[0] as MIRTupleType).entries[idx], (resulttype.options[0] as MIREphemeralListType).entries[i]);
            });

            return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.getMorphirConstructorName(resulttype).cons, pargs), continuation);
        }
    }

    processRecordProjectToEphemeral(op: MIRRecordProjectToEphemeral, continuation: MorphirExp): MorphirExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.epht);

        if(op.isvirtual) {
            const icall = this.generateProjectVirtualRecordInvName(this.typegen.getMIRType(op.argflowtype), op.properties, resulttype);
            if(this.requiredProjectVirtualRecordProperty.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), properties: op.properties, resulttype: resulttype };
                this.requiredProjectVirtualRecordProperty.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.lookupFunctionName(icall), [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            const pargs = op.properties.map((pname, i) => {
                const idxr = this.typegen.generateRecordPropertyGet(argflowtype.options[0] as MIRRecordType, pname, argpp);
                return this.typegen.coerce(idxr, ((argflowtype.options[0] as MIRRecordType).entries.find((vv) => vv.pname === pname) as {pname: string, ptype: MIRType}).ptype, (resulttype.options[0] as MIREphemeralListType).entries[i]);
            });

            return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.getMorphirConstructorName(resulttype).cons, pargs), continuation);
        }
    }

    processEntityProjectToEphemeral(op: MIREntityProjectToEphemeral, continuation: MorphirExp): MorphirExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.epht);

        if(op.isvirtual) {
            const icall = this.generateProjectVirtualEntityInvName(this.typegen.getMIRType(op.argflowtype), op.fields, resulttype);
            if(this.requiredProjectVirtualEntityField.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), fields: op.fields.map((fkey) => this.assembly.fieldDecls.get(fkey) as MIRFieldDecl), resulttype: resulttype };
                this.requiredProjectVirtualEntityField.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.lookupFunctionName(icall), [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            const pargs = op.fields.map((fkey, i) => {
                const fdecl = this.assembly.fieldDecls.get(fkey) as MIRFieldDecl;
                const idxr = this.typegen.generateEntityFieldGet(this.assembly.entityDecls.get(argflowtype.typeID) as MIREntityTypeDecl, fdecl, argpp);
                return this.typegen.coerce(idxr, this.typegen.getMIRType((this.assembly.fieldDecls.get(fkey) as MIRFieldDecl).declaredType), (resulttype.options[0] as MIREphemeralListType).entries[i]);
            });

            return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.getMorphirConstructorName(resulttype).cons, pargs), continuation);
        }
    }

    processTupleUpdate(op: MIRTupleUpdate, continuation: MorphirExp): MorphirExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateUpdateVirtualTupleInvName(this.typegen.getMIRType(op.argflowtype), op.updates.map((upd) => [upd[0], upd[2]]), resulttype);
            if(this.requiredUpdateVirtualTuple.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), updates: op.updates.map((upd) => [upd[0], upd[2]] as [number, MIRResolvedTypeKey]), resulttype: resulttype };
                this.requiredUpdateVirtualTuple.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.lookupFunctionName(icall), [argpp]), continuation);
        }
        else {
            const ttype = argflowtype.options[0] as MIRTupleType;

            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            let cargs: MorphirExp[] = [];
            for (let i = 0; i < ttype.entries.length; ++i) {
                const upd = op.updates.find((vv) => vv[0] === i);
                if(upd === undefined) {
                    cargs.push(this.typegen.generateTupleIndexGet(ttype, i, argpp));
                }
                else {
                    cargs.push(this.argToMorphir(upd[1]));
                }
            }

            return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.getMorphirConstructorName(resulttype).cons, cargs), continuation);
        }
    }

    processRecordUpdate(op: MIRRecordUpdate, continuation: MorphirExp): MorphirExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateUpdateVirtualRecordInvName(this.typegen.getMIRType(op.argflowtype), op.updates.map((upd) => [upd[0], upd[2]]), resulttype);
            if(this.requiredUpdateVirtualRecord.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), updates: op.updates.map((upd) => [upd[0], upd[2]] as [string, MIRResolvedTypeKey]), resulttype: resulttype };
                this.requiredUpdateVirtualRecord.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.lookupFunctionName(icall), [argpp]), continuation);
        }
        else {
            const ttype = argflowtype.options[0] as MIRRecordType;

            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            let cargs: MorphirExp[] = [];
            for (let i = 0; i < ttype.entries.length; ++i) {
                const upd = op.updates.find((vv) => vv[0] === ttype.entries[i].pname);
                if(upd === undefined) {
                    cargs.push(this.typegen.generateRecordPropertyGet(ttype, ttype.entries[i].pname, argpp));
                }
                else {
                    cargs.push(this.argToMorphir(upd[1]));
                }
            }

            return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.getMorphirConstructorName(resulttype).cons, cargs), continuation);
        }
    }

    processEntityUpdate(op: MIREntityUpdate, continuation: MorphirExp): MorphirExp {
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

            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            if (allsafe) {
                return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.lookupFunctionName(icall), [argpp]), continuation);
            }
            else {
                return this.generateGeneralCallValueProcessing(this.currentRType, resulttype, new MorphirCallGeneral(this.typegen.lookupFunctionName(icall), [argpp]), op.trgt, continuation);
            }
        }
        else {
            const ttype = argflowtype.options[0] as MIREntityType;
            const ttdecl = this.assembly.entityDecls.get(ttype.typeID) as MIRObjectEntityTypeDecl;
            const consfunc = ttdecl.consfunc;
            const consfields = ttdecl.consfuncfields.map((ccf) => this.assembly.fieldDecls.get(ccf.cfkey) as MIRFieldDecl);

            const argpp = this.typegen.coerce(this.argToMorphir(op.arg), arglayouttype, argflowtype);
            let cargs: MorphirExp[] = [];
            for (let i = 0; i < consfields.length; ++i) {
                const upd = op.updates.find((vv) => vv[0] === consfields[i].fkey);
                if (upd === undefined) {
                    cargs.push(this.typegen.generateEntityFieldGet(ttdecl, consfields[i], argpp));
                }
                else {
                    cargs.push(this.argToMorphir(upd[1]));
                }
            }

            if (this.isSafeConstructorInvoke(argflowtype)) {
                const ccall = new MorphirCallSimple(this.typegen.getMorphirConstructorName(argflowtype).cons, cargs);
                return new MorphirLet(this.varToMorphirName(op.trgt).vname, ccall, continuation);
            }
            else {
                const ccall = new MorphirCallGeneral(this.typegen.lookupFunctionName(consfunc as MIRInvokeKey), cargs);
                return this.generateGeneralCallValueProcessing(this.currentRType, resulttype, ccall, op.trgt, continuation);
            }
        }
    }

    processLoadFromEpehmeralList(op: MIRLoadFromEpehmeralList, continuation: MorphirExp): MorphirExp {
        const argtype = this.typegen.getMIRType(op.argtype);

        const idxr = this.typegen.generateEphemeralListGet(argtype.options[0] as MIREphemeralListType, op.idx, this.argToMorphir(op.arg));
        return new MorphirLet(this.varToMorphirName(op.trgt).vname, idxr, continuation);
    }

    processMultiLoadFromEpehmeralList(op: MIRMultiLoadFromEpehmeralList, continuation: MorphirExp): MorphirExp {
        const eltype = this.typegen.getMIRType(op.argtype).options[0] as MIREphemeralListType;

        const assigns = op.trgts.map((asgn) => {
            const idxr = this.typegen.generateEphemeralListGet(eltype, asgn.pos, this.argToMorphir(op.arg));
            return { vname: this.varToMorphirName(asgn.into).vname, value: idxr };
        });

        return new MorphirLetMulti(assigns, continuation);
    }

    processSliceEpehmeralList(op: MIRSliceEpehmeralList, continuation: MorphirExp): MorphirExp {
        const eltype = this.typegen.getMIRType(op.argtype).options[0] as MIREphemeralListType;
        const sltype = this.typegen.getMIRType(op.sltype).options[0] as MIREphemeralListType;

        const pargs = sltype.entries.map((sle, i) => this.typegen.generateEphemeralListGet(eltype, i, this.argToMorphir(op.arg)));
        return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.getMorphirConstructorName(this.typegen.getMIRType(op.sltype)).cons, pargs), continuation);
    }

    processInvokeFixedFunction(op: MIRInvokeFixedFunction, continuation: MorphirExp): MorphirExp {
        const invk = (this.assembly.invokeDecls.get(op.mkey) || this.assembly.primitiveInvokeDecls.get(op.mkey)) as MIRInvokeDecl;
        const rtype = this.typegen.getMIRType(invk.resultType);

        if(invk instanceof MIRInvokePrimitiveDecl && invk.implkey === "default") {
            assert(op.sguard === undefined && op.optmask === undefined);

            const args = op.args.map((arg) => this.argToMorphir(arg));
            return this.processDefaultOperatorInvokePrimitiveType(op.sinfo, op.trgt, op.mkey, args, continuation);
        }
        else {
            let mask: MorphirMaskConstruct | undefined = undefined;
            if (op.optmask !== undefined) {
                mask = new MorphirMaskConstruct(op.optmask);
                this.pendingMask.push(mask);
            }

            const args = op.args.map((arg) => this.argToMorphir(arg));
            const call = mask !== undefined ? new MorphirCallGeneralWOptMask(this.typegen.lookupFunctionName(op.mkey), args, mask) : new MorphirCallGeneral(this.typegen.lookupFunctionName(op.mkey), args);
            const gcall = this.generateGuardStmtCond(op.sguard, call, invk.resultType);

            if (this.isSafeInvoke(op.mkey)) {
                return new MorphirLet(this.varToMorphirName(op.trgt).vname, gcall, continuation);
            }
            else {
                return this.generateGeneralCallValueProcessing(this.currentRType, rtype, gcall, op.trgt, continuation);
            }
        }
    }

    processInvokeVirtualFunction(op: MIRInvokeVirtualFunction, continuation: MorphirExp): MorphirExp {
        const rcvrlayouttype = this.typegen.getMIRType(op.rcvrlayouttype);
        const rcvrflowtype = this.typegen.getMIRType(op.rcvrflowtype);
        const resulttype = this.typegen.getMIRType(op.resultType);

        const allsafe = this.isSafeVirtualInvoke(op.vresolve, rcvrflowtype);
        const icall = this.generateVirtualInvokeFunctionName(rcvrflowtype, op.vresolve, op.shortname, op.optmask !== undefined, resulttype);
        if(this.requiredVirtualFunctionInvokes.findIndex((vv) => vv.inv === icall) === -1) {
            const geninfo = { inv: icall, allsafe: allsafe, argflowtype: rcvrflowtype, vfname: op.vresolve, optmask: op.optmask, resulttype: resulttype };
            this.requiredVirtualFunctionInvokes.push(geninfo);
        }

        let mask: MorphirMaskConstruct | undefined = undefined;
        if (op.optmask !== undefined) {
            mask = new MorphirMaskConstruct(op.optmask);
            this.pendingMask.push(mask);
        }
            
        const argpp = this.typegen.coerce(this.argToMorphir(op.args[0]), rcvrlayouttype, rcvrflowtype);
        const args = [argpp, ...op.args.slice(1).map((arg) => this.argToMorphir(arg))];
        const call = mask !== undefined ? new MorphirCallGeneralWOptMask(this.typegen.lookupFunctionName(icall), args, mask) : new MorphirCallGeneral(this.typegen.lookupFunctionName(icall), args);    

        if(allsafe) {
            return new MorphirLet(this.varToMorphirName(op.trgt).vname, call, continuation);
        }
        else {
            return this.generateGeneralCallValueProcessing(this.currentRType, resulttype, call, op.trgt, continuation);
        }
    }

    processInvokeVirtualOperator(op: MIRInvokeVirtualOperator, continuation: MorphirExp): MorphirExp {
        const resulttype = this.typegen.getMIRType(op.resultType);

        //TODO: also need all operator safe here 
        const iop = this.generateVirtualInvokeOperatorName(op.vresolve, op.shortname, op.args.map((arg) => arg.argflowtype), resulttype);
        if(this.requiredVirtualOperatorInvokes.findIndex((vv) => vv.inv === iop) === -1) {
            assert(false);
        }

        return NOT_IMPLEMENTED("processInvokeVirtualOperator");
    }

    processConstructorTuple(op: MIRConstructorTuple, continuation: MorphirExp): MorphirExp {
        const args = op.args.map((arg) => this.argToMorphir(arg));

        return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.getMorphirConstructorName(this.typegen.getMIRType(op.resultTupleType)).cons, args), continuation);
    }

    processConstructorTupleFromEphemeralList(op: MIRConstructorTupleFromEphemeralList, continuation: MorphirExp): MorphirExp {
        const elt = this.typegen.getMIRType(op.elistType).options[0] as MIREphemeralListType;
        const args = elt.entries.map((tt, i) => this.typegen.generateEphemeralListGet(elt, i, this.argToMorphir(op.arg)));

        return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.getMorphirConstructorName(this.typegen.getMIRType(op.resultTupleType)).cons, args), continuation);
    }

    processConstructorRecord(op: MIRConstructorRecord, continuation: MorphirExp): MorphirExp {
        const args = op.args.map((arg) => this.argToMorphir(arg[1]));

        return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.getMorphirConstructorName(this.typegen.getMIRType(op.resultRecordType)).cons, args), continuation);
    }

    processConstructorRecordFromEphemeralList(op: MIRConstructorRecordFromEphemeralList, continuation: MorphirExp): MorphirExp {
        const elt = this.typegen.getMIRType(op.elistType).options[0] as MIREphemeralListType;
        const eargs = elt.entries.map((tt, i) => this.typegen.generateEphemeralListGet(elt, i, this.argToMorphir(op.arg)));

        const rtype = this.typegen.getMIRType(op.resultRecordType).options[0] as MIRRecordType;
        const args = rtype.entries.map((rentry) => {
            const eidx = op.propertyPositions.indexOf(rentry.pname);
            return eargs[eidx];
        });

        return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.getMorphirConstructorName(this.typegen.getMIRType(op.resultRecordType)).cons, args), continuation);
    }

    processStructuredAppendTuple(op: MIRStructuredAppendTuple, continuation: MorphirExp): MorphirExp {
        let args: MorphirExp[] = [];
        for (let i = 0; i < op.args.length; ++i) {
            const tt = this.typegen.getMIRType(op.ttypes[i].flow).options[0] as MIRTupleType;
            const argi = this.argToMorphir(op.args[i]);

            for (let j = 0; j < tt.entries.length; ++j) {
                args.push(this.typegen.generateTupleIndexGet(tt, j, argi));
            }
        }

        return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.getMorphirConstructorName(this.typegen.getMIRType(op.resultTupleType)).cons, args), continuation);
    }

    processStructuredJoinRecord(op: MIRStructuredJoinRecord, continuation: MorphirExp): MorphirExp {
        const rtype = this.typegen.getMIRType(op.resultRecordType).options[0] as MIRRecordType;

        let args: MorphirExp[] = [];
        for (let i = 0; i < op.args.length; ++i) {
            const tt = this.typegen.getMIRType(op.ttypes[i].flow).options[0] as MIRRecordType;
            const argi = this.argToMorphir(op.args[i]);

            for (let j = 0; j < tt.entries.length; ++j) {
                const ppidx = rtype.entries.findIndex((ee) => ee.pname === tt.entries[j].pname);
                args[ppidx] = this.typegen.generateRecordPropertyGet(tt, tt.entries[j].pname, argi);
            }
        }

        return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.getMorphirConstructorName(this.typegen.getMIRType(op.resultRecordType)).cons, args), continuation);
    }

    processConstructorEphemeralList(op: MIRConstructorEphemeralList, continuation: MorphirExp): MorphirExp {
        const args = op.args.map((arg) => this.argToMorphir(arg));

        return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.getMorphirConstructorName(this.typegen.getMIRType(op.resultEphemeralListType)).cons, args), continuation);
    }

    processConstructorEntityDirect(op: MIRConstructorEntityDirect, continuation: MorphirExp): MorphirExp {
        const args = op.args.map((arg) => this.argToMorphir(arg));

        return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.getMorphirConstructorName(this.typegen.getMIRType(op.entityType)).cons, args), continuation);
    }

    processEphemeralListExtend(op: MIREphemeralListExtend, continuation: MorphirExp): MorphirExp {
        const ietype = this.typegen.getMIRType(op.argtype).options[0] as MIREphemeralListType;
        const iargs = ietype.entries.map((ee, i) => this.typegen.generateEphemeralListGet(ietype, i, this.argToMorphir(op.arg)));

        const eargs = op.ext.map((arg) => this.argToMorphir(arg));

        return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirCallSimple(this.typegen.getMorphirConstructorName(this.typegen.getMIRType(op.resultType)).cons, [...iargs, ...eargs]), continuation);
    }

    processConstructorPrimaryCollectionEmpty(op: MIRConstructorPrimaryCollectionEmpty, continuation: MorphirExp): MorphirExp {
        return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirConst("[]"), continuation);
    }

    processConstructorPrimaryCollectionOneElement(op: MIRConstructorPrimaryCollectionOneElement, continuation: MorphirExp): MorphirExp {
        const constype = this.assembly.entityDecls.get(op.tkey) as MIRPrimitiveCollectionEntityTypeDecl;
        const arg = this.argToMorphir(op.arg[1]);

        if(constype instanceof MIRPrimitiveListEntityTypeDecl) {
            return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirConst(`[${arg.emitMorphir(undefined)}]`), continuation);
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
            
            const mapentity = constype as MIRPrimitiveMapEntityTypeDecl;
            const entrytup = this.typegen.assembly.tupleDecls.get(`[${mapentity.getTypeK().typeID}, ${mapentity.getTypeV().typeID}]`) as MIRTupleType;

            const kexp = this.typegen.generateTupleIndexGet(entrytup, 0, arg);
            const vexp = this.typegen.generateTupleIndexGet(entrytup, 1, arg);
            return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirConst(`[MapEntry ${kexp.emitMorphir(undefined)} ${vexp.emitMorphir(undefined)}]`), continuation);
        }
    }

    processConstructorPrimaryCollectionSingletons(op: MIRConstructorPrimaryCollectionSingletons, continuation: MorphirExp): MorphirExp {
        const constype = this.assembly.entityDecls.get(op.tkey) as MIRPrimitiveCollectionEntityTypeDecl;
        const args = op.args.map((arg) => this.argToMorphir(arg[1]));

        if(constype instanceof MIRPrimitiveListEntityTypeDecl) {
            return new MorphirLet(this.varToMorphirName(op.trgt).vname, new MorphirConst(`[${args.map(e => e.emitMorphir(undefined)).join(", ")}]`), continuation);
        }
        else if (constype instanceof MIRPrimitiveStackEntityTypeDecl) {
            return NOT_IMPLEMENTED("MIRPrimitiveStackEntityTypeDecl@cons");
        }
        else {
            return NOT_IMPLEMENTED("MIRPrimitiveQueueEntityTypeDecl@cons");
        }
    }

    processBinKeyEq(op: MIRBinKeyEq, continuation: MorphirExp): MorphirExp {
        const mirlhslayout = this.typegen.getMIRType(op.lhslayouttype);
        const mirrhslayout = this.typegen.getMIRType(op.rhslayouttype);

        let eqcmp: MorphirExp = new MorphirConst("False");
        if(mirlhslayout.typeID === mirrhslayout.typeID && this.typegen.isUniqueType(mirlhslayout) && this.typegen.isUniqueType(mirrhslayout)) {
            eqcmp = MorphirCallSimple.makeEq(this.argToMorphir(op.lhs), this.argToMorphir(op.rhs));
        }
        else {
            const lhs = this.typegen.coerceToKey(this.argToMorphir(op.lhs), mirlhslayout);
            const rhs = this.typegen.coerceToKey(this.argToMorphir(op.rhs), mirrhslayout);

            eqcmp = MorphirCallSimple.makeEq(lhs, rhs);
        }

        const gop = this.generateGuardStmtCond(op.sguard, eqcmp, "Bool");
        return new MorphirLet(this.varToMorphirName(op.trgt).vname, gop, continuation);
    }

    generateBinKeyCmpFor(cmptype: MIRType, lhstype: MIRType, lhsexp: MorphirExp, rhstype: MIRType, rhsexp: MorphirExp): MorphirExp {
        if(lhstype.typeID === cmptype.typeID && rhstype.typeID === cmptype.typeID && this.typegen.isUniqueType(cmptype)) {
            const oftype = this.typegen.getMorphirTypeFor(cmptype);
            return new MorphirCallSimple(`${oftype.morphirtypename}_less`, [lhsexp, rhsexp]);
        }
        else {
            const lhs = this.typegen.coerceToKey(lhsexp, lhstype);
            const rhs = this.typegen.coerceToKey(rhsexp, rhstype);

            return new MorphirCallSimple("BKey_less", [lhs, rhs]);
        }
    }

    processBinKeyLess(op: MIRBinKeyLess, continuation: MorphirExp): MorphirExp {
        const mirlhslayout = this.typegen.getMIRType(op.lhslayouttype);
        const mirrhslayout = this.typegen.getMIRType(op.rhslayouttype);

        const ltcmp = this.generateBinKeyCmpFor(this.typegen.getMIRType(op.cmptype), mirlhslayout, this.argToMorphir(op.lhs), mirrhslayout, this.argToMorphir(op.rhs));
        return new MorphirLet(this.varToMorphirName(op.trgt).vname, ltcmp, continuation);
    }

    processPrefixNotOp(op: MIRPrefixNotOp, continuation: MorphirExp): MorphirExp {
        return new MorphirLet(this.varToMorphirName(op.trgt).vname, MorphirCallSimple.makeNot(this.argToMorphir(op.arg)), continuation);
    }

    processLogicAction(op: MIRLogicAction, continuation: MorphirExp): MorphirExp {
        assert(op.args.length !== 0, "Should not be empty logic argument list");

        if(op.args.length === 1) {
            return new MorphirLet(this.varToMorphirName(op.trgt).vname, this.argToMorphir(op.args[0]), continuation);
        }
        else {
            if (op.opkind === "/\\") {
                return new MorphirLet(this.varToMorphirName(op.trgt).vname, MorphirCallSimple.makeAndOf(...op.args.map((arg) => this.argToMorphir(arg))), continuation);
            }
            else {
                return new MorphirLet(this.varToMorphirName(op.trgt).vname, MorphirCallSimple.makeOrOf(...op.args.map((arg) => this.argToMorphir(arg))), continuation);
            }
        }
    }

    processIsTypeOf(op: MIRIsTypeOf, continuation: MorphirExp): MorphirExp {
        const layout = this.typegen.getMIRType(op.srclayouttype);
        const flow = this.typegen.getMIRType(op.srcflowtype);
        const oftype = this.typegen.getMIRType(op.chktype);

        let ttop: MorphirExp = new MorphirConst("False");
        if(this.assembly.subtypeOf(flow, oftype)) {
            //also handles the oftype is Any case
            ttop = new MorphirConst("True");
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
            .filter((test) => !(test instanceof MorphirConst) || test.cname !== "False");
    
            if(tests.length === 0) {
                ttop = new MorphirConst("False");
            }
            else if(tests.findIndex((test) => (test instanceof MorphirConst) && test.cname === "True") !== -1) {
                ttop = new MorphirConst("True");
            }
            else if(tests.length === 1) {
                ttop = tests[0];
            }
            else {
                ttop = MorphirCallSimple.makeOrOf(...tests);
            }
        }

        const gop = this.generateGuardStmtCond(op.sguard, ttop, "Bool");
        return new MorphirLet(this.varToMorphirName(op.trgt).vname, gop, continuation);
    }

    processRegisterAssign(op: MIRRegisterAssign, continuation: MorphirExp): MorphirExp {
        if(op.sguard === undefined) {
            return new MorphirLet(this.varToMorphirName(op.trgt).vname, this.argToMorphir(op.src), continuation);
        }
        else {
            const cassign = this.generateGuardStmtCond(op.sguard, this.argToMorphir(op.src), op.layouttype);
            return new MorphirLet(this.varToMorphirName(op.trgt).vname, cassign, continuation);
        }
    }

    processReturnAssign(op: MIRReturnAssign, continuation: MorphirExp): MorphirExp {
        return new MorphirLet(this.varToMorphirName(op.name).vname, this.argToMorphir(op.src), continuation);
    }

    processReturnAssignOfCons(op: MIRReturnAssignOfCons, continuation: MorphirExp): MorphirExp {
        const conscall = new MorphirCallSimple(this.typegen.getMorphirConstructorName(this.typegen.getMIRType(op.oftype)).cons, op.args.map((arg) => this.argToMorphir(arg)));
        return new MorphirLet(this.varToMorphirName(op.name).vname, conscall, continuation);
    }

    processOp(op: MIROp, continuation: MorphirExp): MorphirExp | undefined {
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
            case MIROpTag.MIRConstructorPrimaryCollectionOneElement: {
                return this.processConstructorPrimaryCollectionOneElement(op as MIRConstructorPrimaryCollectionOneElement, continuation);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                return this.processConstructorPrimaryCollectionSingletons(op as MIRConstructorPrimaryCollectionSingletons, continuation);
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

    processGenerateResultUnderflowCheck(sinfo: SourceInfo, arg0: MorphirExp, arg1: MorphirExp , oftype: MIRType, val: MorphirExp): MorphirExp {
        return new MorphirIf(new MorphirCallSimple("<", [arg1, arg0], true), this.typegen.generateErrorResultAssert(oftype, this.currentFile, sinfo), this.typegen.generateResultTypeConstructorSuccess(oftype, val));
    }

    processGenerateResultWithZeroArgCheck(sinfo: SourceInfo, zero: MorphirConst, not0arg: MorphirExp, oftype: MIRType, val: MorphirExp): MorphirExp {
        const chkzero = MorphirCallSimple.makeEq(zero, not0arg);
        return new MorphirIf(chkzero, this.typegen.generateErrorResultAssert(oftype, this.currentFile, sinfo), this.typegen.generateResultTypeConstructorSuccess(oftype, val));
    }

    processDefaultOperatorInvokePrimitiveType(sinfo: SourceInfo, trgt: MIRRegisterArgument, op: MIRInvokeKey, args: MorphirExp[], continuation: MorphirExp): MorphirExp {
        let mphe: MorphirExp = new MorphirConst("[INVALID]");
        let erropt = false;
        let rtype = this.typegen.getMIRType("Bool"); //default for all the compare ops

        switch (op) {
            //op unary +
            case "__i__Core::+=prefix=(Int)": {
                rtype = this.typegen.getMIRType("Int");
                mphe = args[0];
                break;
            }
            case "__i__Core::+=prefix=(Nat)": {
                rtype = this.typegen.getMIRType("Nat");
                mphe = args[0];
                break;
            }
            case "__i__Core::+=prefix=(BigInt)": {
                rtype = this.typegen.getMIRType("BigInt");
                mphe = args[0];
                break;
            }
            case "__i__Core::+=prefix=(BigNat)": {
                rtype = this.typegen.getMIRType("BigNat");
                mphe = args[0];
                break;
            }
            case "__i__Core::+=prefix=(Rational)": {
                rtype = this.typegen.getMIRType("Rational");
                mphe = args[0];
                break;
            }
            case "__i__Core::+=prefix=(Float)": {
                rtype = this.typegen.getMIRType("Float");
                mphe = args[0];
                break;
            }
            case "__i__Core::+=prefix=(Decimal)": {
                rtype = this.typegen.getMIRType("Decimal");
                mphe = args[0];
                break;
            }
            //op unary -
            case "__i__Core::-=prefix=(Int)": {
                rtype = this.typegen.getMIRType("Int");
                mphe = new MorphirCallSimple("*", [new MorphirConst("-1"), args[0]], true);
                break;
            }
            case "__i__Core::-=prefix=(BigInt)": {
                rtype = this.typegen.getMIRType("BigInt");
                mphe = new MorphirCallSimple("*", [new MorphirConst("-1"), args[0]], true);
                break;
            }
            case "__i__Core::-=prefix=(Rational)": {
                rtype = this.typegen.getMIRType("Rational");
                mphe = new MorphirCallSimple("*", [new MorphirConst("-1.0"), args[0]], true);
                break;
            }
            case "__i__Core::-=prefix=(Float)": {
                rtype = this.typegen.getMIRType("Float");
                mphe = new MorphirCallSimple("*", [new MorphirConst("-1.0"), args[0]], true);
                break;
            }
            case "__i__Core::-=prefix=(Decimal)": {
                rtype = this.typegen.getMIRType("Decimal");
                mphe = new MorphirCallSimple("*", [new MorphirConst("-1.0"), args[0]], true);
                break;
            }
            //op infix +
            case "__i__Core::+=infix=(Int, Int)": {
                rtype = this.typegen.getMIRType("Int");
                mphe = new MorphirCallSimple("+", args, true);
                break;
            }
            case "__i__Core::+=infix=(Nat, Nat)": {
                rtype = this.typegen.getMIRType("Nat");
                mphe = new MorphirCallSimple("+", args, true);
                break;
            }
            case "__i__Core::+=infix=(BigInt, BigInt)": {
                rtype = this.typegen.getMIRType("BigInt");
                mphe = new MorphirCallSimple("+", args, true);
                break;
            }
            case "__i__Core::+=infix=(BigNat, BigNat)": {
                rtype = this.typegen.getMIRType("BigNat");
                mphe = new MorphirCallSimple("+", args, true);
                break;
            }
            case "__i__Core::+=infix=(Rational, Rational)": {
                rtype = this.typegen.getMIRType("Rational");
                mphe = new MorphirCallSimple("+", args, true);
                break;
            }
            case "__i__Core::+=infix=(Float, Float)": {
                rtype = this.typegen.getMIRType("Float");
                mphe = new MorphirCallSimple("+", args, true);
                break;
            }
            case "__i__Core::+=infix=(Decimal, Decimal)": {
                rtype = this.typegen.getMIRType("Decmial");
                mphe = new MorphirCallSimple("+", args, true);
                break;
            }
            //op infix -
            case "__i__Core::-=infix=(Int, Int)": {
                rtype = this.typegen.getMIRType("Int");
                mphe = new MorphirCallSimple("-", args, true);
                break;
            }
            case "__i__Core::-=infix=(Nat, Nat)": {
                rtype = this.typegen.getMIRType("Nat");
                mphe = this.processGenerateResultUnderflowCheck(sinfo, args[0], args[1], rtype, new MorphirCallSimple("-", args, true));
                erropt = true;
                break;
            }
            case "__i__Core::-=infix=(BigInt, BigInt)": {
                rtype = this.typegen.getMIRType("BigInt");
                mphe = new MorphirCallSimple("-", args, true);
                break;
            }
            case "__i__Core::-=infix=(BigNat, BigNat)": {
                rtype = this.typegen.getMIRType("BigNat");
                mphe = this.processGenerateResultUnderflowCheck(sinfo, args[0], args[1], rtype, new MorphirCallSimple("-", args, true));
                erropt = true;
                break
            }
            case "__i__Core::-=infix=(Rational, Rational)": {
                rtype = this.typegen.getMIRType("Rational");
                mphe = new MorphirCallSimple("-", args, true);
                break;
            }
            case "__i__Core::-=infix=(Float, Float)": {
                rtype = this.typegen.getMIRType("Float");
                mphe = new MorphirCallSimple("-", args, true);
                break;
            }
            case "__i__Core::-=infix=(Decimal, Decimal)": {
                rtype = this.typegen.getMIRType("Decmial");
                mphe = new MorphirCallSimple("-", args, true);
                break;
            }
            //op infix *
            case "__i__Core::*=infix=(Int, Int)": {
                rtype = this.typegen.getMIRType("Int");
                mphe = new MorphirCallSimple("*", args, true);
                break;
            }
            case "__i__Core::*=infix=(Nat, Nat)": {
                rtype = this.typegen.getMIRType("Nat");
                mphe = new MorphirCallSimple("*", args, true);
                break;
            }
            case "__i__Core::*=infix=(BigInt, BigInt)": {
                rtype = this.typegen.getMIRType("BigInt");
                mphe = new MorphirCallSimple("*", args, true);
                break;
            }
            case "__i__Core::*=infix=(BigNat, BigNat)": {
                rtype = this.typegen.getMIRType("BigNat");
                mphe = new MorphirCallSimple("*", args, true);
                break;
            }
            case "__i__Core::*=infix=(Rational, Rational)": {
                rtype = this.typegen.getMIRType("Rational");
                mphe = new MorphirCallSimple("*", args, true);
                break;
            }
            case "__i__Core::*=infix=(Float, Float)": {
                rtype = this.typegen.getMIRType("Float");
                mphe = new MorphirCallSimple("*", args, true);
                break;
            }
            case "__i__Core::*=infix=(Decimal, Decimal)": {
                rtype = this.typegen.getMIRType("Decmial");
                mphe = new MorphirCallSimple("*", args, true);
                break;
            }
            //op infix /
            case "__i__Core::/=infix=(Int, Int)": {
                rtype = this.typegen.getMIRType("Int");
                mphe = this.processGenerateResultWithZeroArgCheck(sinfo, new MorphirConst("bInt_zero"), args[1], rtype, new MorphirCallSimple("//", args, true));
                erropt = true;
                break;
            }
            case "__i__Core::/=infix=(Nat, Nat)": {
                rtype = this.typegen.getMIRType("Nat");
                mphe = this.processGenerateResultWithZeroArgCheck(sinfo, new MorphirConst("bNat_zero"), args[1], rtype, new MorphirCallSimple("//", args, true));
                erropt = true;
                break;
            }
            case "__i__Core::/=infix=(BigInt, BigInt)": {
                rtype = this.typegen.getMIRType("BigInt");
                mphe = this.processGenerateResultWithZeroArgCheck(sinfo, new MorphirConst("bBigInt_zero"), args[1], rtype, new MorphirCallSimple("//", args, true));
                erropt = true;
                break;
            }
            case "__i__Core::/=infix=(BigNat, BigNat)": {
                rtype = this.typegen.getMIRType("BigNat");
                mphe = this.processGenerateResultWithZeroArgCheck(sinfo, new MorphirConst("bBigNat_zero"), args[1], rtype, new MorphirCallSimple("//", args, true));
                erropt = true;
                break
            }
            case "__i__Core::/=infix=(Rational, Rational)": {
                rtype = this.typegen.getMIRType("Rational");
                mphe = this.processGenerateResultWithZeroArgCheck(sinfo, new MorphirConst("bRational_zero"), args[1], rtype, new MorphirCallSimple("/", args, true));
                erropt = true;
                break;
            }
            case "__i__Core::/=infix=(Float, Float)": {
                rtype = this.typegen.getMIRType("Float");
                mphe = this.processGenerateResultWithZeroArgCheck(sinfo, new MorphirConst("bFloat_zero"), args[1], rtype, new MorphirCallSimple("/", args, true));
                erropt = true;
                break;
            }
            case "__i__Core::/=infix=(Decimal, Decimal)": {
                rtype = this.typegen.getMIRType("Decimal");
                mphe = this.processGenerateResultWithZeroArgCheck(sinfo, new MorphirConst("bDecimal_zero"), args[1], rtype, new MorphirCallSimple("/", args, true));
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
                mphe = MorphirCallSimple.makeEq(args[0], args[1]);
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
                mphe = MorphirCallSimple.makeNotEq(args[0], args[1]);
                break;
            }
            //op infix <
            case "__i__Core::<=infix=(Int, Int)": {
                mphe = new MorphirCallSimple("<", args, true);
                break;
            }
            case "__i__Core::<=infix=(Nat, Nat)": {
                mphe = new MorphirCallSimple("<", args, true);
                break;
            }
            case "__i__Core::<=infix=(BigInt, BigInt)": {
                mphe = new MorphirCallSimple("<", args, true);
                break;
            }
            case "__i__Core::<=infix=(BigNat, BigNat)": {
                mphe = new MorphirCallSimple("<", args, true);
                break;
            }
            case "__i__Core::<=infix=(Rational, Rational)": {
                mphe = new MorphirCallSimple("<", args, true);
                break;
            }
            case "__i__Core::<=infix=(Float, Float)": {
                mphe = new MorphirCallSimple("<", args, true);
                break;
            }
            case "__i__Core::<=infix=(Decimal, Decimal)": {
                mphe = new MorphirCallSimple("<", args, true);
                break;
            }
            //op infix >
            case "__i__Core::>=infix=(Int, Int)": {
                mphe = new MorphirCallSimple(">", args, true);
                break;
            }
            case "__i__Core::>=infix=(Nat, Nat)": {
                mphe = new MorphirCallSimple(">", args, true);
                break;
            }
            case "__i__Core::>=infix=(BigInt, BigInt)": {
                mphe = new MorphirCallSimple(">", args, true);
                break;
            }
            case "__i__Core::>=infix=(BigNat, BigNat)": {
                mphe = new MorphirCallSimple(">", args, true);
                break;
            }
            case "__i__Core::>=infix=(Rational, Rational)": {
                mphe = new MorphirCallSimple(">", args, true);
                break;
            }
            case "__i__Core::>=infix=(Float, Float)": {
                mphe = new MorphirCallSimple(">", args, true);
                break;
            }
            case "__i__Core::>=infix=(Decimal, Decimal)": {
                mphe = new MorphirCallSimple(">", args, true);
                break;
            }
            //op infix <=
            case "__i__Core::<==infix=(Int, Int)": {
                mphe = new MorphirCallSimple("<=", args, true);
                break;
            }
            case "__i__Core::<==infix=(Nat, Nat)": {
                mphe = new MorphirCallSimple("<=", args, true);
                break;
            }
            case "__i__Core::<==infix=(BigInt, BigInt)":  {
                mphe = new MorphirCallSimple("<=", args, true);
                break;
            }
            case "__i__Core::<==infix=(BigNat, BigNat)": {
                mphe = new MorphirCallSimple("<=", args, true);
                break;
            }
            case "__i__Core::<==infix=(Rational, Rational)": {
                mphe = new MorphirCallSimple("<=", args, true);
                break;
            }
            case "__i__Core::<==infix=(Float, Float)": {
                mphe = new MorphirCallSimple("<=", args, true);
                break;
            }
            case "__i__Core::<==infix=(Decimal, Decimal)": {
                mphe = new MorphirCallSimple("<=", args, true);
                break;
            }
            //op infix >=
            case "__i__Core::>==infix=(Int, Int)": {
                mphe = new MorphirCallSimple(">=", args, true);
                break;
            }
            case "__i__Core::>==infix=(Nat, Nat)": {
                mphe = new MorphirCallSimple(">=", args, true);
                break;
            }
            case "__i__Core::>==infix=(BigInt, BigInt)": {
                mphe = new MorphirCallSimple(">=", args, true);
                break;
            }
            case "__i__Core::>==infix=(BigNat, BigNat)": {
                mphe = new MorphirCallSimple(">=", args, true);
                break;
            }
            case "__i__Core::>==infix=(Rational, Rational)":{
                mphe = new MorphirCallSimple(">=", args, true);
                break;
            }
            case "__i__Core::>==infix=(Float, Float)":{
                mphe = new MorphirCallSimple(">=", args, true);
                break;
            }
            case "__i__Core::>==infix=(Decimal, Decimal)":{
                mphe = new MorphirCallSimple(">=", args, true);
                break;
            }
            default: {
                assert(false);
            }
        }

        if (!erropt) {
            return new MorphirLet(this.varToMorphirName(trgt).vname, mphe, continuation);
        }
        else {
            const cres = this.generateTempName();

            const okpath = new MorphirLet(this.varToMorphirName(trgt).vname, this.typegen.generateResultGetSuccess(rtype, new MorphirVar(cres)), continuation);
            const mphrtype = this.typegen.getMorphirTypeFor(rtype);
            const mphcurrenttype = this.typegen.getMorphirTypeFor(this.currentRType);
            const errpath = (mphrtype.morphirtypename === mphcurrenttype.morphirtypename) ? new MorphirVar(cres) : this.typegen.generateResultTypeConstructorError(this.currentRType, this.typegen.generateResultGetError(rtype, new MorphirVar(cres)));

            const icond = new MorphirIf(this.typegen.generateResultIsErrorTest(rtype, new MorphirVar(cres)), errpath, okpath);
            return new MorphirLet(cres, mphe, icond);
        }
    }

    getReadyBlock(blocks: Map<string, MIRBasicBlock>, done: Map<string, MorphirExp>): MIRBasicBlock | undefined {
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

    getNextBlockExp(blocks: Map<string, MIRBasicBlock>, MorphirExps: Map<string, MorphirExp>, from: string, trgt: string): MorphirExp {
        if(trgt !== "returnassign") {
            return MorphirExps.get(trgt) as MorphirExp;
        }
        else {
            const eblock = blocks.get("returnassign") as MIRBasicBlock;
            let rexp: MorphirExp = MorphirExps.get("exit") as MorphirExp;

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
                        vname: this.varToMorphirName(phi.trgt).vname,
                        value: this.varToMorphirName(phi.src.get(from) as MIRRegisterArgument)
                    }
                });

                return new MorphirLetMulti(assigns, rexp);
            }
        }
    }

    generateBlockExps(issafe: boolean, blocks: Map<string, MIRBasicBlock>): MorphirExp {
        let MorphirExps = new Map<string, MorphirExp>();

        const eblock = blocks.get("exit") as MIRBasicBlock;
        let rexp: MorphirExp = issafe ? new MorphirVar("$$return") : this.typegen.generateResultTypeConstructorSuccess(this.currentRType, new MorphirVar("$$return"));
        for (let i = eblock.ops.length - 1; i >= 0; --i) {
            const texp = this.processOp(eblock.ops[i], rexp);
            if(texp !== undefined) {
                rexp = texp;
            }
        }
        MorphirExps.set("exit", rexp);
        MorphirExps.set("returnassign", new MorphirConst("[DUMMY RETURN ASSIGN]"));

        let bb = this.getReadyBlock(blocks, MorphirExps);
        while(bb !== undefined) {
           const jop = bb.ops[bb.ops.length - 1];

            let rexp: MorphirExp = new MorphirConst("[UNITIALIZED FLOW]");
            if(jop.tag === MIROpTag.MIRAbort) {
                ; //No continuation so just leave as there is not continuation and let op processing handle it
            }
            else if (jop.tag === MIROpTag.MIRJump) {
                rexp = this.getNextBlockExp(blocks, MorphirExps, bb.label, (jop as MIRJump).trgtblock);
            }
            else if (jop.tag === MIROpTag.MIRJumpCond) {
                const mphcond = this.argToMorphir((jop as MIRJumpCond).arg);
                const texp = this.getNextBlockExp(blocks, MorphirExps, bb.label, (jop as MIRJumpCond).trueblock);
                const fexp = this.getNextBlockExp(blocks, MorphirExps, bb.label, (jop as MIRJumpCond).falseblock);
                
                rexp = new MorphirIf(mphcond, texp, fexp);
            }
            else {
                assert(jop.tag === MIROpTag.MIRJumpNone);

                const mphcond = this.generateNoneCheck((jop as MIRJumpNone).arg, this.typegen.getMIRType((jop as MIRJumpNone).arglayouttype));
                const nexp = this.getNextBlockExp(blocks, MorphirExps, bb.label, (jop as MIRJumpNone).noneblock);
                const sexp = this.getNextBlockExp(blocks, MorphirExps, bb.label, (jop as MIRJumpNone).someblock);
                
                rexp = new MorphirIf(mphcond, nexp, sexp);
            }

            for (let i = bb.ops.length - 1; i >= 0; --i) {
                const texp = this.processOp(bb.ops[i], rexp);
                if(texp !== undefined) {
                    rexp = texp;
                }
            }

            MorphirExps.set(bb.label, rexp);
            bb = this.getReadyBlock(blocks, MorphirExps);
        }

        return MorphirExps.get("entry") as MorphirExp;
    }

    generateMorphirInvoke(idecl: MIRInvokeDecl): MorphirFunction | undefined {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.getMIRType(idecl.resultType);

        const args = idecl.params.map((arg) => {
            return { vname: this.varStringToMorphir(arg.name).vname, vtype: this.typegen.getMorphirTypeFor(this.typegen.getMIRType(arg.type)) };
        });

        const issafe = this.isSafeInvoke(idecl.ikey);
        const restype = issafe ? this.typegen.getMorphirTypeFor(this.typegen.getMIRType(idecl.resultType)) : this.typegen.generateResultType(this.typegen.getMIRType(idecl.resultType));

        if (idecl instanceof MIRInvokeBodyDecl) {
            const body = this.generateBlockExps(issafe, (idecl as MIRInvokeBodyDecl).body.body);

            if (idecl.masksize === 0) {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, restype, body);
            }
            else {
                return MorphirFunction.createWithMask(this.typegen.lookupFunctionName(idecl.ikey), args, "__maskparam__", idecl.masksize, restype, body);
            }
        }
        else {
            assert(idecl instanceof MIRInvokePrimitiveDecl);

            return this.generateBuiltinFunction(idecl as MIRInvokePrimitiveDecl);
        }
    }

    generateBuiltinFunction(idecl: MIRInvokePrimitiveDecl): MorphirFunction | undefined {
        const args = idecl.params.map((arg) => {
            return { vname: this.varStringToMorphir(arg.name).vname, vtype: this.typegen.getMorphirTypeFor(this.typegen.getMIRType(arg.type)) };
        });

        const issafe = this.isSafeInvoke(idecl.ikey);

        const mirrestype = this.typegen.getMIRType(idecl.resultType);
        const mphrestype = this.typegen.getMorphirTypeFor(mirrestype);

        const chkrestype = issafe ? mphrestype : this.typegen.generateResultType(mirrestype);

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
                const lre = bsqre.compileToJS();

                let recons = new MorphirCallSimple("withDefault", [new MorphirConst("Regex.never"), new MorphirCallSimple("Regex.fromString", [new MorphirConst(lre)])]);
                let accept = new MorphirCallSimple("Regex.contains", [recons, new MorphirVar(args[0].vname)]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, accept);
            }
            case "number_nattoint": {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirVar(args[0].vname));
            }
            case "number_inttonat": {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirVar(args[0].vname));
            }
            case "number_nattobignat": {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirVar(args[0].vname));
            }
            case "number_inttobigint": {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirVar(args[0].vname));
            }
            case "number_bignattonat": {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirVar(args[0].vname));
            }
            case "number_biginttoint": {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirVar(args[0].vname)); 
            }
            case "number_bignattobigint": {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirVar(args[0].vname));
            }
            case "number_biginttobignat": {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirVar(args[0].vname));
            }
            case "number_bignattofloat":
            case "number_bignattodecimal":
            case "number_bignattorational":
            case "number_biginttofloat":
            case "number_biginttodecimal":
            case "number_biginttorational": {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirCallSimple("toFloat", [new MorphirVar(args[0].vname)]));
            }
            case "number_floattobigint":
            case "number_decimaltobigint": 
            case "number_rationaltobigint": {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirCallSimple("round", [new MorphirVar(args[0].vname)]));
            }
            case "number_floattodecimal":
            case "number_floattorational":
            case "number_decimaltofloat":
            case "number_decimaltorational":
            case "number_rationaltofloat":
            case "number_rationaltodecimal": {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirVar(args[0].vname));
            }
            case "float_floor":
            case "decimal_floor": {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirCallSimple("floor", [new MorphirVar(args[0].vname)]));
            }
            case "float_ceil":
            case "decimal_ceil": {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirCallSimple("ceiling", [new MorphirVar(args[0].vname)]));
            }
            case "float_truncate":
            case "decimal_truncate":  {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirCallSimple("truncate", [new MorphirVar(args[0].vname)]));
            }
            case "float_power":
            case "decimal_power": {
                const rr = new MorphirCallSimple("^", [new MorphirVar(args[0].vname), new MorphirVar(args[1].vname)]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, rr);
            }
            case "float_sqrt":
            case "decimal_sqrt": {
                const rr = new MorphirCallSimple("^", [new MorphirVar(args[0].vname), new MorphirConst("0.5")]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, rr);
            }
            case "string_empty": {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirCallSimple("List.isEmpty", [new MorphirVar(args[0].vname)]));
            }
            case "string_append": {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirCallSimple("append", [new MorphirVar(args[0].vname), new MorphirVar(args[1].vname)]));
            }
            case "bytebuffer_getformat": {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirConst(`${args[0].vname}.format`));
            }
            case "bytebuffer_getcompression": {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirConst(`${args[0].vname}.compress`));
            }
            case "datetime_create": {
                const dd = new MorphirCallSimple("bdatetime_cons", args.map((arg) => new MorphirVar(arg.vname)));
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "utcdatetime_create": {
                const dd = new MorphirCallSimple("butcdatetime_cons", args.map((arg) => new MorphirVar(arg.vname)));
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "calendardate_create": {
                const dd = new MorphirCallSimple("bcalendardate_cons", args.map((arg) => new MorphirVar(arg.vname)));
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "logicaltime_zero": {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirConst("0"));
            }
            case "logicaltime_increment": {
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, new MorphirCallSimple("+", [new MorphirVar(args[0].vname), new MorphirConst("1")], true));
            }
            case "isotimestamp_create": {
                const dd = new MorphirCallSimple("bisotimestamp_cons", args.map((arg) => new MorphirVar(arg.vname)));
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "latlongcoordinate_create": {
                const dd = new MorphirCallSimple("blatlongcoordinate_cons", args.map((arg) => new MorphirVar(arg.vname)));
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "regex_accepts": {
                let accept = new MorphirCallSimple("Regex.contains", [new MorphirVar(args[0].vname), new MorphirVar(args[1].vname)]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, accept);
            }
            case "s_list_empty": {
                const dd = new MorphirCallSimple("List.isEmpty", [new MorphirVar(args[0].vname)]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "s_list_size": {
                const dd = new MorphirCallSimple("List.length", [new MorphirVar(args[0].vname)]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "s_list_set": {
                const lhead = new MorphirCallSimple("List.take", [new MorphirVar(args[1].vname), new MorphirVar(args[0].vname)]);
                const ltail = new MorphirCallSimple("List.drop", [new MorphirCallSimple("+", [new MorphirVar(args[1].vname), new MorphirConst("1")], true), new MorphirVar(args[0].vname)]);
                const dd = new MorphirCallSimple("List.append", [lhead, new MorphirCallSimple("List.append", [new MorphirConst(`[${args[2].vname}]`), ltail])]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "s_list_push_back": {
                const dd = new MorphirCallSimple("List.append", [new MorphirVar(args[0].vname), new MorphirConst(`[${args[1].vname}]`)]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "s_list_push_front": {
                const dd = new MorphirCallSimple("List.append", [new MorphirConst(`[${args[1].vname}]`), new MorphirVar(args[0].vname)]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "s_list_insert": {
                const lhead = new MorphirCallSimple("List.take", [new MorphirVar(args[1].vname), new MorphirVar(args[0].vname)]);
                const ltail = new MorphirCallSimple("List.drop", [new MorphirVar(args[1].vname), new MorphirVar(args[0].vname)]);
                const dd = new MorphirCallSimple("List.append", [lhead, new MorphirCallSimple("List.append", [new MorphirConst(`[${args[2].vname}]`), ltail])]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "s_list_remove": {
                const lhead = new MorphirCallSimple("List.take", [new MorphirVar(args[1].vname), new MorphirVar(args[0].vname)]);
                const ltail = new MorphirCallSimple("List.drop", [new MorphirCallSimple("+", [new MorphirVar(args[1].vname), new MorphirConst("1")], true), new MorphirVar(args[0].vname)]);
                const dd = new MorphirCallSimple("List.append", [lhead, ltail]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "s_list_pop_back": {
                const lcount = new MorphirCallSimple("-", [new MorphirCallSimple("List.length", [new MorphirVar(args[0].vname)]), new MorphirConst("1")], true);
                const dd = new MorphirCallSimple("List.take", [new MorphirVar(args[0].vname), lcount]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "s_list_pop_front": {
                const dd = new MorphirCallSimple("List.drop", [new MorphirConst("1"), new MorphirVar(args[0].vname)]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "s_list_reduce": {
                const pc = idecl.pcodes.get("f") as MIRPCode;
                const pcfn = this.typegen.lookupFunctionName(pc.code);
                const captured = pc.cargs.map((carg) => carg.cname);

                const implicitlambdas = [pcfn];

                if (this.isSafeInvoke(pc.code)) {
                    const foldcall = new MorphirCallSimple("List.foldl", [
                        new MorphirConst(`(\\acc__ x__ -> (${pcfn} acc__ x__${captured.length !== 0 ? (" " + captured.join(" ")) : ""}))`),
                        new MorphirVar(args[1].vname),
                        new MorphirVar(args[0].vname)
                    ]);

                    return MorphirFunction.createWithImplicitLambdas(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, foldcall, implicitlambdas);
                }
                else {
                    const foldcall = new MorphirCallSimple("List.foldl", [
                        new MorphirConst(`(\\acc__ x__ -> if ${this.typegen.generateResultIsErrorTest(mirrestype, new MorphirVar("acc__")).emitMorphir(undefined)} then acc__ else (${pcfn} ${this.typegen.generateResultGetSuccess(mirrestype, new MorphirVar("acc__")).emitMorphir(undefined)} x${captured.length !== 0 ? (" " + captured.join(" ")) : ""}))`),
                        this.typegen.generateResultTypeConstructorSuccess(mirrestype, new MorphirVar(args[1].vname)),
                        new MorphirVar(args[0].vname)
                    ]);

                    return MorphirFunction.createWithImplicitLambdas(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, foldcall, implicitlambdas);
                }
            }
            case "s_list_reduce_idx": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
                return undefined;
            }
            case "s_list_transduce": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
                return undefined;
            }
            case "s_list_transduce_idx": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
                return undefined;
            }
            case "s_list_range": {
                const dd = new MorphirCallSimple("List.range", [new MorphirVar(args[0].vname), new MorphirVar(args[1].vname)]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "s_list_fill": {
                const dd = new MorphirCallSimple("List.repeat", [new MorphirVar(args[0].vname), new MorphirVar(args[1].vname)]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "s_list_reverse": {
                const dd = new MorphirCallSimple("List.reverse", [new MorphirVar(args[0].vname)]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "s_list_append": {
                const dd = new MorphirCallSimple("List.append", [new MorphirVar(args[0].vname), new MorphirVar(args[1].vname)]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "s_list_slice_start": {
                const dd = new MorphirCallSimple("List.drop", [new MorphirVar(args[1].vname), new MorphirVar(args[0].vname)]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "s_list_slice_end": {
                const dd = new MorphirCallSimple("List.take", [new MorphirVar(args[1].vname), new MorphirVar(args[0].vname)]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "s_list_slice": {
                const dd = new MorphirCallSimple("List.drop", [new MorphirVar(args[2].vname), new MorphirVar(args[0].vname)]);
                const rr = new MorphirCallSimple("List.take", [new MorphirVar(args[1].vname), dd]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, rr);
            }
            case "s_list_get": {
                const lhead = new MorphirCallSimple("List.drop", [new MorphirVar(args[1].vname), new MorphirVar(args[0].vname)]);
                const ldefault = `bsq${this.typegen.getMorphirTypeFor(this.typegen.getMIRType(idecl.resultType)).morphirtypename.toLowerCase()}_default`;
                const vv = new MorphirCallSimple("list_head_w_default", [lhead, new MorphirConst(ldefault)]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, vv);
            }
            case "s_list_back": {
                const lcount = new MorphirCallSimple("-", [new MorphirCallSimple("List.length", [new MorphirVar(args[0].vname)]), new MorphirConst("1")], true);
                const ldefault = `bsq${this.typegen.getMorphirTypeFor(this.typegen.getMIRType(idecl.resultType)).morphirtypename.toLowerCase()}_default`;
                const dd = new MorphirCallSimple("list_head_w_default", [new MorphirCallSimple("List.drop", [new MorphirVar(args[0].vname), lcount]), new MorphirConst(ldefault)]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "s_list_front": {
                const ldefault = `bsq${this.typegen.getMorphirTypeFor(this.typegen.getMIRType(idecl.resultType)).morphirtypename.toLowerCase()}_default`;
                const dd = new MorphirCallSimple("list_head_w_default", [new MorphirVar(args[0].vname), new MorphirConst(ldefault)]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "s_list_has_pred": {
                const pc = idecl.pcodes.get("p") as MIRPCode;
                const pcfn = this.typegen.lookupFunctionName(pc.code);
                const captured = pc.cargs.map((carg) => carg.cname);

                const implicitlambdas = [pcfn];

                if (this.isSafeInvoke(pc.code)) {
                    const bmap = new MorphirCallSimple("List.any", [
                        new MorphirConst(`(\\x__ -> (${pcfn} x__${captured.length !== 0 ? (" " + captured.join(" ")) : ""}))`),
                        new MorphirVar(args[0].vname)
                    ]);

                    return MorphirFunction.createWithImplicitLambdas(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, bmap, implicitlambdas);
                }
                else {
                    const bmap = new MorphirCallSimple("List.map", [
                        new MorphirConst(`(\\x__ -> (${pcfn} x__${captured.length !== 0 ? (" " + captured.join(" ")) : ""}))`),
                        new MorphirVar(args[0].vname)
                    ]);

                    const vres = new MorphirCallSimple("result_reduce", [
                        new MorphirConst(`(\\acc__ vv__ -> (acc__ && v__))`),
                        new MorphirConst("false"),
                        new MorphirVar("vmap")
                    ]);

                    const bbody = new MorphirLet("vmap", bmap, vres);
                    return MorphirFunction.createWithImplicitLambdas(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, bbody, implicitlambdas);
                }
            }
            case "s_list_has_pred_idx": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
                return undefined;
            }
            case "s_list_find_pred": {
                const pc = idecl.pcodes.get("p") as MIRPCode;
                const pcfn = this.typegen.lookupFunctionName(pc.code);
                const captured = pc.cargs.map((carg) => carg.cname);

                const implicitlambdas = [pcfn];

                const bmap = new MorphirCallSimple("List.map", [
                    new MorphirConst(`(\\x__ -> (${pcfn} x__${captured.length !== 0 ? (" " + captured.join(" ")) : ""}))`),
                    new MorphirVar(args[0].vname)
                ]);

                if (this.isSafeInvoke(pc.code)) {
                    const vres = new MorphirCallSimple("List.foldl", [
                        new MorphirConst(`(\\acc__ vv__ -> (if acc__.vv == -1 then && {index = -1, vv = vv__}) else {index = acc__.index + 1, vv = -1})`),
                        new MorphirConst("{index = 0, vv = -1}"),
                        new MorphirVar("vmap")
                    ]);

                    const bbody = new MorphirLet("vmap", bmap, vres);
                    return MorphirFunction.createWithImplicitLambdas(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, bbody, implicitlambdas);
                }
                else {
                    const vres = new MorphirCallSimple("result_reduce", [
                        new MorphirConst(`(\\acc__ vv__ -> (if acc__.vv == -1 then && {index = -1, vv = vv__}) else {index = acc__.index + 1, vv = -1})`),
                        new MorphirConst("{index = 0, vv = -1}"),
                        new MorphirVar("vmap")
                    ]);

                    const bbody = new MorphirLet("vmap", bmap, vres);
                    return MorphirFunction.createWithImplicitLambdas(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, bbody, implicitlambdas);
                }
            }
            case "s_list_find_pred_idx": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
                return undefined;
            }
            case "s_list_find_pred_last": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
                return undefined;
            }
            case "s_list_find_pred_last_idx": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
                return undefined;
            }
            case "s_list_single_index_of": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
                return undefined;
            }
            case "s_list_has": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
                return undefined;
            }
            case "s_list_indexof": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
                return undefined;
            }
            case "s_list_last_indexof": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
                return undefined;
            }
            case "s_list_filter_pred": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
                return undefined;
            }
            case "s_list_filter_pred_idx": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
                return undefined;
            }
            case "s_list_map": {
                const pc = idecl.pcodes.get("f") as MIRPCode;
                const pcfn = this.typegen.lookupFunctionName(pc.code);
                const captured = pc.cargs.map((carg) => carg.cname);

                const implicitlambdas = [pcfn];

                const bmap = new MorphirCallSimple("List.map", [
                    new MorphirConst(`(\\x__ -> (${pcfn} x__${captured.length !== 0 ? (" " + captured.join(" ")) : ""}))`),
                    new MorphirVar(args[0].vname)
                ]);

                if (this.isSafeInvoke(pc.code)) {
                    return MorphirFunction.createWithImplicitLambdas(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, bmap, implicitlambdas);
                }
                else {
                    const vres = new MorphirCallSimple("result_map_map", [
                        new MorphirVar("vmap")
                    ]);

                    const bbody = new MorphirLet("vmap", bmap, vres);
                    return MorphirFunction.createWithImplicitLambdas(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, bbody, implicitlambdas);
                }
            }
            case "s_list_map_idx": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
                return undefined;
            }
            case "s_list_map_sync": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
                return undefined;
            }
            case "s_list_filter_map_fn": {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
                return undefined;
            }
            case "s_map_empty":{
                const dd = new MorphirCallSimple("List.isEmpty", [new MorphirVar(args[0].vname)]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            case "s_map_count": {
                const dd = new MorphirCallSimple("List.length", [new MorphirVar(args[0].vname)]);
                return MorphirFunction.create(this.typegen.lookupFunctionName(idecl.ikey), args, chkrestype, dd);
            }
            /*
    s_map_entries,
    s_map_min_key,
    s_map_max_key,
    s_map_has,
    s_map_get,
    s_map_find,
    s_map_union_fast,
    s_map_submap,
    s_map_remap,
    s_map_add,
    s_map_set,
    s_map_remove
            */
            default: {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
                return undefined;
            }
        }
    }
}

export {
     MorphirBodyEmitter
};
