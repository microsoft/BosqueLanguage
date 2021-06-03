//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRConceptType, MIREntityType, MIREntityTypeDecl, MIREphemeralListType, MIRFieldDecl, MIRInvokeBodyDecl, MIRInvokeDecl, MIRInvokePrimitiveDecl, MIRPCode, MIRRecordType, MIRRecordTypeEntry, MIRTupleType, MIRTupleTypeEntry, MIRType } from "../../../compiler/mir_assembly";
import { ICPPTypeEmitter } from "./icpptype_emitter";
import { MIRAbort, MIRAllTrue, MIRArgGuard, MIRArgument, MIRAssertCheck, MIRBasicBlock, MIRBinKeyEq, MIRBinKeyLess, MIRConstantArgument, MIRConstantBigInt, MIRConstantBigNat, MIRConstantDataString, MIRConstantDecimal, MIRConstantFalse, MIRConstantFloat, MIRConstantInt, MIRConstantNat, MIRConstantNone, MIRConstantRational, MIRConstantRegex, MIRConstantString, MIRConstantStringOf, MIRConstantTrue, MIRConstantTypedNumber, MIRConstructorEphemeralList, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionMixed, MIRConstructorPrimaryCollectionSingletons, MIRConstructorRecord, MIRConstructorRecordFromEphemeralList, MIRConstructorTuple, MIRConstructorTupleFromEphemeralList, MIRConvertValue, MIRDeclareGuardFlagLocation, MIREntityProjectToEphemeral, MIREntityUpdate, MIREphemeralListExtend, MIRFieldKey, MIRGlobalKey, MIRGlobalVariable, MIRGuard, MIRInvokeFixedFunction, MIRInvokeKey, MIRInvokeVirtualFunction, MIRInvokeVirtualOperator, MIRIsTypeOf, MIRJump, MIRJumpCond, MIRJumpNone, MIRLoadConst, MIRLoadField, MIRLoadFromEpehmeralList, MIRLoadRecordProperty, MIRLoadRecordPropertySetGuard, MIRLoadTupleIndex, MIRLoadTupleIndexSetGuard, MIRLoadUnintVariableValue, MIRMaskGuard, MIRMultiLoadFromEpehmeralList, MIROp, MIROpTag, MIRPhi, MIRPrefixNotOp, MIRRecordHasProperty, MIRRecordProjectToEphemeral, MIRRecordUpdate, MIRRegisterArgument, MIRRegisterAssign, MIRResolvedTypeKey, MIRReturnAssign, MIRReturnAssignOfCons, MIRSetConstantGuardFlag, MIRSliceEpehmeralList, MIRSomeTrue, MIRStatmentGuard, MIRStructuredAppendTuple, MIRStructuredJoinRecord, MIRTupleHasIndex, MIRTupleProjectToEphemeral, MIRTupleUpdate, MIRVirtualMethodKey } from "../../../compiler/mir_ops";
import { Argument, ArgumentTag, EMPTY_CONST_POSITION, ICPPGuard, ICPPOp, ICPPOpEmitter, ICPPStatementGuard, OpCodeTag, TargetVar } from "./icpp_exp";
import { SourceInfo } from "../../../ast/parser";
import { ICPPFunctionParameter, ICPPInvokeBodyDecl, ICPPInvokeDecl, ICPPType, ICPPTypeEntity, ICPPTypeEphemeralList, ICPPTypeInlineUnion, ICPPTypeKind, ICPPTypeRecord, ICPPTypeRefUnion, ICPPTypeTuple, RefMask, TranspilerOptions, UNIVERSAL_SIZE } from "./icpp_assembly";

import * as assert from "assert";
import { BSQRegex } from "../../../ast/bsqregex";

function NOT_IMPLEMENTED(msg: string): ICPPOp {
    throw new Error(`Not Implemented: ${msg}`);
}

class ICPPBodyEmitter {
    readonly assembly: MIRAssembly;
    readonly typegen: ICPPTypeEmitter;
    
    readonly vopts: TranspilerOptions;

    currentFile: string = "[No File]";
    currentRType: MIRType;

    private argsMap: Map<string, number> = new Map<string, number>();
    private stackMap: Map<string, number> = new Map<string, number>();
    private stacksize: number = 0;
    private stacklayout: {offset: number, occupied: boolean, storage: ICPPType}[] = [];

    private literalMap: Map<string, number> = new Map<string, number>();
    private constMap: Map<MIRGlobalKey, number> = new Map<MIRGlobalKey, number>();
    private constsize: number = UNIVERSAL_SIZE;
    private constlayout: {offset: number, storage: ICPPType, value: string}[] = [];
    
    private maskMap: Map<string, number> = new Map<string, number>();
    private masksize: number = 0;
    private masklayout: {offset: number, occupied: boolean, name: string, size: number}[] = [];
    

    private ops: Map<string, ICPPOp[]> = new Map<string, ICPPOp[]>();
    private cblock: ICPPOp[];

    requiredProjectVirtualTupleIndex: { inv: string, argflowtype: MIRType, indecies: number[], resulttype: MIRType }[] = [];
    requiredProjectVirtualRecordProperty: { inv: string, argflowtype: MIRType, properties: string[], resulttype: MIRType }[] = [];
    requiredProjectVirtualEntityField: { inv: string, argflowtype: MIRType, fields: MIRFieldDecl[], resulttype: MIRType }[] = [];

    requiredUpdateVirtualTuple: { inv: string, argflowtype: MIRType, updates: [number, MIRResolvedTypeKey][], resulttype: MIRType }[] = [];
    requiredUpdateVirtualRecord: { inv: string, argflowtype: MIRType, updates: [string, MIRResolvedTypeKey][], resulttype: MIRType }[] = [];

    requiredUpdateEntityWithInvariant: { inv: string, oftype: MIRType, updates: [MIRFieldKey, MIRResolvedTypeKey][], resulttype: MIRType }[] = [];
    requiredUpdateVirtualEntity: { inv: string, argflowtype: MIRType, updates: [MIRFieldKey, MIRResolvedTypeKey][], resulttype: MIRType }[] = [];

    requiredTupleAppend: { inv: string, args: {layout: MIRType, flow: MIRType}[], resulttype: MIRType }[] = [];
    requiredRecordMerge: { inv: string, args: {layout: MIRType, flow: MIRType}[], resulttype: MIRType }[] = [];

    private getStackInfoForArgVar(vname: string): Argument {
        if(this.argsMap.has(vname)) {
            return ICPPOpEmitter.genParameterArgument(this.argsMap.get(vname) as number);
        }
        else {
            return ICPPOpEmitter.genLocalArgument(this.stackMap.get(vname) as number);
        }
    }

    private getStackInfoForTargetVar(vname: string, oftype: ICPPType): TargetVar {
        let openidx = this.stacklayout.findIndex((opt) => !opt.occupied && opt.storage.tkey === oftype.tkey);
        if(openidx === -1) {
            this.stacklayout.push({offset: this.stacksize, occupied: true, storage: oftype});
            this.stacksize = this.stacksize + oftype.allocinfo.inlinedatasize;

            openidx = this.stacksize - 1;
        }

        const spos = this.stacklayout[openidx];
        this.stackMap.set(vname, spos.offset);
        spos.occupied = true;

        return {offset: spos.offset};
    }

    private releaseStackSlotForVar(vname: string) {
        const offset = this.stackMap.get(vname) as number;

        const spos = this.stacklayout.find((opt) => opt.offset === offset) as {offset: number, occupied: boolean, storage: ICPPType};
        spos.occupied = false;
    }

    private generateScratchVarInfo(oftype: ICPPType): [TargetVar, Argument] {
        let openidx = this.stacklayout.findIndex((opt) => !opt.occupied && opt.storage.tkey === oftype.tkey);
        if(openidx === -1) {
            this.stacklayout.push({offset: this.stacksize, occupied: true, storage: oftype});
            this.stacksize = this.stacksize + oftype.allocinfo.inlinedatasize;

            openidx = this.stacksize - 1;
        }

        const spos = this.stacklayout[openidx];
        spos.occupied = true;

        return [{offset: spos.offset}, ICPPOpEmitter.genLocalArgument(spos.offset)];
    }

    private releaseScratchVar(vv: TargetVar) {
        const spos = this.stacklayout.find((opt) => opt.offset === vv.offset) as {offset: number, occupied: boolean, storage: ICPPType};
        spos.occupied = false;
    }

    private genMaskForStack(): RefMask {
        let mask: RefMask = "";
        for(let i = 0; i < this.stacklayout.length; ++i) {
            mask = mask + this.stacklayout[i].storage.allocinfo.inlinedmask;
        }
        return mask;
    }

    private generateProjectVirtualTupleInvName(argflowtype: MIRType, indecies: number[], resulttype: MIRType): string {
        const idxs = indecies.map((idx) => `${idx}`).join(",");
        return `$TupleProject_${argflowtype.trkey}.[${idxs}]->${resulttype.trkey}`;
    }

    private generateProjectVirtualRecordInvName(argflowtype: MIRType, properties: string[], resulttype: MIRType): string {
        const pnames = properties.join(",");
        return `$RecordProject_${argflowtype.trkey}.{${pnames}}->${resulttype.trkey}`;
    }

    private generateProjectVirtualEntityInvName(argflowtype: MIRType, fields: MIRFieldKey[], resulttype: MIRType): string {
        const fkeys = fields.join(",");
        return `$EntityProject_${argflowtype.trkey}.{${fkeys}}->${resulttype.trkey}`;
    }

    private generateUpdateVirtualTupleInvName(argflowtype: MIRType, indecies: [number, MIRResolvedTypeKey][], resulttype: MIRType): string {
        const idxs = indecies.map((idx) => `(${idx[0]} ${idx[1]})`).join(",");
        return `$TupleUpdate_${argflowtype.trkey}.[${idxs}]->${resulttype.trkey}`;
    }

    private generateUpdateVirtualRecordInvName(argflowtype: MIRType, properties: [string, MIRResolvedTypeKey][], resulttype: MIRType): string {
        const pnames = properties.map((pname) => `(${pname[0]} ${pname[1]})`).join(",");
        return `$RecordUpdate_${argflowtype.trkey}.{${pnames}}->${resulttype.trkey}`;
    }

    private generateUpdateEntityWithInvariantName(oftype: MIRType, fields: [MIRFieldKey, MIRResolvedTypeKey][], resulttype: MIRType): string {
        const fnames = fields.map((fname) => `(${fname[0]} ${fname[1]})`).join(",");
        return `$EntityUpdateDirectWithInvariantCheck_${oftype.trkey}.{${fnames}}->${resulttype.trkey}`;
    }

    private generateUpdateVirtualEntityInvName(argflowtype: MIRType, fields: [MIRFieldKey, MIRResolvedTypeKey][], resulttype: MIRType): string {
        const fnames = fields.map((fname) => `(${fname[0]} ${fname[1]})`).join(",");
        return `$EntityUpdate_${argflowtype.trkey}.{${fnames}}->${resulttype.trkey}`;
    }

    private generateTupleAppendInvName(args: { flow: MIRType, layout: MIRType }[], resulttype: MIRType): string {
        const anames = args.map((fl) => `(${fl.flow.trkey} ${fl.layout.trkey})`).join(",");
        return `$TupleAppend_{${anames}}->${resulttype.trkey}`;
    }

    private generateRecordMergeInvName(args: { flow: MIRType, layout: MIRType }[], resulttype: MIRType): string {
        const mnames = args.map((fl) => `(${fl.flow.trkey} ${fl.layout.trkey})`).join(",");
        return `$RecordMerge_{${mnames}}->${resulttype.trkey}`;
    }

    generateProjectTupleIndexVirtual(geninfo: { inv: string, argflowtype: MIRType, indecies: number[], resulttype: MIRType }, sinfo: SourceInfo, tupletype: MIRType): ICPPInvokeDecl {
        const rtype = this.typegen.getICPPTypeData(geninfo.resulttype) as ICPPTypeEphemeralList;
        const name = geninfo.inv + `@${tupletype.trkey}`;

        const icpptuple = this.typegen.getICPPTypeData(tupletype) as ICPPTypeTuple;
        const params = [new ICPPFunctionParameter("arg", icpptuple)];
        const parg = ICPPOpEmitter.genParameterArgument(0);

        let ops: ICPPOp[] = [];
        let pargs: Argument[] = [];
        geninfo.indecies.forEach((idx, i) => {
            const tupleidxtype = this.typegen.getMIRType(icpptuple.ttypes[idx]);
            const elidxtype = (geninfo.resulttype.options[0] as MIREphemeralListType).entries[i];

            const [ltrgt, larg] = this.generateScratchVarInfo(this.typegen.getICPPTypeData(tupleidxtype));
            ops.push(ICPPOpEmitter.genLoadTupleIndexDirectOp(sinfo, ltrgt, tupleidxtype.trkey, parg, icpptuple.tkey, icpptuple.idxoffsets[idx], idx));

            if(tupleidxtype.trkey === elidxtype.trkey) {
                pargs.push(larg);
            }
            else {
                const [ctrgt, carg] = this.generateScratchVarInfo(this.typegen.getICPPTypeData(elidxtype));
                ops.push(this.typegen.coerce(sinfo, larg, tupleidxtype, ctrgt, elidxtype, ICPPOpEmitter.genNoStatmentGuard()));
                pargs.push(carg);
            }
        });

        const [constrgt, consarg] = this.generateScratchVarInfo(this.typegen.getICPPTypeData(geninfo.resulttype));
        ops.push(ICPPOpEmitter.genConstructorEphemeralListOp(sinfo, constrgt, geninfo.resulttype.trkey, pargs));
        ops.push(ICPPOpEmitter.genReturnAssignOp(sinfo, consarg, geninfo.resulttype.trkey));
        
        return new ICPPInvokeBodyDecl(name, name, "[GENERATED]", sinfo, false, params, rtype, this.stacksize, this.genMaskForStack(), 0, ops, 0);
    }

    generateProjectRecordPropertyVirtual(geninfo: { inv: string, argflowtype: MIRType, properties: string[], resulttype: MIRType }, sinfo: SourceInfo, recordtype: MIRType): ICPPInvokeDecl {
        const rtype = this.typegen.getICPPTypeData(geninfo.resulttype) as ICPPTypeEphemeralList;
        const name = geninfo.inv + `@${recordtype.trkey}`;

        const icpprecord = this.typegen.getICPPTypeData(recordtype) as ICPPTypeRecord;
        const params = [new ICPPFunctionParameter("arg", icpprecord)];
        const parg = ICPPOpEmitter.genParameterArgument(0);

        let ops: ICPPOp[] = [];
        let pargs: Argument[] = [];
        geninfo.properties.forEach((pname, i) => {
            const pidx = icpprecord.propertynames.findIndex((v) => v === pname);

            const recordpnametype = this.typegen.getMIRType(icpprecord.propertytypes[pidx]);
            const elidxtype = (geninfo.resulttype.options[0] as MIREphemeralListType).entries[i];

            const [ltrgt, larg] = this.generateScratchVarInfo(this.typegen.getICPPTypeData(recordpnametype));
            ops.push(ICPPOpEmitter.genLoadRecordPropertyDirectOp(sinfo, ltrgt, recordpnametype.trkey, parg, icpprecord.tkey, icpprecord.propertyoffsets[pidx], pname));

            if(recordpnametype.trkey === elidxtype.trkey) {
                pargs.push(larg);
            }
            else {
                const [ctrgt, carg] = this.generateScratchVarInfo(this.typegen.getICPPTypeData(elidxtype));
                ops.push(this.typegen.coerce(sinfo, larg, recordpnametype, ctrgt, elidxtype, ICPPOpEmitter.genNoStatmentGuard()));
                pargs.push(carg);
            }
        });

        const [constrgt, consarg] = this.generateScratchVarInfo(this.typegen.getICPPTypeData(geninfo.resulttype));
        ops.push(ICPPOpEmitter.genConstructorEphemeralListOp(sinfo, constrgt, geninfo.resulttype.trkey, pargs));
        ops.push(ICPPOpEmitter.genReturnAssignOp(sinfo, consarg, geninfo.resulttype.trkey));
        
        return new ICPPInvokeBodyDecl(name, name, "[GENERATED]", sinfo, false, params, rtype, this.stacksize, this.genMaskForStack(), 0, ops, 0);
    }

    generateProjectEntityFieldVirtual(geninfo: { inv: string, argflowtype: MIRType, fields: MIRFieldDecl[], resulttype: MIRType }, sinfo: SourceInfo, entitytype: MIRType): ICPPInvokeDecl {
        const rtype = this.typegen.getICPPTypeData(geninfo.resulttype) as ICPPTypeEphemeralList;
        const name = geninfo.inv + `@${entitytype.trkey}`;

        const icppentity = this.typegen.getICPPTypeData(entitytype) as ICPPTypeEntity;
        const params = [new ICPPFunctionParameter("arg", icppentity)];
        const parg = ICPPOpEmitter.genParameterArgument(0);

        let ops: ICPPOp[] = [];
        let pargs: Argument[] = [];
        geninfo.fields.forEach((f, i) => {
            const fidx = icppentity.fieldnames.findIndex((v) => v === f.fkey);

            const entityfieldtype = this.typegen.getMIRType(f.declaredType);
            const elidxtype = (geninfo.resulttype.options[0] as MIREphemeralListType).entries[i];

            const [ltrgt, larg] = this.generateScratchVarInfo(this.typegen.getICPPTypeData(entityfieldtype));
            ops.push(ICPPOpEmitter.genLoadEntityFieldDirectOp(sinfo, ltrgt, entityfieldtype.trkey, parg, icppentity.tkey, icppentity.fieldoffsets[fidx], f.fkey));

            if(entityfieldtype.trkey === elidxtype.trkey) {
                pargs.push(larg);
            }
            else {
                const [ctrgt, carg] = this.generateScratchVarInfo(this.typegen.getICPPTypeData(elidxtype));
                ops.push(this.typegen.coerce(sinfo, larg, entityfieldtype, ctrgt, elidxtype, ICPPOpEmitter.genNoStatmentGuard()));
                pargs.push(carg);
            }
        });

        const [constrgt, consarg] = this.generateScratchVarInfo(this.typegen.getICPPTypeData(geninfo.resulttype));
        ops.push(ICPPOpEmitter.genConstructorEphemeralListOp(sinfo, constrgt, geninfo.resulttype.trkey, pargs));
        ops.push(ICPPOpEmitter.genReturnAssignOp(sinfo, consarg, geninfo.resulttype.trkey));
        
        return new ICPPInvokeBodyDecl(name, name, "[GENERATED]", sinfo, false, params, rtype, this.stacksize, this.genMaskForStack(), 0, ops, 0);
    }

    generateUpdateEntityFieldDirectWithInvariantCheck(geninfo: { inv: string, oftype: MIRType, updates: [MIRFieldKey, MIRResolvedTypeKey][], resulttype: MIRType }): SMTFunction {
        xxxx;
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
            
            const ccall = new SMTCallGeneral(this.typegen.mangle(consfunc as MIRInvokeKey), cargs);

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
        return SMTFunction.create(geninfo.inv, fargs, rtype, new SMTCond(ops, orelse));
    }

    generateTupleAppend(geninfo: { inv: string, args: {layout: MIRType, flow: MIRType}[], resulttype: MIRType }, sinfo: SourceInfo): ICPPInvokeDecl {
        xxxx;
    }

    generateRecordMerge(geninfo: { inv: string, args: {layout: MIRType, flow: MIRType}[], resulttype: MIRType }, sinfo: SourceInfo): ICPPInvokeDecl {
        xxxx;
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

    constructor(assembly: MIRAssembly, typegen: ICPPTypeEmitter, vopts: TranspilerOptions) {
        this.assembly = assembly;
        this.typegen = typegen;
       
        this.vopts = vopts;

        this.currentRType = typegen.getMIRType("NSCore::None");

        this.registerSpecialLiteralValue("none", "NSCore::None");
        this.registerSpecialLiteralValue("true", "NSCore::Bool");
        this.registerSpecialLiteralValue("false", "NSCore::Bool");
    }

    private registerSpecialLiteralValue(vlit: string, vtype: MIRResolvedTypeKey) {
        if (!this.literalMap.has(vlit)) {
            const ttype = this.typegen.getICPPTypeData(this.typegen.getMIRType(vtype));
            this.literalMap.set(vlit, this.constsize);
            this.constlayout.push({ offset: this.constsize, storage: ttype, value: vlit });
            this.constsize += ttype.allocinfo.inlinedatasize;
        }
    }

    private getSpecialLiteralValue(vlit: string): Argument {
        return ICPPOpEmitter.genConstArgument(this.literalMap.get(vlit) as number);
    }

    constantToICPP(cval: MIRConstantArgument): Argument {
        if (cval instanceof MIRConstantNone) {
            return this.getSpecialLiteralValue("none");
        }
        else if (cval instanceof MIRConstantTrue) {
            return this.getSpecialLiteralValue("true");
        }
        else if (cval instanceof MIRConstantFalse) {
            return this.getSpecialLiteralValue("false");
        }
        else if (cval instanceof MIRConstantInt) {
            this.registerSpecialLiteralValue(cval.value, "NSCore::Int");
            return this.getSpecialLiteralValue(cval.value);
        }
        else if (cval instanceof MIRConstantNat) {
            this.registerSpecialLiteralValue(cval.value, "NSCore::Nat");
            return this.getSpecialLiteralValue(cval.value);
        }
        else if (cval instanceof MIRConstantBigInt) {
            this.registerSpecialLiteralValue(cval.value, "NSCore::BigInt");
            return this.getSpecialLiteralValue(cval.value);
        }
        else if (cval instanceof MIRConstantBigNat) {
            this.registerSpecialLiteralValue(cval.value, "NSCore::BigNat");
            return this.getSpecialLiteralValue(cval.value);
        }
        else if (cval instanceof MIRConstantRational) {
            this.registerSpecialLiteralValue(cval.value, "NSCore::Rational");
            return this.getSpecialLiteralValue(cval.value);
        }
        else if (cval instanceof MIRConstantFloat) {
            this.registerSpecialLiteralValue(cval.value, "NSCore::Float");
            return this.getSpecialLiteralValue(cval.value);
        }
        else if (cval instanceof MIRConstantDecimal) {
            this.registerSpecialLiteralValue(cval.value, "NSCore::Decimal");
            return this.getSpecialLiteralValue(cval.value);
        }
        else if (cval instanceof MIRConstantString) {
            this.registerSpecialLiteralValue(cval.value, "NSCore::String");
            return this.getSpecialLiteralValue(cval.value);
        }
        else if (cval instanceof MIRConstantTypedNumber) {
            return this.constantToICPP(cval.value);
        }
        else if (cval instanceof MIRConstantStringOf) {
            this.registerSpecialLiteralValue(cval.value, "NSCore::String");
            return this.getSpecialLiteralValue(cval.value);
        }
        else if (cval instanceof MIRConstantDataString) {
            this.registerSpecialLiteralValue(cval.value, "NSCore::String");
            return this.getSpecialLiteralValue(cval.value);
        }
        else {
            assert(cval instanceof MIRConstantRegex);

            const rval = (cval as MIRConstantRegex).value;
            return this.getSpecialLiteralValue(rval.restr);
        }
    }

    argToICPPLocation(arg: MIRArgument): Argument {
        if (arg instanceof MIRRegisterArgument) {
            return this.getStackInfoForArgVar(arg.nameID);
        }
        else if(arg instanceof MIRGlobalVariable) {
            return ICPPOpEmitter.genConstArgument(this.constMap.get(arg.gkey) as number);
        }
        else {
            return this.constantToICPP(arg as MIRConstantArgument);
        }
    }

    trgtToICPPTargetLocation(trgt: MIRRegisterArgument, oftype: MIRResolvedTypeKey): TargetVar {
        return this.getStackInfoForTargetVar(trgt.nameID, this.typegen.getICPPTypeData(this.typegen.getMIRType(oftype)));
    }

    generateGuardToInfo(gg: MIRGuard): ICPPGuard {
        if(gg instanceof MIRArgGuard) {
            return ICPPOpEmitter.genVarGuard(this.stackMap.get(gg.greg.nameID) as number);
        }
        else {
            const mg = gg as MIRMaskGuard;
            if(mg.gmask === "#maskparam#") {
                return ICPPOpEmitter.genMaskGuard(-1, mg.gindex);
            }
            else {
                return ICPPOpEmitter.genMaskGuard(this.maskMap.get(mg.gmask) as number, mg.gindex);
            }
        }
    }

    generateStatmentGuardInfo(sguard: MIRStatmentGuard | undefined): ICPPStatementGuard {
        if (sguard === undefined) {
            return ICPPOpEmitter.genNoStatmentGuard();
        }
        else {
            const gg = this.generateGuardToInfo(sguard.guard);
            const dvar = sguard.defaultvar !== undefined ? this.argToICPPLocation(sguard.defaultvar) : ICPPOpEmitter.genConstArgument(EMPTY_CONST_POSITION);
            return ICPPOpEmitter.genStatmentGuard(gg, sguard.usedefault === "defaultontrue", dvar);
        }
    }

    generateNoneCheck(sinfo: SourceInfo, trgt: MIRRegisterArgument, arg: MIRArgument, argtype: MIRType): ICPPOp {
        if (this.typegen.isType(argtype, "NSCore::None")) {
            return ICPPOpEmitter.genDirectAssignOp(sinfo, this.trgtToICPPTargetLocation(trgt, "NSCore::Bool"), "NSCore::Bool", this.getSpecialLiteralValue("true"), ICPPOpEmitter.genNoStatmentGuard());
        }
        else if (!this.assembly.subtypeOf(this.typegen.getMIRType("NScore::None"), argtype)) {
            return ICPPOpEmitter.genDirectAssignOp(sinfo, this.trgtToICPPTargetLocation(trgt, "NSCore::Bool"), "NSCore::Bool", this.getSpecialLiteralValue("false"), ICPPOpEmitter.genNoStatmentGuard());
        }
        else {
            return ICPPOpEmitter.genTypeIsNoneOp(sinfo, trgt, arg, argtype);
        }
    }

    generateSomeCheck(sinfo: SourceInfo, trgt: MIRRegisterArgument, arg: MIRArgument, argtype: MIRType): ICPPOp {
        if (this.typegen.isType(argtype, "NSCore::None")) {
            return ICPPOpEmitter.genDirectAssignOp(sinfo, this.trgtToICPPTargetLocation(trgt, "NSCore::Bool"), "NSCore::Bool", this.getSpecialLiteralValue("false"), ICPPOpEmitter.genNoStatmentGuard());
        }
        else if (!this.assembly.subtypeOf(this.typegen.getMIRType("NScore::None"), argtype)) {
            return ICPPOpEmitter.genDirectAssignOp(sinfo, this.trgtToICPPTargetLocation(trgt, "NSCore::Bool"), "NSCore::Bool", this.getSpecialLiteralValue("true"), ICPPOpEmitter.genNoStatmentGuard());
        }
        else {
            return ICPPOpEmitter.genTypeIsSomeOp(sinfo, trgt, arg, argtype);
        }
    }
    
    processAbort(op: MIRAbort): ICPPOp {
        return ICPPOpEmitter.genAbortOp(op.sinfo, op.info);
    }

    processAssertCheck(op: MIRAssertCheck): ICPPOp {
        const chkval = this.argToICPPLocation(op.arg);
        
        return ICPPOpEmitter.genAssertOp(op.sinfo, chkval, op.info);
    }

    processLoadUnintVariableValue(op: MIRLoadUnintVariableValue): ICPPOp {
        return ICPPOpEmitter.genLoadUnintVariableValueOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.oftype), op.oftype);
    }

    processDeclareGuardFlagLocation(op: MIRDeclareGuardFlagLocation) {
        let minfo = this.masklayout.find((mloc) => !mloc.occupied && mloc.size === op.count);
        if(minfo === undefined) {
            minfo = {offset: this.masksize, occupied: true, name: "[CLEAR]", size: op.count};
            this.masklayout.push(minfo);
            this.masksize += op.count;
        }

        minfo.occupied = true;
        minfo.name = op.name;
    }

    processSetConstantGuardFlag(op: MIRSetConstantGuardFlag) {
        const minfo = this.masklayout.find((mloc) => mloc.name === op.name) as {offset: number, occupied: boolean, name: string, size: number};
        ICPPOpEmitter.genStoreConstantMaskValueOp(op.sinfo, minfo.offset, op.position, op.flag);
    }

    processConvertValue(op: MIRConvertValue): ICPPOp {
        return this.typegen.coerce(op.sinfo, this.argToICPPLocation(op.src), this.typegen.getMIRType(op.srctypelayout), this.trgtToICPPTargetLocation(op.trgt, op.intotype), this.typegen.getMIRType(op.intotype), this.generateStatmentGuardInfo(op.sguard));
    }

    processLoadConst(op: MIRLoadConst): ICPPOp {
        return ICPPOpEmitter.genLoadConstOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.consttype), this.argToICPPLocation(op.src), op.consttype);
    }

    processTupleHasIndex(op: MIRTupleHasIndex): ICPPOp {
        return ICPPOpEmitter.genTupleHasIndexOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "NSCore::Bool"), this.argToICPPLocation(op.arg), op.arglayouttype, op.idx);
    }

    processRecordHasProperty(op: MIRRecordHasProperty): ICPPOp {
        return ICPPOpEmitter.genRecordHasPropertyOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "NSCore::Bool"), this.argToICPPLocation(op.arg), op.arglayouttype, op.pname);
    }

    processLoadTupleIndex(op: MIRLoadTupleIndex): ICPPOp {
        if(op.isvirtual) {
            return ICPPOpEmitter.genLoadTupleIndexVirtualOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resulttype), op.resulttype, this.argToICPPLocation(op.arg), op.arglayouttype, op.idx);
        }
        else {
            const icppargt = this.typegen.getICPPTypeData(this.typegen.getMIRType(op.argflowtype)) as ICPPTypeTuple;
            return ICPPOpEmitter.genLoadTupleIndexDirectOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resulttype), op.resulttype, this.argToICPPLocation(op.arg), op.arglayouttype, icppargt.idxoffsets[op.idx], op.idx);
        }
    }

    processLoadTupleIndexSetGuard(op: MIRLoadTupleIndexSetGuard): ICPPOp {
        const guard = this.generateGuardToInfo(op.guard);

        if(op.isvirtual) {
            return ICPPOpEmitter.genLoadTupleIndexSetGuardVirtualOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resulttype), op.resulttype, this.argToICPPLocation(op.arg), op.arglayouttype, op.idx, guard);
        }
        else {
            const icppargt = this.typegen.getICPPTypeData(this.typegen.getMIRType(op.argflowtype)) as ICPPTypeTuple;
            return ICPPOpEmitter.genLoadTupleIndexSetGuardDirectOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resulttype), op.resulttype, this.argToICPPLocation(op.arg), op.arglayouttype, icppargt.idxoffsets[op.idx], op.idx, guard);
        }
    }

    processLoadRecordProperty(op: MIRLoadRecordProperty): ICPPOp {
        if(op.isvirtual) {
            return ICPPOpEmitter.genLoadRecordPropertyVirtualOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resulttype), op.resulttype, this.argToICPPLocation(op.arg), op.arglayouttype, op.pname);
        }
        else {
            const icppargt = this.typegen.getICPPTypeData(this.typegen.getMIRType(op.argflowtype)) as ICPPTypeRecord;
            const slotidx = icppargt.propertynames.indexOf(op.pname);

            return ICPPOpEmitter.genLoadRecordPropertyDirectOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resulttype), op.resulttype, this.argToICPPLocation(op.arg), op.arglayouttype, icppargt.propertyoffsets[slotidx], op.pname);
        }
    }

    processLoadRecordPropertySetGuard(op: MIRLoadRecordPropertySetGuard): ICPPOp {
        const guard = this.generateGuardToInfo(op.guard);

        if(op.isvirtual) {
            return ICPPOpEmitter.genLoadRecordPropertySetGuardVirtualOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resulttype), op.resulttype, this.argToICPPLocation(op.arg), op.arglayouttype, op.pname, guard);
        }
        else {
            const icppargt = this.typegen.getICPPTypeData(this.typegen.getMIRType(op.argflowtype)) as ICPPTypeRecord;
            const slotidx = icppargt.propertynames.indexOf(op.pname);

            return ICPPOpEmitter.genLoadRecordPropertySetGuardDirectOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resulttype), op.resulttype, this.argToICPPLocation(op.arg), op.arglayouttype, icppargt.propertyoffsets[slotidx], op.pname, guard);
        }
    }

    processLoadField(op: MIRLoadField): ICPPOp {
        if(op.isvirtual) {
            return ICPPOpEmitter.genLoadEntityFieldVirtualOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resulttype), op.resulttype, this.argToICPPLocation(op.arg), op.arglayouttype, op.field);
        }
        else {
            const icppargt = this.typegen.getICPPTypeData(this.typegen.getMIRType(op.argflowtype)) as ICPPTypeEntity;
            const slotidx = icppargt.fieldnames.indexOf(op.field);

            return ICPPOpEmitter.genLoadEntityFieldDirectOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resulttype), op.resulttype, this.argToICPPLocation(op.arg), op.arglayouttype, icppargt.fieldoffsets[slotidx], op.field);
        }
    }

    processTupleProjectToEphemeral(op: MIRTupleProjectToEphemeral): ICPPOp {
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.epht);

        if(op.isvirtual) {
            const icall = this.generateProjectVirtualTupleInvName(this.typegen.getMIRType(op.argflowtype), op.indecies, resulttype);
            if(this.requiredProjectVirtualTupleIndex.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), indecies: op.indecies, resulttype: resulttype };
                this.requiredProjectVirtualTupleIndex.push(geninfo);
            }
            
            return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.epht), op.epht, icall, [this.argToICPPLocation(op.arg)], -1);
        }
        else {
            let sametypes = true;
            for(let i = 0; i < op.indecies.length; ++i) {
                const idx = op.indecies[i];
                sametypes = sametypes && ((argflowtype.options[0] as MIRTupleType).entries[idx].type.trkey === (resulttype.options[0] as MIREphemeralListType).entries[i].trkey);
            }

            if(sametypes) {
                const tuptype = this.typegen.getICPPTypeData(this.typegen.getMIRType((argflowtype.options[0] as MIRTupleType).trkey)) as ICPPTypeTuple;
                
                let idxs: [number, number, MIRResolvedTypeKey][] = [];
                op.indecies.forEach((idx) => {
                    idxs.push([idx, tuptype.idxoffsets[idx], tuptype.ttypes[idx]]);
                });

                return ICPPOpEmitter.genProjectTupleOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.epht), op.epht, this.argToICPPLocation(op.arg), op.arglayouttype, op.argflowtype, idxs);
            }
            else {
                //If we need to do coercsion then just build a vmethod call that will handle it 

                const icall = this.generateProjectVirtualTupleInvName(this.typegen.getMIRType(op.argflowtype), op.indecies, resulttype);
                if (this.requiredProjectVirtualTupleIndex.findIndex((vv) => vv.inv === icall) === -1) {
                    const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), indecies: op.indecies, resulttype: resulttype };
                    this.requiredProjectVirtualTupleIndex.push(geninfo);
                }

                return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.epht), op.epht, icall, [this.argToICPPLocation(op.arg)], -1);
            }
        }
    }

    processRecordProjectToEphemeral(op: MIRRecordProjectToEphemeral): ICPPOp {
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.epht);

        if(op.isvirtual) {
            const icall = this.generateProjectVirtualRecordInvName(this.typegen.getMIRType(op.argflowtype), op.properties, resulttype);
            if(this.requiredProjectVirtualRecordProperty.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), properties: op.properties, resulttype: resulttype };
                this.requiredProjectVirtualRecordProperty.push(geninfo);
            }
            
            return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.epht), op.epht, icall, [this.argToICPPLocation(op.arg)], -1);
        }
        else {
            let sametypes = true;
            for(let i = 0; i < op.properties.length; ++i) {
                const pname = op.properties[i];
                const pentry = (argflowtype.options[0] as MIRRecordType).entries.find((entry) => entry.name === pname) as MIRRecordTypeEntry;
                sametypes = sametypes && (pentry.type.trkey === (resulttype.options[0] as MIREphemeralListType).entries[i].trkey);
            }

            if(sametypes) {
                const rectype = this.typegen.getICPPTypeData(this.typegen.getMIRType((argflowtype.options[0] as MIRRecordType).trkey)) as ICPPTypeRecord;
                
                let props: [string, number, MIRResolvedTypeKey][] = [];
                op.properties.forEach((pname) => {
                    const pentryidx = rectype.propertynames.findIndex((pn) => pn === pname);
                    props.push([pname, rectype.propertyoffsets[pentryidx], rectype.propertytypes[pentryidx]]);
                });

                return ICPPOpEmitter.genProjectRecordOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.epht), op.epht, this.argToICPPLocation(op.arg), op.arglayouttype, op.argflowtype, props);
            }
            else {
                //If we need to do coercsion then just build a vmethod call that will handle it 

                const icall = this.generateProjectVirtualRecordInvName(this.typegen.getMIRType(op.argflowtype), op.properties, resulttype);
                if(this.requiredProjectVirtualRecordProperty.findIndex((vv) => vv.inv === icall) === -1) {
                    const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), properties: op.properties, resulttype: resulttype };
                    this.requiredProjectVirtualRecordProperty.push(geninfo);
                }
                
                return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.epht), op.epht, icall, [this.argToICPPLocation(op.arg)], -1);
            }
        }
    }

    processEntityProjectToEphemeral(op: MIREntityProjectToEphemeral): ICPPOp {
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.epht);

        if(op.isvirtual) {
            const icall = this.generateProjectVirtualEntityInvName(this.typegen.getMIRType(op.argflowtype), op.fields, resulttype);
            if(this.requiredProjectVirtualEntityField.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), fields: op.fields.map((fkey) => this.assembly.fieldDecls.get(fkey) as MIRFieldDecl), resulttype: resulttype };
                this.requiredProjectVirtualEntityField.push(geninfo);
            }
            
            return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.epht), op.epht, icall, [this.argToICPPLocation(op.arg)], -1);
        }
        else {
            let sametypes = true;
            for(let i = 0; i < op.fields.length; ++i) {
                const fkey = op.fields[i];
                const fentry = this.assembly.fieldDecls.get(fkey) as MIRFieldDecl;
                sametypes = sametypes && (fentry.declaredType === (resulttype.options[0] as MIREphemeralListType).entries[i].trkey);
            }

            if(sametypes) {
                const etype = this.typegen.getICPPTypeData(this.typegen.getMIRType((argflowtype.options[0] as MIREntityType).trkey)) as ICPPTypeEntity;
                
                let fields: [MIRFieldKey, number, MIRResolvedTypeKey][] = [];
                op.fields.forEach((fkey) => {
                    const fentryidx = etype.fieldnames.findIndex((fn) => fn === fkey);
                    fields.push([fkey, etype.fieldoffsets[fentryidx], etype.fieldtypes[fentryidx]]);
                });

                return ICPPOpEmitter.genProjectEntityOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.epht), op.epht, this.argToICPPLocation(op.arg), op.arglayouttype, op.argflowtype, fields);
            }
            else {
                //If we need to do coercsion then just build a vmethod call that will handle it 

                const icall = this.generateProjectVirtualEntityInvName(this.typegen.getMIRType(op.argflowtype), op.fields, resulttype);
                if(this.requiredProjectVirtualEntityField.findIndex((vv) => vv.inv === icall) === -1) {
                    const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), fields: op.fields.map((fkey) => this.assembly.fieldDecls.get(fkey) as MIRFieldDecl), resulttype: resulttype };
                    this.requiredProjectVirtualEntityField.push(geninfo);
                }
                
                return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.epht), op.epht, icall, [this.argToICPPLocation(op.arg)], -1);
            }
        }
    }

    processTupleUpdate(op: MIRTupleUpdate): ICPPOp {
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateUpdateVirtualTupleInvName(this.typegen.getMIRType(op.argflowtype), op.updates.map((upd) => [upd[0], upd[2]]), resulttype);
            if(this.requiredUpdateVirtualTuple.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), updates: op.updates.map((upd) => [upd[0], upd[2]] as [number, MIRResolvedTypeKey]), resulttype: resulttype };
                this.requiredUpdateVirtualTuple.push(geninfo);
            }
            
            return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.argflowtype), resulttype.trkey, icall, [this.argToICPPLocation(op.arg)], -1);
        }
        else {
            let sametypes = true;
            for (let i = 0; i < op.updates.length; ++i) {
                const idx = op.updates[i][0];
                sametypes = sametypes && ((argflowtype.options[0] as MIRTupleType).entries[idx].type.trkey === op.updates[i][2]);
            }

            if (sametypes) {
                const tuptype = this.typegen.getICPPTypeData(this.typegen.getMIRType((argflowtype.options[0] as MIRTupleType).trkey)) as ICPPTypeTuple;

                let idxs: [number, number, MIRResolvedTypeKey, Argument][] = [];
                op.updates.forEach((upd) => {
                    const idx = upd[0];
                    idxs.push([idx, tuptype.idxoffsets[idx], tuptype.ttypes[idx], this.argToICPPLocation(upd[1])]);
                });

                return ICPPOpEmitter.genUpdateTupleOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.argflowtype), resulttype.trkey, this.argToICPPLocation(op.arg), op.arglayouttype, op.argflowtype, idxs);
            }
            else {
                //If we need to do coercsion then just build a vmethod call that will handle it 

                const icall = this.generateUpdateVirtualTupleInvName(this.typegen.getMIRType(op.argflowtype), op.updates.map((upd) => [upd[0], upd[2]]), resulttype);
                if(this.requiredUpdateVirtualTuple.findIndex((vv) => vv.inv === icall) === -1) {
                    const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), updates: op.updates.map((upd) => [upd[0], upd[2]] as [number, MIRResolvedTypeKey]), resulttype: resulttype };
                    this.requiredUpdateVirtualTuple.push(geninfo);
                }
                
                return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.argflowtype), resulttype.trkey, icall, [this.argToICPPLocation(op.arg)], -1);
            }
        }
    }

    processRecordUpdate(op: MIRRecordUpdate): ICPPOp {
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateUpdateVirtualRecordInvName(this.typegen.getMIRType(op.argflowtype), op.updates.map((upd) => [upd[0], upd[2]]), resulttype);
            if(this.requiredUpdateVirtualRecord.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), updates: op.updates.map((upd) => [upd[0], upd[2]] as [string, MIRResolvedTypeKey]), resulttype: resulttype };
                this.requiredUpdateVirtualRecord.push(geninfo);
            }
            
            return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.argflowtype), resulttype.trkey, icall, [this.argToICPPLocation(op.arg)], -1);
        }
        else {
            let sametypes = true;
            for(let i = 0; i < op.updates.length; ++i) {
                const pname = op.updates[i][0];
                const pentry = (argflowtype.options[0] as MIRRecordType).entries.find((entry) => entry.name === pname) as MIRRecordTypeEntry;
                sametypes = sametypes && (pentry.type.trkey === op.updates[i][2]);
            }

            if(sametypes) {
                const rectype = this.typegen.getICPPTypeData(this.typegen.getMIRType((argflowtype.options[0] as MIRRecordType).trkey)) as ICPPTypeRecord;
                
                let props: [string, number, MIRResolvedTypeKey, Argument][] = [];
                op.updates.forEach((upd) => {
                    const pname = upd[0];
                    const pentryidx = rectype.propertynames.findIndex((pn) => pn === pname);
                    props.push([pname, rectype.propertyoffsets[pentryidx], rectype.propertytypes[pentryidx], this.argToICPPLocation(upd[1])]);
                });

                return ICPPOpEmitter.genUpdateRecordOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.argflowtype), resulttype.trkey, this.argToICPPLocation(op.arg), op.arglayouttype, op.argflowtype, props);
            }
            else {
                //If we need to do coercsion then just build a vmethod call that will handle it 

                const icall = this.generateUpdateVirtualRecordInvName(this.typegen.getMIRType(op.argflowtype), op.updates.map((upd) => [upd[0], upd[2]]), resulttype);
                if(this.requiredUpdateVirtualRecord.findIndex((vv) => vv.inv === icall) === -1) {
                    const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), updates: op.updates.map((upd) => [upd[0], upd[2]] as [string, MIRResolvedTypeKey]), resulttype: resulttype };
                    this.requiredUpdateVirtualRecord.push(geninfo);
                }
                
                return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.argflowtype), resulttype.trkey, icall, [this.argToICPPLocation(op.arg)], -1);
            }
        }
    }

    processEntityUpdate(op: MIREntityUpdate): ICPPOp {
        const resulttype = this.typegen.getMIRType(op.argflowtype);

        if (op.isvirtual) {
            const icall = this.generateUpdateVirtualEntityInvName(this.typegen.getMIRType(op.argflowtype), op.updates.map((upd) => [upd[0], upd[2]]), resulttype);
            if (this.requiredUpdateVirtualEntity.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), updates: op.updates.map((upd) => [upd[0], upd[2]] as [MIRFieldKey, MIRResolvedTypeKey]), resulttype: resulttype };
                this.requiredUpdateVirtualEntity.push(geninfo);
            }

            return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.argflowtype), resulttype.trkey, icall, [this.argToICPPLocation(op.arg)], -1);
        }
        else {
            const icall = this.generateUpdateEntityWithInvariantName(this.typegen.getMIRType(op.argflowtype), op.updates.map((upd) => [upd[0], upd[2]]), resulttype);
            if (this.requiredUpdateVirtualEntity.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), updates: op.updates.map((upd) => [upd[0], upd[2]] as [MIRFieldKey, MIRResolvedTypeKey]), resulttype: resulttype };
                this.requiredUpdateVirtualEntity.push(geninfo);
            }

            return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.argflowtype), resulttype.trkey, icall, [this.argToICPPLocation(op.arg)], -1);
        }
    }

    processLoadFromEpehmeralList(op: MIRLoadFromEpehmeralList): ICPPOp {
        const icppargtype = this.typegen.getICPPTypeData(this.typegen.getMIRType(op.argtype)) as ICPPTypeEphemeralList;
        const offset = icppargtype.eoffsets[op.idx];

        return ICPPOpEmitter.genLoadFromEpehmeralListOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resulttype), op.resulttype, this.argToICPPLocation(op.arg), op.argtype, offset, op.idx);
    }

    processMultiLoadFromEpehmeralList(op: MIRMultiLoadFromEpehmeralList): ICPPOp {
        const icppargtype = this.typegen.getICPPTypeData(this.typegen.getMIRType(op.argtype)) as ICPPTypeEphemeralList;

        let trgts: TargetVar[] = []
        let trgttypes: MIRResolvedTypeKey[] = [];
        let offsets: number[] = [];
        let idxs: number[] = [];
        op.trgts.forEach((asgn) => {
            trgts.push(this.trgtToICPPTargetLocation(asgn.into, asgn.oftype));
            trgttypes.push(asgn.oftype);
            offsets.push(icppargtype.eoffsets[asgn.pos]);
            idxs.push(asgn.pos);
        });

        return ICPPOpEmitter.genMultiLoadFromEpehmeralListOp(op.sinfo, trgts, trgttypes, this.argToICPPLocation(op.arg), op.argtype, offsets, idxs);
    }

    processSliceEpehmeralList(op: MIRSliceEpehmeralList): ICPPOp {
        const slicpp = this.typegen.getICPPTypeData(this.typegen.getMIRType(op.sltype)) as ICPPTypeEphemeralList;
        const elicpp = this.typegen.getICPPTypeData(this.typegen.getMIRType(op.argtype)) as ICPPTypeEphemeralList;

        if(slicpp.allocinfo.inlinedatasize === elicpp.allocinfo.inlinedatasize) {
            return ICPPOpEmitter.genDirectAssignOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.sltype), op.sltype, this.argToICPPLocation(op.arg), ICPPOpEmitter.genNoStatmentGuard());
        }
        else {
            const offsetend = slicpp.allocinfo.inlinedatasize;
            return ICPPOpEmitter.genSliceEphemeralListOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.sltype), op.sltype, this.argToICPPLocation(op.arg), op.argtype, offsetend, slicpp.eoffsets.length);
        }
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
            const call = mask !== undefined ? new SMTCallGeneralWOptMask(this.typegen.mangle(op.mkey), args, mask) : new SMTCallGeneral(this.typegen.mangle(op.mkey), args);
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

    processConstructorTuple(op: MIRConstructorTuple): ICPPOp {
        const args = op.args.map((arg) => this.argToICPPLocation(arg));
        return ICPPOpEmitter.genConstructorTupleOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resultTupleType), op.resultTupleType, args);
    }

    processConstructorTupleFromEphemeralList(op: MIRConstructorTupleFromEphemeralList): ICPPOp {
        return ICPPOpEmitter.genConstructorTupleFromEphemeralListOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resultTupleType), op.resultTupleType, this.argToICPPLocation(op.arg), op.elistType);
    }

    processConstructorRecord(op: MIRConstructorRecord): ICPPOp {
        const args = op.args.map((arg) => this.argToICPPLocation(arg[1]));

        return ICPPOpEmitter.genConstructorRecordOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resultRecordType), op.resultRecordType, args);
    }

    processConstructorRecordFromEphemeralList(op: MIRConstructorRecordFromEphemeralList): ICPPOp {
        const rtype = this.typegen.getMIRType(op.resultRecordType).options[0] as MIRRecordType;
        let proppositions = rtype.entries.map((rentry) => {
            const eidx = op.propertyPositions.indexOf(rentry.name);
            return eidx;
        });

        let total = proppositions.length === 0 || proppositions[0] === 0;
        for(let i = 1; i < proppositions.length; ++i)
        {
            total = total && (proppositions[i - 1] + 1 === proppositions[i]);
        }
        if(total) {
            proppositions = [];
        }

        return ICPPOpEmitter.genConstructorRecordFromEphemeralListOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resultRecordType), op.resultRecordType, this.argToICPPLocation(op.arg), op.elistType, proppositions);
    }

    processStructuredAppendTuple(op: MIRStructuredAppendTuple): ICPPOp {
        const targs = op.ttypes.map((tt) => {
            return { flow: this.typegen.getMIRType(tt.flow), layout: this.typegen.getMIRType(tt.layout) };
        });
        const rtype = this.typegen.getMIRType(op.resultTupleType);
        const cargs = op.args.map((arg) => this.argToICPPLocation(arg));

        const icall = this.generateTupleAppendInvName(targs, rtype);
        if(this.requiredTupleAppend.findIndex((vv) => vv.inv === icall) === -1) {
            const geninfo = { inv: icall, args: targs, resulttype: rtype };
            this.requiredTupleAppend.push(geninfo);
        }
            
        return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resultTupleType), op.resultTupleType, icall, cargs, -1);
    }

    processStructuredJoinRecord(op: MIRStructuredJoinRecord): ICPPOp {
        const targs = op.ttypes.map((tt) => {
            return { flow: this.typegen.getMIRType(tt.flow), layout: this.typegen.getMIRType(tt.layout) };
        });
        const rtype = this.typegen.getMIRType(op.resultRecordType);
        const cargs = op.args.map((arg) => this.argToICPPLocation(arg));

        const icall = this.generateRecordMergeInvName(targs, rtype);
        if(this.requiredRecordMerge.findIndex((vv) => vv.inv === icall) === -1) {
            const geninfo = { inv: icall, args: targs, resulttype: rtype };
            this.requiredRecordMerge.push(geninfo);
        }
            
        return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resultRecordType), op.resultRecordType, icall, cargs, -1);
    }

    processConstructorEphemeralList(op: MIRConstructorEphemeralList): ICPPOp {
        const args = op.args.map((arg) => this.argToICPPLocation(arg));
        return ICPPOpEmitter.genConstructorEphemeralListOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resultEphemeralListType), op.resultEphemeralListType, args);
    }

    processEphemeralListExtend(op: MIREphemeralListExtend): ICPPOp {
        const ext = op.ext.map((arg) => this.argToICPPLocation(arg));
        return ICPPOpEmitter.genEphemeralListExtendOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resultType), op.resultType, this.argToICPPLocation(op.arg), op.argtype, ext);
    }

    processConstructorPrimaryCollectionEmpty(op: MIRConstructorPrimaryCollectionEmpty): ICPPOp {
        return ICPPOpEmitter.genConstructorPrimaryCollectionEmptyOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.tkey), op.tkey);
    }

    processConstructorPrimaryCollectionSingletons(op: MIRConstructorPrimaryCollectionSingletons): ICPPOp {
        const args = op.args.map((arg) => this.argToICPPLocation(arg[1]));
        return ICPPOpEmitter.genConstructorPrimaryCollectionSingletonsOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.tkey), op.tkey, args);
    }

    processConstructorPrimaryCollectionCopies(op: MIRConstructorPrimaryCollectionCopies): ICPPOp {
        return NOT_IMPLEMENTED("processConstructorPrimaryCollectionCopies");
    }

    processConstructorPrimaryCollectionMixed(op: MIRConstructorPrimaryCollectionMixed): ICPPOp {
        return NOT_IMPLEMENTED("processConstructorPrimaryCollectionMixed");
    }

    processBinKeyEq(op: MIRBinKeyEq): ICPPOp {
        xxxx;
    }

    processBinKeyLess(op: MIRBinKeyLess): ICPPOp {
        xxxx;
    }

    processPrefixNotOp(op: MIRPrefixNotOp): ICPPOp {
        return ICPPOpEmitter.genPrefixNotOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "NSCore::Bool"), this.argToICPPLocation(op.arg));
    }

    processAllTrue(op: MIRAllTrue): ICPPOp {
        return ICPPOpEmitter.genAllTrueOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "NSCore::Bool"), op.args.map((arg) => this.argToICPPLocation(arg)));
    }

    processSomeTrue(op: MIRSomeTrue): ICPPOp {
        return ICPPOpEmitter.genSomeTrueOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "NSCore::Bool"), op.args.map((arg) => this.argToICPPLocation(arg)));
    }

    processIsTypeOf(op: MIRIsTypeOf): ICPPOp {
        const layout = this.typegen.getMIRType(op.srclayouttype);
        const flow = this.typegen.getMIRType(op.srcflowtype);
        const oftype = this.typegen.getMIRType(op.chktype);

        //
        //TODO: to complicated in the sub options? Maybe should look more like the interpreter version
        //

        let ttop: SMTExp = new SMTConst("false");
        if(this.assembly.subtypeOf(flow, oftype)) {
            //also handles the oftype is Any case
            ttop = new SMTConst("true");
        }
        else if(this.typegen.isType(oftype, "NSCore::None")) {
            ttop = this.generateNoneCheck(op.arg, layout);
        }
        else if (this.typegen.isType(oftype, "NSCore::Some")) {
            ttop = this.generateSomeCheck(op.arg, layout);
        }
        else {
            const tests = oftype.options.map((topt) => {
                const mtype = this.typegen.getMIRType(topt.trkey);
                assert(mtype !== undefined, "We should generate all the component types by default??");
    
                if(topt instanceof MIREntityType) {
                    return new SMTLet(this.varToSMTName(op.trgt).vname, this.generateSubtypeCheckEntity(op.arg, layout, flow, mtype), continuation);
                }
                else if (topt instanceof MIRConceptType) {
                    return new SMTLet(this.varToSMTName(op.trgt).vname, this.generateSubtypeCheckConcept(op.arg, layout, flow, mtype), continuation);
                }
                else if (topt instanceof MIRTupleType) {
                    return new SMTLet(this.varToSMTName(op.trgt).vname, this.generateSubtypeCheckTuple(op.arg, layout, flow, mtype), continuation);
                }
                else {
                    assert(topt instanceof MIRRecordType, "All other cases should be handled previously (e.g. dynamic subtype of ephemeral or literal types is not good here)");

                    return new SMTLet(this.varToSMTName(op.trgt).vname, this.generateSubtypeCheckRecord(op.arg, layout, flow, mtype), continuation);
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
                ttop = new SMTCallSimple("or", tests);
            }
        }

        const gop = this.generateGuardStmtCond(op.sguard, ttop, "NSCore::Bool");
        return new SMTLet(this.varToSMTName(op.trgt).vname, gop, continuation);
    }

    processRegisterAssign(op: MIRRegisterAssign): ICPPOp {
        if(op.sguard === undefined) {
            return new SMTLet(this.varToSMTName(op.trgt).vname, this.argToSMT(op.src), continuation);
        }
        else {
            const cassign = this.generateGuardStmtCond(op.sguard, this.argToSMT(op.src), op.layouttype);
            return new SMTLet(this.varToSMTName(op.trgt).vname, cassign, continuation);
        }
    }

    processReturnAssign(op: MIRReturnAssign): ICPPOp {
        return new SMTLet(this.varToSMTName(op.name).vname, this.argToSMT(op.src), continuation);
    }

    processReturnAssignOfCons(op: MIRReturnAssignOfCons): ICPPOp {
        const conscall = new SMTCallSimple(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.oftype)).cons, op.args.map((arg) => this.argToSMT(arg)));
        return new SMTLet(this.varToSMTName(op.name).vname, conscall, continuation);
    }

    processOp(op: MIROp): ICPPOp | undefined {
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
            case MIROpTag.MIRSomeTrue: {
                return this.processSomeTrue(op as MIRSomeTrue, continuation);
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

    processGenerateResultWithZeroArgCheck(sinfo: SourceInfo, zero: SMTConst, not0arg: SMTExp, oftype: MIRType, val: SMTExp): SMTExp {
        const chkzero = new SMTCallSimple("=", [zero, not0arg]);
        return new SMTIf(chkzero, this.generateErrorCreate(sinfo, oftype, "Div by 0"), this.typegen.generateResultTypeConstructorSuccess(oftype, val));
    }

    processGenerateResultWithBounds(sinfo: SourceInfo, op: string, args: SMTExp[], oftype: MIRType): SMTExp {
        //TODO: Bounds check -- also for signed need to do check for -Int::max (since range of negative values is one less than positive)
        //https://stackoverflow.com/questions/40605207/how-to-zero-sign-extend-bitvectors-in-z3
        //https://github.com/Z3Prover/z3/issues/574
        //https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/z3prefix.pdf
        //(declare-const a (_ BitVec 1))
        //(declare-const b (_ BitVec 2))
        //(assert (= b ((_ zero_extend 1) a)))

        //TODO: Suppose we try to refute the feasibility of an error on a small width bitvector say 5 and we get unsat
        //      Hypothesis -- if the unsat core does not contain an arith overflow failure then the core also holds for any larger BV size
        //      If so then we can A* up the bit-vector sizes

        if(!this.vopts.OverflowEnabled) {
            if(op === "-" && (oftype.trkey === "NSCore::Nat" || oftype.trkey === "NSCore::BigNat")) {
                const vtmp = this.generateTempName();
                const val = new SMTVar(vtmp);

                const chkbounds = new SMTCallSimple("bvult", args);
                const bop = new SMTIf(chkbounds, this.generateErrorCreate(sinfo, oftype, "Unsigned subtract underflow"), this.typegen.generateResultTypeConstructorSuccess(oftype, val));

                if(oftype.trkey === "NSCore::Nat") {
                    return new SMTLet(vtmp, new SMTCallSimple("bvsub", args), bop);
                }
                else {
                    const subop = this.vopts.BigXMode === "Int" ? new SMTCallSimple(op, args) : new SMTCallSimple("bvsub", args);
                    return new SMTLet(vtmp, subop, bop);
                }
            }
            else {
                if(this.vopts.BigXMode === "Int" && (oftype.trkey === "NSCore::BigInt" || oftype.trkey === "NSCore::BigNat")) {
                    return new SMTCallSimple(op, args);
                }
                else {
                    const opbvbasic = { "+": "bvadd", "-": "bvsub", "*": "bvmul" }[op as "+" | "-" | "*"];
                    return new SMTCallSimple(opbvbasic, args);
                }
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

        xxxx;


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
                smte = new SMTCallSimple("bvneg", args);
                break;
            }
            case "NSCore::-=prefix=(NSCore::BigInt)": {
                smte = new SMTCallSimple("-", args);
                break;
            }
            case "NSCore::-=prefix=(NSCore::Rational)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BRationalUnary_UF", [new SMTConst("\"op_unary_negate\""), ...args]) : new SMTCallSimple("-", args);
                break;
            }
            case "NSCore::-=prefix=(NSCore::Float)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BFloatUnary_UF", [new SMTConst("\"op_unary_negate\""), ...args]) : new SMTCallSimple("-", args);
                break;
            }
            case "NSCore::-=prefix=(NSCore::Decimal)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BDecimalUnary_UF", [new SMTConst("\"op_unary_negate\""), ...args]) : new SMTCallSimple("-", args);
                break;
            }
            //op infix +
            case "NSCore::+=infix=(NSCore::Int, NSCore::Int)": {
                rtype = this.typegen.getMIRType("NSCore::Int");
                smte = this.processGenerateResultWithBounds(sinfo, "+", args, rtype);
                erropt = this.vopts.OverflowEnabled;
                break;
            }
            case "NSCore::+=infix=(NSCore::Nat, NSCore::Nat)": {
                rtype = this.typegen.getMIRType("NSCore::Nat");
                smte = this.processGenerateResultWithBounds(sinfo, "+", args, rtype);
                erropt = this.vopts.OverflowEnabled;
                break;
            }
            case "NSCore::+=infix=(NSCore::BigInt, NSCore::BigInt)": {
                rtype = this.typegen.getMIRType("NSCore::BigInt");
                smte = this.processGenerateResultWithBounds(sinfo, "+", args, rtype);
                erropt = this.vopts.OverflowEnabled;
                break;
            }
            case "NSCore::+=infix=(NSCore::BigNat, NSCore::BigNat)": {
                rtype = this.typegen.getMIRType("NSCore::BigNat");
                smte = this.processGenerateResultWithBounds(sinfo, "+", args, rtype);
                erropt = this.vopts.OverflowEnabled;
                break;
            }
            case "NSCore::+=infix=(NSCore::Rational, NSCore::Rational)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BRationalBinary_UF", [new SMTConst("\"op_binary_plus\""), ...args]) : new SMTCallSimple("+", args);
                break;
            }
            case "NSCore::+=infix=(NSCore::Float, NSCore::Float)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BFloatBinary_UF", [new SMTConst("\"op_binary_plus\""), ...args]) : new SMTCallSimple("+", args);
                break;
            }
            case "NSCore::+=infix=(NSCore::Decimal, NSCore::Decimal)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BDecimalBinary_UF", [new SMTConst("\"op_binary_plus\""), ...args]) : new SMTCallSimple("+", args);
                break;
            }
            //op infix -
            case "NSCore::-=infix=(NSCore::Int, NSCore::Int)": {
                rtype = this.typegen.getMIRType("NSCore::Int");
                smte = this.processGenerateResultWithBounds(sinfo, "-", args, rtype);
                erropt = this.vopts.OverflowEnabled;
                break;
            }
            case "NSCore::-=infix=(NSCore::Nat, NSCore::Nat)": {
                rtype = this.typegen.getMIRType("NSCore::Nat");
                smte = this.processGenerateResultWithBounds(sinfo, "-", args, rtype);
                erropt = true;
                break;
            }
            case "NSCore::-=infix=(NSCore::BigInt, NSCore::BigInt)": {
                rtype = this.typegen.getMIRType("NSCore::BigInt");
                smte = this.processGenerateResultWithBounds(sinfo, "-", args, rtype);
                erropt = this.vopts.OverflowEnabled;
                break;
            }
            case "NSCore::-=infix=(NSCore::BigNat, NSCore::BigNat)": {
                rtype = this.typegen.getMIRType("NSCore::BigNat");
                smte = this.processGenerateResultWithBounds(sinfo, "-", args, rtype);
                erropt = true;
                break
            }
            case "NSCore::-=infix=(NSCore::Rational, NSCore::Rational)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BRationalBinary_UF", [new SMTConst("\"op_binary_minus\""), ...args]) : new SMTCallSimple("-", args);
                break;
            }
            case "NSCore::-=infix=(NSCore::Float, NSCore::Float)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BFloatBinary_UF", [new SMTConst("\"op_binary_minus\""), ...args]) : new SMTCallSimple("-", args);
                break;
            }
            case "NSCore::-=infix=(NSCore::Decimal, NSCore::Decimal)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BDecimalBinary_UF", [new SMTConst("\"op_binary_minus\""), ...args]) : new SMTCallSimple("-", args);
                break;
            }
            //op infix *
            case "NSCore::*=infix=(NSCore::Int, NSCore::Int)": {
                rtype = this.typegen.getMIRType("NSCore::Int");
                smte = this.processGenerateResultWithBounds(sinfo, "*", args, rtype);
                erropt = this.vopts.OverflowEnabled;
                break;
            }
            case "NSCore::*=infix=(NSCore::Nat, NSCore::Nat)": {
                rtype = this.typegen.getMIRType("NSCore::Nat");
                smte = this.processGenerateResultWithBounds(sinfo, "*", args, rtype);
                erropt = this.vopts.OverflowEnabled;
                break;
            }
            case "NSCore::*=infix=(NSCore::BigInt, NSCore::BigInt)": {
                rtype = this.typegen.getMIRType("NSCore::BigInt");
                smte = this.processGenerateResultWithBounds(sinfo, "*", args, rtype);
                erropt = this.vopts.OverflowEnabled;
                break;
            }
            case "NSCore::*=infix=(NSCore::BigNat, NSCore::BigNat)": {
                rtype = this.typegen.getMIRType("NSCore::BigNat");
                smte = this.processGenerateResultWithBounds(sinfo, "*", args, rtype);
                erropt = this.vopts.OverflowEnabled;
                break;
            }
            case "NSCore::*=infix=(NSCore::Rational, NSCore::Rational)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BRationalBinary_UF", [new SMTConst("\"op_binary_mult\""), ...args]) : new SMTCallSimple("*", args);
                break;
            }
            case "NSCore::*=infix=(NSCore::Float, NSCore::Float)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BFloatBinary_UF", [new SMTConst("\"op_binary_mult\""), ...args]) : new SMTCallSimple("*", args);
                break;
            }
            case "NSCore::*=infix=(NSCore::Decimal, NSCore::Decimal)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BDecimalBinary_UF", [new SMTConst("\"op_binary_mult\""), ...args]) : new SMTCallSimple("*", args);
                break;
            }
            //op infix /
            case "NSCore::/=infix=(NSCore::Int, NSCore::Int)": {
                rtype = this.typegen.getMIRType("NSCore::Int");
                smte = this.processGenerateResultWithZeroArgCheck(sinfo, new SMTConst("BInt@zero"), args[1], rtype, new SMTCallSimple("bvsrem", args));
                erropt = true;
                break;
            }
            case "NSCore::/=infix=(NSCore::Nat, NSCore::Nat)": {
                rtype = this.typegen.getMIRType("NSCore::Nat");
                smte = this.processGenerateResultWithZeroArgCheck(sinfo, new SMTConst("BNat@zero"), args[1], rtype, new SMTCallSimple("bvurem", args));
                erropt = true;
                break;
            }
            case "NSCore::/=infix=(NSCore::BigInt, NSCore::BigInt)": {
                rtype = this.typegen.getMIRType("NSCore::BigInt");
                smte = this.processGenerateResultWithZeroArgCheck(sinfo, new SMTConst("BBigInt@zero"), args[1], rtype, new SMTCallSimple(this.vopts.BigXMode === "BV" ? "bvsrem" : "/", args));
                erropt = true;
                break;
            }
            case "NSCore::/=infix=(NSCore::BigNat, NSCore::BigNat)": {
                rtype = this.typegen.getMIRType("NSCore::BigNat");
                smte = this.processGenerateResultWithZeroArgCheck(sinfo, new SMTConst("BBigNat@zero"), args[1], rtype, new SMTCallSimple(this.vopts.BigXMode === "BV" ? "bvurem" : "/", args));
                erropt = true;
                break
            }
            case "NSCore::/=infix=(NSCore::Rational, NSCore::Rational)": {
                rtype = this.typegen.getMIRType("NSCore::Rational");
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BRationalBinary_UF", [new SMTConst("\"op_binary_div\""), ...args]) : this.processGenerateResultWithZeroArgCheck(sinfo, new SMTConst("BRational@zero"), args[1], rtype, new SMTCallSimple("/", args));
                erropt = true;
                break;
            }
            case "NSCore::/=infix=(NSCore::Float, NSCore::Float)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BFloatBinary_UF", [new SMTConst("\"op_binary_div\""), ...args]) : new SMTCallSimple("/", args);
                break;
            }
            case "NSCore::/=infix=(NSCore::Decimal, NSCore::Decimal)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BDecimalBinary_UF", [new SMTConst("\"op_binary_div\""), ...args]) : new SMTCallSimple("/", args);
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
            case "NSCore::!==infix=(NSCore::Int, NSCore::Int)":
            case "NSCore::!==infix=(NSCore::Nat, NSCore::Nat)":
            case "NSCore::!==infix=(NSCore::BigInt, NSCore::BigInt)":
            case "NSCore::!==infix=(NSCore::BigNat, NSCore::BigNat)":
            case "NSCore::!==infix=(NSCore::Rational, NSCore::Rational)": {
                smte = new SMTCallSimple("not", [new SMTCallSimple("=", args)]);
                break;
            }
            //op infix <
            case "NSCore::<=infix=(NSCore::Int, NSCore::Int)": {
                smte = new SMTCallSimple("bvslt", args);
                break;
            }
            case "NSCore::<=infix=(NSCore::Nat, NSCore::Nat)": {
                smte = new SMTCallSimple("bvult", args);
                break;
            }
            case "NSCore::<=infix=(NSCore::BigInt, NSCore::BigInt)": {
                smte = (this.vopts.BigXMode === "BV") ? new SMTCallSimple("bvslt", args) : new SMTCallSimple("<", args);
                break;
            }
            case "NSCore::<=infix=(NSCore::BigNat, NSCore::BigNat)": {
                smte = (this.vopts.BigXMode === "BV") ? new SMTCallSimple("bvult", args) : new SMTCallSimple("<", args);
                break;
            }
            case "NSCore::<=infix=(NSCore::Rational, NSCore::Rational)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BRationalBinaryPred_UF", [new SMTConst("\"op_binary_lt\""), ...args]) : new SMTCallSimple("<", args);
                break;
            }
            case "NSCore::<=infix=(NSCore::Float, NSCore::Float)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BFloatBinaryPred_UF", [new SMTConst("\"op_binary_lt\""), ...args]) : new SMTCallSimple("<", args);
                break;
            }
            case "NSCore::<=infix=(NSCore::Decimal, NSCore::Decimal)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BDecimalBinaryPred_UF", [new SMTConst("\"op_binary_lt\""), ...args]) : new SMTCallSimple("<", args);
                break;
            }
            //op infix >
            case "NSCore::>=infix=(NSCore::Int, NSCore::Int)": {
                smte = new SMTCallSimple("bvsgt", args);
                break;
            }
            case "NSCore::>=infix=(NSCore::Nat, NSCore::Nat)": {
                smte = new SMTCallSimple("bvugt", args);
                break;
            }
            case "NSCore::>=infix=(NSCore::BigInt, NSCore::BigInt)": {
                smte = (this.vopts.BigXMode === "BV") ? new SMTCallSimple("bvsgt", args) : new SMTCallSimple(">", args);
                break;
            }
            case "NSCore::>=infix=(NSCore::BigNat, NSCore::BigNat)": {
                smte = (this.vopts.BigXMode === "BV") ? new SMTCallSimple("bvugt", args) : new SMTCallSimple(">", args);
                break;
            }
            case "NSCore::>=infix=(NSCore::Rational, NSCore::Rational)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BRationalBinaryPred_UF", [new SMTConst("\"op_binary_gt\""), ...args]) : new SMTCallSimple(">", args);
                break;
            }
            case "NSCore::>=infix=(NSCore::Float, NSCore::Float)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BFloatBinaryPred_UF", [new SMTConst("\"op_binary_gt\""), ...args]) : new SMTCallSimple(">", args);
                break;
            }
            case "NSCore::>=infix=(NSCore::Decimal, NSCore::Decimal)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BDecimalBinaryPred_UF", [new SMTConst("\"op_binary_gt\""), ...args]) : new SMTCallSimple(">", args);
                break;
            }
            //op infix <=
            case "NSCore::<==infix=(NSCore::Int, NSCore::Int)": {
                smte = new SMTCallSimple("bvsle", args);
                break;
            }
            case "NSCore::<==infix=(NSCore::Nat, NSCore::Nat)": {
                smte = new SMTCallSimple("bvule", args);
                break;
            }
            case "NSCore::<==infix=(NSCore::BigInt, NSCore::BigInt)":  {
                smte = (this.vopts.BigXMode === "BV") ? new SMTCallSimple("bvsle", args) : new SMTCallSimple("<=", args);
                break;
            }
            case "NSCore::<==infix=(NSCore::BigNat, NSCore::BigNat)": {
                smte = (this.vopts.BigXMode === "BV") ? new SMTCallSimple("bvule", args) : new SMTCallSimple("<=", args);
                break;
            }
            case "NSCore::<==infix=(NSCore::Rational, NSCore::Rational)": {
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BRationalBinaryPred_UF", [new SMTConst("\"op_binary_lte\""), ...args]) : new SMTCallSimple("<=", args);
                break;
            }
            //op infix >=
            case "NSCore::>==infix=(NSCore::Int, NSCore::Int)": {
                smte = new SMTCallSimple("bvsge", args);
                break;
            }
            case "NSCore::>==infix=(NSCore::Nat, NSCore::Nat)": {
                smte = new SMTCallSimple("bvuge", args);
                break;
            }
            case "NSCore::>==infix=(NSCore::BigInt, NSCore::BigInt)": {
                smte = (this.vopts.BigXMode === "BV") ? new SMTCallSimple("bvsge", args) : new SMTCallSimple(">=", args);
                break;
            }
            case "NSCore::>==infix=(NSCore::BigNat, NSCore::BigNat)": {
                smte = (this.vopts.BigXMode === "BV") ? new SMTCallSimple("bvuge", args) : new SMTCallSimple(">=", args);
                break;
            }
            case "NSCore::>==infix=(NSCore::Rational, NSCore::Rational)":{
                smte = (this.vopts.FPOpt === "UF") ? new SMTCallSimple("BRationalBinaryPred_UF", [new SMTConst("\"op_binary_gte\""), ...args]) : new SMTCallSimple(">=", args);
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

    generateSMTInvoke(idecl: MIRInvokeDecl, cscc: Set<string>, gas: number | undefined, gasdown: number | undefined): SMTFunction | SMTFunctionUninterpreted | undefined {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.getMIRType(idecl.resultType);
        this.currentSCC = cscc;

        //
        //TODO: handle gas for recursive calls!!!
        //

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

            if (idecl.masksize === 0) {
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, restype, body);
            }
            else {
                return SMTFunction.createWithMask(this.typegen.mangle(idecl.key), args, this.typegen.mangle("#maskparam#"), idecl.masksize, restype, body);
            }
        }
        else {
            assert(idecl instanceof MIRInvokePrimitiveDecl);

            return this.generateBuiltinFunction(idecl as MIRInvokePrimitiveDecl);
        }
    }

    generateBuiltinFunction(idecl: MIRInvokePrimitiveDecl): SMTFunction | SMTFunctionUninterpreted | undefined {
        const args = idecl.params.map((arg) => {
            return { vname: this.varStringToSMT(arg.name).vname, vtype: this.typegen.getSMTTypeFor(this.typegen.getMIRType(arg.type)) };
        });

        const issafe = this.isSafeInvoke(idecl.key);
        const encltypekey = idecl.enclosingDecl !== undefined ? idecl.enclosingDecl : "NSCore::None";

        const mirrestype = this.typegen.getMIRType(idecl.resultType);
        const smtrestype = this.typegen.getSMTTypeFor(mirrestype);

        const chkrestype = issafe ? smtrestype : this.typegen.generateResultType(mirrestype);

        switch(idecl.implkey) {
            case "default": {
                return undefined;
            }
            case "validator_accepts": {
                const bsqre = this.assembly.validatorRegexs.get(encltypekey) as BSQRegex;
                const lre = bsqre.compileToSMTValidator(this.vopts.StringOpt === "ASCII");

                let accept: SMTExp = new SMTConst("false");
                if (this.vopts.StringOpt === "ASCII") {
                    accept = new SMTCallSimple("str.in.re", [new SMTVar(args[0].vname), new SMTConst(lre)]);
                }
                else {
                    accept = new SMTCallSimple("seq.in.re", [new SMTVar(args[0].vname), new SMTConst(lre)]);
                }

                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, accept);
            }
            case "string_empty": {
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, new SMTCallSimple("=", [new SMTCallSimple("str.len", [new SMTVar(args[0].vname)]), new SMTConst("0")]));
            }
            case "string_append": {
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, new SMTCallSimple("str.++", [new SMTVar(args[0].vname), new SMTVar(args[1].vname)]));
            }
            case "list_fill": {
                const [count, value] = args.map((arg) => new SMTVar(arg.vname));
                const fbody = this.lopsManager.processFillOperation(this.typegen.getMIRType(encltypekey), count, value);
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, fbody);
            }
            case "list_rangeofint": {
                const [low, high, count] = args.map((arg) => new SMTVar(arg.vname));
                const fbody = this.lopsManager.processRangeOfIntOperation(mirrestype, low, high, count);
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, fbody);
            }
            case "list_rangeofnat": {
                const [low, high, count] = args.map((arg) => new SMTVar(arg.vname));
                const fbody = this.lopsManager.processRangeOfNatOperation(mirrestype, low, high, count);
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, fbody);
            }
            case "list_safecheckpred": {
                const pcode = idecl.pcodes.get("p") as MIRPCode;
                const [l, count] = args.map((arg) => new SMTVar(arg.vname));
                const fbody = this.lopsManager.processSafePredCheck(this.typegen.getMIRType(encltypekey), pcode.code, pcode, l, count); 
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, fbody);
            }
            case "list_safecheckfn": {
                const pcode = idecl.pcodes.get("f") as MIRPCode;
                const pcrtype = this.typegen.getMIRType((this.assembly.invokeDecls.get(pcode.code) as MIRInvokeBodyDecl).resultType);
                const [l, count] = args.map((arg) => new SMTVar(arg.vname));
                const fbody = this.lopsManager.processSafeFnCheck(this.typegen.getMIRType(encltypekey), pcrtype, pcode.code, pcode, l, count); 
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, fbody);
            }
            case "list_computeisequence": {
                const pcode = idecl.pcodes.get("p") as MIRPCode;
                const [l, count] = args.map((arg) => new SMTVar(arg.vname));
                const fbody = this.lopsManager.processISequence(this.typegen.getMIRType(encltypekey), pcode.code, pcode, l, count); 
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, fbody);
            }
            case "list_hascheck": {
                const [l, count, val] = args.map((arg) => new SMTVar(arg.vname));
                const fbody = this.lopsManager.processHasCheck(this.typegen.getMIRType(encltypekey), l, count, val); 
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, fbody);
            }
            case "list_haspredcheck": {
                const pcode = idecl.pcodes.get("p") as MIRPCode;
                const [l, count] = args.map((arg) => new SMTVar(arg.vname));
                const fbody = this.lopsManager.processHasPredCheck(this.typegen.getMIRType(encltypekey), pcode.code, pcode, l, count); 
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, fbody);
            }
            case "list_size": {
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, this.lopsManager.generateListSizeCall(new SMTVar(args[0].vname), args[0].vtype));
            }
            case "list_empty": {
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, new SMTCallSimple("=", [new SMTConst("BNat@zero"), this.lopsManager.generateListSizeCall(new SMTVar(args[0].vname), args[0].vtype)]));
            }
            case "list_unsafe_get": {
                const [l, n] = args.map((arg) => new SMTVar(arg.vname));
                const fbody = this.lopsManager.processGet(this.typegen.getMIRType(encltypekey), l, n);
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, fbody);
            }
            case "list_fill": {
                const [n, v] = args.map((arg) => new SMTVar(arg.vname));
                const fbody = this.lopsManager.processFillOperation(this.typegen.getMIRType(encltypekey), n, v);
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, fbody);
            }
            case "list_concat2": {
                const [l1, l2, count] = args.map((arg) => new SMTVar(arg.vname));
                const fbody = this.lopsManager.processConcat2(mirrestype, l1, l2, count);
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, fbody);
            }
            case "list_findindexof_keyhelper": {
                const [l, count, val] = args.map((arg) => new SMTVar(arg.vname));
                const fbody = this.lopsManager.processIndexOf(this.typegen.getMIRType(encltypekey), l, count, val); 
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, fbody);
            }
            case "list_findindexoflast_keyhelper": {
                const [l, count, val] = args.map((arg) => new SMTVar(arg.vname));
                const fbody = this.lopsManager.processIndexOfLast(this.typegen.getMIRType(encltypekey), l, count, val); 
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, fbody);
            }
            case "list_findindexof_predicatehelper": {
                const pcode = idecl.pcodes.get("p") as MIRPCode;
                const [l, count] = args.map((arg) => new SMTVar(arg.vname));
                const fbody = this.lopsManager.processFindIndexOf(this.typegen.getMIRType(encltypekey), pcode.code, pcode, l, count); 
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, fbody);
            }
            case "list_findindexoflast_predicatehelper": {
                const pcode = idecl.pcodes.get("p") as MIRPCode;
                const [l, count] = args.map((arg) => new SMTVar(arg.vname));
                const fbody = this.lopsManager.processFindLastIndexOf(this.typegen.getMIRType(encltypekey), pcode.code, pcode, l, count); 
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, fbody);
            }
            case "list_countif_helper": {
                const pcode = idecl.pcodes.get("p") as MIRPCode;
                const [l, isq, count] = args.map((arg) => new SMTVar(arg.vname));
                const fbody = this.lopsManager.processCountIf(this.typegen.getMIRType(encltypekey), pcode.code, pcode, l, isq, count); 
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, fbody);
            }
            case "list_filter_helper": {
                const pcode = idecl.pcodes.get("p") as MIRPCode;
                const [l, isq, count] = args.map((arg) => new SMTVar(arg.vname));
                const fbody = this.lopsManager.processFilter(this.typegen.getMIRType(encltypekey), pcode.code, pcode, l, isq, count); 
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, fbody);
            }
            case "list_slice": {
                const [l1, start, end, count] = args.map((arg) => new SMTVar(arg.vname));
                const fbody = this.lopsManager.processSlice(mirrestype, l1, start, end, count);
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, fbody);
            }
            case "list_map": {
                const pcode = idecl.pcodes.get("f") as MIRPCode;
                const [l, count] = args.map((arg) => new SMTVar(arg.vname));
                const fbody = this.lopsManager.processMap(this.typegen.getMIRType(encltypekey), mirrestype, pcode.code, pcode, l, count);
                return SMTFunction.create(this.typegen.mangle(idecl.key), args, chkrestype, fbody);
            }
            default: {
                assert(false, `[NOT IMPLEMENTED -- ${idecl.implkey}]`);
                return undefined;
            }
        }
    }
}

export {
     ICPPBodyEmitter
};
