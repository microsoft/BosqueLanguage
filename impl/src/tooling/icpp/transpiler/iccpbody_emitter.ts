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
    private scalarStackMap: Map<string, number> = new Map<string, number>();
    private scalarStackSize: number = 0;
    private scalarStackLayout: {offset: number, name: string | undefined, storage: ICPPType}[] = [];
    private mixedStackMap: Map<string, number> = new Map<string, number>();
    private mixedStackSize: number = 0;
    private mixedStackLayout: {offset: number, name: string | undefined, storage: ICPPType}[] = [];

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
            if(this.scalarStackMap.has(vname)) {
                return ICPPOpEmitter.genLocalArgument(this.scalarStackMap.get(vname) as number);
            }
            else {
                return ICPPOpEmitter.genLocalArgument(this.mixedStackMap.get(vname) as number);
            }
        }
    }

    private getStackInfoForTargetVar(vname: string, oftype: ICPPType): TargetVar {
        if(oftype.allocinfo.isScalarOnlyInline()) {
            let openidx = this.scalarStackLayout.findIndex((opt) => opt.name === undefined && opt.storage.tkey === oftype.tkey);
            if (openidx === -1) {
                this.scalarStackLayout.push({ offset: this.scalarStackSize, name: vname, storage: oftype });
                this.scalarStackSize = this.scalarStackSize + oftype.allocinfo.inlinedatasize;

                openidx = this.scalarStackSize - 1;
            }

            const spos = this.scalarStackLayout[openidx];
            this.scalarStackMap.set(vname, spos.offset);
            spos.name = vname;

            return { offset: spos.offset };
        }
        else {
            let openidx = this.mixedStackLayout.findIndex((opt) => opt.name === undefined && opt.storage.tkey === oftype.tkey);
            if (openidx === -1) {
                this.mixedStackLayout.push({ offset: this.mixedStackSize, name: vname, storage: oftype });
                this.mixedStackSize = this.mixedStackSize + oftype.allocinfo.inlinedatasize;

                openidx = this.mixedStackSize - 1;
            }

            const spos = this.mixedStackLayout[openidx];
            this.mixedStackMap.set(vname, spos.offset);
            spos.name = vname;

            return { offset: spos.offset };
        }
    }

    private releaseStackSlotForVar(vname: string) {
        const spos = this.scalarStackLayout.find((opt) => opt.name === vname);
        if(spos !== undefined) {
            spos.name = undefined;
        }

        const mpos = this.mixedStackLayout.find((opt) => opt.name === vname);
        if(mpos !== undefined) {
            mpos.name = undefined;
        } 
    }

    private generateScratchVarInfo(oftype: ICPPType): [TargetVar, Argument] {
        if (oftype.allocinfo.isScalarOnlyInline()) {
            let openidx = this.scalarStackLayout.findIndex((opt) => opt.name === undefined && opt.storage.tkey === oftype.tkey);
            if (openidx === -1) {
                this.scalarStackLayout.push({ offset: this.scalarStackSize, name: undefined, storage: oftype });
                this.scalarStackSize = this.scalarStackSize + oftype.allocinfo.inlinedatasize;

                openidx = this.scalarStackSize - 1;
            }

            const spos = this.scalarStackLayout[openidx];
            spos.name = `@scalar_scratch_${openidx}`;

            return [{ offset: spos.offset }, ICPPOpEmitter.genLocalArgument(spos.offset)];
        }
        else {
            let openidx = this.mixedStackLayout.findIndex((opt) => opt.name === undefined && opt.storage.tkey === oftype.tkey);
            if (openidx === -1) {
                this.mixedStackLayout.push({ offset: this.mixedStackSize, name: undefined, storage: oftype });
                this.mixedStackSize = this.mixedStackSize + oftype.allocinfo.inlinedatasize;

                openidx = this.mixedStackSize - 1;
            }

            const spos = this.mixedStackLayout[openidx];
            spos.name = `@mixed_scratch_${openidx}`;

            return [{ offset: spos.offset }, ICPPOpEmitter.genLocalArgument(spos.offset)];
        }
    }

    private genMaskForStack(): RefMask {
        let mask: RefMask = "";
        for(let i = 0; i < this.mixedStackLayout.length; ++i) {
            mask = mask + this.mixedStackLayout[i].storage.allocinfo.inlinedmask;
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

        const rt = this.getStackInfoForTargetVar("$$return", this.typegen.getICPPTypeData(this.typegen.getMIRType(geninfo.resulttype.trkey)));
        ops.push(ICPPOpEmitter.genConstructorEphemeralListOp(sinfo, rt, geninfo.resulttype.trkey, pargs));
        
        return new ICPPInvokeBodyDecl(name, name, "[GENERATED]", sinfo, false, params, rtype, this.scalarStackSize, this.mixedStackSize, this.genMaskForStack(), 0, ops, 0);
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

        const rt = this.getStackInfoForTargetVar("$$return", this.typegen.getICPPTypeData(this.typegen.getMIRType(geninfo.resulttype.trkey)));
        ops.push(ICPPOpEmitter.genConstructorEphemeralListOp(sinfo, rt, geninfo.resulttype.trkey, pargs));
        
        return new ICPPInvokeBodyDecl(name, name, "[GENERATED]", sinfo, false, params, rtype, this.scalarStackSize, this.mixedStackSize, this.genMaskForStack(), 0, ops, 0);
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

        const rt = this.getStackInfoForTargetVar("$$return", this.typegen.getICPPTypeData(this.typegen.getMIRType(geninfo.resulttype.trkey)));
        ops.push(ICPPOpEmitter.genConstructorEphemeralListOp(sinfo, rt, geninfo.resulttype.trkey, pargs));
        
        return new ICPPInvokeBodyDecl(name, name, "[GENERATED]", sinfo, false, params, rtype, this.scalarStackSize, this.mixedStackSize, this.genMaskForStack(), 0, ops, 0);
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
            return ICPPOpEmitter.genVarGuard(this.scalarStackMap.get(gg.greg.nameID) as number);
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
            return ICPPOpEmitter.genTypeIsNoneOp(sinfo, this.trgtToICPPTargetLocation(trgt, "NSCore::Bool"), this.argToICPPLocation(arg), argtype.trkey, ICPPOpEmitter.genNoStatmentGuard());
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
            return ICPPOpEmitter.genTypeIsSomeOp(sinfo, this.trgtToICPPTargetLocation(trgt, "NSCore::Bool"), this.argToICPPLocation(arg), argtype.trkey, ICPPOpEmitter.genNoStatmentGuard());
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
        const mirlhsflow = this.typegen.getMIRType(op.lhsflowtype);
        const mirrhsflow = this.typegen.getMIRType(op.rhsflowtype);

        const mirlhslayout = this.typegen.getMIRType(op.lhslayouttype);
        const mirrhslayout = this.typegen.getMIRType(op.rhslayouttype);

        if(mirlhsflow.trkey === mirrhsflow.trkey && this.typegen.isUniqueType(mirlhsflow) && this.typegen.isUniqueType(mirrhsflow)) {
            if(this.typegen.isUniqueType(mirlhslayout) && this.typegen.isUniqueType(mirrhslayout)) {
                return ICPPOpEmitter.genBinKeyEqFastOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "NSCore::Bool"), mirlhsflow.trkey, this.argToICPPLocation(op.lhs), this.argToICPPLocation(op.rhs));
            }
            else {
                return ICPPOpEmitter.genBinKeyEqStaticOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "NSCore::Bool"), mirlhsflow.trkey, this.argToICPPLocation(op.lhs), mirlhslayout.trkey, this.argToICPPLocation(op.rhs), mirrhslayout.trkey);
            }
        }
        else {
            return ICPPOpEmitter.genBinKeyEqVirtualOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "NSCore::Bool"), this.argToICPPLocation(op.lhs), mirlhslayout.trkey, this.argToICPPLocation(op.rhs), mirrhslayout.trkey);
        }
    }

    processBinKeyLess(op: MIRBinKeyLess): ICPPOp {
        const mirlhsflow = this.typegen.getMIRType(op.lhsflowtype);
        const mirrhsflow = this.typegen.getMIRType(op.rhsflowtype);

        const mirlhslayout = this.typegen.getMIRType(op.lhslayouttype);
        const mirrhslayout = this.typegen.getMIRType(op.rhslayouttype);

        if(mirlhsflow.trkey === mirrhsflow.trkey && this.typegen.isUniqueType(mirlhsflow) && this.typegen.isUniqueType(mirrhsflow)) {
            if(this.typegen.isUniqueType(mirlhslayout) && this.typegen.isUniqueType(mirrhslayout)) {
                return ICPPOpEmitter.genBinKeyLessFastOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "NSCore::Bool"), mirlhsflow.trkey, this.argToICPPLocation(op.lhs), this.argToICPPLocation(op.rhs));
            }
            else {
                return ICPPOpEmitter.genBinKeyLessStaticOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "NSCore::Bool"), mirlhsflow.trkey, this.argToICPPLocation(op.lhs), mirlhslayout.trkey, this.argToICPPLocation(op.rhs), mirrhslayout.trkey);
            }
        }
        else {
            return ICPPOpEmitter.genBinKeyLessVirtualOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "NSCore::Bool"), this.argToICPPLocation(op.lhs), mirlhslayout.trkey, this.argToICPPLocation(op.rhs), mirrhslayout.trkey);
        }
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

        const sguard = this.generateStatmentGuardInfo(op.sguard);
        if(this.assembly.subtypeOf(flow, oftype)) {
            return ICPPOpEmitter.genDirectAssignOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "NSCore::Bool"), "NSCore::Bool", this.getSpecialLiteralValue("true"), sguard);
        }
        else if(this.typegen.isType(oftype, "NSCore::None")) {
            return ICPPOpEmitter.genTypeIsNoneOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "NSCore::Bool"), this.argToICPPLocation(op.arg), layout.trkey, sguard);
        }
        else if (this.typegen.isType(oftype, "NSCore::Some")) {
            return ICPPOpEmitter.genTypeIsSomeOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "NSCore::Bool"), this.argToICPPLocation(op.arg), layout.trkey, sguard);
        }
        else {
            if(this.typegen.isUniqueType(oftype)) {
                return ICPPOpEmitter.genTypeTagIsOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "NSCore::Bool"), oftype.trkey, this.argToICPPLocation(op.arg), layout.trkey, sguard);
            }
            else {
                return ICPPOpEmitter.genTypeTagSubtypeOfOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "NSCore::Bool"), oftype.trkey, this.argToICPPLocation(op.arg), layout.trkey, sguard);
            }
        }
    }

    processRegisterAssign(op: MIRRegisterAssign): ICPPOp {
        return ICPPOpEmitter.genRegisterAssignOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.layouttype), this.argToICPPLocation(op.src), op.layouttype, this.generateStatmentGuardInfo(op.sguard));
    }

    processReturnAssign(op: MIRReturnAssign): ICPPOp {
        return ICPPOpEmitter.genReturnAssignOp(op.sinfo, this.trgtToICPPTargetLocation(op.name, op.oftype), this.argToICPPLocation(op.src), op.oftype);
    }

    processReturnAssignOfCons(op: MIRReturnAssignOfCons): ICPPOp {
        return ICPPOpEmitter.genReturnAssignOfConsOp(op.sinfo,  this.trgtToICPPTargetLocation(op.name, op.oftype), op.args.map((arg) => this.argToICPPLocation(arg)), op.oftype);
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
                return this.processAssertCheck(op as MIRAssertCheck);
            }
            case MIROpTag.MIRLoadUnintVariableValue: {
                return this.processLoadUnintVariableValue(op as MIRLoadUnintVariableValue);
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
                return this.processConvertValue(op as MIRConvertValue);
            }
            case MIROpTag.MIRLoadConst: {
                return this.processLoadConst(op as MIRLoadConst);
            }
            case MIROpTag.MIRTupleHasIndex: {
                return this.processTupleHasIndex(op as MIRTupleHasIndex);
            }
            case MIROpTag.MIRRecordHasProperty: {
                return this.processRecordHasProperty(op as MIRRecordHasProperty);
            }
            case MIROpTag.MIRLoadTupleIndex: {
                return this.processLoadTupleIndex(op as MIRLoadTupleIndex);
            }
            case MIROpTag.MIRLoadTupleIndexSetGuard: {
                return this.processLoadTupleIndexSetGuard(op as MIRLoadTupleIndexSetGuard);
            }
            case MIROpTag.MIRLoadRecordProperty: {
                return this.processLoadRecordProperty(op as MIRLoadRecordProperty);
            }
            case MIROpTag.MIRLoadRecordPropertySetGuard: {
                return this.processLoadRecordPropertySetGuard(op as MIRLoadRecordPropertySetGuard);
            }
            case MIROpTag.MIRLoadField: {
                return this.processLoadField(op as MIRLoadField);
            }
            case MIROpTag.MIRTupleProjectToEphemeral: {
                return this.processTupleProjectToEphemeral(op as MIRTupleProjectToEphemeral);
            }
            case MIROpTag.MIRRecordProjectToEphemeral: {
                return this.processRecordProjectToEphemeral(op as MIRRecordProjectToEphemeral);
            }
            case MIROpTag.MIREntityProjectToEphemeral: {
                return this.processEntityProjectToEphemeral(op as MIREntityProjectToEphemeral);
            }
            case MIROpTag.MIRTupleUpdate: {
                return this.processTupleUpdate(op as MIRTupleUpdate);
            }
            case MIROpTag.MIRRecordUpdate: {
                return this.processRecordUpdate(op as MIRRecordUpdate);
            }
            case MIROpTag.MIREntityUpdate: {
                return this.processEntityUpdate(op as MIREntityUpdate);
            }
            case MIROpTag.MIRLoadFromEpehmeralList: {
                return this.processLoadFromEpehmeralList(op as MIRLoadFromEpehmeralList);
            }
            case MIROpTag.MIRMultiLoadFromEpehmeralList: {
                return this.processMultiLoadFromEpehmeralList(op as MIRMultiLoadFromEpehmeralList);
            }
            case MIROpTag.MIRSliceEpehmeralList: {
                return this.processSliceEpehmeralList(op as MIRSliceEpehmeralList);
            }
            case MIROpTag.MIRInvokeFixedFunction: {
                return this.processInvokeFixedFunction(op as MIRInvokeFixedFunction);
            }
            case MIROpTag.MIRInvokeVirtualFunction: {
                return this.processInvokeVirtualFunction(op as MIRInvokeVirtualFunction);
            }
            case MIROpTag.MIRInvokeVirtualOperator: {
                return this.processInvokeVirtualOperator(op as MIRInvokeVirtualOperator);
            }
            case MIROpTag.MIRConstructorTuple: {
                return this.processConstructorTuple(op as MIRConstructorTuple);
            }
            case MIROpTag.MIRConstructorTupleFromEphemeralList: {
                return this.processConstructorTupleFromEphemeralList(op as MIRConstructorTupleFromEphemeralList);
            }
            case MIROpTag.MIRConstructorRecord: {
                return this.processConstructorRecord(op as MIRConstructorRecord);
            }
            case MIROpTag.MIRConstructorRecordFromEphemeralList: {
                return this.processConstructorRecordFromEphemeralList(op as MIRConstructorRecordFromEphemeralList);
            }
            case MIROpTag.MIRStructuredAppendTuple: {
                return this.processStructuredAppendTuple(op as MIRStructuredAppendTuple);
            }
            case MIROpTag.MIRStructuredJoinRecord: {
                return this.processStructuredJoinRecord(op as MIRStructuredJoinRecord);
            }
            case MIROpTag.MIRConstructorEphemeralList: {
                return this.processConstructorEphemeralList(op as MIRConstructorEphemeralList);
            }
            case MIROpTag.MIREphemeralListExtend: {
                return this.processEphemeralListExtend(op as MIREphemeralListExtend);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
                return this.processConstructorPrimaryCollectionEmpty(op as MIRConstructorPrimaryCollectionEmpty);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                return this.processConstructorPrimaryCollectionSingletons(op as MIRConstructorPrimaryCollectionSingletons);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
                return this.processConstructorPrimaryCollectionCopies(op as MIRConstructorPrimaryCollectionCopies);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                return this.processConstructorPrimaryCollectionMixed(op as MIRConstructorPrimaryCollectionMixed);
            }
            case MIROpTag.MIRBinKeyEq: {
                return this.processBinKeyEq(op as MIRBinKeyEq);
            }
            case MIROpTag.MIRBinKeyLess: {
                return this.processBinKeyLess(op as MIRBinKeyLess);
            }
            case MIROpTag.MIRPrefixNotOp: {
                return this.processPrefixNotOp(op as MIRPrefixNotOp);
            }
            case MIROpTag.MIRAllTrue: {
                return this.processAllTrue(op as MIRAllTrue);
            }
            case MIROpTag.MIRSomeTrue: {
                return this.processSomeTrue(op as MIRSomeTrue);
            }
            case MIROpTag.MIRIsTypeOf: {
                return this.processIsTypeOf(op as MIRIsTypeOf);
            }
            case MIROpTag.MIRRegisterAssign: {
                return this.processRegisterAssign(op as MIRRegisterAssign);
            }
            case MIROpTag.MIRReturnAssign: {
                return this.processReturnAssign(op as MIRReturnAssign);
            }
            case MIROpTag.MIRReturnAssignOfCons: {
                return this.processReturnAssignOfCons(op as MIRReturnAssignOfCons);
            }
            default: {
                assert(false, "Should be eliminated elsewhere");
                return undefined;
            }
        }
    }

    processDefaultOperatorInvokePrimitiveType(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey, op: MIRInvokeKey, args: Argument[], argtypes: MIRResolvedTypeKey): ICPPOp {
        switch (op) {
            //op unary +
            case "NSCore::+=prefix=(NSCore::Int)":
            case "NSCore::+=prefix=(NSCore::Nat)":
            case "NSCore::+=prefix=(NSCore::BigInt)":
            case "NSCore::+=prefix=(NSCore::BigNat)":
            case "NSCore::+=prefix=(NSCore::Rational)":
            case "NSCore::+=prefix=(NSCore::Float)":
            case "NSCore::+=prefix=(NSCore::Decimal)": {
                return ICPPOpEmitter.genDirectAssignOp(sinfo, trgt, oftype, args[0], ICPPOpEmitter.genNoStatmentGuard());
            }
            //op unary -
            case "NSCore::-=prefix=(NSCore::Int)": {
                return ICPPOpEmitter.genNegateOp(sinfo, OpCodeTag.NegateIntOp, trgt, oftype, args[0]);
            }
            case "NSCore::-=prefix=(NSCore::BigInt)": {
                return ICPPOpEmitter.genNegateOp(sinfo, OpCodeTag.NegateBigIntOp, trgt, oftype, args[0]);
            }
            case "NSCore::-=prefix=(NSCore::Rational)": {
                return ICPPOpEmitter.genNegateOp(sinfo, OpCodeTag.NegateRationalOp, trgt, oftype, args[0]);
            }
            case "NSCore::-=prefix=(NSCore::Float)": {
                return ICPPOpEmitter.genNegateOp(sinfo, OpCodeTag.NegateFloatOp, trgt, oftype, args[0]);
            }
            case "NSCore::-=prefix=(NSCore::Decimal)": {
                return ICPPOpEmitter.genNegateOp(sinfo, OpCodeTag.NegateDecimalOp, trgt, oftype, args[0]);
            }
            //op infix +
            case "NSCore::+=infix=(NSCore::Int, NSCore::Int)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.AddIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::+=infix=(NSCore::Nat, NSCore::Nat)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.AddNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::+=infix=(NSCore::BigInt, NSCore::BigInt)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.AddBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::+=infix=(NSCore::BigNat, NSCore::BigNat)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.AddBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::+=infix=(NSCore::Rational, NSCore::Rational)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.AddRationalOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::+=infix=(NSCore::Float, NSCore::Float)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.AddFloatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::+=infix=(NSCore::Decimal, NSCore::Decimal)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.AddDecimalOp, trgt, oftype, args[0], args[1]);
            }
            //op infix -
            case "NSCore::-=infix=(NSCore::Int, NSCore::Int)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.SubIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::-=infix=(NSCore::Nat, NSCore::Nat)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.SubNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::-=infix=(NSCore::BigInt, NSCore::BigInt)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.SubBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::-=infix=(NSCore::BigNat, NSCore::BigNat)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.SubBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::-=infix=(NSCore::Rational, NSCore::Rational)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.SubRationalOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::-=infix=(NSCore::Float, NSCore::Float)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.SubFloatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::-=infix=(NSCore::Decimal, NSCore::Decimal)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.SubDecimalOp, trgt, oftype, args[0], args[1]);
            }
            //op infix *
            case "NSCore::*=infix=(NSCore::Int, NSCore::Int)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.MultIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::*=infix=(NSCore::Nat, NSCore::Nat)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.MultNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::*=infix=(NSCore::BigInt, NSCore::BigInt)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.MultBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::*=infix=(NSCore::BigNat, NSCore::BigNat)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.MultBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::*=infix=(NSCore::Rational, NSCore::Rational)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.MultRationalOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::*=infix=(NSCore::Float, NSCore::Float)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.MultFloatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::*=infix=(NSCore::Decimal, NSCore::Decimal)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.MultDecimalOp, trgt, oftype, args[0], args[1]);
            }
            //op infix /
            case "NSCore::/=infix=(NSCore::Int, NSCore::Int)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.DivIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::/=infix=(NSCore::Nat, NSCore::Nat)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.DivNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::/=infix=(NSCore::BigInt, NSCore::BigInt)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.DivBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::/=infix=(NSCore::BigNat, NSCore::BigNat)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.DivBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::/=infix=(NSCore::Rational, NSCore::Rational)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.DivRationalOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::/=infix=(NSCore::Float, NSCore::Float)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.DivFloatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::/=infix=(NSCore::Decimal, NSCore::Decimal)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.DivDecimalOp, trgt, oftype, args[0], args[1]);
            }
            //op infix ==
            case "NSCore::===infix=(NSCore::Int, NSCore::Int)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.EqIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::===infix=(NSCore::Nat, NSCore::Nat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.EqNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::===infix=(NSCore::BigInt, NSCore::BigInt)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.EqBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::===infix=(NSCore::BigNat, NSCore::BigNat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.EqBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::===infix=(NSCore::Rational, NSCore::Rational)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.EqRationalOp, trgt, oftype, args[0], args[1]);
            }
            //op infix !=
            case "NSCore::!==infix=(NSCore::Int, NSCore::Int)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.NeqIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::!==infix=(NSCore::Nat, NSCore::Nat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.NeqNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::!==infix=(NSCore::BigInt, NSCore::BigInt)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.NeqBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::!==infix=(NSCore::BigNat, NSCore::BigNat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.NeqBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::!==infix=(NSCore::Rational, NSCore::Rational)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.NeqRationalOp, trgt, oftype, args[0], args[1]);
            }
            //op infix <
            case "NSCore::<=infix=(NSCore::Int, NSCore::Int)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LtIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::<=infix=(NSCore::Nat, NSCore::Nat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LtNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::<=infix=(NSCore::BigInt, NSCore::BigInt)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LtBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::<=infix=(NSCore::BigNat, NSCore::BigNat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LtBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::<=infix=(NSCore::Rational, NSCore::Rational)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LtRationalOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::<=infix=(NSCore::Float, NSCore::Float)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LtFloatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::<=infix=(NSCore::Decimal, NSCore::Decimal)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LtDecimalOp, trgt, oftype, args[0], args[1]);
            }
            //op infix >
            case "NSCore::>=infix=(NSCore::Int, NSCore::Int)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GtIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::>=infix=(NSCore::Nat, NSCore::Nat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GtNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::>=infix=(NSCore::BigInt, NSCore::BigInt)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GtBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::>=infix=(NSCore::BigNat, NSCore::BigNat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GtBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::>=infix=(NSCore::Rational, NSCore::Rational)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GtRationalOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::>=infix=(NSCore::Float, NSCore::Float)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GtFloatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::>=infix=(NSCore::Decimal, NSCore::Decimal)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GtDecimalOp, trgt, oftype, args[0], args[1]);
            }
            //op infix <=
            case "NSCore::<==infix=(NSCore::Int, NSCore::Int)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LeIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::<==infix=(NSCore::Nat, NSCore::Nat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LeNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::<==infix=(NSCore::BigInt, NSCore::BigInt)":  {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LeBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::<==infix=(NSCore::BigNat, NSCore::BigNat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LeBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::<==infix=(NSCore::Rational, NSCore::Rational)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LeRationalOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::<==infix=(NSCore::Float, NSCore::Float)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LeFloatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::<==infix=(NSCore::Decimal, NSCore::Decimal)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LeDecimalOp, trgt, oftype, args[0], args[1]);
            }
            //op infix >=
            case "NSCore::>==infix=(NSCore::Int, NSCore::Int)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GeIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::>==infix=(NSCore::Nat, NSCore::Nat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GeNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::>==infix=(NSCore::BigInt, NSCore::BigInt)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GeBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::>==infix=(NSCore::BigNat, NSCore::BigNat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GeBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::>==infix=(NSCore::Rational, NSCore::Rational)":{
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GeRationalOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::>==infix=(NSCore::Float, NSCore::Float)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GeFloatOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::>==infix=(NSCore::Decimal, NSCore::Decimal)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GeDecimalOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::===infix=(NSCore::StringPos, NSCore::StringPos)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.EqStrPosOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::!==infix=(NSCore::StringPos, NSCore::StringPos)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.NeqStrPosOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::<=infix=(NSCore::StringPos, NSCore::StringPos)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LtStrPosOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::>=infix=(NSCore::StringPos, NSCore::StringPos)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GtStrPosOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::<==infix=(NSCore::StringPos, NSCore::StringPos)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LeStrPosOp, trgt, oftype, args[0], args[1]);
            }
            case "NSCore::>==infix=(NSCore::StringPos, NSCore::StringPos)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GeStrPosOp, trgt, oftype, args[0], args[1]);
            }
            default: {
                return NOT_IMPLEMENTED(op);
            }
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
