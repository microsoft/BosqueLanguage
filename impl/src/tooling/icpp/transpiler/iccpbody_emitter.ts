//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIREntityType, MIREphemeralListType, MIRFieldDecl, MIRInvokeBodyDecl, MIRInvokeDecl, MIRInvokePrimitiveDecl, MIRRecordType, MIRRecordTypeEntry, MIRTupleType, MIRType } from "../../../compiler/mir_assembly";
import { ICPPTypeEmitter } from "./icpptype_emitter";
import { MIRAbort, MIRArgGuard, MIRArgument, MIRAssertCheck, MIRBasicBlock, MIRBinKeyEq, MIRBinKeyLess, MIRConstantArgument, MIRConstantBigInt, MIRConstantBigNat, MIRConstantDataString, MIRConstantDecimal, MIRConstantFalse, MIRConstantFloat, MIRConstantInt, MIRConstantNat, MIRConstantNone, MIRConstantRational, MIRConstantRegex, MIRConstantString, MIRConstantStringOf, MIRConstantTrue, MIRConstantTypedNumber, MIRConstructorEphemeralList, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionMixed, MIRConstructorPrimaryCollectionSingletons, MIRConstructorRecord, MIRConstructorRecordFromEphemeralList, MIRConstructorTuple, MIRConstructorTupleFromEphemeralList, MIRConvertValue, MIRDeclareGuardFlagLocation, MIREntityProjectToEphemeral, MIREntityUpdate, MIREphemeralListExtend, MIRFieldKey, MIRGlobalKey, MIRGlobalVariable, MIRGuard, MIRInvokeFixedFunction, MIRInvokeKey, MIRInvokeVirtualFunction, MIRInvokeVirtualOperator, MIRIsTypeOf, MIRJump, MIRJumpCond, MIRJumpNone, MIRLoadConst, MIRLoadField, MIRLoadFromEpehmeralList, MIRLoadRecordProperty, MIRLoadRecordPropertySetGuard, MIRLoadTupleIndex, MIRLoadTupleIndexSetGuard, MIRLoadUnintVariableValue, MIRMaskGuard, MIRMultiLoadFromEpehmeralList, MIROp, MIROpTag, MIRPhi, MIRPrefixNotOp, MIRRecordHasProperty, MIRRecordProjectToEphemeral, MIRRecordUpdate, MIRRegisterArgument, MIRRegisterAssign, MIRResolvedTypeKey, MIRReturnAssign, MIRReturnAssignOfCons, MIRSetConstantGuardFlag, MIRSliceEpehmeralList, MIRStatmentGuard, MIRStructuredAppendTuple, MIRStructuredJoinRecord, MIRTupleHasIndex, MIRTupleProjectToEphemeral, MIRTupleUpdate } from "../../../compiler/mir_ops";
import { Argument, ArgumentTag, EMPTY_CONST_POSITION, ICPPGuard, ICPPOp, ICPPOpEmitter, ICPPStatementGuard, OpCodeTag, TargetVar } from "./icpp_exp";
import { SourceInfo } from "../../../ast/parser";
import { ICPPFunctionParameter, ICPPInvokeBodyDecl, ICPPInvokeDecl, ICPPInvokePrimitiveDecl, ICPPPCode, ICPPType, ICPPTypeEntity, ICPPTypeEphemeralList,  ICPPTypeRecord, ICPPTypeTuple, RefMask, TranspilerOptions, UNIVERSAL_SIZE } from "./icpp_assembly";

import * as assert from "assert";
import { topologicalOrder } from "../../../compiler/mir_info";

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
    private scalarStackLayout: {offset: number, name: string, storage: ICPPType}[] = [];
    private mixedStackMap: Map<string, number> = new Map<string, number>();
    private mixedStackSize: number = 0;
    private mixedStackLayout: {offset: number, name: string, storage: ICPPType}[] = [];

    literalMap: Map<string, number> = new Map<string, number>();
    constMap: Map<MIRGlobalKey, number> = new Map<MIRGlobalKey, number>();
    constsize: number = UNIVERSAL_SIZE;
    constlayout: {offset: number, storage: ICPPType, value: string, isliteral: boolean}[] = [];
    
    private maskMap: Map<string, number> = new Map<string, number>();
    private masksize: number = 0;
    private masklayout: {offset: number, occupied: boolean, name: string, size: number}[] = [];

    requiredProjectVirtualTupleIndex: { inv: string, argflowtype: MIRType, indecies: number[], resulttype: MIRType }[] = [];
    requiredProjectVirtualRecordProperty: { inv: string, argflowtype: MIRType, properties: string[], resulttype: MIRType }[] = [];
    requiredProjectVirtualEntityField: { inv: string, argflowtype: MIRType, fields: MIRFieldDecl[], resulttype: MIRType }[] = [];

    //
    //TODO: need to implement (and integrate) the code that generates these functions
    //
    requiredUpdateVirtualTuple: { inv: string, argflowtype: MIRType, updates: [number, MIRResolvedTypeKey][], resulttype: MIRType }[] = [];
    requiredUpdateVirtualRecord: { inv: string, argflowtype: MIRType, updates: [string, MIRResolvedTypeKey][], resulttype: MIRType }[] = [];
    requiredUpdateVirtualEntity: { inv: string, argflowtype: MIRType, updates: [MIRFieldKey, MIRResolvedTypeKey][], resulttype: MIRType }[] = [];

    //
    //TODO: need to implement (and integrate) the code that generates these functions
    //
    requiredTupleAppend: { inv: string, args: {layout: MIRType, flow: MIRType}[], resulttype: MIRType }[] = [];
    requiredRecordMerge: { inv: string, args: {layout: MIRType, flow: MIRType}[], resulttype: MIRType }[] = [];

    private getStackInfoForArgVar(vname: string): Argument {
        if(this.argsMap.has(vname)) {
            return ICPPOpEmitter.genParameterArgument(this.argsMap.get(vname) as number);
        }
        else {
            if(this.scalarStackMap.has(vname)) {
                return ICPPOpEmitter.genLocalScalarArgument(this.scalarStackMap.get(vname) as number);
            }
            else {
                return ICPPOpEmitter.genLocalMixedArgument(this.mixedStackMap.get(vname) as number);
            }
        }
    }

    private getStackInfoForTargetVar(vname: string, oftype: ICPPType): TargetVar {
        //
        //TODO: later we should make this an abstract index and do "register allocation" on the live ranges -- will also need to convert this to offsets at emit time (or something)
        //
        if(oftype.allocinfo.isScalarOnlyInline()) {
            const trgt = { kind: ArgumentTag.LocalScalar, offset: this.scalarStackSize };

            this.scalarStackLayout.push({ offset: this.scalarStackSize, name: vname, storage: oftype });
            this.scalarStackMap.set(vname, this.scalarStackSize);
            this.scalarStackSize = this.scalarStackSize + oftype.allocinfo.inlinedatasize;

            return trgt;
        }
        else {
            const trgt = { kind: ArgumentTag.LocalMixed, offset: this.mixedStackSize };

            this.mixedStackLayout.push({ offset: this.mixedStackSize, name: vname, storage: oftype });
            this.mixedStackMap.set(vname, this.mixedStackSize);
            this.mixedStackSize = this.mixedStackSize + oftype.allocinfo.inlinedatasize;

            return trgt;
        }
    }

    private generateScratchVarInfo(oftype: ICPPType): [TargetVar, Argument] {
        if (oftype.allocinfo.isScalarOnlyInline()) {
            const trgt = { kind: ArgumentTag.LocalScalar, offset: this.scalarStackSize };

            const vname = `@scalar_scratch_${this.scalarStackLayout.length}`;
            this.scalarStackLayout.push({ offset: this.scalarStackSize, name: vname, storage: oftype });
            this.scalarStackMap.set(vname, this.scalarStackSize);
            this.scalarStackSize = this.scalarStackSize + oftype.allocinfo.inlinedatasize;

            return [trgt, ICPPOpEmitter.genLocalScalarArgument(trgt.offset)];
        }
        else {
            const trgt = { kind: ArgumentTag.LocalMixed, offset: this.mixedStackSize };

            const vname = `@mixed_scratch_${this.mixedStackLayout.length}`;
            this.mixedStackLayout.push({ offset: this.mixedStackSize, name: vname, storage: oftype });
            this.mixedStackMap.set(vname, this.mixedStackSize);
            this.mixedStackSize = this.mixedStackSize + oftype.allocinfo.inlinedatasize;


            return [trgt, ICPPOpEmitter.genLocalMixedArgument(trgt.offset)];
        }
    }

    private generateStorageLocationForPhi(vname: MIRRegisterArgument, oftype: string) {
        this.trgtToICPPTargetLocation(vname, oftype);
    }

    private getStorageTargetForPhi(vname: MIRRegisterArgument): TargetVar {
        if(this.scalarStackMap.has(vname.nameID)) {
            return { kind: ArgumentTag.LocalScalar, offset: this.scalarStackMap.get(vname.nameID) as number };
        }
        else {
            return { kind: ArgumentTag.LocalMixed, offset:  this.mixedStackMap.get(vname.nameID) as number };
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
        
        return new ICPPInvokeBodyDecl(name, name, "[GENERATED]", sinfo, false, params, rtype, this.getStackInfoForArgVar("$$return"), this.scalarStackSize, this.mixedStackSize, this.genMaskForStack(), 0, ops, 0);
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
        
        return new ICPPInvokeBodyDecl(name, name, "[GENERATED]", sinfo, false, params, rtype, this.getStackInfoForArgVar("$$return"), this.scalarStackSize, this.mixedStackSize, this.genMaskForStack(), 0, ops, 0);
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
        
        return new ICPPInvokeBodyDecl(name, name, "[GENERATED]", sinfo, false, params, rtype, this.getStackInfoForArgVar("$$return"), this.scalarStackSize, this.mixedStackSize, this.genMaskForStack(), 0, ops, 0);
    }

    constructor(assembly: MIRAssembly, typegen: ICPPTypeEmitter, vopts: TranspilerOptions) {
        this.assembly = assembly;
        this.typegen = typegen;
       
        this.vopts = vopts;

        this.currentRType = typegen.getMIRType("None");

        this.constlayout.push({ offset: 0, storage: this.typegen.getICPPTypeData(this.typegen.getMIRType("None")), value: "None", isliteral: true });
        this.constsize = UNIVERSAL_SIZE;

        this.registerSpecialLiteralValue("none", "None");
        this.registerSpecialLiteralValue("true", "Bool");
        this.registerSpecialLiteralValue("false", "Bool");

        this.assembly.constantDecls.forEach((cdecl) => {
            const decltype = this.typegen.getICPPTypeData(this.typegen.getMIRType(cdecl.declaredType));
            this.constlayout.push({ offset: this.constsize, storage: decltype, value: cdecl.gkey, isliteral: false });

            this.constsize += decltype.allocinfo.inlinedatasize;
        });
    }

    initializeBodyGen(srcFile: string, rtype: MIRType, argsmap: Map<string, number>) {
        this.currentFile = srcFile;
        this.currentRType = rtype;

        this.argsMap = argsmap;
        this.scalarStackMap = new Map<string, number>();
        this.scalarStackSize = 0;
        this.scalarStackLayout = [];
        this.mixedStackMap = new Map<string, number>();
        this.mixedStackSize = 0;
        this.mixedStackLayout = [];
    
        this.maskMap = new Map<string, number>();
        this.masksize = 0;
        this.masklayout = [];
    }

    private registerSpecialLiteralValue(vlit: string, vtype: MIRResolvedTypeKey) {
        if (!this.literalMap.has(vlit)) {
            const ttype = this.typegen.getICPPTypeData(this.typegen.getMIRType(vtype));
            this.literalMap.set(vlit, this.constsize);
            this.constlayout.push({ offset: this.constsize, storage: ttype, value: vlit, isliteral: true });
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
            this.registerSpecialLiteralValue(cval.value, "Int");
            return this.getSpecialLiteralValue(cval.value);
        }
        else if (cval instanceof MIRConstantNat) {
            this.registerSpecialLiteralValue(cval.value, "Nat");
            return this.getSpecialLiteralValue(cval.value);
        }
        else if (cval instanceof MIRConstantBigInt) {
            this.registerSpecialLiteralValue(cval.value, "BigInt");
            return this.getSpecialLiteralValue(cval.value);
        }
        else if (cval instanceof MIRConstantBigNat) {
            this.registerSpecialLiteralValue(cval.value, "BigNat");
            return this.getSpecialLiteralValue(cval.value);
        }
        else if (cval instanceof MIRConstantRational) {
            this.registerSpecialLiteralValue(cval.value, "Rational");
            return this.getSpecialLiteralValue(cval.value);
        }
        else if (cval instanceof MIRConstantFloat) {
            this.registerSpecialLiteralValue(cval.value, "Float");
            return this.getSpecialLiteralValue(cval.value);
        }
        else if (cval instanceof MIRConstantDecimal) {
            this.registerSpecialLiteralValue(cval.value, "Decimal");
            return this.getSpecialLiteralValue(cval.value);
        }
        else if (cval instanceof MIRConstantString) {
            this.registerSpecialLiteralValue(cval.value, "String");
            return this.getSpecialLiteralValue(cval.value);
        }
        else if (cval instanceof MIRConstantTypedNumber) {
            return this.constantToICPP(cval.value);
        }
        else if (cval instanceof MIRConstantStringOf) {
            this.registerSpecialLiteralValue(cval.value, "String");
            return this.getSpecialLiteralValue(cval.value);
        }
        else if (cval instanceof MIRConstantDataString) {
            this.registerSpecialLiteralValue(cval.value, "String");
            return this.getSpecialLiteralValue(cval.value);
        }
        else {
            assert(cval instanceof MIRConstantRegex);

            const rval = (cval as MIRConstantRegex).value;
            this.registerSpecialLiteralValue(rval.restr, "Regex");
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
            if(mg.gmask === "@maskparam@") {
                return ICPPOpEmitter.genMaskGuard(mg.gindex, -1);
            }
            else {
                return ICPPOpEmitter.genMaskGuard(mg.gindex, this.maskMap.get(mg.gmask) as number);
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
        if (this.typegen.isType(argtype, "None")) {
            return ICPPOpEmitter.genDirectAssignOp(sinfo, this.trgtToICPPTargetLocation(trgt, "Bool"), "Bool", this.getSpecialLiteralValue("true"), ICPPOpEmitter.genNoStatmentGuard());
        }
        else if (!this.assembly.subtypeOf(this.typegen.getMIRType("None"), argtype)) {
            return ICPPOpEmitter.genDirectAssignOp(sinfo, this.trgtToICPPTargetLocation(trgt, "Bool"), "Bool", this.getSpecialLiteralValue("false"), ICPPOpEmitter.genNoStatmentGuard());
        }
        else {
            return ICPPOpEmitter.genTypeIsNoneOp(sinfo, this.trgtToICPPTargetLocation(trgt, "Bool"), this.argToICPPLocation(arg), argtype.trkey, ICPPOpEmitter.genNoStatmentGuard());
        }
    }

    generateSomeCheck(sinfo: SourceInfo, trgt: MIRRegisterArgument, arg: MIRArgument, argtype: MIRType): ICPPOp {
        if (this.typegen.isType(argtype, "None")) {
            return ICPPOpEmitter.genDirectAssignOp(sinfo, this.trgtToICPPTargetLocation(trgt, "Bool"), "Bool", this.getSpecialLiteralValue("false"), ICPPOpEmitter.genNoStatmentGuard());
        }
        else if (!this.assembly.subtypeOf(this.typegen.getMIRType("None"), argtype)) {
            return ICPPOpEmitter.genDirectAssignOp(sinfo, this.trgtToICPPTargetLocation(trgt, "Bool"), "Bool", this.getSpecialLiteralValue("true"), ICPPOpEmitter.genNoStatmentGuard());
        }
        else {
            return ICPPOpEmitter.genTypeIsSomeOp(sinfo, this.trgtToICPPTargetLocation(trgt, "Bool"), this.argToICPPLocation(arg), argtype.trkey, ICPPOpEmitter.genNoStatmentGuard());
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
        this.maskMap.set(op.name, minfo.offset);
    }

    processSetConstantGuardFlag(op: MIRSetConstantGuardFlag): ICPPOp {
        const minfo = this.masklayout.find((mloc) => mloc.name === op.name) as {offset: number, occupied: boolean, name: string, size: number};
        return ICPPOpEmitter.genStoreConstantMaskValueOp(op.sinfo, minfo.offset, op.position, op.flag);
    }

    processConvertValue(op: MIRConvertValue): ICPPOp {
        return this.typegen.coerce(op.sinfo, this.argToICPPLocation(op.src), this.typegen.getMIRType(op.srctypelayout), this.trgtToICPPTargetLocation(op.trgt, op.intotype), this.typegen.getMIRType(op.intotype), this.generateStatmentGuardInfo(op.sguard));
    }

    processLoadConst(op: MIRLoadConst): ICPPOp {
        return ICPPOpEmitter.genLoadConstOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.consttype), this.argToICPPLocation(op.src), op.consttype);
    }

    processTupleHasIndex(op: MIRTupleHasIndex): ICPPOp {
        return ICPPOpEmitter.genTupleHasIndexOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "Bool"), this.argToICPPLocation(op.arg), op.arglayouttype, op.idx);
    }

    processRecordHasProperty(op: MIRRecordHasProperty): ICPPOp {
        return ICPPOpEmitter.genRecordHasPropertyOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "Bool"), this.argToICPPLocation(op.arg), op.arglayouttype, op.pname);
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
            
            return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.epht), op.epht, icall, op.arglayouttype, [this.argToICPPLocation(op.arg)], -1);
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

                return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.epht), op.epht, icall, op.arglayouttype, [this.argToICPPLocation(op.arg)], -1);
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
            
            return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.epht), op.epht, icall, op.arglayouttype, [this.argToICPPLocation(op.arg)], -1);
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
                
                return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.epht), op.epht, icall, op.arglayouttype, [this.argToICPPLocation(op.arg)], -1);
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
            
            return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.epht), op.epht, icall, op.arglayouttype, [this.argToICPPLocation(op.arg)], -1);
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
                
                return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.epht), op.epht, icall, op.arglayouttype, [this.argToICPPLocation(op.arg)], -1);
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
            
            return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.argflowtype), resulttype.trkey, icall, op.arglayouttype, [this.argToICPPLocation(op.arg)], -1);
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
                
                return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.argflowtype), resulttype.trkey, icall, op.arglayouttype, [this.argToICPPLocation(op.arg)], -1);
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
            
            return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.argflowtype), resulttype.trkey, icall, op.arglayouttype, [this.argToICPPLocation(op.arg)], -1);
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
                
                return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.argflowtype), resulttype.trkey, icall, op.arglayouttype, [this.argToICPPLocation(op.arg)], -1);
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

            return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.argflowtype), resulttype.trkey, icall, op.arglayouttype, [this.argToICPPLocation(op.arg)], -1);
        }
        else {
            //
            //TODO: we probably want to have a special case here that just data constructs if no invariant (or provably satisifed)
            //

            const icall = this.generateUpdateEntityWithInvariantName(this.typegen.getMIRType(op.argflowtype), op.updates.map((upd) => [upd[0], upd[2]]), resulttype);
            if (this.requiredUpdateVirtualEntity.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), updates: op.updates.map((upd) => [upd[0], upd[2]] as [MIRFieldKey, MIRResolvedTypeKey]), resulttype: resulttype };
                this.requiredUpdateVirtualEntity.push(geninfo);
            }

            return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.argflowtype), resulttype.trkey, icall, op.arglayouttype, [this.argToICPPLocation(op.arg)], -1);
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

    processInvokeFixedFunction(op: MIRInvokeFixedFunction): ICPPOp {
        const invk = (this.assembly.invokeDecls.get(op.mkey) || this.assembly.primitiveInvokeDecls.get(op.mkey)) as MIRInvokeDecl;

        if(invk instanceof MIRInvokePrimitiveDecl && invk.implkey === "default") {
            assert(op.sguard === undefined && op.optmask === undefined);

            const trgt = this.trgtToICPPTargetLocation(op.trgt, op.resultType);
            const args = op.args.map((arg) => this.argToICPPLocation(arg));
            return this.processDefaultOperatorInvokePrimitiveType(op.sinfo, trgt, op.resultType, op.mkey, args);
        }
        else {
            const maskidx = op.optmask !== undefined ? this.maskMap.get(op.optmask) as number : -1;

            const args = op.args.map((arg) => this.argToICPPLocation(arg));
            const sguard = this.generateStatmentGuardInfo(op.sguard);

            return ICPPOpEmitter.genInvokeFixedFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resultType), op.resultType, invk.key, args, maskidx, sguard);
        }
    }

    processInvokeVirtualFunction(op: MIRInvokeVirtualFunction): ICPPOp {
        const maskidx = op.optmask !== undefined ? this.maskMap.get(op.optmask) as number : -1;
        return ICPPOpEmitter.genInvokeVirtualFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resultType), op.resultType, op.vresolve, op.rcvrlayouttype, op.args.map((arg) => this.argToICPPLocation(arg)), maskidx);
    }

    processInvokeVirtualOperator(op: MIRInvokeVirtualOperator): ICPPOp {
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
            
        return ICPPOpEmitter.genInvokeFixedFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resultTupleType), op.resultTupleType, icall, cargs, -1, ICPPOpEmitter.genNoStatmentGuard());
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
            
        return ICPPOpEmitter.genInvokeFixedFunctionOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, op.resultRecordType), op.resultRecordType, icall, cargs, -1, ICPPOpEmitter.genNoStatmentGuard());
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

        const oftype = this.typegen.getMIRType(op.cmptype);
        const sguard = this.generateStatmentGuardInfo(op.sguard);
        if(mirlhsflow.trkey === mirrhsflow.trkey && this.typegen.isUniqueType(mirlhsflow) && this.typegen.isUniqueType(mirrhsflow)) {
            if(this.typegen.isUniqueType(mirlhslayout) && this.typegen.isUniqueType(mirrhslayout)) {
                return ICPPOpEmitter.genBinKeyEqFastOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "Bool"), oftype.trkey, this.argToICPPLocation(op.lhs), this.argToICPPLocation(op.rhs), sguard);
            }
            else {
                return ICPPOpEmitter.genBinKeyEqStaticOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "Bool"), oftype.trkey, this.argToICPPLocation(op.lhs), mirlhslayout.trkey, this.argToICPPLocation(op.rhs), mirrhslayout.trkey, sguard);
            }
        }
        else {
            return ICPPOpEmitter.genBinKeyEqVirtualOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "Bool"), oftype.trkey, this.argToICPPLocation(op.lhs), mirlhslayout.trkey, this.argToICPPLocation(op.rhs), mirrhslayout.trkey, sguard);
        }
    }

    processBinKeyLess(op: MIRBinKeyLess): ICPPOp {
        const mirlhsflow = this.typegen.getMIRType(op.lhsflowtype);
        const mirrhsflow = this.typegen.getMIRType(op.rhsflowtype);

        const mirlhslayout = this.typegen.getMIRType(op.lhslayouttype);
        const mirrhslayout = this.typegen.getMIRType(op.rhslayouttype);

        const oftype = this.typegen.getMIRType(op.cmptype);
        const sguard = this.generateStatmentGuardInfo(op.sguard);
        if(mirlhsflow.trkey === mirrhsflow.trkey && this.typegen.isUniqueType(mirlhsflow) && this.typegen.isUniqueType(mirrhsflow)) {
            if(this.typegen.isUniqueType(mirlhslayout) && this.typegen.isUniqueType(mirrhslayout)) {
                return ICPPOpEmitter.genBinKeyLessFastOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "Bool"), oftype.trkey, this.argToICPPLocation(op.lhs), this.argToICPPLocation(op.rhs), sguard);
            }
            else {
                return ICPPOpEmitter.genBinKeyLessStaticOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "Bool"), oftype.trkey, this.argToICPPLocation(op.lhs), mirlhslayout.trkey, this.argToICPPLocation(op.rhs), mirrhslayout.trkey, sguard);
            }
        }
        else {
            return ICPPOpEmitter.genBinKeyLessVirtualOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "Bool"), oftype.trkey, this.argToICPPLocation(op.lhs), mirlhslayout.trkey, this.argToICPPLocation(op.rhs), mirrhslayout.trkey, sguard);
        }
    }

    processPrefixNotOp(op: MIRPrefixNotOp): ICPPOp {
        return ICPPOpEmitter.genPrefixNotOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "Bool"), this.argToICPPLocation(op.arg));
    }

    processIsTypeOf(op: MIRIsTypeOf): ICPPOp {
        const layout = this.typegen.getMIRType(op.srclayouttype);
        const flow = this.typegen.getMIRType(op.srcflowtype);
        const oftype = this.typegen.getMIRType(op.chktype);

        const sguard = this.generateStatmentGuardInfo(op.sguard);
        if(this.assembly.subtypeOf(flow, oftype)) {
            return ICPPOpEmitter.genDirectAssignOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "Bool"), "Bool", this.getSpecialLiteralValue("true"), sguard);
        }
        else if(this.typegen.isType(oftype, "None")) {
            return ICPPOpEmitter.genTypeIsNoneOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "Bool"), this.argToICPPLocation(op.arg), layout.trkey, sguard);
        }
        else if (this.typegen.isType(oftype, "Some")) {
            return ICPPOpEmitter.genTypeIsSomeOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "Bool"), this.argToICPPLocation(op.arg), layout.trkey, sguard);
        }
        else {
            if(this.typegen.isUniqueType(oftype)) {
                return ICPPOpEmitter.genTypeTagIsOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "Bool"), oftype.trkey, this.argToICPPLocation(op.arg), layout.trkey, sguard);
            }
            else {
                return ICPPOpEmitter.genTypeTagSubtypeOfOp(op.sinfo, this.trgtToICPPTargetLocation(op.trgt, "Bool"), oftype.trkey, this.argToICPPLocation(op.arg), layout.trkey, sguard);
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
                return this.processSetConstantGuardFlag(op as MIRSetConstantGuardFlag);
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
            case MIROpTag.MIRLogicAction: {
                return xxxx;
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

    processDefaultOperatorInvokePrimitiveType(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey, op: MIRInvokeKey, args: Argument[]): ICPPOp {
        switch (op) {
            //op unary +
            case "+=prefix=(Int)":
            case "+=prefix=(Nat)":
            case "+=prefix=(BigInt)":
            case "+=prefix=(BigNat)":
            case "+=prefix=(Rational)":
            case "+=prefix=(Float)":
            case "+=prefix=(Decimal)": {
                return ICPPOpEmitter.genDirectAssignOp(sinfo, trgt, oftype, args[0], ICPPOpEmitter.genNoStatmentGuard());
            }
            //op unary -
            case "-=prefix=(Int)": {
                return ICPPOpEmitter.genNegateOp(sinfo, OpCodeTag.NegateIntOp, trgt, oftype, args[0]);
            }
            case "-=prefix=(BigInt)": {
                return ICPPOpEmitter.genNegateOp(sinfo, OpCodeTag.NegateBigIntOp, trgt, oftype, args[0]);
            }
            case "-=prefix=(Rational)": {
                return ICPPOpEmitter.genNegateOp(sinfo, OpCodeTag.NegateRationalOp, trgt, oftype, args[0]);
            }
            case "-=prefix=(Float)": {
                return ICPPOpEmitter.genNegateOp(sinfo, OpCodeTag.NegateFloatOp, trgt, oftype, args[0]);
            }
            case "-=prefix=(Decimal)": {
                return ICPPOpEmitter.genNegateOp(sinfo, OpCodeTag.NegateDecimalOp, trgt, oftype, args[0]);
            }
            //op infix +
            case "+=infix=(Int, Int)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.AddIntOp, trgt, oftype, args[0], args[1]);
            }
            case "+=infix=(Nat, Nat)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.AddNatOp, trgt, oftype, args[0], args[1]);
            }
            case "+=infix=(BigInt, BigInt)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.AddBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case "+=infix=(BigNat, BigNat)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.AddBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case "+=infix=(Rational, Rational)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.AddRationalOp, trgt, oftype, args[0], args[1]);
            }
            case "+=infix=(Float, Float)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.AddFloatOp, trgt, oftype, args[0], args[1]);
            }
            case "+=infix=(Decimal, Decimal)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.AddDecimalOp, trgt, oftype, args[0], args[1]);
            }
            //op infix -
            case "-=infix=(Int, Int)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.SubIntOp, trgt, oftype, args[0], args[1]);
            }
            case "-=infix=(Nat, Nat)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.SubNatOp, trgt, oftype, args[0], args[1]);
            }
            case "-=infix=(BigInt, BigInt)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.SubBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case "-=infix=(BigNat, BigNat)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.SubBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case "-=infix=(Rational, Rational)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.SubRationalOp, trgt, oftype, args[0], args[1]);
            }
            case "-=infix=(Float, Float)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.SubFloatOp, trgt, oftype, args[0], args[1]);
            }
            case "-=infix=(Decimal, Decimal)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.SubDecimalOp, trgt, oftype, args[0], args[1]);
            }
            //op infix *
            case "*=infix=(Int, Int)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.MultIntOp, trgt, oftype, args[0], args[1]);
            }
            case "*=infix=(Nat, Nat)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.MultNatOp, trgt, oftype, args[0], args[1]);
            }
            case "*=infix=(BigInt, BigInt)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.MultBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case "*=infix=(BigNat, BigNat)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.MultBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case "*=infix=(Rational, Rational)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.MultRationalOp, trgt, oftype, args[0], args[1]);
            }
            case "*=infix=(Float, Float)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.MultFloatOp, trgt, oftype, args[0], args[1]);
            }
            case "*=infix=(Decimal, Decimal)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.MultDecimalOp, trgt, oftype, args[0], args[1]);
            }
            //op infix /
            case "/=infix=(Int, Int)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.DivIntOp, trgt, oftype, args[0], args[1]);
            }
            case "/=infix=(Nat, Nat)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.DivNatOp, trgt, oftype, args[0], args[1]);
            }
            case "/=infix=(BigInt, BigInt)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.DivBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case "/=infix=(BigNat, BigNat)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.DivBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case "/=infix=(Rational, Rational)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.DivRationalOp, trgt, oftype, args[0], args[1]);
            }
            case "/=infix=(Float, Float)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.DivFloatOp, trgt, oftype, args[0], args[1]);
            }
            case "/=infix=(Decimal, Decimal)": {
                return ICPPOpEmitter.genBinaryOp(sinfo, OpCodeTag.DivDecimalOp, trgt, oftype, args[0], args[1]);
            }
            //op infix ==
            case "===infix=(Int, Int)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.EqIntOp, trgt, oftype, args[0], args[1]);
            }
            case "===infix=(Nat, Nat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.EqNatOp, trgt, oftype, args[0], args[1]);
            }
            case "===infix=(BigInt, BigInt)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.EqBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case "===infix=(BigNat, BigNat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.EqBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case "===infix=(Rational, Rational)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.EqRationalOp, trgt, oftype, args[0], args[1]);
            }
            //op infix !=
            case "!==infix=(Int, Int)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.NeqIntOp, trgt, oftype, args[0], args[1]);
            }
            case "!==infix=(Nat, Nat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.NeqNatOp, trgt, oftype, args[0], args[1]);
            }
            case "!==infix=(BigInt, BigInt)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.NeqBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case "!==infix=(BigNat, BigNat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.NeqBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case "!==infix=(Rational, Rational)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.NeqRationalOp, trgt, oftype, args[0], args[1]);
            }
            //op infix <
            case "<=infix=(Int, Int)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LtIntOp, trgt, oftype, args[0], args[1]);
            }
            case "<=infix=(Nat, Nat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LtNatOp, trgt, oftype, args[0], args[1]);
            }
            case "<=infix=(BigInt, BigInt)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LtBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case "<=infix=(BigNat, BigNat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LtBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case "<=infix=(Rational, Rational)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LtRationalOp, trgt, oftype, args[0], args[1]);
            }
            case "<=infix=(Float, Float)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LtFloatOp, trgt, oftype, args[0], args[1]);
            }
            case "<=infix=(Decimal, Decimal)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LtDecimalOp, trgt, oftype, args[0], args[1]);
            }
            //op infix >
            case ">=infix=(Int, Int)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GtIntOp, trgt, oftype, args[0], args[1]);
            }
            case ">=infix=(Nat, Nat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GtNatOp, trgt, oftype, args[0], args[1]);
            }
            case ">=infix=(BigInt, BigInt)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GtBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case ">=infix=(BigNat, BigNat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GtBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case ">=infix=(Rational, Rational)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GtRationalOp, trgt, oftype, args[0], args[1]);
            }
            case ">=infix=(Float, Float)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GtFloatOp, trgt, oftype, args[0], args[1]);
            }
            case ">=infix=(Decimal, Decimal)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GtDecimalOp, trgt, oftype, args[0], args[1]);
            }
            //op infix <=
            case "<==infix=(Int, Int)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LeIntOp, trgt, oftype, args[0], args[1]);
            }
            case "<==infix=(Nat, Nat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LeNatOp, trgt, oftype, args[0], args[1]);
            }
            case "<==infix=(BigInt, BigInt)":  {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LeBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case "<==infix=(BigNat, BigNat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LeBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case "<==infix=(Rational, Rational)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LeRationalOp, trgt, oftype, args[0], args[1]);
            }
            case "<==infix=(Float, Float)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LeFloatOp, trgt, oftype, args[0], args[1]);
            }
            case "<==infix=(Decimal, Decimal)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.LeDecimalOp, trgt, oftype, args[0], args[1]);
            }
            //op infix >=
            case ">==infix=(Int, Int)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GeIntOp, trgt, oftype, args[0], args[1]);
            }
            case ">==infix=(Nat, Nat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GeNatOp, trgt, oftype, args[0], args[1]);
            }
            case ">==infix=(BigInt, BigInt)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GeBigIntOp, trgt, oftype, args[0], args[1]);
            }
            case ">==infix=(BigNat, BigNat)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GeBigNatOp, trgt, oftype, args[0], args[1]);
            }
            case ">==infix=(Rational, Rational)":{
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GeRationalOp, trgt, oftype, args[0], args[1]);
            }
            case ">==infix=(Float, Float)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GeFloatOp, trgt, oftype, args[0], args[1]);
            }
            case ">==infix=(Decimal, Decimal)": {
                return ICPPOpEmitter.genCmpOp(sinfo, OpCodeTag.GeDecimalOp, trgt, oftype, args[0], args[1]);
            }
            default: {
                return NOT_IMPLEMENTED(op);
            }
        }
    }

    generateBlockExps(blocks: Map<string, MIRBasicBlock>, blockrevorder: string[]): ICPPOp[] {
        let icppblocks = new Map<string, ICPPOp[]>();

        //Generate basic logic
        blocks.forEach((bb) => {
            let ii = Math.max(0, bb.ops.findIndex((op) => !(op instanceof MIRPhi)));

            if(ii !== 0) { 
                //create stack locations for each of the phi vars
                for(let i = 0; i < ii; ++i) {
                    const phi = bb.ops[i] as MIRPhi;
                    this.generateStorageLocationForPhi(phi.trgt, phi.layouttype);
                }
            }

            let done = false;
            let icpp: ICPPOp[] = [];
            while (!done && ii < bb.ops.length) {
                const op = bb.ops[ii];
                if (op.tag === MIROpTag.MIRJump || op.tag === MIROpTag.MIRJumpCond || op.tag === MIROpTag.MIRJumpNone || op.tag === MIROpTag.MIRAbort) {
                    break;
                }

                const icppop = this.processOp(op);
                if (icppop !== undefined) {
                    icpp.push(icppop);
                }

                ii++;
            }

            icppblocks.set(bb.label, icpp);
        });

        //Fixup phi assigns
        blocks.forEach((bb) => {
            const ii = Math.max(0, bb.ops.findIndex((op) => !(op instanceof MIRPhi)));
            for(let i = 0; i < ii; ++i) {
                const phi = bb.ops[i] as MIRPhi;
                const icpptrgt = this.getStorageTargetForPhi(phi.trgt);

                phi.src.forEach((arg, bfrom) => {
                    let insblock = icppblocks.get(bfrom) as ICPPOp[];
                    insblock.push(ICPPOpEmitter.genRegisterAssignOp(phi.sinfo, icpptrgt, this.argToICPPLocation(arg), phi.layouttype, ICPPOpEmitter.genNoStatmentGuard()));
                });
            }
        });

        //Fixup jump offsets and append blocks
        let ops: ICPPOp[] = [];
        let blockdeltas: Map<string, number> = new Map<string, number>();
        for(let j = 0; j < blockrevorder.length; ++j) {
            const bb = blocks.get(blockrevorder[j]) as MIRBasicBlock;
            
            if(bb.label === "exit") {
                blockdeltas.set(bb.label, ops.length);
                continue;
            }

            const jop = bb.ops[bb.ops.length - 1];
            let insblock = icppblocks.get(blockrevorder[j]) as ICPPOp[];
            if (jop.tag === MIROpTag.MIRAbort) {
                insblock.push(this.processAbort(jop as MIRAbort));
            }
            else if (jop.tag === MIROpTag.MIRJump) {
                const djump = jop as MIRJump;
                const jdelta = (ops.length + 1) - (blockdeltas.get(djump.trgtblock) as number);
                insblock.push(ICPPOpEmitter.genJumpOp(djump.sinfo, jdelta, djump.trgtblock));
            }
            else if (jop.tag === MIROpTag.MIRJumpCond) {
                const djump = jop as MIRJumpCond;
                const jdeltatrue = (ops.length + 1) - (blockdeltas.get(djump.trueblock) as number);
                const jdeltafalse = (ops.length + 1) - (blockdeltas.get(djump.falseblock) as number);
                insblock.push(ICPPOpEmitter.genJumpCondOp(djump.sinfo, this.argToICPPLocation(djump.arg), jdeltatrue, jdeltafalse, djump.trueblock, djump.falseblock));
            }
            else {
                assert(jop.tag === MIROpTag.MIRJumpNone);

                const djump = jop as MIRJumpNone;
                const jdeltanone = (ops.length + 1) - (blockdeltas.get(djump.noneblock) as number);
                const jdeltasome = (ops.length + 1) - (blockdeltas.get(djump.someblock) as number);
                insblock.push(ICPPOpEmitter.genJumpNoneOp(djump.sinfo, this.argToICPPLocation(djump.arg), djump.arglayouttype, jdeltanone, jdeltasome, djump.noneblock, djump.someblock));
            }

            ops = [...insblock, ...ops];
            blockdeltas.set(bb.label, ops.length);
        }

        return ops;
    }

    generateICPPInvoke(idecl: MIRInvokeDecl): ICPPInvokeDecl | undefined {
        const params = idecl.params.map((arg) => {
            return new ICPPFunctionParameter(arg.name, this.typegen.getICPPTypeData(this.typegen.getMIRType(arg.type)));
        });

        let paramsmap: Map<string, number> = new Map<string, number>();
        for(let i = 0; i < idecl.params.length; ++i) {
            const param = idecl.params[i];
            paramsmap.set(param.name, i);
        }

        const rtype = this.typegen.getICPPTypeData(this.typegen.getMIRType(idecl.resultType));

        this.initializeBodyGen(idecl.srcFile, this.typegen.getMIRType(idecl.resultType), paramsmap);

        if (idecl instanceof MIRInvokeBodyDecl) {
            const revblocks = topologicalOrder((idecl as MIRInvokeBodyDecl).body.body).reverse().map((bb) => bb.label);
            const body = this.generateBlockExps((idecl as MIRInvokeBodyDecl).body.body, revblocks);

            return new ICPPInvokeBodyDecl(idecl.iname, idecl.key, idecl.srcFile, idecl.sourceLocation, idecl.recursive, params, rtype, this.getStackInfoForArgVar("$$return"), this.scalarStackSize, this.mixedStackSize, this.genMaskForStack(), this.masksize, body, idecl.masksize);
        }
        else {
            assert(idecl instanceof MIRInvokePrimitiveDecl);

            return this.generateBuiltinICPPInvoke(idecl as MIRInvokePrimitiveDecl);
        }
    }

    generateBuiltinICPPInvoke(idecl: MIRInvokePrimitiveDecl): ICPPInvokeDecl | undefined {
        if(idecl.implkey === "default") {
            return undefined;
        }
        
        const params = idecl.params.map((arg) => {
            return new ICPPFunctionParameter(arg.name, this.typegen.getICPPTypeData(this.typegen.getMIRType(arg.type)));
        });

        const rtype = this.typegen.getICPPTypeData(this.typegen.getMIRType(idecl.resultType));

        let scalarsmap: Map<string, [number, MIRResolvedTypeKey]> = new Map<string, [number, MIRResolvedTypeKey]>();
        let spoffset: number = 0;
        for(let i = 0; i < idecl.scalarslotsinfo.length; ++i) {
            const slot = idecl.scalarslotsinfo[i];
            const stype = this.typegen.getICPPTypeData(this.typegen.getMIRType(slot.vtype));
            scalarsmap.set(slot.vname, [spoffset, slot.vtype]);
            spoffset += stype.allocinfo.inlinedatasize;
        }

        let mixedmap: Map<string, [number, MIRResolvedTypeKey]> = new Map<string, [number, MIRResolvedTypeKey]>();
        let mpoffset: number = 0;
        let mmask = "";
        for(let i = 0; i < idecl.mixedslotsinfo.length; ++i) {
            const slot = idecl.mixedslotsinfo[i];
            const mtype = this.typegen.getICPPTypeData(this.typegen.getMIRType(slot.vtype));
            mixedmap.set(slot.vname, [mpoffset, slot.vtype]);
            mpoffset += mtype.allocinfo.inlinedatasize;
            mmask = mmask + mtype.allocinfo.inlinedmask;
        }

        let binds: Map<string, ICPPType> = new Map<string, ICPPType>();
        idecl.binds.forEach((btype, bname) => {
            binds.set(bname, this.typegen.getICPPTypeData(this.typegen.getMIRType(btype)));
        });

        let pcodes: Map<string, ICPPPCode> = new Map<string, ICPPPCode>();
        idecl.pcodes.forEach((pc, pcname) => {
            const icpppc = new ICPPPCode(pc.code, pc.cargs.map((carg) => ICPPOpEmitter.genParameterArgument(this.argsMap.get(carg) as number)));
            pcodes.set(pcname, icpppc);
        });

        return new ICPPInvokePrimitiveDecl(idecl.iname, idecl.key, idecl.srcFile, idecl.sourceLocation, idecl.recursive, params, rtype, spoffset, mpoffset, mmask, 0, idecl.enclosingDecl, idecl.implkey, scalarsmap, mixedmap, binds, pcodes);
    }
}

export {
     ICPPBodyEmitter
};
