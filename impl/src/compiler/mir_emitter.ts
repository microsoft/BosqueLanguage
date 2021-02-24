//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo, Parser } from "../ast/parser";
import { MIRAbort, MIRAllTrue, MIRArgument, MIRAssertCheck, MIRBasicBlock, MIRBinKeyEq, MIRBinKeyLess, MIRBody, MIRConstantArgument, MIRConstantBigInt, MIRConstantBigNat, MIRConstantDataString, MIRConstantDecimal, MIRConstantFalse, MIRConstantFloat, MIRConstantInt, MIRConstantNat, MIRConstantNone, MIRConstantRational, MIRConstantRegex, MIRConstantString, MIRConstantStringOf, MIRConstantTrue, MIRConstantTypedNumber, MIRConstructorEphemeralList, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionMixed, MIRConstructorPrimaryCollectionSingletons, MIRConstructorRecord, MIRConstructorRecordFromEphemeralList, MIRConstructorTuple, MIRConstructorTupleFromEphemeralList, MIRConvertValue, MIRDeadFlow, MIRDebug, MIRDeclareGuardFlagLocation, MIREntityProjectToEphemeral, MIREntityUpdate, MIREphemeralListExtend, MIRFieldKey, MIRGlobalKey, MIRGuard, MIRInvokeFixedFunction, MIRInvokeKey, MIRInvokeVirtualFunction, MIRInvokeVirtualOperator, MIRIsTypeOf, MIRJump, MIRJumpCond, MIRJumpNone, MIRLoadConst, MIRLoadField, MIRLoadFromEpehmeralList, MIRLoadRecordProperty, MIRLoadRecordPropertySetGuard, MIRLoadTupleIndex, MIRLoadTupleIndexSetGuard, MIRLoadUnintVariableValue, MIRMultiLoadFromEpehmeralList, MIRNop, MIROp, MIRPrefixNotOp, MIRRecordHasProperty, MIRRecordProjectToEphemeral, MIRRecordUpdate, MIRRegisterArgument, MIRResolvedTypeKey, MIRReturnAssign, MIRReturnAssignOfCons, MIRSetConstantGuardFlag, MIRSliceEpehmeralList, MIRStatmentGuard, MIRStructuredAppendTuple, MIRStructuredJoinRecord, MIRRegisterAssign, MIRTupleHasIndex, MIRTupleProjectToEphemeral, MIRTupleUpdate, MIRVarLifetimeEnd, MIRVarLifetimeStart, MIRVirtualMethodKey, MIRSomeTrue } from "./mir_ops";
import { Assembly, BuildLevel, ConceptTypeDecl, EntityTypeDecl, InvokeDecl, MemberMethodDecl, NamespaceConstDecl, NamespaceFunctionDecl, NamespaceOperatorDecl, OOMemberLookupInfo, OOPTypeDecl, StaticFunctionDecl, StaticMemberDecl, StaticOperatorDecl } from "../ast/assembly";
import { ResolvedConceptAtomType, ResolvedConceptAtomTypeEntry, ResolvedEntityAtomType, ResolvedEphemeralListType, ResolvedFunctionType, ResolvedLiteralAtomType, ResolvedRecordAtomType, ResolvedTupleAtomType, ResolvedType } from "../ast/resolved_type";
import { MIRAssembly, MIRConceptType, MIREntityType, MIREphemeralListType, MIRLiteralType, MIRRecordType, MIRRecordTypeEntry, MIRTupleType, MIRTupleTypeEntry, MIRType, MIRTypeOption, PackageConfig } from "./mir_assembly";

import { TypeChecker } from "../type_checker/type_checker";
import { simplifyBody } from "./mir_cleanup";
import { ssaConvertInvokes } from "./mir_ssa";
import { functionalizeInvokes } from "./functionalize";
import { BSQRegex } from "../ast/bsqregex";
import { ConstantExpressionValue, LiteralExpressionValue } from "../ast/body";
import { ValueType } from "../type_checker/type_environment";

import * as Crypto from "crypto";

type PCode = {
    code: InvokeDecl,
    scope: MIRInvokeKey,
    captured: Map<string, ResolvedType>,
    ftype: ResolvedFunctionType
};

class MIRKeyGenerator {
    static computeBindsKeyInfo(binds: Map<string, ResolvedType>): string {
        if (binds.size === 0) {
            return "";
        }

        let terms: string[] = [];
        binds.forEach((v, k) => terms.push(`${k}=${v.idStr}`));

        return `<${terms.sort().join(", ")}>`;
    }

    static computePCodeKeyInfo(pcodes: PCode[]): string {
        if (pcodes.length === 0) {
            return "";
        }

        return "[" + pcodes.map((pc) => `${pc.code.srcFile}%${pc.code.sourceLocation.line}%${pc.code.sourceLocation.column}`).join(",") + "]";
    }

    static generateTypeKey(t: ResolvedType): MIRResolvedTypeKey {
        return t.idStr;
    }

    static generateFieldKey(t: ResolvedType, name: string): MIRFieldKey {
        return `${MIRKeyGenerator.generateTypeKey(t)}.${name}`;
    }

    static generateFunctionKey(prefix: string, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[]): MIRInvokeKey {
        return `${prefix}::${name}${MIRKeyGenerator.computeBindsKeyInfo(binds)}${MIRKeyGenerator.computePCodeKeyInfo(pcodes)}`;
    }

    static generateMethodKey(name: string, t: MIRResolvedTypeKey, binds: Map<string, ResolvedType>, pcodes: PCode[]): MIRInvokeKey {
        return `${t}::${name}${MIRKeyGenerator.computeBindsKeyInfo(binds)}${MIRKeyGenerator.computePCodeKeyInfo(pcodes)}`;
    }

    static generateVirtualMethodKey(vname: string, binds: Map<string, ResolvedType>, pcodes: PCode[]): MIRVirtualMethodKey {
        return `${vname}${MIRKeyGenerator.computeBindsKeyInfo(binds)}${MIRKeyGenerator.computePCodeKeyInfo(pcodes)}`;
    }

    static generatePCodeKey(inv: InvokeDecl): MIRInvokeKey {
        return `fn--${inv.srcFile}+${inv.sourceLocation.line}##${inv.sourceLocation.pos}`;
    }

    static generateOperatorSignatureKey(ikey: MIRInvokeKey, isprefix: boolean, isinfix: boolean, sigkeys: string[]): string {
        if(isprefix) {
            ikey = ikey + "=prefix";
        }
        if(isinfix) {
            ikey = ikey + "=infix";
        }

        return ikey + `=(${sigkeys.join(", ")})`
    }
}

class MIREmitter {
    readonly assembly: Assembly;
    readonly masm: MIRAssembly;
    
    private readonly pendingOOProcessing: [MIRResolvedTypeKey, OOPTypeDecl, Map<string, ResolvedType>][] = [];

    private readonly pendingConstExprProcessing: [MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, ConstantExpressionValue, string[], Map<string, ResolvedType>, ResolvedType][] = [];
    private readonly pendingFunctionProcessing: [MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, InvokeDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];
    private readonly pendingOperatorProcessing: [MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, InvokeDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];
    private readonly pendingOOMethodProcessing: [MIRVirtualMethodKey, MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>], MemberMethodDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];
    private readonly pendingPCodeProcessing: [MIRInvokeKey, InvokeDecl, ResolvedFunctionType, Map<string, ResolvedType>, [string, ResolvedType][]][] = [];
    private readonly pendingOPVirtualProcessing: [MIRVirtualMethodKey, string | undefined, [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, string, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];
    private readonly entityInstantiationInfo: [MIRResolvedTypeKey, OOPTypeDecl, Map<string, ResolvedType>][] = [];
    private readonly allVInvokes: [MIRVirtualMethodKey, MIRResolvedTypeKey, ResolvedType, string, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];

    private emitEnabled: boolean;
    
    private m_blockMap: Map<string, MIRBasicBlock> = new Map<string, MIRBasicBlock>();
    private m_currentBlockName = "UNDEFINED";
    private m_currentBlock: MIROp[] = [];

    private m_tmpIDCtr = 0;

    private yieldPatchInfo: [string, MIRRegisterArgument, ValueType][][] = [];
    private returnPatchInfo: [string, MIRRegisterArgument, ValueType][] = [];

    private constructor(assembly: Assembly, masm: MIRAssembly, emitEnabled: boolean) {
        this.assembly = assembly;
        this.masm = masm;

        this.emitEnabled = emitEnabled;
    }

    getEmitEnabled(): boolean {
        return this.emitEnabled;
    }

    setEmitEnabled(enabled: boolean) {
        this.emitEnabled = enabled;
    }

    initializeBodyEmitter() {
        this.m_tmpIDCtr = 0;

        this.m_blockMap = new Map<string, MIRBasicBlock>();
        this.m_blockMap.set("entry", new MIRBasicBlock("entry", []));
        this.m_blockMap.set("returnassign", new MIRBasicBlock("returnassign", []));
        this.m_blockMap.set("exit", new MIRBasicBlock("exit", []));

        this.m_currentBlockName = "entry";
        this.m_currentBlock = (this.m_blockMap.get("entry") as MIRBasicBlock).ops;

        this.yieldPatchInfo = [];
        this.returnPatchInfo = [];
    }

    generateTmpRegister(): MIRRegisterArgument {
        if(!this.emitEnabled) {
            return new MIRRegisterArgument(`#tmp_${-1}`);
        }

        return new MIRRegisterArgument(`#tmp_${this.m_tmpIDCtr++}`);
    }

    generateCapturedVarName(name: string): string {
        return "__c_" + name;
    }

    createNewBlock(pfx: string): string {
        if(!this.emitEnabled) {
            return "DISABLED";
        }

        const name = `${pfx}_${this.m_blockMap.size}`;
        this.m_blockMap.set(name, new MIRBasicBlock(name, []));

        return name;
    }

    getActiveBlockName(): string {
        return this.m_currentBlockName;
    }

    setActiveBlock(name: string) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlockName = name;
        this.m_currentBlock = (this.m_blockMap.get(name) as MIRBasicBlock).ops;
    }

    emitNOP(sinfo: SourceInfo) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRNop(sinfo));
    }

    emitDeadBlock(sinfo: SourceInfo) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRDeadFlow(sinfo));
    }

    emitAbort(sinfo: SourceInfo, info: string) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRAbort(sinfo, info));
    }

    emitAssertCheck(sinfo: SourceInfo, msg: string, src: MIRArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRAssertCheck(sinfo, msg, src));
    }

    emitDebugBreak(sinfo: SourceInfo) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRDebug(sinfo, undefined));
    }

    emitDebugPrint(sinfo: SourceInfo, value: MIRArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRDebug(sinfo, value));
    }

    emitRegisterStore(sinfo: SourceInfo, src: MIRArgument, trgt: MIRRegisterArgument, vtype: MIRType, guard: MIRStatmentGuard | undefined) {
        if (!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRRegisterAssign(sinfo, src, trgt, vtype.trkey, guard));
    }

    emitLoadUninitVariableValue(sinfo: SourceInfo, oftype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        //This value will not be accessed from but can be passed/assigned atomically
        //we need to have space for it etc. so just plop a "fresh" or zero-filled value there
        this.m_currentBlock.push(new MIRLoadUnintVariableValue(sinfo, trgt, oftype.trkey));
    }

    emitGuardFlagLocation(sinfo: SourceInfo, name: string, count: number): string | undefined {
        if(!this.emitEnabled || count === 0) {
            return undefined;
        }

        this.m_currentBlock.push(new MIRDeclareGuardFlagLocation(sinfo, name, count));
        return name;
    }

    emitSetGuardFlagConstant(sinfo: SourceInfo, name: string, position: number, flag: boolean) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRSetConstantGuardFlag(sinfo, name, position, flag));
    }

    emitConvert(sinfo: SourceInfo, srctypelayout: MIRType, srctypeflow: MIRType, intotype: MIRType, src: MIRArgument, trgt: MIRRegisterArgument, guard: MIRStatmentGuard | undefined) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConvertValue(sinfo, srctypelayout.trkey, srctypeflow.trkey, intotype.trkey, src, trgt, guard));
    }

    emitCheckNoError(sinfo: SourceInfo, src: MIRArgument, srctype: MIRType, oktype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRIsTypeOf(sinfo, trgt, oktype.trkey, src, srctype.trkey, srctype.trkey, undefined));
    }

    emitExtractResultOkValue(sinfo: SourceInfo, src: MIRArgument, srctype: MIRType, oktype: MIRType, vfield: MIRFieldKey, valuetype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const okr = this.generateTmpRegister();
        this.m_currentBlock.push(new MIRConvertValue(sinfo, srctype.trkey, srctype.trkey, oktype.trkey, src, okr, undefined));
        this.m_currentBlock.push(new MIRLoadField(sinfo, okr, oktype.trkey, oktype.trkey, vfield, false, valuetype.trkey, trgt));
    }

    emitLoadConstNone(sinfo: SourceInfo, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantNone(), this.registerResolvedTypeReference(this.assembly.getSpecialNoneType()).trkey, trgt));
    }

    emitLoadConstBool(sinfo: SourceInfo, bv: boolean, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, bv ? new MIRConstantTrue() : new MIRConstantFalse(), this.registerResolvedTypeReference(this.assembly.getSpecialBoolType()).trkey, trgt));
    }

    emitLoadConstIntegralValue(sinfo: SourceInfo, itype: MIRType, vv: string, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        if(itype.trkey === "NSCore::Int") {
            this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantInt(vv), itype.trkey, trgt));
        }
        else if(itype.trkey === "NSCore::Nat") {
            this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantNat(vv), itype.trkey, trgt));
        }
        else if(itype.trkey === "NSCore::BigInt") {
            this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantBigInt(vv), itype.trkey, trgt));
        }
        else {
            this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantBigNat(vv), itype.trkey, trgt));
        }
    }

    emitLoadConstRational(sinfo: SourceInfo, iv: string, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantRational(iv), this.registerResolvedTypeReference(this.assembly.getSpecialRationalType()).trkey, trgt));
    }

    emitLoadConstFloatPoint(sinfo: SourceInfo, ftype: MIRType, fv: string, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        if(ftype.trkey === "NSCore::Float") {
            this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantFloat(fv), ftype.trkey, trgt));
        }
        else {
            this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantDecimal(fv), ftype.trkey, trgt));
        }
    }

    emitLoadConstString(sinfo: SourceInfo, sv: string, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantString(sv), this.registerResolvedTypeReference(this.assembly.getSpecialStringType()).trkey, trgt));
    }

    emitLoadLiteralRegex(sinfo: SourceInfo, restr: BSQRegex, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantRegex(restr), this.registerResolvedTypeReference(this.assembly.getSpecialRegexType()).trkey, trgt));
    }

    emitLoadLiteralStringOf(sinfo: SourceInfo, sv: string, tskey: MIRResolvedTypeKey, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantStringOf(sv, tskey), tskey, trgt));
    }

    emitLoadConstDataString(sinfo: SourceInfo, sv: string, tskey: MIRResolvedTypeKey, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantDataString(sv, tskey), tskey, trgt));
    }

    emitLoadTypedNumeric(sinfo: SourceInfo, nv: MIRConstantArgument, tnkey: MIRResolvedTypeKey, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantTypedNumber(nv, tnkey), tnkey, trgt));
    }

    emitTupleHasIndex(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, idx: number, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRTupleHasIndex(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, idx, trgt));
    }

    emitRecordHasProperty(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, pname: string, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRRecordHasProperty(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, pname, trgt));
    }
    
    emitLoadTupleIndex(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, idx: number, isvirtual: boolean, resulttype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRLoadTupleIndex(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, idx, isvirtual, resulttype.trkey, trgt));
    }

    emitLoadTupleIndexSetGuard(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, idx: number, isvirtual: boolean, resulttype: MIRType, trgt: MIRRegisterArgument, guard: MIRGuard) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRLoadTupleIndexSetGuard(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, idx, isvirtual, resulttype.trkey, trgt, guard));
    }

    emitLoadProperty(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, pname: string, isvirtual: boolean, resulttype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadRecordProperty(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, pname, isvirtual, resulttype.trkey, trgt));
    }

    emitLoadRecordPropertySetGuard(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, pname: string, isvirtual: boolean, resulttype: MIRType, trgt: MIRRegisterArgument, guard: MIRGuard) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadRecordPropertySetGuard(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, pname, isvirtual, resulttype.trkey, trgt, guard));
    }

    emitLoadField(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, fname: MIRFieldKey, isvirtual: boolean, resulttype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadField(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, fname, isvirtual, resulttype.trkey, trgt));
    }

    emitTupleProjectToEphemeral(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, indecies: number[], isvirtual: boolean, epht: ResolvedEphemeralListType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRTupleProjectToEphemeral(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, indecies, isvirtual, this.registerResolvedTypeReference(ResolvedType.createSingle(epht)).trkey, trgt));
    }

    emitRecordProjectToEphemeral(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, properties: string[], isvirtual: boolean, epht: ResolvedEphemeralListType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRRecordProjectToEphemeral(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, properties, isvirtual, this.registerResolvedTypeReference(ResolvedType.createSingle(epht)).trkey, trgt));
    }

    emitEntityProjectToEphemeral(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, fields: MIRFieldKey[], isvirtual: boolean, epht: ResolvedEphemeralListType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIREntityProjectToEphemeral(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, fields, isvirtual, this.registerResolvedTypeReference(ResolvedType.createSingle(epht)).trkey, trgt));
    }

    emitTupleUpdate(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, updates: [number, ResolvedType, MIRArgument][], isvirtual: boolean, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const upds = updates.map((upd) => [upd[0], upd[2], this.registerResolvedTypeReference(upd[1]).trkey] as [number, MIRArgument, MIRResolvedTypeKey]);
        this.m_currentBlock.push(new MIRTupleUpdate(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, upds, isvirtual, trgt));
    }

    emitRecordUpdate(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, updates: [string, ResolvedType, MIRArgument][], isvirtual: boolean, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const upds = updates.map((upd) => [upd[0], upd[2], this.registerResolvedTypeReference(upd[1]).trkey] as [string, MIRArgument, MIRResolvedTypeKey]);
        this.m_currentBlock.push(new MIRRecordUpdate(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, upds, isvirtual, trgt));
    }

    emitEntityUpdate(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, updates: [MIRFieldKey, ResolvedType, MIRArgument][], isvirtual: boolean, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const upds = updates.map((upd) => [upd[0], upd[2], this.registerResolvedTypeReference(upd[1]).trkey] as [MIRFieldKey, MIRArgument, MIRResolvedTypeKey]);
        this.m_currentBlock.push(new MIREntityUpdate(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, upds, isvirtual, trgt));
    }

    emitLoadFromEpehmeralList(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRType, idx: number, resulttype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRLoadFromEpehmeralList(sinfo, arg, argtype.trkey, idx, resulttype.trkey, trgt));
    }

    emitMultiLoadFromEpehmeralList(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRType, trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRType }[]) {
        if (!this.emitEnabled) {
            return;
        }

        const etrgts = trgts.map((trgt) => {
            return { pos: trgt.pos, into: trgt.into, oftype: trgt.oftype.trkey };
        });
        this.m_currentBlock.push(new MIRMultiLoadFromEpehmeralList(sinfo, arg, argtype.trkey, etrgts));
    }

    emitInvokeFixedFunction(sinfo: SourceInfo, ikey: MIRInvokeKey, args: MIRArgument[], optstatusmask: string | undefined, rretinfo: MIRType | { declresult: MIRType, runtimeresult: MIRType, elrcount: number, refargs: [MIRRegisterArgument, MIRType][] }, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const retinfo = rretinfo instanceof MIRType ? { declresult: rretinfo, runtimeresult: rretinfo, elrcount: -1, refargs: [] } : rretinfo;
        if (retinfo.refargs.length === 0) {
            this.m_currentBlock.push(new MIRInvokeFixedFunction(sinfo, retinfo.declresult.trkey, ikey, args, optstatusmask, trgt, undefined));
        }
        else {
            const rr = this.generateTmpRegister();
            this.m_currentBlock.push(new MIRInvokeFixedFunction(sinfo, retinfo.runtimeresult.trkey, ikey, args, optstatusmask, rr, undefined));

            if (retinfo.elrcount === -1) {
                this.m_currentBlock.push(new MIRLoadFromEpehmeralList(sinfo, rr, retinfo.runtimeresult.trkey, 0, retinfo.declresult.trkey, trgt));
            }
            else {
                this.m_currentBlock.push(new MIRSliceEpehmeralList(sinfo, rr, retinfo.runtimeresult.trkey, retinfo.declresult.trkey, trgt));
            }

            const refbase = retinfo.elrcount != -1 ? retinfo.elrcount : 1;
            const argvs = retinfo.refargs.map((rinfo, idx) => {
                return { pos: refbase + idx, into: rinfo[0], oftype: (retinfo.declresult.options[0] as MIREphemeralListType).entries[refbase + idx]};
            });

            this.emitMultiLoadFromEpehmeralList(sinfo, rr, retinfo.declresult, argvs);
        }
    }

    emitInvokeFixedFunctionWithGuard(sinfo: SourceInfo, ikey: MIRInvokeKey, args: MIRArgument[], optstatusmask: string | undefined, retinfo: MIRType, trgt: MIRRegisterArgument, guard: MIRStatmentGuard | undefined) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRInvokeFixedFunction(sinfo, retinfo.trkey, ikey, args, optstatusmask, trgt, guard));
    }

    emitInvokeVirtualFunction(sinfo: SourceInfo, vresolve: MIRVirtualMethodKey, rcvrlayouttype: MIRType, rcvrflowtype: MIRType, args: MIRArgument[], optstatusmask: string | undefined, rretinfo: MIRType | { declresult: MIRType, runtimeresult: MIRType, elrcount: number, refargs: [MIRRegisterArgument, MIRType][] }, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const retinfo = rretinfo instanceof MIRType ? { declresult: rretinfo, runtimeresult: rretinfo, elrcount: -1, refargs: [] as [MIRRegisterArgument, MIRType][] } : rretinfo;
        if (retinfo.refargs.length === 0) {
            this.m_currentBlock.push(new MIRInvokeVirtualFunction(sinfo, retinfo.declresult.trkey, vresolve, rcvrlayouttype.trkey, rcvrflowtype.trkey, args, optstatusmask, trgt));
        }
        else {
            const rr = this.generateTmpRegister();
            this.m_currentBlock.push(new MIRInvokeVirtualFunction(sinfo, retinfo.runtimeresult.trkey, vresolve, rcvrlayouttype.trkey, rcvrflowtype.trkey, args, optstatusmask, rr));
           
            if (retinfo.elrcount === -1) {
                this.m_currentBlock.push(new MIRLoadFromEpehmeralList(sinfo, rr, retinfo.runtimeresult.trkey, 0, retinfo.declresult.trkey, trgt));
            }
            else {
                this.m_currentBlock.push(new MIRSliceEpehmeralList(sinfo, rr, retinfo.runtimeresult.trkey, retinfo.declresult.trkey, trgt));
            }

            const refbase = retinfo.elrcount != -1 ? retinfo.elrcount : 1;
            const argvs = retinfo.refargs.map((rinfo, idx) => {
                return {pos: refbase + idx, into: rinfo[0], oftype: (retinfo.declresult.options[0] as MIREphemeralListType).entries[refbase + idx]};
            });

            this.emitMultiLoadFromEpehmeralList(sinfo, rr, retinfo.declresult, argvs);
        }
    }

    emitInvokeVirtualOperator(sinfo: SourceInfo, vresolve: MIRVirtualMethodKey, args: { arglayouttype: MIRType, argflowtype: MIRType, arg: MIRArgument }[], retinfo: { declresult: MIRType, runtimeresult: MIRType, elrcount: number, refargs: [MIRRegisterArgument, MIRType][] }, trgt: MIRRegisterArgument) {
        const eargs = args.map((arg) => {
            return { arglayouttype: arg.arglayouttype.trkey, argflowtype: arg.argflowtype.trkey, arg: arg.arg };
        });

        if (retinfo.refargs.length === 0) {
            this.m_currentBlock.push(new MIRInvokeVirtualOperator(sinfo, retinfo.declresult.trkey, vresolve, eargs, trgt));
        }
        else {
            const rr = this.generateTmpRegister();
            this.m_currentBlock.push(new MIRInvokeVirtualOperator(sinfo, retinfo.runtimeresult.trkey, vresolve, eargs, rr));

            if (retinfo.elrcount === -1) {
                this.m_currentBlock.push(new MIRLoadFromEpehmeralList(sinfo, rr, retinfo.runtimeresult.trkey, 0, retinfo.declresult.trkey, trgt));
            }
            else {
                this.m_currentBlock.push(new MIRSliceEpehmeralList(sinfo, rr, retinfo.runtimeresult.trkey, retinfo.declresult.trkey, trgt));
            }

            const refbase = retinfo.elrcount != -1 ? retinfo.elrcount : 1;
            const argvs = retinfo.refargs.map((rinfo, idx) => {
                return { pos: refbase + idx, into: rinfo[0], oftype: (retinfo.declresult.options[0] as MIREphemeralListType).entries[refbase + idx] };
            });

            this.emitMultiLoadFromEpehmeralList(sinfo, rr, retinfo.declresult, argvs);
        }
    }

    emitConstructorTuple(sinfo: SourceInfo, resultTupleType: MIRType, args: MIRArgument[], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorTuple(sinfo, resultTupleType.trkey, args, trgt));
    }

    emitConstructorTupleFromEphemeralList(sinfo: SourceInfo, resultTupleType: MIRType, arg: MIRArgument, elisttype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorTupleFromEphemeralList(sinfo, resultTupleType.trkey, arg, elisttype.trkey, trgt));
    }

    emitConstructorRecord(sinfo: SourceInfo, resultRecordType: MIRType, args: [string, MIRArgument][], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorRecord(sinfo, resultRecordType.trkey, args, trgt));
    }

    emitConstructorRecordFromEphemeralList(sinfo: SourceInfo, resultRecordType: MIRType, arg: MIRArgument, elisttype: MIRType, namelayout: string[], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorRecordFromEphemeralList(sinfo, resultRecordType.trkey, arg, elisttype.trkey, namelayout, trgt));
    }

    emitStructuredAppendTuple(sinfo: SourceInfo, resultTupleType: MIRType, args: MIRArgument[], ttypes: {layout: MIRType, flow: MIRType}[], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const etypes = ttypes.map((tt) => {
            return { layout: tt.layout.trkey, flow: tt.flow.trkey };
        });
        this.m_currentBlock.push(new MIRStructuredAppendTuple(sinfo, resultTupleType.trkey, args, etypes, trgt));
    } 

    emitStructuredJoinRecord(sinfo: SourceInfo, resultRecordType: MIRType, args: MIRArgument[], ttypes: {layout: MIRType, flow: MIRType}[], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const etypes = ttypes.map((tt) => {
            return { layout: tt.layout.trkey, flow: tt.flow.trkey };
        });
        this.m_currentBlock.push(new MIRStructuredJoinRecord(sinfo, resultRecordType.trkey, args, etypes, trgt));
    }

    emitConstructorValueList(sinfo: SourceInfo, resultEphemeralType: MIRType, args: MIRArgument[], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorEphemeralList(sinfo, resultEphemeralType.trkey, args, trgt));
    }

    emitMIRPackExtend(sinfo: SourceInfo, basepack: MIRArgument, basetype: MIRType, ext: MIRArgument[], sltype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIREphemeralListExtend(sinfo, basepack, basetype.trkey, ext, sltype.trkey, trgt));
    }

    emitConstructorPrimaryCollectionEmpty(sinfo: SourceInfo, tkey: MIRResolvedTypeKey, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorPrimaryCollectionEmpty(sinfo, tkey, trgt));
    }

    emitConstructorPrimaryCollectionSingletons(sinfo: SourceInfo, tkey: MIRResolvedTypeKey, args: [MIRType, MIRArgument][], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorPrimaryCollectionSingletons(sinfo, tkey, args.map((arg) => [arg[0].trkey, arg[1]]), trgt));
    }

    emitConstructorPrimaryCollectionCopies(sinfo: SourceInfo, tkey: MIRResolvedTypeKey, args: [MIRType, MIRArgument][], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorPrimaryCollectionCopies(sinfo, tkey, args.map((arg) => [arg[0].trkey, arg[1]]), trgt));
    }

    emitConstructorPrimaryCollectionMixed(sinfo: SourceInfo, tkey: MIRResolvedTypeKey, args: [boolean, MIRType, MIRArgument][], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRConstructorPrimaryCollectionMixed(sinfo, tkey, args.map((arg) => [arg[0], arg[1].trkey, arg[2]]), trgt));
    }

    emitBinKeyEq(sinfo: SourceInfo, lhslayouttype: MIRType, lhsflowtype: MIRType, lhs: MIRArgument, rhslayouttype: MIRType, rhsflowtype: MIRType, rhs: MIRArgument, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRBinKeyEq(sinfo, lhslayouttype.trkey, lhsflowtype.trkey, lhs, rhslayouttype.trkey, rhsflowtype.trkey, rhs, trgt));
    }

    emitBinKeyLess(sinfo: SourceInfo, lhslayouttype: MIRType, lhsflowtype: MIRType, lhs: MIRArgument, rhslayouttype: MIRType, rhsflowtype: MIRType, rhs: MIRArgument, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRBinKeyLess(sinfo, lhslayouttype.trkey, lhsflowtype.trkey, lhs, rhslayouttype.trkey, rhsflowtype.trkey, rhs, trgt));
    }

    emitPrefixNotOp(sinfo: SourceInfo, arg: MIRArgument, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRPrefixNotOp(sinfo, arg, trgt));
    }

    emitAllTrue(sinfo: SourceInfo, args: MIRArgument[], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRAllTrue(sinfo, args, trgt));
    }

    emitSomeTrue(sinfo: SourceInfo, args: MIRArgument[], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRSomeTrue(sinfo, args, trgt));
    }
    
    emitTypeOf(sinfo: SourceInfo, trgt: MIRRegisterArgument, chktype: MIRType, src: MIRArgument, srclayouttype: MIRType, srcflowtype: MIRType, guard: MIRStatmentGuard | undefined) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRIsTypeOf(sinfo, trgt, chktype.trkey, src, srclayouttype.trkey, srcflowtype.trkey, guard));
    }

    emitDirectJump(sinfo: SourceInfo, blck: string) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRJump(sinfo, blck));
    }

    emitBoolJump(sinfo: SourceInfo, arg: MIRRegisterArgument, trueblck: string, falseblck: string) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRJumpCond(sinfo, arg, trueblck, falseblck));
    }

    emitNoneJump(sinfo: SourceInfo, arg: MIRRegisterArgument, arglayout: MIRType, noneblck: string, someblk: string, ) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRJumpNone(sinfo, arg, arglayout.trkey, noneblck, someblk));
    }

    emitReturnAssign(sinfo: SourceInfo, src: MIRArgument, rtype: MIRType) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRReturnAssign(sinfo, src, rtype.trkey));
    }

    emitReturnAssignOfCons(sinfo: SourceInfo, oftype: MIRType, args: MIRArgument[]) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRReturnAssignOfCons(sinfo, oftype.trkey, args));
    }

    processEnterYield() {
        if(!this.emitEnabled) {
            return;
        }

        this.yieldPatchInfo.push([]);
    }

    getActiveYieldSet(): [string, MIRRegisterArgument, ValueType][] {
        return this.emitEnabled ? this.yieldPatchInfo[this.yieldPatchInfo.length - 1] : [];
    }

    processExitYield() {
        if(!this.emitEnabled) {
            return;
        }

        this.yieldPatchInfo.pop();
    }

    getActiveReturnSet(): [string, MIRRegisterArgument, ValueType][] {
        return this.emitEnabled ? this.returnPatchInfo : [];
    }


    localLifetimeStart(sinfo: SourceInfo, name: string, vtype: MIRType) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRVarLifetimeStart(sinfo, name, vtype.trkey));
    }

    localLifetimeEnd(sinfo: SourceInfo, name: string) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRVarLifetimeEnd(sinfo, name));
    }

    getBody(file: string, sinfo: SourceInfo): MIRBody | undefined {
        if(!this.emitEnabled) {
            return undefined;
        }

        let ibody = new MIRBody(file, sinfo, this.m_blockMap);
        simplifyBody(ibody);

        return ibody;
    }

    getVCallInstantiations(assembly: Assembly): [MIRVirtualMethodKey, MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>], MemberMethodDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] {
        if (this.allVInvokes.length === 0) {
            return [];
        }

        let resvi = new Map<string, [MIRVirtualMethodKey, MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>], MemberMethodDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]]>();
        for (let i = 0; i < this.allVInvokes.length; ++i) {
            const vinv = this.allVInvokes[i];

            const vcpt = vinv[2];
            const impls = this.entityInstantiationInfo.filter((iinfo) => {
                if (iinfo[1] instanceof EntityTypeDecl) {
                    const etype = ResolvedType.createSingle(ResolvedEntityAtomType.create(iinfo[1] as EntityTypeDecl, iinfo[2]));
                    return assembly.subtypeOf(etype, vcpt);
                }
                else {
                    const cpt = ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(iinfo[1] as ConceptTypeDecl, iinfo[2])]);
                    const ctype = ResolvedType.createSingle(cpt);
                    return assembly.subtypeOf(ctype, vcpt);
                }
            });

            for (let j = 0; j < impls.length; ++j) {
                const impl = impls[j];
                const itype = ResolvedType.createSingle(ResolvedEntityAtomType.create(impl[1] as EntityTypeDecl, impl[2]));

                const mcreate_multi = assembly.tryGetMethodUniqueConcreteDeclFromType(itype, vinv[3]);
                if (mcreate_multi !== undefined) {
                    const mcreate = new OOMemberLookupInfo<MemberMethodDecl>(mcreate_multi.contiainingType, mcreate_multi.decl[0], mcreate_multi.binds);
                    const binds = new Map<string, ResolvedType>(mcreate.binds);
                    vinv[4].forEach((v, k) => binds.set(k, v));

                    const mctype = (mcreate.contiainingType instanceof EntityTypeDecl) ? ResolvedType.createSingle(ResolvedEntityAtomType.create(mcreate.contiainingType, mcreate.binds)) : ResolvedType.createSingle(ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(mcreate.contiainingType as ConceptTypeDecl, mcreate.binds)]));
                    const mirmctype = this.registerResolvedTypeReference(mctype);
                    const mkey = MIRKeyGenerator.generateMethodKey(mcreate.decl.name, mirmctype.trkey, binds, vinv[5]);
                    if (!resvi.has(mkey)) {
                        resvi.set(mkey, [vinv[0], mkey, mcreate.decl.name, `${mirmctype.trkey}::${mcreate.decl.name}`, [mirmctype, mcreate.contiainingType, mcreate.binds], mcreate.decl, binds, vinv[5], vinv[6]] as [MIRVirtualMethodKey, MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>], MemberMethodDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]]);
                    }
                }
            }
        }

        let fres: [MIRVirtualMethodKey, MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>], MemberMethodDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];
        resvi.forEach((v) => fres.push(v));

        return fres;
    }

    private generateSigKeys(invoke: InvokeDecl, binds: Map<string, ResolvedType>): string[] {
        const sigkeys: string[] = [];

        for (let i = 0; i < invoke.params.length; ++i) {
            const ptype = this.assembly.normalizeTypeGeneral(invoke.params[i], binds);
            if (ptype instanceof ResolvedFunctionType || ptype.isEmptyType()) {
                continue;
            }

            if (invoke.params[i].litexp === undefined) {
                sigkeys.push(this.registerResolvedTypeReference(ptype).trkey);
            }
            else {
                const lev = (invoke.params[i].litexp as LiteralExpressionValue);
                const cexp = this.assembly.reduceLiteralValueToCanonicalForm(lev.exp, binds, ptype);
                if(cexp === undefined) {
                    return [];
                }

                sigkeys.push(cexp[2]);
            }
        }

        return sigkeys;
    }

    private getVirtualOpImpls(vkey: MIRVirtualMethodKey, optns: string | undefined, optenclosingType: [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]): [MIRVirtualMethodKey, MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, InvokeDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] {
        let impls: [MIRVirtualMethodKey, MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, InvokeDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];
        
        if(optns !== undefined) {
            const ns = optns as string;

            const nsd = this.assembly.getNamespace(ns);
            if (nsd !== undefined) {
                nsd.operators.forEach((op) => {
                    if (op[1].name === name && !OOPTypeDecl.attributeSetContains("abstract", op[1].invoke.attributes)) {
                        const sigkeys = this.generateSigKeys(op[1].invoke, binds);
                        const key = MIRKeyGenerator.generateFunctionKey(ns, name, binds, pcodes);
                        const okey = MIRKeyGenerator.generateOperatorSignatureKey(key, op[1].isPrefix, op[1].isInfix, sigkeys);

                        impls.push([vkey, okey, op[1].name, `${ns}::${op[1].name}`, undefined, op[1].invoke, binds, pcodes, cargs]);
                    }
                });
            }
        }
        else {
            const enclosingType = optenclosingType as [MIRType, OOPTypeDecl, Map<string, ResolvedType>];

            const ootype = enclosingType[1];
            ootype.staticOperators.forEach((op) => {
                if (op.name === name && !OOPTypeDecl.attributeSetContains("abstract", op.invoke.attributes)) {
                    const sigkeys = this.generateSigKeys(op.invoke, binds);
                    const key = MIRKeyGenerator.generateFunctionKey(enclosingType[0].trkey, name, binds, pcodes);
                    const okey = MIRKeyGenerator.generateOperatorSignatureKey(key, op.isPrefix, op.isInfix, sigkeys);

                    impls.push([vkey, okey, op.name, `${enclosingType[0].trkey}::${op.name}`, enclosingType, op.invoke, binds, pcodes, cargs]);
                }
            });
        }

        return impls;
    }

    private registerTypeInstantiation(rtype: ResolvedType, decl: OOPTypeDecl, binds: Map<string, ResolvedType>) {
        if(!this.emitEnabled) {
            return;
        }

        const key = MIRKeyGenerator.generateTypeKey(rtype);
        if (this.masm.conceptDecls.has(key) || this.masm.entityDecls.has(key) || this.pendingOOProcessing.findIndex((oop) => oop[0] === key) !== -1) {
            return;
        }

        if (decl.ns === "NSCore" && decl.name === "Result") {    
            const okdecl = this.assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Result::Ok") as EntityTypeDecl;
            const okkey = MIRKeyGenerator.generateTypeKey(ResolvedType.createSingle(ResolvedEntityAtomType.create(okdecl, binds)));
            if (!this.masm.entityDecls.has(okkey) && this.pendingOOProcessing.findIndex((oop) => oop[0] === okkey) === -1) {
                this.pendingOOProcessing.push([okkey, okdecl, binds]);
                this.entityInstantiationInfo.push([okkey, okdecl, binds]);
            }

            const errdecl = this.assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Result::Err") as EntityTypeDecl;
            const errkey = MIRKeyGenerator.generateTypeKey(ResolvedType.createSingle(ResolvedEntityAtomType.create(errdecl, binds)));
            if (!this.masm.entityDecls.has(errkey) && this.pendingOOProcessing.findIndex((oop) => oop[0] === errkey) === -1) {
                this.pendingOOProcessing.push([errkey, errdecl, binds]);
                this.entityInstantiationInfo.push([errkey, errdecl, binds]);
            }
        }

        this.pendingOOProcessing.push([key, decl, binds]);
        this.entityInstantiationInfo.push([key, decl, binds]);
    }

    registerResolvedTypeReference(t: ResolvedType): MIRType {
        if (t.options.length > 1) {
            const oopts = t.options.map((opt) => this.registerResolvedTypeReference(ResolvedType.createSingle(opt)).options);
            const ft = MIRType.create(([] as MIRTypeOption[]).concat(...oopts));

            if(this.emitEnabled) {
                this.masm.typeMap.set(ft.trkey, ft);
            }

            return ft;
        }
        else {
            const sopt = t.options[0];
            const rtt = ResolvedType.createSingle(sopt);
            let rt: MIRTypeOption | undefined = undefined;

            if (sopt instanceof ResolvedEntityAtomType) {
                this.registerTypeInstantiation(rtt, sopt.object, sopt.binds);
                rt = MIREntityType.create(MIRKeyGenerator.generateTypeKey(rtt));
            }
            else if (sopt instanceof ResolvedConceptAtomType) {
                if(sopt.conceptTypes.length > 1) {
                    sopt.conceptTypes.forEach((opt) => this.registerResolvedTypeReference(ResolvedType.createSingle(ResolvedConceptAtomType.create([opt]))));
                }
                
                const natoms = sopt.conceptTypes.map((cpt) => {
                    this.registerTypeInstantiation(rtt, cpt.concept, cpt.binds);
                    return MIRKeyGenerator.generateTypeKey(rtt);
                });
                rt = MIRConceptType.create(natoms);
            }
            else if (sopt instanceof ResolvedTupleAtomType) {
                const tatoms = sopt.types.map((entry) => new MIRTupleTypeEntry(this.registerResolvedTypeReference(entry.type), entry.isOptional));
                rt = MIRTupleType.create(sopt.isvalue, sopt.grounded, tatoms);
                if(!this.masm.tupleDecls.has(rt.trkey)) {
                    this.masm.tupleDecls.set(rt.trkey, rt as MIRTupleType);
                }
            }
            else if (sopt instanceof ResolvedRecordAtomType) {
                const tatoms = sopt.entries.map((entry) => new MIRRecordTypeEntry(entry.name, this.registerResolvedTypeReference(entry.type), entry.isOptional));
                rt = MIRRecordType.create(sopt.isvalue, sopt.grounded, tatoms);
                if(!this.masm.recordDecls.has(rt.trkey)) {
                    this.masm.recordDecls.set(rt.trkey, rt as MIRRecordType);
                }
            }
            else if(sopt instanceof ResolvedLiteralAtomType) {
                const 
                rt = MIRLiteralType.create(sopt.idStr, sopt.ofvalue);
                if(!this.masm.literalTypes.has(rt.trkey)) {
                    this.masm.literalTypes.set(rt.trkey, rt as MIRLiteralType);
                }
            }
            else {
                const vpatoms = (sopt as ResolvedEphemeralListType).types.map((tt) => this.registerResolvedTypeReference(tt));
                rt = MIREphemeralListType.create(vpatoms);
                if(!this.masm.ephemeralListDecls.has(rt.trkey)) {
                    this.masm.ephemeralListDecls.set(rt.trkey, rt as MIREphemeralListType);
                }
            }

            const ft = MIRType.create([(rt as MIRTypeOption)]);
            if(this.emitEnabled) {
                this.masm.typeMap.set(ft.trkey, ft);
            }

            return ft;
        }
    }

    registerPendingGlobalProcessing(decl: NamespaceConstDecl, etype: ResolvedType): MIRGlobalKey {
        const key = MIRKeyGenerator.generateFunctionKey(`global@${decl.ns}`, decl.name, new Map<string, ResolvedType>(), []);
        const gkey = "$global_" + key;
        if (!this.emitEnabled || this.masm.constantDecls.has(gkey) || this.pendingConstExprProcessing.findIndex((gp) => gp[0] === key) !== -1) {
            return key;
        }

        this.pendingConstExprProcessing.push([key, decl.srcFile, decl.name, undefined, decl.value, ["static_initializer", ...decl.attributes], new Map<string, ResolvedType>(), etype]);
        return gkey;
    }

    registerPendingConstProcessing(containingtype: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], decl: StaticMemberDecl, binds: Map<string, ResolvedType>, etype: ResolvedType): MIRGlobalKey {
        const key = MIRKeyGenerator.generateFunctionKey(`static@${containingtype[0].trkey}`, decl.name, new Map<string, ResolvedType>(), []);
        const gkey = "$global_" + key;
        if (!this.emitEnabled || this.masm.constantDecls.has(gkey) || this.pendingConstExprProcessing.findIndex((cp) => cp[0] === key) !== -1) {
            return key;
        }

        this.pendingConstExprProcessing.push([key, decl.srcFile, decl.name, containingtype, decl.value as ConstantExpressionValue, ["static_initializer", ...decl.attributes], binds, etype]);
        return gkey;
    }

    registerConstExpr(srcFile: string, exp: ConstantExpressionValue, binds: Map<string, ResolvedType>, etype: ResolvedType): MIRGlobalKey {
        const key = MIRKeyGenerator.generateFunctionKey(`cexpr@${srcFile}#${exp.exp.sinfo.pos}`, "expr", new Map<string, ResolvedType>(), []);
        const gkey = "$global_" + key;
        if (!this.emitEnabled || this.masm.constantDecls.has(gkey) || this.pendingConstExprProcessing.findIndex((cp) => cp[0] === key) !== -1) {
            return key;
        }

        this.pendingConstExprProcessing.push([key, srcFile, "[CONST]", undefined, exp, ["constexp_initializer"], binds, etype]);
        return gkey;
    }

    registerFunctionCall(ns: string, name: string, f: NamespaceFunctionDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generateFunctionKey(ns, name, binds, pcodes);
        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingFunctionProcessing.findIndex((fp) => fp[0] === key) !== -1) {
            return key;
        }

        this.pendingFunctionProcessing.push([key, f.name, name, undefined, f.invoke, binds, pcodes, cinfo]);
        return key;
    }

    registerNamespaceOperatorCall(ns: string, name: string, opdecl: NamespaceOperatorDecl, sigkeys: string[], pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generateFunctionKey(ns, name, new Map<string, ResolvedType>(), pcodes);
        const okey = MIRKeyGenerator.generateOperatorSignatureKey(key, opdecl.isPrefix, opdecl.isInfix, sigkeys);

        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingOperatorProcessing.findIndex((fp) => fp[0] === okey) !== -1) {
            return okey;
        }

        this.pendingOperatorProcessing.push([okey, opdecl.name, name, undefined, opdecl.invoke, new Map<string, ResolvedType>(), pcodes, cinfo]);
        return okey;
    }

    registerStaticCall(containingType: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], f: StaticFunctionDecl, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generateFunctionKey(containingType[0].trkey, name, binds, pcodes);
        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingFunctionProcessing.findIndex((sp) => sp[0] === key) !== -1) {
            return key;
        }

        this.pendingFunctionProcessing.push([key, f.name, name, containingType, f.invoke, binds, pcodes, cinfo]);
        return key;
    }

    registerStaticOperatorCall(containingType: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], name: string, opdecl: StaticOperatorDecl, sigkeys: string[], binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generateFunctionKey(containingType[0].trkey, name, binds, pcodes);
        const okey = MIRKeyGenerator.generateOperatorSignatureKey(key, opdecl.isPrefix, opdecl.isInfix, sigkeys);

        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingOperatorProcessing.findIndex((sp) => sp[0] === key) !== -1) {
            return okey;
        }

        this.pendingOperatorProcessing.push([okey, opdecl.name, name, containingType, opdecl.invoke, binds, pcodes, cinfo]);
        return okey;
    }

    registerMethodCall(containingType: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], m: MemberMethodDecl, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const vkey = MIRKeyGenerator.generateVirtualMethodKey(name, binds, pcodes);
        const key = MIRKeyGenerator.generateMethodKey(name, containingType[0].trkey, binds, pcodes);
        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingOOMethodProcessing.findIndex((mp) => mp[1] === key) !== -1) {
            return key;
        }

        this.pendingOOMethodProcessing.push([vkey, key, m.name, name, containingType, m, binds, pcodes, cinfo]);
        return key;
    }

    registerVirtualMethodCall(containingType: ResolvedType, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRVirtualMethodKey {
        const key = MIRKeyGenerator.generateVirtualMethodKey(name, binds, pcodes);
        const tkey = containingType.idStr;
        if (!this.emitEnabled || this.allVInvokes.findIndex((vi) => vi[0] === key && vi[1] === tkey) !== -1) {
            return key;
        }

        this.allVInvokes.push([key, tkey, containingType, name, binds, pcodes, cinfo]);
        return key;
    }

    registerVirtualNamespaceOperatorCall(ns: string, name: string, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRVirtualMethodKey {
        const key = MIRKeyGenerator.generateVirtualMethodKey(`${ns}::${name}`, new Map<string, ResolvedType>(), pcodes);
        if (!this.emitEnabled || this.masm.virtualOperatorDecls.has(key) || this.pendingOPVirtualProcessing.findIndex((vi) => vi[0] === key) !== -1) {
            return key;
        }

        this.pendingOPVirtualProcessing.push([key, ns, undefined, name, new Map<string, ResolvedType>(), pcodes, cinfo]);
        return key;
    }

    registerVirtualStaticOperatorCall(containingType: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRVirtualMethodKey {
        const key = MIRKeyGenerator.generateVirtualMethodKey(`${containingType[0].trkey}::${name}`, new Map<string, ResolvedType>(), pcodes);
        if (!this.emitEnabled || this.masm.virtualOperatorDecls.has(key) || this.pendingOPVirtualProcessing.findIndex((vi) => vi[0] === key) !== -1) {
            return key;
        }

        this.pendingOPVirtualProcessing.push([key, undefined, containingType, name, binds, pcodes, cinfo]);
        return key;
    }

    registerPCode(idecl: InvokeDecl, fsig: ResolvedFunctionType, binds: Map<string, ResolvedType>, cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generatePCodeKey(idecl);
        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingPCodeProcessing.findIndex((fp) => fp[0] === key) !== -1) {
            return key;
        }

        this.pendingPCodeProcessing.push([key, idecl, fsig, binds, cinfo]);
        return key;
    }

    static generateMASM(pckge: PackageConfig, buildLevel: BuildLevel, entrypoints: { namespace: string, names: string[] }, functionalize: boolean, srcFiles: { relativePath: string, contents: string }[]): { masm: MIRAssembly | undefined, errors: string[] } {
        ////////////////
        //Parse the contents and generate the assembly
        const assembly = new Assembly();
        let p = new Parser(assembly);
        try {
            for (let i = 0; i < srcFiles.length; ++i) {
                p.parseCompilationUnitPass1(srcFiles[i].relativePath, srcFiles[i].contents);
            }

            for (let i = 0; i < srcFiles.length; ++i) {
                p.parseCompilationUnitPass2(srcFiles[i].relativePath, srcFiles[i].contents);
            }
        }
        catch (ex) {
            return { masm: undefined, errors: [`Hard failure in parse with exception -- ${ex}`] };
        }

        const parseErrors = p.getParseErrors();
        if (parseErrors !== undefined) {
            return { masm: undefined, errors: parseErrors.map((err: [string, number, string]) => JSON.stringify(err)) };
        }

        ////////////////
        //Compute the assembly hash and initialize representations
        const hash = Crypto.createHash("sha512");
        const data = [...srcFiles].sort((a, b) => a.relativePath.localeCompare(b.relativePath));
        data.forEach((sf) => {
            hash.update(sf.relativePath);
            hash.update(sf.contents);
        });

        const masm = new MIRAssembly(pckge, srcFiles, hash.digest("hex"));
        const emitter = new MIREmitter(assembly, masm, true);
        const checker = new TypeChecker(assembly, emitter, buildLevel);

        emitter.registerResolvedTypeReference(assembly.getSpecialAnyConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialSomeConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialKeyTypeConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialPODTypeConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialAPITypeConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialAPIValueConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialObjectConceptType());

        emitter.registerResolvedTypeReference(assembly.getSpecialNoneType());
        emitter.registerResolvedTypeReference(assembly.getSpecialBoolType());
        emitter.registerResolvedTypeReference(assembly.getSpecialIntType());
        emitter.registerResolvedTypeReference(assembly.getSpecialNatType());
        emitter.registerResolvedTypeReference(assembly.getSpecialBigIntType());
        emitter.registerResolvedTypeReference(assembly.getSpecialBigNatType());
        emitter.registerResolvedTypeReference(assembly.getSpecialRationalType());
        emitter.registerResolvedTypeReference(assembly.getSpecialFloatType());
        emitter.registerResolvedTypeReference(assembly.getSpecialDecimalType());
        emitter.registerResolvedTypeReference(assembly.getSpecialStringType());
        emitter.registerResolvedTypeReference(assembly.getSpecialBufferFormatType());
        emitter.registerResolvedTypeReference(assembly.getSpecialBufferEncodingType());
        emitter.registerResolvedTypeReference(assembly.getSpecialBufferCompressionType());
        emitter.registerResolvedTypeReference(assembly.getSpecialByteBufferType());
        emitter.registerResolvedTypeReference(assembly.getSpecialUUIDType());
        emitter.registerResolvedTypeReference(assembly.getSpecialCryptoHashType());
        emitter.registerResolvedTypeReference(assembly.getSpecialRegexType());
        emitter.registerResolvedTypeReference(assembly.getSpecialRegexMatchType());

        //get any entrypoint functions and initialize the checker there
        const epns = assembly.getNamespace(entrypoints.namespace);
        if (epns === undefined) {
            return { masm: undefined, errors: [`Could not find namespace ${entrypoints.namespace}`] };
        }
        else {
            if(entrypoints.names.length === 0) {
                return { masm: undefined, errors: ["No entrypoints specified"] };
            }

            for(let i = 0; i < entrypoints.names.length; ++i) {
                const f = epns.functions.get(entrypoints.names[i]);
                if(f === undefined) {
                    return { masm: undefined, errors: [`Could not find function ${entrypoints.names[i]}`] };
                }

                emitter.registerFunctionCall(f.ns, f.name, f, new Map<string, ResolvedType>(), [], []);
            }
        }

        ////////////////
        //While there is more to process get an item and run the checker on it
        try {
            let lastVCount = -1;
            while (true) {
                while (emitter.pendingOOProcessing.length !== 0 || emitter.pendingConstExprProcessing.length !== 0
                    || emitter.pendingFunctionProcessing.length !== 0 || emitter.pendingOperatorProcessing.length !== 0 
                    || emitter.pendingOOMethodProcessing.length !== 0 || emitter.pendingPCodeProcessing.length !== 0
                    || emitter.pendingOPVirtualProcessing.length !== 0) {

                    while (emitter.pendingOOProcessing.length !== 0) {
                        const tt = emitter.pendingOOProcessing.pop() as [MIRResolvedTypeKey, OOPTypeDecl, Map<string, ResolvedType>];
                        checker.processOOType(...tt);
                    }

                    if(emitter.pendingConstExprProcessing.length !== 0) {
                        const pc = emitter.pendingConstExprProcessing.pop() as [MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, ConstantExpressionValue, string[], Map<string, ResolvedType>, ResolvedType];
                        checker.processConstExpr(...pc);
                    }
                    else if (emitter.pendingFunctionProcessing.length !== 0) {
                        const pf = emitter.pendingFunctionProcessing.pop() as [MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, InvokeDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]];
                        checker.processFunctionDecl(...pf);
                    }
                    else if (emitter.pendingOperatorProcessing.length !== 0) {
                        const pf = emitter.pendingOperatorProcessing.pop() as [MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, InvokeDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]];
                        checker.processFunctionDecl(...pf);
                    }
                    else if (emitter.pendingOOMethodProcessing.length !== 0) {
                        const mf = emitter.pendingOOMethodProcessing.pop() as [MIRVirtualMethodKey, MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>], MemberMethodDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]];
                        checker.processMethodFunction(...mf);
                    }
                    else if (emitter.pendingPCodeProcessing.length !== 0) {
                        const lf = emitter.pendingPCodeProcessing.pop() as [MIRInvokeKey, InvokeDecl, ResolvedFunctionType, Map<string, ResolvedType>, [string, ResolvedType][]];
                        checker.processLambdaFunction(...lf);
                    }
                    else if (emitter.pendingOPVirtualProcessing.length !== 0) {
                        const vop = emitter.pendingOPVirtualProcessing.pop() as [MIRVirtualMethodKey, string | undefined, [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, string, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]];
                        const opimpls = emitter.getVirtualOpImpls(...vop);
                        for (let i = 0; i < opimpls.length; ++i) {
                            checker.processVirtualOperator(...opimpls[i]);
                        }
                    }
                    else {
                        ;
                    }
                }

                //make sure all vcall candidates are processed
                const vcgens = emitter.getVCallInstantiations(assembly);
                if (vcgens.length === lastVCount) {
                    break;
                }
                lastVCount = vcgens.length;
                
                for (let i = 0; i < vcgens.length; ++i) {
                    checker.processMethodFunction(...vcgens[i]);
                }
            }

            if (checker.getErrorList().length === 0) {
                checker.processRegexInfo();

                if (functionalize) {
                    functionalizeInvokes(emitter, masm);
                    ssaConvertInvokes(masm);
                }
            }
        }
        catch (ex) {
            //ignore
        }

        const tcerrors = checker.getErrorList();
        if (tcerrors.length !== 0) {
            return { masm: undefined, errors: tcerrors.map((err: [string, number, string]) => JSON.stringify(err)) };
        }
        else {
            return { masm: masm, errors: [] };
        }
    }
}

export { PCode, MIRKeyGenerator, MIREmitter };
