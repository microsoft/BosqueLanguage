//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo, Parser } from "../ast/parser";
import { MIRAbort, MIRArgument, MIRAssertCheck, MIRBasicBlock, MIRBinKeyEq, MIRBinKeyLess, MIRBody, MIRConstantArgument, MIRConstantBigInt, MIRConstantBigNat, MIRConstantDataString, MIRConstantDecimal, MIRConstantFalse, MIRConstantFloat, MIRConstantInt, MIRConstantNat, MIRConstantNone, MIRConstantRational, MIRConstantRegex, MIRConstantString, MIRConstantStringOf, MIRConstantTrue, MIRConstantTypedNumber, MIRConstructorEphemeralList, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionMixed, MIRConstructorPrimaryCollectionSingletons, MIRConstructorRecord, MIRConstructorRecordFromEphemeralList, MIRConstructorTuple, MIRConstructorTupleFromEphemeralList, MIRConvertValue, MIRDeadFlow, MIRDebug, MIRDeclareGuardFlagLocation, MIREntityProjectToEphemeral, MIREntityUpdate, MIREphemeralListExtend, MIRFieldKey, MIRGlobalKey, MIRGuard, MIRInvokeFixedFunction, MIRInvokeKey, MIRInvokeVirtualFunction, MIRInvokeVirtualOperator, MIRIsTypeOf, MIRJump, MIRJumpCond, MIRJumpNone, MIRLoadConst, MIRLoadField, MIRLoadFromEpehmeralList, MIRLoadRecordProperty, MIRLoadRecordPropertySetGuard, MIRLoadTupleIndex, MIRLoadTupleIndexSetGuard, MIRLoadUnintVariableValue, MIRMultiLoadFromEpehmeralList, MIRNop, MIROp, MIRPrefixNotOp, MIRRecordHasProperty, MIRRecordProjectToEphemeral, MIRRecordUpdate, MIRRegisterArgument, MIRResolvedTypeKey, MIRReturnAssign, MIRReturnAssignOfCons, MIRSetConstantGuardFlag, MIRSliceEpehmeralList, MIRStatmentGuard, MIRStructuredAppendTuple, MIRStructuredJoinRecord, MIRRegisterAssign, MIRTupleHasIndex, MIRTupleProjectToEphemeral, MIRTupleUpdate, MIRVarLifetimeEnd, MIRVarLifetimeStart, MIRVirtualMethodKey, MIRInject, MIRExtract, MIRGuardedOptionInject, MIRConstantNothing } from "./mir_ops";
import { Assembly, BuildLevel, ConceptTypeDecl, EntityTypeDecl, InvokeDecl, MemberMethodDecl, NamespaceConstDecl, NamespaceFunctionDecl, NamespaceOperatorDecl, OOMemberLookupInfo, OOPTypeDecl, StaticFunctionDecl, StaticMemberDecl, StaticOperatorDecl } from "../ast/assembly";
import { ResolvedConceptAtomType, ResolvedConceptAtomTypeEntry, ResolvedEntityAtomType, ResolvedEphemeralListType, ResolvedFunctionType, ResolvedRecordAtomType, ResolvedTupleAtomType, ResolvedType } from "../ast/resolved_type";
import { MIRAssembly, MIRConceptType, MIREntityType, MIREphemeralListType, MIRRecordType, MIRTupleType, MIRType, MIRTypeOption, PackageConfig } from "./mir_assembly";

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
    ikey: MIRInvokeKey,
    captured: Map<string, ResolvedType>,
    capturedpcode: Map<string, PCode>,
    ftype: ResolvedFunctionType
};

type GeneratedKeyName<T> = {
    keyid: T,
    shortname: string
}

class MIRKeyGenerator {
    static computeBindsKeyInfo(binds: Map<string, ResolvedType>): [string, string] {
        if (binds.size === 0) {
            return ["", ""];
        }

        let terms: string[] = [];
        binds.forEach((v, k) => terms.push(`${k}=${v.typeID}`));

        let shortterms: string[] = [];
        binds.forEach((v, k) => terms.push(`${k}=${v.shortID}`));

        return [`<${terms.sort().join(", ")}>`, `<${shortterms.sort().join(", ")}>`];
    }

    static computePCodeKeyInfo(pcodes: PCode[]): string {
        if (pcodes.length === 0) {
            return "";
        }

        return "[" + pcodes.map((pc) => `${pc.ikey}`).join(",") + "]";
    }

    static generateTypeKey(t: ResolvedType): GeneratedKeyName<MIRResolvedTypeKey> {
        return {keyid: t.typeID, shortname: t.shortID};
    }

    static generateFieldKey(t: ResolvedType, name: string): MIRFieldKey {
        const tkey = this.generateTypeKey(t);
        return `__f__${tkey.keyid}.${name}`;
    }

    static generateGlobalKeyWNamespace(ns: string, name: string, prefix?: string): GeneratedKeyName<MIRGlobalKey> {
        const fname = `__g__${prefix !== undefined ? (prefix + "#") : ""}${ns}::${name}`;
        const shortfname = `${prefix !== undefined ? (prefix + "#") : ""}${ns}::${name}`;

        return {keyid: fname, shortname: shortfname};
    }

    static generateGlobalKeyWType(t: ResolvedType, name: string, prefix?: string): GeneratedKeyName<MIRGlobalKey> {
        const tinfo = MIRKeyGenerator.generateTypeKey(t);

        const fname = `__g__${prefix !== undefined ? (prefix + "#") : ""}${tinfo.keyid}::${name}`;
        const shortfname = `${prefix !== undefined ? (prefix + "#") : ""}${tinfo.shortname}::${name}`;
        return {keyid: fname, shortname: shortfname};
    }

    static generateFunctionKeyWNamespace(ns: string, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], prefix?: string): GeneratedKeyName<MIRInvokeKey> {
        const [binfo, shortbinfo] = MIRKeyGenerator.computeBindsKeyInfo(binds);
        const pcinfo = MIRKeyGenerator.computePCodeKeyInfo(pcodes);

        const fname = `__i__${prefix !== undefined ? (prefix + "#") : ""}${ns}::${name}${binfo}${pcinfo}`;
        const shortfname = `${prefix !== undefined ? (prefix + "#") : ""}${ns}::${name}${shortbinfo}${pcinfo}`;
        return {keyid: fname, shortname: shortfname};
    }

    static generateFunctionKeyWType(t: ResolvedType, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], prefix?: string): GeneratedKeyName<MIRInvokeKey> {
        const tinfo = MIRKeyGenerator.generateTypeKey(t);
        const [binfo, shortbinfo] = MIRKeyGenerator.computeBindsKeyInfo(binds);
        const pcinfo = MIRKeyGenerator.computePCodeKeyInfo(pcodes);

        const fname = `__i__${prefix !== undefined ? (prefix + "#") : ""}${tinfo.keyid}::${name}${binfo}${pcinfo}`;
        const shortfname = `${prefix !== undefined ? (prefix + "#") : ""}${tinfo.shortname}::${name}${shortbinfo}${pcinfo}`;
        return {keyid: fname, shortname: shortfname};
    }

    static generateVirtualMethodKey(vname: string, binds: Map<string, ResolvedType>, pcodes: PCode[]): GeneratedKeyName<MIRVirtualMethodKey> {
        const [binfo, shortbinfo] = MIRKeyGenerator.computeBindsKeyInfo(binds);
        const pcinfo = MIRKeyGenerator.computePCodeKeyInfo(pcodes);


        const iname = `__v__${vname}${binfo}${pcinfo}`;
        const shortvname =  `${vname}${shortbinfo}${pcinfo}`;
        return {keyid: iname, shortname: shortvname};
    }

    static generatePCodeKey(isPCodeFn: boolean, bodyID: string): MIRInvokeKey {
        return `${isPCodeFn ? "fn" : "pred"}--${bodyID}`;
    }

    static generateOperatorSignatureKey(ikey: MIRInvokeKey, shortname: string, isprefix: boolean, isinfix: boolean, sigkeys: string[]): GeneratedKeyName<MIRInvokeKey> {
        if(isprefix) {
            ikey = ikey + "=prefix";
            shortname = shortname + "=prefix";
        }
        if(isinfix) {
            ikey = ikey + "=infix";
            shortname = shortname + "=infix";
        }

        return {keyid: ikey + `=(${sigkeys.join(", ")})`, shortname: shortname + `=(${sigkeys.join(", ")})`};
    }
}

type PendingConstExprProcessingInfo = { gkey: MIRGlobalKey, shortname: string, name: string, srcFile: string, containingType: [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, cexp: ConstantExpressionValue, attribs: string[], binds: Map<string, ResolvedType>, ddecltype: ResolvedType };
type PendingFunctionProcessingInfo = { fkey: MIRInvokeKey, shortname: string, name: string, enclosingdecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, invoke: InvokeDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][] };
type PendingOOMethodProcessingInfo = { vkey: MIRVirtualMethodKey, mkey: MIRInvokeKey, shortname: string, name: string, enclosingDecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], mdecl: MemberMethodDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][] };
type PendingPCodeProcessingInfo = { lkey: MIRInvokeKey, lshort: string, invoke: InvokeDecl, sigt: ResolvedFunctionType, bodybinds: Map<string, ResolvedType>, cargs: [string, ResolvedType][], capturedpcodes: [string, PCode][] };
type PendingOPVirtualProcessingInfo = { vkey: MIRVirtualMethodKey, optns: string | undefined, optenclosingType: [ResolvedType, MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][] };

type EntityInstantiationInfo = { tkey: MIRResolvedTypeKey, shortname: string, ootype: OOPTypeDecl, binds: Map<string, ResolvedType> };
type AllVInvokesInfo = { vkey: MIRVirtualMethodKey, enclosingtype: ResolvedType, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][] };

class MIREmitter {
    readonly assembly: Assembly;
    readonly masm: MIRAssembly;
    
    private readonly pendingOOProcessing: EntityInstantiationInfo[] = [];

    private readonly pendingConstExprProcessing: PendingConstExprProcessingInfo[] = [];
    private readonly pendingFunctionProcessing: PendingFunctionProcessingInfo[] = [];
    private readonly pendingOperatorProcessing: PendingFunctionProcessingInfo[] = [];
    private readonly pendingOOMethodProcessing: PendingOOMethodProcessingInfo[] = [];
    private readonly pendingPCodeProcessing: PendingPCodeProcessingInfo[] = [];
    private readonly pendingOPVirtualProcessing: PendingOPVirtualProcessingInfo[] = [];
    private readonly entityInstantiationInfo: EntityInstantiationInfo[] = [];
    private readonly allVInvokes: AllVInvokesInfo[] = [];

    private emitEnabled: boolean;
    
    private m_blockMap: Map<string, MIRBasicBlock> = new Map<string, MIRBasicBlock>();
    private m_currentBlockName = "UNDEFINED";
    private m_currentBlock: MIROp[] = [];

    private m_tmpIDCtr = 0;

    private m_capturedNameIDMap: Map<string, number> = new Map<string, number>();

    private yieldPatchInfo: [string, MIRRegisterArgument, ValueType][][] = [];
    private returnPatchInfo: [string, MIRRegisterArgument, ValueType][] = [];

    m_activeResultType: ResolvedType | undefined = undefined;

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

    initializeBodyEmitter(activeResultType: ResolvedType | undefined) {
        this.m_tmpIDCtr = 0;

        this.m_blockMap = new Map<string, MIRBasicBlock>();
        this.m_blockMap.set("entry", new MIRBasicBlock("entry", []));
        this.m_blockMap.set("returnassign", new MIRBasicBlock("returnassign", []));
        this.m_blockMap.set("exit", new MIRBasicBlock("exit", []));

        this.m_currentBlockName = "entry";
        this.m_currentBlock = (this.m_blockMap.get("entry") as MIRBasicBlock).ops;

        this.yieldPatchInfo = [];
        this.returnPatchInfo = [];

        this.m_activeResultType = activeResultType; 
    }

    generateTmpRegister(): MIRRegisterArgument {
        if(!this.emitEnabled) {
            return new MIRRegisterArgument(`@tmp_${-1}`);
        }

        return new MIRRegisterArgument(`@tmp_${this.m_tmpIDCtr++}`);
    }

    generateCapturedVarName(name: string, bodyid: string): string {
        if(!this.m_capturedNameIDMap.has(bodyid)) {
            this.m_capturedNameIDMap.set(bodyid, this.m_capturedNameIDMap.size);
        }

        return `@@c_${this.m_capturedNameIDMap.get(bodyid)}_${name}`;
    }

    
    flattenCapturedPCodeVarCaptures(cc: Map<string, PCode>): string[] {
        const ccopts = [...cc].map((ccx) => {
           return [...ccx[1].captured].map((cv) => this.generateCapturedVarName(cv[0], ccx[1].code.bodyID));
        });

        return ([] as string[]).concat(...ccopts).sort();
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

        this.m_currentBlock.push(new MIRRegisterAssign(sinfo, src, trgt, vtype.typeID, guard));
    }

    emitLoadUninitVariableValue(sinfo: SourceInfo, oftype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        //This value will not be accessed from but can be passed/assigned atomically
        //we need to have space for it etc. so just plop a "fresh" or zero-filled value there
        this.m_currentBlock.push(new MIRLoadUnintVariableValue(sinfo, trgt, oftype.typeID));
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

        this.m_currentBlock.push(new MIRConvertValue(sinfo, srctypelayout.typeID, srctypeflow.typeID, intotype.typeID, src, trgt, guard));
    }

    emitInject(sinfo: SourceInfo, srctype: MIRType, intotype: MIRType, src: MIRArgument, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRInject(sinfo, srctype.typeID, intotype.typeID, src, trgt));
    }

    emitGuardedOptionInject(sinfo: SourceInfo, srctype: MIRType, somethingtype: MIRType, optiontype: MIRType, src: MIRArgument, trgt: MIRRegisterArgument, guard: MIRStatmentGuard | undefined) {
        if(!this.emitEnabled) {
            return;
        }

        //either use default or inject into something and convert to Option

        this.m_currentBlock.push(new MIRGuardedOptionInject(sinfo, srctype.typeID, somethingtype.typeID, optiontype.typeID, src, trgt, guard));
    }

    emitExtract(sinfo: SourceInfo, srctype: MIRType, intotype: MIRType, src: MIRArgument, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRExtract(sinfo, srctype.typeID, intotype.typeID, src, trgt));
    }

    emitCheckNoError(sinfo: SourceInfo, src: MIRArgument, srctype: MIRType, oktype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRIsTypeOf(sinfo, trgt, oktype.typeID, src, srctype.typeID, srctype.typeID, undefined));
    }

    emitLoadConstNone(sinfo: SourceInfo, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantNone(), this.registerResolvedTypeReference(this.assembly.getSpecialNoneType()).typeID, trgt));
    }

    emitLoadConstNothing(sinfo: SourceInfo, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantNothing(), this.registerResolvedTypeReference(this.assembly.getSpecialNothingType()).typeID, trgt));
    }

    emitLoadConstBool(sinfo: SourceInfo, bv: boolean, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, bv ? new MIRConstantTrue() : new MIRConstantFalse(), this.registerResolvedTypeReference(this.assembly.getSpecialBoolType()).typeID, trgt));
    }

    emitLoadConstIntegralValue(sinfo: SourceInfo, itype: MIRType, vv: string, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        if(itype.typeID === "NSCore::Int") {
            this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantInt(vv), itype.typeID, trgt));
        }
        else if(itype.typeID === "NSCore::Nat") {
            this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantNat(vv), itype.typeID, trgt));
        }
        else if(itype.typeID === "NSCore::BigInt") {
            this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantBigInt(vv), itype.typeID, trgt));
        }
        else {
            this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantBigNat(vv), itype.typeID, trgt));
        }
    }

    emitLoadConstRational(sinfo: SourceInfo, iv: string, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantRational(iv), this.registerResolvedTypeReference(this.assembly.getSpecialRationalType()).typeID, trgt));
    }

    emitLoadConstFloatPoint(sinfo: SourceInfo, ftype: MIRType, fv: string, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        if(ftype.typeID === "NSCore::Float") {
            this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantFloat(fv), ftype.typeID, trgt));
        }
        else {
            this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantDecimal(fv), ftype.typeID, trgt));
        }
    }

    emitLoadConstString(sinfo: SourceInfo, sv: string, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantString(sv), this.registerResolvedTypeReference(this.assembly.getSpecialStringType()).typeID, trgt));
    }

    emitLoadLiteralRegex(sinfo: SourceInfo, restr: BSQRegex, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantRegex(restr), this.registerResolvedTypeReference(this.assembly.getSpecialRegexType()).typeID, trgt));
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
        
        this.m_currentBlock.push(new MIRTupleHasIndex(sinfo, arg, arglayouttype.typeID, argflowtype.typeID, idx, trgt));
    }

    emitRecordHasProperty(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, pname: string, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRRecordHasProperty(sinfo, arg, arglayouttype.typeID, argflowtype.typeID, pname, trgt));
    }
    
    emitLoadTupleIndex(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, idx: number, isvirtual: boolean, resulttype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRLoadTupleIndex(sinfo, arg, arglayouttype.typeID, argflowtype.typeID, idx, isvirtual, resulttype.typeID, trgt));
    }

    emitLoadTupleIndexSetGuard(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, idx: number, isvirtual: boolean, resulttype: MIRType, trgt: MIRRegisterArgument, guard: MIRGuard) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRLoadTupleIndexSetGuard(sinfo, arg, arglayouttype.typeID, argflowtype.typeID, idx, isvirtual, resulttype.typeID, trgt, guard));
    }

    emitLoadProperty(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, pname: string, isvirtual: boolean, resulttype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadRecordProperty(sinfo, arg, arglayouttype.typeID, argflowtype.typeID, pname, isvirtual, resulttype.typeID, trgt));
    }

    emitLoadRecordPropertySetGuard(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, pname: string, isvirtual: boolean, resulttype: MIRType, trgt: MIRRegisterArgument, guard: MIRGuard) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadRecordPropertySetGuard(sinfo, arg, arglayouttype.typeID, argflowtype.typeID, pname, isvirtual, resulttype.typeID, trgt, guard));
    }

    emitLoadField(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, fname: MIRFieldKey, isvirtual: boolean, resulttype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadField(sinfo, arg, arglayouttype.typeID, argflowtype.typeID, fname, isvirtual, resulttype.typeID, trgt));
    }

    emitTupleProjectToEphemeral(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, indecies: number[], isvirtual: boolean, epht: ResolvedEphemeralListType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRTupleProjectToEphemeral(sinfo, arg, arglayouttype.typeID, argflowtype.typeID, indecies, isvirtual, this.registerResolvedTypeReference(ResolvedType.createSingle(epht)).typeID, trgt));
    }

    emitRecordProjectToEphemeral(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, properties: string[], isvirtual: boolean, epht: ResolvedEphemeralListType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRRecordProjectToEphemeral(sinfo, arg, arglayouttype.typeID, argflowtype.typeID, properties, isvirtual, this.registerResolvedTypeReference(ResolvedType.createSingle(epht)).typeID, trgt));
    }

    emitEntityProjectToEphemeral(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, fields: MIRFieldKey[], isvirtual: boolean, epht: ResolvedEphemeralListType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIREntityProjectToEphemeral(sinfo, arg, arglayouttype.typeID, argflowtype.typeID, fields, isvirtual, this.registerResolvedTypeReference(ResolvedType.createSingle(epht)).typeID, trgt));
    }

    emitTupleUpdate(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, updates: [number, ResolvedType, MIRArgument][], isvirtual: boolean, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const upds = updates.map((upd) => [upd[0], upd[2], this.registerResolvedTypeReference(upd[1]).typeID] as [number, MIRArgument, MIRResolvedTypeKey]);
        this.m_currentBlock.push(new MIRTupleUpdate(sinfo, arg, arglayouttype.typeID, argflowtype.typeID, upds, isvirtual, trgt));
    }

    emitRecordUpdate(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, updates: [string, ResolvedType, MIRArgument][], isvirtual: boolean, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const upds = updates.map((upd) => [upd[0], upd[2], this.registerResolvedTypeReference(upd[1]).typeID] as [string, MIRArgument, MIRResolvedTypeKey]);
        this.m_currentBlock.push(new MIRRecordUpdate(sinfo, arg, arglayouttype.typeID, argflowtype.typeID, upds, isvirtual, trgt));
    }

    emitEntityUpdate(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, updates: [MIRFieldKey, ResolvedType, MIRArgument][], isvirtual: boolean, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const upds = updates.map((upd) => [upd[0], upd[2], this.registerResolvedTypeReference(upd[1]).typeID] as [MIRFieldKey, MIRArgument, MIRResolvedTypeKey]);
        this.m_currentBlock.push(new MIREntityUpdate(sinfo, arg, arglayouttype.typeID, argflowtype.typeID, upds, isvirtual, trgt));
    }

    emitLoadFromEpehmeralList(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRType, idx: number, resulttype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRLoadFromEpehmeralList(sinfo, arg, argtype.typeID, idx, resulttype.typeID, trgt));
    }

    emitMultiLoadFromEpehmeralList(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRType, trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRType }[]) {
        if (!this.emitEnabled) {
            return;
        }

        const etrgts = trgts.map((trgt) => {
            return { pos: trgt.pos, into: trgt.into, oftype: trgt.oftype.typeID };
        });
        this.m_currentBlock.push(new MIRMultiLoadFromEpehmeralList(sinfo, arg, argtype.typeID, etrgts));
    }

    emitInvokeFixedFunction(sinfo: SourceInfo, ikey: MIRInvokeKey, args: MIRArgument[], optstatusmask: string | undefined, rretinfo: MIRType | { declresult: MIRType, runtimeresult: MIRType, elrcount: number, refargs: [MIRRegisterArgument, MIRType][] }, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const retinfo = rretinfo instanceof MIRType ? { declresult: rretinfo, runtimeresult: rretinfo, elrcount: -1, refargs: [] } : rretinfo;
        if (retinfo.refargs.length === 0) {
            this.m_currentBlock.push(new MIRInvokeFixedFunction(sinfo, retinfo.declresult.typeID, ikey, args, optstatusmask, trgt, undefined));
        }
        else {
            const rr = this.generateTmpRegister();
            this.m_currentBlock.push(new MIRInvokeFixedFunction(sinfo, retinfo.runtimeresult.typeID, ikey, args, optstatusmask, rr, undefined));

            if (retinfo.elrcount === -1) {
                this.m_currentBlock.push(new MIRLoadFromEpehmeralList(sinfo, rr, retinfo.runtimeresult.typeID, 0, retinfo.declresult.typeID, trgt));
            }
            else {
                this.m_currentBlock.push(new MIRSliceEpehmeralList(sinfo, rr, retinfo.runtimeresult.typeID, retinfo.declresult.typeID, trgt));
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

        this.m_currentBlock.push(new MIRInvokeFixedFunction(sinfo, retinfo.typeID, ikey, args, optstatusmask, trgt, guard));
    }

    emitInvokeVirtualFunction(sinfo: SourceInfo, vresolve: MIRVirtualMethodKey, shortvname: string, rcvrlayouttype: MIRType, rcvrflowtype: MIRType, args: MIRArgument[], optstatusmask: string | undefined, rretinfo: MIRType | { declresult: MIRType, runtimeresult: MIRType, elrcount: number, refargs: [MIRRegisterArgument, MIRType][] }, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const retinfo = rretinfo instanceof MIRType ? { declresult: rretinfo, runtimeresult: rretinfo, elrcount: -1, refargs: [] as [MIRRegisterArgument, MIRType][] } : rretinfo;
        if (retinfo.refargs.length === 0) {
            this.m_currentBlock.push(new MIRInvokeVirtualFunction(sinfo, retinfo.declresult.typeID, vresolve, shortvname, rcvrlayouttype.typeID, rcvrflowtype.typeID, args, optstatusmask, trgt));
        }
        else {
            const rr = this.generateTmpRegister();
            this.m_currentBlock.push(new MIRInvokeVirtualFunction(sinfo, retinfo.runtimeresult.typeID, vresolve, shortvname, rcvrlayouttype.typeID, rcvrflowtype.typeID, args, optstatusmask, rr));
           
            if (retinfo.elrcount === -1) {
                this.m_currentBlock.push(new MIRLoadFromEpehmeralList(sinfo, rr, retinfo.runtimeresult.typeID, 0, retinfo.declresult.typeID, trgt));
            }
            else {
                this.m_currentBlock.push(new MIRSliceEpehmeralList(sinfo, rr, retinfo.runtimeresult.typeID, retinfo.declresult.typeID, trgt));
            }

            const refbase = retinfo.elrcount != -1 ? retinfo.elrcount : 1;
            const argvs = retinfo.refargs.map((rinfo, idx) => {
                return {pos: refbase + idx, into: rinfo[0], oftype: (retinfo.declresult.options[0] as MIREphemeralListType).entries[refbase + idx]};
            });

            this.emitMultiLoadFromEpehmeralList(sinfo, rr, retinfo.declresult, argvs);
        }
    }

    emitInvokeVirtualOperator(sinfo: SourceInfo, vresolve: MIRVirtualMethodKey, shortvname: string, args: { arglayouttype: MIRType, argflowtype: MIRType, arg: MIRArgument }[], retinfo: { declresult: MIRType, runtimeresult: MIRType, elrcount: number, refargs: [MIRRegisterArgument, MIRType][] }, trgt: MIRRegisterArgument) {
        const eargs = args.map((arg) => {
            return { arglayouttype: arg.arglayouttype.typeID, argflowtype: arg.argflowtype.typeID, arg: arg.arg };
        });

        if (retinfo.refargs.length === 0) {
            this.m_currentBlock.push(new MIRInvokeVirtualOperator(sinfo, retinfo.declresult.typeID, vresolve, shortvname, eargs, trgt));
        }
        else {
            const rr = this.generateTmpRegister();
            this.m_currentBlock.push(new MIRInvokeVirtualOperator(sinfo, retinfo.runtimeresult.typeID, vresolve, shortvname, eargs, rr));

            if (retinfo.elrcount === -1) {
                this.m_currentBlock.push(new MIRLoadFromEpehmeralList(sinfo, rr, retinfo.runtimeresult.typeID, 0, retinfo.declresult.typeID, trgt));
            }
            else {
                this.m_currentBlock.push(new MIRSliceEpehmeralList(sinfo, rr, retinfo.runtimeresult.typeID, retinfo.declresult.typeID, trgt));
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

        this.m_currentBlock.push(new MIRConstructorTuple(sinfo, resultTupleType.typeID, args, trgt));
    }

    emitConstructorTupleFromEphemeralList(sinfo: SourceInfo, resultTupleType: MIRType, arg: MIRArgument, elisttype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorTupleFromEphemeralList(sinfo, resultTupleType.typeID, arg, elisttype.typeID, trgt));
    }

    emitConstructorRecord(sinfo: SourceInfo, resultRecordType: MIRType, args: [string, MIRArgument][], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorRecord(sinfo, resultRecordType.typeID, args, trgt));
    }

    emitConstructorRecordFromEphemeralList(sinfo: SourceInfo, resultRecordType: MIRType, arg: MIRArgument, elisttype: MIRType, namelayout: string[], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorRecordFromEphemeralList(sinfo, resultRecordType.typeID, arg, elisttype.typeID, namelayout, trgt));
    }

    emitStructuredAppendTuple(sinfo: SourceInfo, resultTupleType: MIRType, args: MIRArgument[], ttypes: {layout: MIRType, flow: MIRType}[], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const etypes = ttypes.map((tt) => {
            return { layout: tt.layout.typeID, flow: tt.flow.typeID };
        });
        this.m_currentBlock.push(new MIRStructuredAppendTuple(sinfo, resultTupleType.typeID, args, etypes, trgt));
    } 

    emitStructuredJoinRecord(sinfo: SourceInfo, resultRecordType: MIRType, args: MIRArgument[], ttypes: {layout: MIRType, flow: MIRType}[], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const etypes = ttypes.map((tt) => {
            return { layout: tt.layout.typeID, flow: tt.flow.typeID };
        });
        this.m_currentBlock.push(new MIRStructuredJoinRecord(sinfo, resultRecordType.typeID, args, etypes, trgt));
    }

    emitConstructorValueList(sinfo: SourceInfo, resultEphemeralType: MIRType, args: MIRArgument[], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorEphemeralList(sinfo, resultEphemeralType.typeID, args, trgt));
    }

    emitMIRPackExtend(sinfo: SourceInfo, basepack: MIRArgument, basetype: MIRType, ext: MIRArgument[], sltype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIREphemeralListExtend(sinfo, basepack, basetype.typeID, ext, sltype.typeID, trgt));
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

        this.m_currentBlock.push(new MIRConstructorPrimaryCollectionSingletons(sinfo, tkey, args.map((arg) => [arg[0].typeID, arg[1]]), trgt));
    }

    emitConstructorPrimaryCollectionCopies(sinfo: SourceInfo, tkey: MIRResolvedTypeKey, args: [MIRType, MIRArgument][], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorPrimaryCollectionCopies(sinfo, tkey, args.map((arg) => [arg[0].typeID, arg[1]]), trgt));
    }

    emitConstructorPrimaryCollectionMixed(sinfo: SourceInfo, tkey: MIRResolvedTypeKey, args: [boolean, MIRType, MIRArgument][], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRConstructorPrimaryCollectionMixed(sinfo, tkey, args.map((arg) => [arg[0], arg[1].typeID, arg[2]]), trgt));
    }

    emitBinKeyEq(sinfo: SourceInfo, lhslayouttype: MIRType, lhs: MIRArgument, rhslayouttype: MIRType, rhs: MIRArgument, cmptype: MIRType, trgt: MIRRegisterArgument, guard: MIRStatmentGuard | undefined, lhsflowtype: MIRType, rhsflowtype: MIRType) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRBinKeyEq(sinfo, lhslayouttype.typeID, lhs, rhslayouttype.typeID, rhs, cmptype.typeID, trgt, guard, lhsflowtype.typeID, rhsflowtype.typeID));
    }

    emitBinKeyLess(sinfo: SourceInfo, lhslayouttype: MIRType, lhs: MIRArgument, rhslayouttype: MIRType, rhs: MIRArgument, cmptype: MIRType, trgt: MIRRegisterArgument, guard: MIRStatmentGuard | undefined, lhsflowtype: MIRType, rhsflowtype: MIRType) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRBinKeyLess(sinfo, lhslayouttype.typeID, lhs, rhslayouttype.typeID, rhs, cmptype.typeID, trgt, guard, lhsflowtype.typeID, rhsflowtype.typeID));
    }

    emitPrefixNotOp(sinfo: SourceInfo, arg: MIRArgument, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRPrefixNotOp(sinfo, arg, trgt));
    }
    
    emitTypeOf(sinfo: SourceInfo, trgt: MIRRegisterArgument, chktype: MIRType, src: MIRArgument, srclayouttype: MIRType, srcflowtype: MIRType, guard: MIRStatmentGuard | undefined) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRIsTypeOf(sinfo, trgt, chktype.typeID, src, srclayouttype.typeID, srcflowtype.typeID, guard));
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

        this.m_currentBlock.push(new MIRJumpNone(sinfo, arg, arglayout.typeID, noneblck, someblk));
    }

    emitReturnAssign(sinfo: SourceInfo, src: MIRArgument, rtype: MIRType) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRReturnAssign(sinfo, src, rtype.typeID));
    }

    emitReturnAssignOfCons(sinfo: SourceInfo, oftype: MIRType, args: MIRArgument[]) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRReturnAssignOfCons(sinfo, oftype.typeID, args));
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

        this.m_currentBlock.push(new MIRVarLifetimeStart(sinfo, name, vtype.typeID));
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

            const vcpt = vinv.enclosingtype;
            const impls = this.entityInstantiationInfo.filter((iinfo) => {
                if (iinfo.ootype instanceof EntityTypeDecl) {
                    const etype = ResolvedType.createSingle(ResolvedEntityAtomType.create(iinfo.ootype as EntityTypeDecl, iinfo.binds));
                    return assembly.subtypeOf(etype, vcpt);
                }
                else {
                    const cpt = ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(iinfo.ootype as ConceptTypeDecl, iinfo.binds)]);
                    const ctype = ResolvedType.createSingle(cpt);
                    return assembly.subtypeOf(ctype, vcpt);
                }
            });

            for (let j = 0; j < impls.length; ++j) {
                const impl = impls[j];
                const itype = ResolvedType.createSingle(ResolvedEntityAtomType.create(impl.ootype as EntityTypeDecl, impl.binds));

                const mcreate_multi = assembly.tryGetMethodUniqueConcreteDeclFromType(itype, vinv.name);
                if (mcreate_multi !== undefined) {
                    const mcreate = new OOMemberLookupInfo<MemberMethodDecl>(mcreate_multi.contiainingType, mcreate_multi.decl[0], mcreate_multi.binds);
                    const binds = new Map<string, ResolvedType>(mcreate.binds);
                    vinv.binds.forEach((v, k) => binds.set(k, v));

                    const mctype = (mcreate.contiainingType instanceof EntityTypeDecl) ? ResolvedType.createSingle(ResolvedEntityAtomType.create(mcreate.contiainingType, mcreate.binds)) : ResolvedType.createSingle(ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(mcreate.contiainingType as ConceptTypeDecl, mcreate.binds)]));
                    const mirmctype = this.registerResolvedTypeReference(mctype);
                    const mkey = MIRKeyGenerator.generateFunctionKeyWType(mctype, mcreate.decl.name, binds, vinv.pcodes);
                    if (!resvi.has(mkey.keyid)) {
                        resvi.set(mkey.keyid, [vinv.vkey, mkey.keyid, mcreate.decl.name, `${mirmctype.typeID}::${mcreate.decl.name}`, [mirmctype, mcreate.contiainingType, mcreate.binds], mcreate.decl, binds, vinv.pcodes, vinv.cargs] as [MIRVirtualMethodKey, MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>], MemberMethodDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]]);
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
                sigkeys.push(this.registerResolvedTypeReference(ptype).typeID);
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

    private getVirtualOpImpls(vkey: MIRVirtualMethodKey, optns: string | undefined, optenclosingType: [ResolvedType, MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]): [MIRVirtualMethodKey, MIRInvokeKey, string, string, [ResolvedType, MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, InvokeDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] {
        let impls: [MIRVirtualMethodKey, MIRInvokeKey, string, string, [ResolvedType, MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, InvokeDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];
        
        if(optns !== undefined) {
            const ns = optns as string;

            const nsd = this.assembly.getNamespace(ns);
            if (nsd !== undefined) {
                nsd.operators.forEach((op) => {
                    if (op[1].name === name && !OOPTypeDecl.attributeSetContains("abstract", op[1].invoke.attributes)) {
                        const sigkeys = this.generateSigKeys(op[1].invoke, binds);
                        const key = MIRKeyGenerator.generateFunctionKeyWNamespace(ns, name, binds, pcodes);
                        const okey = MIRKeyGenerator.generateOperatorSignatureKey(key.keyid, key.shortname, op[1].isPrefix, op[1].isInfix, sigkeys);

                        impls.push([vkey, okey.keyid, op[1].name, `${ns}::${op[1].name}`, undefined, op[1].invoke, binds, pcodes, cargs]);
                    }
                });
            }
        }
        else {
            const enclosingType = optenclosingType as [ResolvedType, MIRType, OOPTypeDecl, Map<string, ResolvedType>];

            const ootype = enclosingType[2];
            ootype.staticOperators.forEach((op) => {
                if (op.name === name && !OOPTypeDecl.attributeSetContains("abstract", op.invoke.attributes)) {
                    const sigkeys = this.generateSigKeys(op.invoke, binds);
                    const key = MIRKeyGenerator.generateFunctionKeyWType(enclosingType[0], name, binds, pcodes);
                    const okey = MIRKeyGenerator.generateOperatorSignatureKey(key.keyid, key.shortname, op.isPrefix, op.isInfix, sigkeys);

                    impls.push([vkey, okey.keyid, op.name, `${enclosingType[0].typeID}::${op.name}`, enclosingType, op.invoke, binds, pcodes, cargs]);
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
        if (this.masm.conceptDecls.has(key.keyid) || this.masm.entityDecls.has(key.keyid) || this.pendingOOProcessing.findIndex((oop) => oop.tkey === key.keyid) !== -1) {
            return;
        }

        if (decl.ns === "NSCore" && decl.name === "Result") {
            const okdecl = this.assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Result::Ok") as EntityTypeDecl;
            const okkey = MIRKeyGenerator.generateTypeKey(ResolvedType.createSingle(ResolvedEntityAtomType.create(okdecl, binds)));
            const okentry = { tkey: okkey.keyid, shortname: okkey.shortname, ootype: okdecl, binds: binds }
            if (!this.masm.entityDecls.has(okkey.keyid) && this.pendingOOProcessing.findIndex((oop) => oop.tkey === okkey.keyid) === -1) {
                this.pendingOOProcessing.push(okentry);
                this.entityInstantiationInfo.push(okentry);

                if(this.emitEnabled) {
                    const ft = MIREntityType.create(okkey.keyid, okkey.shortname);
                    this.masm.typeMap.set(ft.typeID, MIRType.createSingle(ft));
                }
            }

            const errdecl = this.assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Result::Err") as EntityTypeDecl;
            const errkey = MIRKeyGenerator.generateTypeKey(ResolvedType.createSingle(ResolvedEntityAtomType.create(errdecl, binds)));
            const errentry = { tkey: errkey.keyid, shortname: errkey.shortname, ootype: errdecl, binds: binds }
            if (!this.masm.entityDecls.has(errkey.keyid) && this.pendingOOProcessing.findIndex((oop) => oop.tkey === errkey.keyid) === -1) {
                this.pendingOOProcessing.push(errentry);
                this.entityInstantiationInfo.push(errentry);

                if(this.emitEnabled) {
                    const ft = MIREntityType.create(errkey.keyid, errkey.shortname);
                    this.masm.typeMap.set(ft.typeID, MIRType.createSingle(ft));
                }
            }
        }

        if (decl.ns === "NSCore" && decl.name === "Option") {
            const somethingdecl = this.assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Something") as EntityTypeDecl;
            const somethngkey = MIRKeyGenerator.generateTypeKey(ResolvedType.createSingle(ResolvedEntityAtomType.create(somethingdecl, binds)));
            const somethingentry = { tkey: somethngkey.keyid, shortname: somethngkey.shortname, ootype: somethingdecl, binds: binds }
            if (!this.masm.entityDecls.has(somethngkey.keyid) && this.pendingOOProcessing.findIndex((oop) => oop.tkey === somethngkey.keyid) === -1) {
                this.pendingOOProcessing.push(somethingentry);
                this.entityInstantiationInfo.push(somethingentry);

                if(this.emitEnabled) {
                    const ft = MIREntityType.create(somethngkey.keyid, somethngkey.shortname);
                    this.masm.typeMap.set(ft.typeID, MIRType.createSingle(ft));
                }
            }
        }

        if (decl.ns === "NSCore" && decl.name === "Map") {
            const tatoms = [this.registerResolvedTypeReference(binds.get("K") as ResolvedType), this.registerResolvedTypeReference(binds.get("V") as ResolvedType)];
            const rt = MIRTupleType.create(tatoms);
            
            if(!this.masm.tupleDecls.has(rt.typeID) && this.emitEnabled) {
                this.masm.tupleDecls.set(rt.typeID, rt as MIRTupleType);
            }
        }

        this.pendingOOProcessing.push({ tkey: key.keyid, shortname: key.shortname, ootype: decl, binds: binds});
        this.entityInstantiationInfo.push({ tkey: key.keyid, shortname: key.shortname, ootype: decl, binds: binds});
    }

    registerResolvedTypeReference(t: ResolvedType): MIRType {
        if (t.options.length > 1) {
            const oopts = t.options.map((opt) => this.registerResolvedTypeReference(ResolvedType.createSingle(opt)).options);
            const ft = MIRType.create(([] as MIRTypeOption[]).concat(...oopts));

            if(this.emitEnabled) {
                this.masm.typeMap.set(ft.typeID, ft);
            }

            return ft;
        }
        else {
            const sopt = t.options[0];
            const rtt = ResolvedType.createSingle(sopt);
            let rt: MIRTypeOption | undefined = undefined;

            if (sopt instanceof ResolvedEntityAtomType) {
                if(this.emitEnabled) {
                    this.registerTypeInstantiation(rtt, sopt.object, sopt.binds);
                }

                const ekey = MIRKeyGenerator.generateTypeKey(rtt);
                rt = MIREntityType.create(ekey.keyid, ekey.shortname);
            }
            else if (sopt instanceof ResolvedConceptAtomType) {
                if(sopt.conceptTypes.length > 1) {
                    sopt.conceptTypes.forEach((opt) => this.registerResolvedTypeReference(ResolvedType.createSingle(ResolvedConceptAtomType.create([opt]))));
                }
                
                const natoms = sopt.conceptTypes.map((cpt) => {
                    this.registerTypeInstantiation(rtt, cpt.concept, cpt.binds);
                    return MIRKeyGenerator.generateTypeKey(rtt);
                });
                rt = MIRConceptType.create(natoms.map((kk) => [kk.keyid, kk.shortname]));
            }
            else if (sopt instanceof ResolvedTupleAtomType) {
                const tatoms = sopt.types.map((entry) => this.registerResolvedTypeReference(entry));
                rt = MIRTupleType.create(tatoms);
                if(!this.masm.tupleDecls.has(rt.typeID)) {
                    this.masm.tupleDecls.set(rt.typeID, rt as MIRTupleType);
                }
            }
            else if (sopt instanceof ResolvedRecordAtomType) {
                const tatoms = sopt.entries.map((entry) => { return {pname: entry.pname, ptype: this.registerResolvedTypeReference(entry.ptype)} });
                rt = MIRRecordType.create(tatoms);
                if(!this.masm.recordDecls.has(rt.typeID)) {
                    this.masm.recordDecls.set(rt.typeID, rt as MIRRecordType);
                }
            }
            else {
                const vpatoms = (sopt as ResolvedEphemeralListType).types.map((tt) => this.registerResolvedTypeReference(tt));
                rt = MIREphemeralListType.create(vpatoms);
                if(!this.masm.ephemeralListDecls.has(rt.typeID)) {
                    this.masm.ephemeralListDecls.set(rt.typeID, rt as MIREphemeralListType);
                }
            }

            const ft = MIRType.create([(rt as MIRTypeOption)]);
            if(this.emitEnabled) {
                this.masm.typeMap.set(ft.typeID, ft);
            }

            return ft;
        }
    }

    registerPendingGlobalProcessing(decl: NamespaceConstDecl, etype: ResolvedType): GeneratedKeyName<MIRGlobalKey> {
        const gkey = MIRKeyGenerator.generateGlobalKeyWNamespace(decl.ns, decl.name);
        if (!this.emitEnabled || this.masm.constantDecls.has(gkey.keyid) || this.pendingConstExprProcessing.findIndex((gp) => gp.gkey === gkey.keyid) !== -1) {
            return gkey;
        }

        this.pendingConstExprProcessing.push({ gkey: gkey.keyid, shortname: gkey.shortname, name: decl.name, srcFile: decl.srcFile, containingType: undefined, cexp: decl.value as ConstantExpressionValue, attribs: ["static_initializer", ...decl.attributes], binds: new Map<string, ResolvedType>(), ddecltype: etype });
        return gkey;
    }

    registerPendingConstProcessing(resolvedcontaining: ResolvedType, containingtype: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], decl: StaticMemberDecl, binds: Map<string, ResolvedType>, etype: ResolvedType): GeneratedKeyName<MIRGlobalKey> {
        const gkey = MIRKeyGenerator.generateGlobalKeyWType(resolvedcontaining, decl.name);
        if (!this.emitEnabled || this.masm.constantDecls.has(gkey.keyid) || this.pendingConstExprProcessing.findIndex((cp) => cp.gkey === gkey.keyid) !== -1) {
            return gkey;
        }

        this.pendingConstExprProcessing.push({ gkey: gkey.keyid, shortname: gkey.shortname, name: decl.name, srcFile: decl.srcFile, containingType: containingtype, cexp: decl.value as ConstantExpressionValue, attribs: ["static_initializer", ...decl.attributes], binds: binds, ddecltype: etype });
        return gkey;
    }

    registerFunctionCall(ns: string, name: string, f: NamespaceFunctionDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generateFunctionKeyWNamespace(ns, name, binds, pcodes);
        if (!this.emitEnabled || this.masm.invokeDecls.has(key.keyid) || this.masm.primitiveInvokeDecls.has(key.keyid) || this.pendingFunctionProcessing.findIndex((fp) => fp.fkey === key.keyid) !== -1) {
            return key.keyid;
        }

        this.pendingFunctionProcessing.push({ fkey: key.keyid, shortname: key.shortname, name: name, enclosingdecl: undefined, invoke: f.invoke, binds: binds, pcodes: pcodes, cargs: cinfo });
        return key.keyid;
    }

    registerNamespaceOperatorCall(ns: string, name: string, opdecl: NamespaceOperatorDecl, sigkeys: string[], pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generateFunctionKeyWNamespace(ns, name, new Map<string, ResolvedType>(), pcodes);
        const okey = MIRKeyGenerator.generateOperatorSignatureKey(key.keyid, key.shortname, opdecl.isPrefix, opdecl.isInfix, sigkeys);

        if (!this.emitEnabled || this.masm.invokeDecls.has(okey.keyid) || this.masm.primitiveInvokeDecls.has(okey.keyid) || this.pendingOperatorProcessing.findIndex((fp) => fp.fkey === okey.keyid) !== -1) {
            return okey.keyid;
        }

        this.pendingOperatorProcessing.push({ fkey: okey.keyid, shortname: okey.shortname, name: name, enclosingdecl: undefined, invoke: opdecl.invoke, binds: new Map<string, ResolvedType>(), pcodes: pcodes, cargs: cinfo });
        return okey.keyid;
    }

    registerStaticCall(resolvedcontaining: ResolvedType, containingType: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], f: StaticFunctionDecl, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generateFunctionKeyWType(resolvedcontaining, name, binds, pcodes);
        if (!this.emitEnabled || this.masm.invokeDecls.has(key.keyid) || this.masm.primitiveInvokeDecls.has(key.keyid) || this.pendingFunctionProcessing.findIndex((sp) => sp.fkey === key.keyid) !== -1) {
            return key.keyid;
        }

        this.pendingFunctionProcessing.push({ fkey: key.keyid, shortname: key.shortname, name: name, enclosingdecl: containingType, invoke: f.invoke, binds: binds, pcodes: pcodes, cargs: cinfo });
        return key.keyid;
    }

    registerStaticOperatorCall(resolvedcontaining: ResolvedType, containingType: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], name: string, opdecl: StaticOperatorDecl, sigkeys: string[], binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generateFunctionKeyWType(resolvedcontaining, name, binds, pcodes);
        const okey = MIRKeyGenerator.generateOperatorSignatureKey(key.keyid, key.shortname, opdecl.isPrefix, opdecl.isInfix, sigkeys);

        if (!this.emitEnabled || this.masm.invokeDecls.has(okey.keyid) || this.masm.primitiveInvokeDecls.has(okey.keyid) || this.pendingOperatorProcessing.findIndex((fp) => fp.fkey === okey.keyid) !== -1) {
            return okey.keyid;
        }

        this.pendingOperatorProcessing.push({ fkey: okey.keyid, shortname: okey.shortname, name: name, enclosingdecl: containingType, invoke: opdecl.invoke, binds: binds, pcodes: pcodes, cargs: cinfo });
        return okey.keyid;
    }

    registerMethodCall(resolvedcontaining: ResolvedType, containingType: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], m: MemberMethodDecl, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const vkey = MIRKeyGenerator.generateVirtualMethodKey(name, binds, pcodes);
        const key = MIRKeyGenerator.generateFunctionKeyWType(resolvedcontaining, name, binds, pcodes);
        if (!this.emitEnabled || this.masm.invokeDecls.has(key.keyid) || this.masm.primitiveInvokeDecls.has(key.keyid) || this.pendingOOMethodProcessing.findIndex((mp) => mp.mkey === key.keyid) !== -1) {
            return key.keyid;
        }

        this.pendingOOMethodProcessing.push({ vkey: vkey.keyid, mkey: key.keyid, shortname: key.shortname, name: name, enclosingDecl: containingType, mdecl: m, binds: binds, pcodes: pcodes, cargs: cinfo });
        return key.keyid;
    }

    registerVirtualMethodCall(containingType: ResolvedType, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): GeneratedKeyName<MIRVirtualMethodKey> {
        const key = MIRKeyGenerator.generateVirtualMethodKey(name, binds, pcodes);
        if (!this.emitEnabled || this.allVInvokes.findIndex((vi) => vi.vkey === key.keyid && vi.enclosingtype.typeID === containingType.typeID) !== -1) {
            return key;
        }

        this.allVInvokes.push({ vkey: key.keyid, enclosingtype: containingType, name: name, binds: binds, pcodes: pcodes, cargs: cinfo });
        return key;
    }

    registerVirtualNamespaceOperatorCall(ns: string, name: string, pcodes: PCode[], cinfo: [string, ResolvedType][]): GeneratedKeyName<MIRVirtualMethodKey> {
        const key = MIRKeyGenerator.generateVirtualMethodKey(`${ns}::${name}`, new Map<string, ResolvedType>(), pcodes);
        if (!this.emitEnabled || this.masm.virtualOperatorDecls.has(key.keyid) || this.pendingOPVirtualProcessing.findIndex((vi) => vi.vkey === key.keyid) !== -1) {
            return key;
        }

        this.pendingOPVirtualProcessing.push({vkey: key.keyid, optns: ns, optenclosingType: undefined, name: name, binds: new Map<string, ResolvedType>(), pcodes: pcodes, cargs: cinfo });
        return key;
    }

    registerVirtualStaticOperatorCall(containingType: [ResolvedType, MIRType, OOPTypeDecl, Map<string, ResolvedType>], name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): GeneratedKeyName<MIRVirtualMethodKey> {
        const key = MIRKeyGenerator.generateVirtualMethodKey(`${containingType[0].typeID}::${name}`, new Map<string, ResolvedType>(), pcodes);
        if (!this.emitEnabled || this.masm.virtualOperatorDecls.has(key.keyid) || this.pendingOPVirtualProcessing.findIndex((vi) => vi.vkey === key.keyid) !== -1) {
            return key;
        }

        this.pendingOPVirtualProcessing.push({  vkey: key.keyid, optns: undefined, optenclosingType: containingType, name: name, binds: binds, pcodes: pcodes, cargs: cinfo  });
        return key;
    }

    registerPCode(ikey: MIRInvokeKey, shortname: string, idecl: InvokeDecl, fsig: ResolvedFunctionType, bodybinds: Map<string, ResolvedType>, cinfo: [string, ResolvedType][], capturedpcode: [string, PCode][]) {
        if (!this.emitEnabled || this.masm.invokeDecls.has(ikey) || this.masm.primitiveInvokeDecls.has(ikey) || this.pendingPCodeProcessing.findIndex((fp) => fp.lkey === ikey) !== -1) {
            return;
        }

        this.pendingPCodeProcessing.push({ lkey: ikey, lshort: shortname, invoke: idecl, sigt: fsig, bodybinds: bodybinds, cargs: cinfo, capturedpcodes: capturedpcode });
    }

    static generateMASM(pckge: PackageConfig, buildLevel: BuildLevel, macrodefs: string[], entrypoints: { namespace: string, names: string[] }, functionalize: boolean, srcFiles: { fpath: string, filepath: string, contents: string }[]): { masm: MIRAssembly | undefined, errors: string[] } {
        ////////////////
        //Parse the contents and generate the assembly
        const assembly = new Assembly();
        let p = new Parser(assembly, srcFiles.map((sfi) => { return {fullname: sfi.fpath, shortname: sfi.filepath}; }));
        try {
            for (let i = 0; i < srcFiles.length; ++i) {
                p.parseCompilationUnitPass1(srcFiles[i].fpath, srcFiles[i].contents, macrodefs);
            }

            for (let i = 0; i < srcFiles.length; ++i) {
                p.parseCompilationUnitPass2(srcFiles[i].fpath, srcFiles[i].contents, macrodefs);
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
        const data = [...srcFiles].sort((a, b) => a.fpath.localeCompare(b.fpath));
        data.forEach((sf) => {
            hash.update(sf.fpath);
            hash.update(sf.contents);
        });

        const masm = new MIRAssembly(pckge, srcFiles, hash.digest("hex"));
        const emitter = new MIREmitter(assembly, masm, true);
        const checker = new TypeChecker(assembly, emitter, buildLevel, p.sortedSrcFiles);

        emitter.registerResolvedTypeReference(assembly.getSpecialAnyConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialSomeConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialKeyTypeConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialValidatorConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialParsableConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialAPITypeConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialAlgebraicConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialOrderableConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialTupleConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialRecordConceptType());
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
        emitter.registerResolvedTypeReference(assembly.getSpecialBufferCompressionType());
        emitter.registerResolvedTypeReference(assembly.getSpecialByteBufferType());
        emitter.registerResolvedTypeReference(assembly.getSpecialISOTimeType());
        emitter.registerResolvedTypeReference(assembly.getSpecialLogicalTimeType());
        emitter.registerResolvedTypeReference(assembly.getSpecialUUIDType());
        emitter.registerResolvedTypeReference(assembly.getSpecialContentHashType());
        emitter.registerResolvedTypeReference(assembly.getSpecialRegexType());
        emitter.registerResolvedTypeReference(assembly.getSpecialNothingType());
        emitter.registerResolvedTypeReference(assembly.getSpecialHavocType());

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
                        const tt = emitter.pendingOOProcessing[0];
                        checker.processOOType(tt.tkey, tt.shortname, tt.ootype, tt.binds);

                        emitter.pendingOOProcessing.shift();
                    }

                    if(emitter.pendingConstExprProcessing.length !== 0) {
                        const pc = emitter.pendingConstExprProcessing[0];
                        checker.processConstExpr(pc.gkey, pc.shortname, pc.name, pc.srcFile, pc.containingType, pc.cexp, pc.attribs, pc.binds, pc.ddecltype);

                        emitter.pendingConstExprProcessing.shift();
                    }
                    else if (emitter.pendingFunctionProcessing.length !== 0) {
                        const pf = emitter.pendingFunctionProcessing[0];
                        checker.processFunctionDecl(pf.fkey, pf.shortname, pf.name, pf.enclosingdecl, pf.invoke, pf.binds, pf.pcodes, pf.cargs);

                        emitter.pendingFunctionProcessing.shift();
                    }
                    else if (emitter.pendingOperatorProcessing.length !== 0) {
                        const pf = emitter.pendingOperatorProcessing[0];
                        checker.processFunctionDecl(pf.fkey, pf.shortname, pf.name, pf.enclosingdecl, pf.invoke, pf.binds, pf.pcodes, pf.cargs);

                        emitter.pendingOperatorProcessing.shift();
                    }
                    else if (emitter.pendingOOMethodProcessing.length !== 0) {
                        const mf = emitter.pendingOOMethodProcessing[0];
                        checker.processMethodFunction(mf.vkey, mf.mkey, mf.shortname, mf.name, mf.enclosingDecl, mf.mdecl, mf.binds, mf.pcodes, mf.cargs);

                        emitter.pendingOOMethodProcessing.shift();
                    }
                    else if (emitter.pendingPCodeProcessing.length !== 0) {
                        const lf = emitter.pendingPCodeProcessing[0];
                        checker.processLambdaFunction(lf.lkey, lf.lshort, lf.invoke, lf.sigt, lf.bodybinds, lf.cargs, lf.capturedpcodes);

                        emitter.pendingPCodeProcessing.shift();
                    }
                    else if (emitter.pendingOPVirtualProcessing.length !== 0) {
                        const vop = emitter.pendingOPVirtualProcessing[0];
                        const opimpls = emitter.getVirtualOpImpls(vop.vkey, vop.optns, vop.optenclosingType, vop.name, vop.binds, vop.pcodes, vop.cargs);
                        for (let i = 0; i < opimpls.length; ++i) {
                            checker.processVirtualOperator(...opimpls[i]);
                        }

                        emitter.pendingOPVirtualProcessing.shift();
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
                }
                
                ssaConvertInvokes(masm);
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

export { PCode, GeneratedKeyName, MIRKeyGenerator, MIREmitter };
