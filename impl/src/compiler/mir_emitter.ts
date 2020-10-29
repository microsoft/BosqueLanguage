//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo, Parser } from "../ast/parser";
import { MIRTempRegister, MIROp, MIRLoadConst, MIRConstantNone, MIRConstantTrue, MIRConstantFalse, MIRConstantInt, MIRConstantString, MIRArgument, MIRLoadConstDataString, MIRConstructorPrimary, MIRConstructorPrimaryCollectionSingletons, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionMixed, MIRAccessFromIndex, MIRProjectFromIndecies, MIRProjectFromProperties, MIRProjectFromFields, MIRAccessFromProperty, MIRAccessFromField, MIRConstructorTuple, MIRConstructorRecord, MIRConstructorPrimaryCollectionEmpty, MIRResolvedTypeKey, MIRFieldKey, MIRLoadFieldDefaultValue, MIRProjectFromTypeTuple, MIRProjectFromTypeRecord, MIRProjectFromTypeNominal, MIRModifyWithIndecies, MIRModifyWithProperties, MIRModifyWithFields, MIRStructuredExtendTuple, MIRStructuredExtendRecord, MIRStructuredExtendObject, MIRVirtualMethodKey, MIRJump, MIRJumpCond, MIRBinOp, MIRBinCmp, MIRBinEq, MIRTempRegisterAssign, MIRParameterVarStore, MIRLocalVarStore, MIRReturnAssign, MIRVarLifetimeStart, MIRVarLifetimeEnd, MIRBody, MIRBasicBlock, MIRTruthyConvert, MIRJumpNone, MIRDebug, MIRAbort, MIRInvokeKey, MIRConstantKey, MIRAccessConstantValue, MIRInvokeFixedFunction, MIRInvokeVirtualFunction, MIRConstructorEphemeralValueList, MIRInvokeInvariantCheckDirect, MIRInvokeInvariantCheckVirtualTarget, MIRLoadFromEpehmeralList, MIRRegisterArgument, MIRPackSlice, MIRPackExtend, MIRConstantBigInt, MIRConstantFloat, MIRBinLess, MIRConstantRegex, MIRConstantEmpty, MIRConstantStringOf, MIRConstantDecmial, MIRConstantBigNat, MIRConstantRational, MIRVariableArgument, MIRParameterVariable, MIRLocalVariable, MIRConstantNat, MIRConstantComplex, MIRGlobalKey } from "./mir_ops";
import { OOPTypeDecl, StaticFunctionDecl, MemberMethodDecl, InvokeDecl, Assembly, NamespaceFunctionDecl, NamespaceConstDecl, StaticMemberDecl, ConceptTypeDecl, EntityTypeDecl, BuildLevel, NamespaceOperatorDecl, StaticOperatorDecl } from "../ast/assembly";
import { ResolvedType, ResolvedEntityAtomType, ResolvedConceptAtomType, ResolvedTupleAtomType, ResolvedRecordAtomType, ResolvedFunctionType, ResolvedConceptAtomTypeEntry, ResolvedEphemeralListType } from "../ast/resolved_type";
import { PackageConfig, MIRAssembly, MIRType, MIRTypeOption, MIREntityType, MIRConceptType, MIRTupleTypeEntry, MIRTupleType, MIRRecordTypeEntry, MIRRecordType, MIRConceptTypeDecl, MIREntityTypeDecl, MIREphemeralListType } from "./mir_assembly";

import * as Crypto from "crypto";
import { TypeChecker } from "../type_checker/type_checker";
import { propagateTmpAssignForBody, removeDeadTempAssignsFromBody } from "./mir_cleanup";
import { convertBodyToSSA } from "./mir_ssa";
import { computeVarTypesForInvoke } from "./mir_vartype";
import { functionalizeInvokes } from "./functionalize";
import { BSQRegex } from "../ast/bsqregex";
import { ConstantExpressionValue } from "../ast/body";
import { ValueType } from "../type_checker/type_environment";

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

    static generateMethodKey(name: string, t: ResolvedType, binds: Map<string, ResolvedType>, pcodes: PCode[]): MIRInvokeKey {
        return `${this.generateTypeKey(t)}::${name}${MIRKeyGenerator.computeBindsKeyInfo(binds)}${MIRKeyGenerator.computePCodeKeyInfo(pcodes)}`;
    }

    static generateVirtualMethodKey(vname: string, binds: Map<string, ResolvedType>): MIRVirtualMethodKey {
        return `${vname}${MIRKeyGenerator.computeBindsKeyInfo(binds)}`;
    }

    static generatePCodeKey(inv: InvokeDecl): MIRInvokeKey {
        return `fn--${inv.srcFile}+${inv.sourceLocation.line}##${inv.sourceLocation.pos}`;
    }
}

class MIREmitter {
    readonly assembly: Assembly;
    readonly masm: MIRAssembly;
    
    private readonly pendingOOProcessing: [MIRResolvedTypeKey, OOPTypeDecl, Map<string, ResolvedType>][] = [];

    private readonly pendingGlobalProcessing: [MIRConstantKey, NamespaceConstDecl][] = [];
    private readonly pendingConstProcessing: [MIRConstantKey, OOPTypeDecl, StaticMemberDecl, Map<string, ResolvedType>][] = [];

    private readonly pendingOOStaticProcessing: [MIRInvokeKey, OOPTypeDecl, Map<string, ResolvedType>, StaticFunctionDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];
    private readonly pendingOOMethodProcessing: [MIRVirtualMethodKey, MIRInvokeKey, OOPTypeDecl, Map<string, ResolvedType>, MemberMethodDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];
    private readonly pendingFunctionProcessing: [MIRInvokeKey, NamespaceFunctionDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];
    private readonly pendingPCodeProcessing: [MIRInvokeKey, InvokeDecl, ResolvedFunctionType, Map<string, ResolvedType>, [string, ResolvedType][]][] = [];

    private readonly entityInstantiationInfo: [MIRResolvedTypeKey, OOPTypeDecl, Map<string, ResolvedType>][] = [];
    private readonly allVInvokes: [MIRVirtualMethodKey, MIRResolvedTypeKey, OOPTypeDecl, Map<string, ResolvedType>, string, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];

    private emitEnabled: boolean;
    
    private m_blockMap: Map<string, MIRBasicBlock> = new Map<string, MIRBasicBlock>();
    private m_currentBlockName = "UNDEFINED";
    private m_currentBlock: MIROp[] = [];

    private m_tmpIDCtr = 0;

    private yieldPatchInfo: [string, MIRTempRegister, ValueType][][] = [];
    private returnPatchInfo: [string, MIRTempRegister, ValueType][] = [];

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

    generateTmpRegister(): MIRTempRegister {
        if(!this.emitEnabled) {
            return new MIRTempRegister(-1);
        }

        return new MIRTempRegister(this.m_tmpIDCtr++);
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

        xxxx;
    }

    emitDeadBlock(sinfo: SourceInfo) {
        if(!this.emitEnabled) {
            return;
        }

        xxxx;
    }

    emitTempRegisterAssign(sinfo: SourceInfo, src: MIRArgument, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        xxxx;
    }

    emitLocalVarStore(sinfo: SourceInfo, src: MIRArgument, name: string, vtype: MIRType) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLocalVarStore(sinfo, src, new MIRLocalVariable(name)));
    }

    emitArgVarStore(sinfo: SourceInfo, src: MIRArgument, name: string, vtype: MIRType) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRArgumentVarStore(sinfo, src, new MIRVariable(name)));
    }

    emitStoreWithGuard(sinfo: SourceInfo, maskname: string, maskidx: number, src: MIRArgument, trgt: MIRVariableArgument, vtype: MIRType) {
        if(!this.emitEnabled) {
            return;
        }

        if(trgt instanceof MIRParameterVariable) {
            this.m_currentBlock.push(new MIRParmaterVarStore(sinfo, src, trgt, vtype.trkey));
        }
        else {
            this.m_currentBlock.push(new MIRLocalVarStore(sinfo, src, trgt, vtype.trkey));
        }
    }

    emitConvert(sinfo: SourceInfo, srctypelayout: MIRType, srctypeflow: MIRType, intotype: MIRType, src: MIRArgument, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        xxxx;
    }

    emitCheckedConvert(sinfo: SourceInfo, srctypelayout: MIRType, srctypeflow: MIRType, intotype: MIRType, src: MIRArgument, trgt: MIRRegisterArgument, fflag: string, index: number) {
        if(!this.emitEnabled) {
            return;
        }

        xxxx;
    }

    emitLoadUninitVariableValue(sinfo: SourceInfo, oftype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        //This value will not be read from but will be passed as an arg 
        //we need to have space for it etc. so just plop a "fresh" or zero-filled value there
        xxxx;
    }

    emitCheckNoError(sinfo: SourceInfo, src: MIRArgument, srctype: MIRType, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        xxxx;
    }

    emitAssertCheck(sinfo: SourceInfo, msg: string, src: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        xxxx;
    }

    emitExtractResultOkValue(sinfo: SourceInfo, src: MIRArgument, srctype: MIRType, valuetype: MIRType, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        xxxx;
    }

    emitLoadConstNone(sinfo: SourceInfo, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantNone(), trgt));
    }

    emitLoadConstBool(sinfo: SourceInfo, bv: boolean, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, bv ? new MIRConstantTrue() : new MIRConstantFalse(), trgt));
    }

    emitLoadConstIntegralValue(sinfo: SourceInfo, itype: MIRType, vv: string, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantInt(iv), trgt));
    }

    emitLoadConstRational(sinfo: SourceInfo, iv: string, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantRational(iv), trgt));
    }

    emitLoadConstFloatPoint(sinfo: SourceInfo,ftype: MIRType,  fv: string, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantFloat(fv), trgt));
    }

    emitLoadConstComplex(sinfo: SourceInfo, rv: string, iv: string, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantComplex(rv, iv), trgt));
    }

    emitLoadConstString(sinfo: SourceInfo, sv: string, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantString(sv), trgt));
    }

    emitLoadLiteralRegex(sinfo: SourceInfo, restr: BSQRegex, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantRegex(restr), trgt));
    }

    emitLoadLiteralStringOf(sinfo: SourceInfo, sv: string, tskey: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantStringOf(sv, tskey), trgt));
    }

    emitLoadConstDataString(sinfo: SourceInfo, sv: string, tskey: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConstDataString(sinfo, sv, tskey, trgt));
    }

    emitHasFlagLocation(name: string, count: number): string {
        if(!this.emitEnabled || count === 0) {
            return "[IGNORE]";
        }

        xxxx;
    }

    emitSetHasFlagConstant(hasflag: string, position: number, has: boolean) {
        if(!this.emitEnabled) {
            return;
        }

        xxxx;
    }

    emitAllTrue(sinfo: SourceInfo, args: MIRArgument[], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        xxxx;
    }

    emitTupleHasIndex(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRType, idx: number, isvirtual: boolean, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }
        
        xxxx;
    }

    emitRecordHasProperty(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRType, pname: string, isvirtual: boolean, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }
        
        xxxx;
    }
    
    emitLoadTupleIndex(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRType, idx: number, isvirtual: boolean, resulttype: MIRType, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRAccessFromIndex(sinfo, arg, argInferType, idx, trgt));
    }

    emitCheckedLoadTupleIndex(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRType, idx: number, isvirtual: boolean, resulttype: MIRType, trgt: MIRTempRegister, hasflag?: string, position?: number) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRAccessFromIndex(sinfo, arg, argInferType, idx, trgt));
    }

    emitLoadTupleIndexTry(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRType, idx: number, isvirtual: boolean, resulttype: MIRType, trgt: MIRTempRegister, hastrgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRAccessFromIndex(sinfo, arg, argInferType, idx, trgt));
    }

    emitLoadProperty(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRType, pname: string, isvirtual: boolean, resulttype: MIRType, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRAccessFromProperty(sinfo, resultAccessType, arg, argInferType, pname, trgt));
    }

    emitCheckedLoadProperty(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRType, pname: string, isvirtual: boolean, resulttype: MIRType, trgt: MIRTempRegister, hasflag?: string, position?: number) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRAccessFromProperty(sinfo, resultAccessType, arg, argInferType, pname, trgt));
    }

    emitLoadPropertyTry(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRType, pname: string, isvirtual: boolean, resulttype: MIRType, trgt: MIRTempRegister, hastrgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRAccessFromIndex(sinfo, arg, argInferType, idx, trgt));
    }

    emitLoadField(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRType, fname: MIRFieldKey, isvirtual: boolean, resulttype: MIRType, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRAccessFromField(sinfo, resultAccessType, arg, argInferType, fname, trgt));
    }

    emitLoadFromEpehmeralList(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRType, idx: number, resulttype: MIRType, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRLoadFromEpehmeralList(sinfo, arg, resultType, argInferType, idx, trgt));
    }

    emitMultiLoadFromEpehmeralList(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRType, trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRType }[]) {
        if (!this.emitEnabled) {
            return;
        }
        
        //CAREFUL: this is going to assume that the types of the elist values and storage locations match (so no conversion is needed)

        this.m_currentBlock.push(new MIRLoadFromEpehmeralList(sinfo, arg, resultType, argInferType, idx, trgt));
    }

    emitInvokeFixedFunctionWithGuard(sinfo: SourceInfo, ikey: MIRInvokeKey, args: MIRArgument[], maskname: string, maskidx: number, rretinfo: MIRType, trgt: MIRVariableArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRInvokeFixedFunctionWithGuard(sinfo, rretinfo, ikey, args, maskname, maskidx, trgt));
    }

    emitInvokeFixedFunction(sinfo: SourceInfo, ikey: MIRInvokeKey, args: MIRArgument[], optstatusmask: string | undefined, rretinfo: MIRType | { declresult: MIRType, runtimeresult: MIRType, elrcount: number, refargs: [MIRVariableArgument, MIRType][] }, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        const retinfo = rretinfo instanceof MIRType ? { declresult: rretinfo, runtimeresult: rretinfo, elrcount: -1, refargs: [] } : rretinfo;
        if (retinfo.refargs.length === 0) {
            this.m_currentBlock.push(new MIRInvokeFixedFunction(sinfo, retinfo[0].trkey, ikey, args, optstatusmask, trgt));
        }
        else {
            const rr = this.generateTmpRegister();
            this.m_currentBlock.push(new MIRInvokeFixedFunction(sinfo, retinfo[1].trkey, ikey, args, optstatusmask, rr));

            if (retinfo.elrcount === -1) {
                this.m_currentBlock.push(new MIRLoadFromEpehmeralList(sinfo, rr, retinfo[0].trkey, retinfo[1].trkey, 0, trgt));
            }
            else {
                this.m_currentBlock.push(new MIRPackSlice(sinfo, rr, retinfo[0].trkey, trgt));
            }

            const refbase = retinfo.elrcount != -1 ? retinfo.elrcount : 1;
            const argvs = retinfo.refargs.map((rinfo, idx) => {
                return {pos: refbase + idx, into: rinfo[0], oftype: (retinfo.declresult.options[0] as MIREphemeralListType).entries[refbase + idx]};
            });

            this.emitMultiLoadFromEpehmeralList(sinfo, rr, retinfo.declresult, argvs);
        }
    }

    emitInvokeVirtualFunction(sinfo: SourceInfo, vresolve: MIRVirtualMethodKey, rcvrflowtype: MIRType, args: MIRArgument[], optstatusmask: string | undefined, rretinfo: MIRType | { declresult: MIRType, runtimeresult: MIRType, elrcount: number, refargs: [MIRVariableArgument, MIRType][] }, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        const retinfo = rretinfo instanceof MIRType ? { declresult: rretinfo, runtimeresult: rretinfo, elrcount: -1, refargs: [] as [MIRVariableArgument, MIRType][] } : rretinfo;
        if (retinfo.refargs.length === 0) {
            this.m_currentBlock.push(new MIRInvokeVirtualFunction(sinfo, retinfo[0].trkey, vresolve, args, thisInferType, trgt));
        }
        else {
            const rr = this.generateTmpRegister();
            this.m_currentBlock.push(new MIRInvokeVirtualFunction(sinfo, retinfo[1].trkey, vresolve, args, thisInferType, rr));
           
            if (retinfo.elrcount === -1) {
                this.m_currentBlock.push(new MIRLoadFromEpehmeralList(sinfo, rr, retinfo[0].trkey, retinfo[1].trkey, 0, trgt));
            }
            else {
                this.m_currentBlock.push(new MIRPackSlice(sinfo, rr, retinfo[0].trkey, trgt));
            }

            const refbase = retinfo.elrcount != -1 ? retinfo.elrcount : 1;
            const argvs = retinfo.refargs.map((rinfo, idx) => {
                return {pos: refbase + idx, into: rinfo[0], oftype: (retinfo.declresult.options[0] as MIREphemeralListType).entries[refbase + idx]};
            });

            this.emitMultiLoadFromEpehmeralList(sinfo, rr, retinfo.declresult, argvs);
        }
    }

    emitInvokeVirtualOperator(sinfo: SourceInfo, vresolve: MIRVirtualMethodKey, args: MIRArgument[], retinfo: { declresult: MIRType, runtimeresult: MIRType, elrcount: number, refargs: [MIRVariableArgument, MIRType][] }, trgt: MIRTempRegister) {
        if (retinfo.refargs.length === 0) {
            this.m_currentBlock.push(new MIRInvokeVirtualFunction(sinfo, retinfo[0].trkey, vresolve, args, thisInferType, trgt));
        }
        else {
            const rr = this.generateTmpRegister();
            this.m_currentBlock.push(new MIRInvokeVirtualFunction(sinfo, retinfo[1].trkey, vresolve, args, thisInferType, rr));
           
            if (retinfo.elrcount === -1) {
                this.m_currentBlock.push(new MIRLoadFromEpehmeralList(sinfo, rr, retinfo[0].trkey, retinfo[1].trkey, 0, trgt));
            }
            else {
                this.m_currentBlock.push(new MIRPackSlice(sinfo, rr, retinfo[0].trkey, trgt));
            }

            const refbase = retinfo.elrcount != -1 ? retinfo.elrcount : 1;
            const argvs = retinfo.refargs.map((rinfo, idx) => {
                return {pos: refbase + idx, into: rinfo[0], oftype: (retinfo.declresult.options[0] as MIREphemeralListType).entries[refbase + idx]};
            });

            this.emitMultiLoadFromEpehmeralList(sinfo, rr, retinfo.declresult, argvs);
        }
    }

    emitConstructorTuple(sinfo: SourceInfo, resultTupleType: MIRType, args: MIRArgument[], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorTuple(sinfo, resultTupleType, args, trgt));
    }

    emitConstructorTupleFromEphemeralList(sinfo: SourceInfo, resultTupleType: MIRType, arg: MIRArgument, elisttype: MIRType, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        xxxx;
    }

    emitMIRPackExtend(sinfo: SourceInfo, basepack: MIRArgument, ext: MIRArgument[], sltype: MIRType, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRPackExtend(sinfo, basepack, ext, sltype, trgt));
    }

    emitConstructorRecord(sinfo: SourceInfo, resultRecordType: MIRType, args: [string, MIRArgument][], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorRecord(sinfo, resultRecordType, args, trgt));
    }

    emitConstructorRecordFromEphemeralList(sinfo: SourceInfo, resultTupleType: MIRType, arg: MIRArgument, elisttype: MIRType, namelayout: string[], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        xxxx;
    }

    emitConstructorValueList(sinfo: SourceInfo, resultEphemeralType: MIRType, args: MIRArgument[], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorEphemeralValueList(sinfo, resultEphemeralType, args, trgt));
    }

    emitConstructorPrimaryCollectionEmpty(sinfo: SourceInfo, tkey: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorPrimaryCollectionEmpty(sinfo, tkey, trgt));
    }

    emitConstructorPrimaryCollectionSingletons(sinfo: SourceInfo, tkey: MIRResolvedTypeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorPrimaryCollectionSingletons(sinfo, tkey, args, trgt));
    }

    emitConstructorPrimaryCollectionCopies(sinfo: SourceInfo, tkey: MIRResolvedTypeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorPrimaryCollectionCopies(sinfo, tkey, args, trgt));
    }

    emitConstructorPrimaryCollectionMixed(sinfo: SourceInfo, tkey: MIRResolvedTypeKey, args: [boolean, MIRArgument][], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRConstructorPrimaryCollectionMixed(sinfo, tkey, args, trgt));
    }

    emitBinKeyEq(sinfo: SourceInfo, lhstype: MIRType, lhs: MIRArgument, rhstype: MIRType, rhs: MIRArgument, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRBinKeyEq(sinfo, lhsType, lhs, rhsType, rhs, trgt, relaxed));
    }

    emitBinKeyLess(sinfo: SourceInfo, lhstype: MIRType, lhs: MIRArgument, rhstype: MIRType, rhs: MIRArgument, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRBinKeyLess(sinfo, lhsType, lhs, rhsType, rhs, trgt, relaxed));
    }

    emitStructuredAppendTuple(sinfo: SourceInfo, resultTupleType: MIRType, args: MIRArgument[], ttypes: MIRType[], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRStructuredAppendTuple(sinfo, resultTupleType, arg, argInferType, update, updateInferType, trgt));
    } 

    emitStructuredJoinRecord(sinfo: SourceInfo, resultRecordType: MIRType, args: MIRArgument[], ttypes: MIRType[], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRStructuredJoinRecord(sinfo, resultRecordType, arg, argInferType, update, updateInferType, trgt));
    }

    emitPrefixNotOp(sinfo: SourceInfo, arg: MIRArgument, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRPrefixNotOp(sinfo, op, arg, infertype, trgt));
    }

    emitBinOp(sinfo: SourceInfo, lhstype: MIRType, lhs: MIRArgument, op: string, rhstype: MIRType, rhs: MIRArgument, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRBinOp(sinfo, lhsInferType, lhs, op, rhsInferType, rhs, trgt));
    }

    emitBinCmp(sinfo: SourceInfo, lhstype: MIRType, lhs: MIRArgument, op: string, rhstype: MIRType, rhs: MIRArgument, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRBinCmp(sinfo, lhsInferType, lhs, op, rhsInferType, rhs, trgt));
    }

    emitMultiTestOp(sinfo: SourceInfo, alltrue: MIRTempRegister[], allfalse: MIRTempRegister[], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        xxxx;
    }

    emitTypeOf(sinfo: SourceInfo, trgt: MIRTempRegister, chktype: MIRType, src: MIRArgument, srclayouttype: MIRType, srcflowtype: MIRType) {
        if(!this.emitEnabled) {
            return;
        }

        if (chktype === "NSCore::None") {
            this.m_currentBlock.push(new MIRIsTypeOfNone(sinfo, src, trgt));
        }
        else if (chktype === "NSCore::Some") {
            this.m_currentBlock.push(new MIRIsTypeOfSome(sinfo, src, trgt));
        }
        else {
            this.m_currentBlock.push(new MIRIsTypeOf(sinfo, srcInferType, src, chktype, trgt));
        }
    }

    emitTypeOfGuarded(sinfo: SourceInfo, trgt: MIRTempRegister, chktype: MIRType, src: MIRArgument, srclayouttype: MIRType, srcflowtype: MIRType, guard: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        xxxx;
    }

    emitAbort(sinfo: SourceInfo, info: string) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRAbort(sinfo, info));
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

    emitDirectJump(sinfo: SourceInfo, blck: string) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRJump(sinfo, blck));
    }

    emitBoolJump(sinfo: SourceInfo, arg: MIRTempRegister, trueblck: string, falseblck: string) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRJumpCond(sinfo, arg, trueblck, falseblck));
    }

    emitNoneJump(sinfo: SourceInfo, arg: MIRTempRegister, noneblck: string, someblk: string, ) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRJumpNone(sinfo, arg, noneblck, someblk));
    }

    emitReturnAssign(sinfo: SourceInfo, src: MIRArgument, rtype: MIRType) {
        if(!this.emitEnabled) {
            return;
        }

        xxxx;
        this.m_currentBlock.push(new MIRReturnAssign(sinfo, src));
    }

    emitReturnAssignOfCons(sinfo: SourceInfo, oftype: MIRType, args: MIRArgument[]) {
        if(!this.emitEnabled) {
            return;
        }

        xxxx;
    }

    processEnterYield() {
        if(!this.emitEnabled) {
            return;
        }

        this.yieldPatchInfo.push([]);
    }

    getActiveYieldSet(): [string, MIRTempRegister, ValueType][] {
        return this.emitEnabled ? this.yieldPatchInfo[this.yieldPatchInfo.length - 1] : [];
    }

    processExitYield() {
        if(!this.emitEnabled) {
            return;
        }

        this.yieldPatchInfo.pop();
    }

    getActiveReturnSet(): [string, MIRTempRegister, ValueType][] {
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

    getBody(file: string, sinfo: SourceInfo, args: Map<string, MIRType>): MIRBody | undefined {
        if(!this.emitEnabled) {
            return undefined;
        }

        let ibody = new MIRBody(file, sinfo, this.m_blockMap);

        propagateTmpAssignForBody(ibody);
        removeDeadTempAssignsFromBody(ibody);

        convertBodyToSSA(ibody, args);

        return ibody;
    }

    getVCallInstantiations(assembly: Assembly): [MIRVirtualMethodKey, MIRInvokeKey, OOPTypeDecl, Map<string, ResolvedType>, MemberMethodDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] | undefined {
        if (this.allVInvokes.length === 0) {
            return undefined;
        }

        let resvi = new Map<string, [MIRVirtualMethodKey, MIRInvokeKey, OOPTypeDecl, Map<string, ResolvedType>, MemberMethodDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]]>();
        for (let i = 0; i < this.allVInvokes.length; ++i) {
            const vinv = this.allVInvokes[i];

            const vcpt = ResolvedType.createSingle(ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(vinv[2] as ConceptTypeDecl, vinv[3])]));
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

                const mcreate = assembly.tryGetOOMemberDeclUnique(itype, "method", vinv[4]);
                if (mcreate !== undefined) {
                    const binds = new Map<string, ResolvedType>(mcreate.binds);
                    vinv[5].forEach((v, k) => binds.set(k, v));

                    const mkey = MIRKeyGenerator.generateMethodKey(mcreate.contiainingType, (mcreate.decl as MemberMethodDecl).name, mcreate.binds, vinv[6]);
                    if (!resvi.has(mkey)) {
                        resvi.set(mkey, [vinv[0], mkey, mcreate.contiainingType, mcreate.binds, mcreate.decl as MemberMethodDecl, binds as Map<string, ResolvedType>, vinv[6], vinv[7]]);
                    }
                }
            }
        }

        let fres: [MIRVirtualMethodKey, MIRInvokeKey, OOPTypeDecl, Map<string, ResolvedType>, MemberMethodDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];
        resvi.forEach((v, k) => fres.push(v));

        return fres;
    }

    private registerTypeInstantiation(decl: OOPTypeDecl, binds: Map<string, ResolvedType>) {
        if(!this.emitEnabled) {
            return;
        }

        const key = MIRKeyGenerator.generateTypeKey(decl, binds);
        if (this.masm.conceptDecls.has(key) || this.masm.entityDecls.has(key) || this.pendingOOProcessing.findIndex((oop) => oop[0] === key) !== -1) {
            return;
        }

        if (decl.ns === "NSCore" && decl.name === "Result") {    
            const okdecl = this.assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Ok") as EntityTypeDecl;
            const okkey = MIRKeyGenerator.generateTypeKey(okdecl, binds);
            if (!this.masm.entityDecls.has(okkey) && this.pendingOOProcessing.findIndex((oop) => oop[0] === okkey) === -1) {
                this.pendingOOProcessing.push([okkey, okdecl, binds]);
                this.entityInstantiationInfo.push([okkey, okdecl, binds]);
            }

            const errdecl = this.assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Err") as EntityTypeDecl;
            const errkey = MIRKeyGenerator.generateTypeKey(errdecl, binds);
            if (!this.masm.entityDecls.has(errkey) && this.pendingOOProcessing.findIndex((oop) => oop[0] === errkey) === -1) {
                this.pendingOOProcessing.push([errkey, errdecl, binds]);
                this.entityInstantiationInfo.push([errkey, errdecl, binds]);
            }
        }

        if (decl.ns === "NSCore" && decl.name === "Option") {
            const optdecl = this.assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Opt") as EntityTypeDecl;
            const optkey = MIRKeyGenerator.generateTypeKey(optdecl, binds);
            if (!this.masm.entityDecls.has(optkey) && this.pendingOOProcessing.findIndex((oop) => oop[0] === optkey) === -1) {
                this.pendingOOProcessing.push([optkey, optdecl, binds]);
                this.entityInstantiationInfo.push([optkey, optdecl, binds]);
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
            let rt: MIRTypeOption | undefined = undefined;

            if (sopt instanceof ResolvedEntityAtomType) {
                this.registerTypeInstantiation(sopt.object, sopt.binds);
                rt = MIREntityType.create(MIRKeyGenerator.generateTypeKey(sopt.object, sopt.binds));
            }
            else if (sopt instanceof ResolvedConceptAtomType) {
                const natoms = sopt.conceptTypes.map((cpt) => {
                    this.registerTypeInstantiation(cpt.concept, cpt.binds);
                    return MIRKeyGenerator.generateTypeKey(cpt.concept, cpt.binds);
                });
                rt = MIRConceptType.create(natoms);
            }
            else if (sopt instanceof ResolvedTupleAtomType) {
                const tatoms = sopt.types.map((entry) => new MIRTupleTypeEntry(this.registerResolvedTypeReference(entry.type), entry.isOptional));
                rt = MIRTupleType.create(tatoms);
                if(!this.masm.tupleDecls.has(rt.trkey)) {
                    this.masm.tupleDecls.set(rt.trkey, rt as MIRTupleType);
                }
            }
            else if (sopt instanceof ResolvedRecordAtomType) {
                const tatoms = sopt.entries.map((entry) => new MIRRecordTypeEntry(entry.name, this.registerResolvedTypeReference(entry.type), entry.isOptional));
                rt = MIRRecordType.create(tatoms);
                if(!this.masm.recordDecls.has(rt.trkey)) {
                    this.masm.recordDecls.set(rt.trkey, rt as MIRRecordType);
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

    registerPendingGlobalProcessing(decl: NamespaceConstDecl): MIRGlobalKey {
        const key = MIRKeyGenerator.generateFunctionKey(`global@${decl.ns}`, decl.name, new Map<string, ResolvedType>(), []);
        if (!this.emitEnabled || this.masm.constantDecls.has(key) || this.pendingGlobalProcessing.findIndex((gp) => gp[0] === key) !== -1) {
            return key;
        }

        this.pendingGlobalProcessing.push([key, decl]);
        return key;
    }

    registerPendingConstProcessing(mircontaining: MIRType, containingType: OOPTypeDecl, decl: StaticMemberDecl, binds: Map<string, ResolvedType>): MIRGlobalKey {
        const key = MIRKeyGenerator.generateFunctionKey(`static@${mircontaining.trkey}`, decl.name, new Map<string, ResolvedType>(), []);
        if (!this.emitEnabled || this.masm.constantDecls.has(key) || this.pendingConstProcessing.findIndex((cp) => cp[0] === key) !== -1) {
            return key;
        }

        this.pendingConstProcessing.push([key, containingType, decl, binds]);
        return key;
    }

    registerConstExpr(srcFile: string, exp: ConstantExpressionValue, binds: Map<string, ResolvedType>, etype: ResolvedType): MIRGlobalKey {
        const key = MIRKeyGenerator.generateFunctionKey(`cexpr@${srcFile}#${exp.exp.sinfo.pos}`, "expr", new Map<string, ResolvedType>(), []);
        if (!this.emitEnabled || this.masm.constantDecls.has(key) || this.pendingConstProcessing.findIndex((cp) => cp[0] === key) !== -1) {
            return key;
        }

        this.pendingConstExprProcessing.push([key, exp, binds, etype]);
        return key;
    }

    registerFunctionCall(ns: string, name: string, f: NamespaceFunctionDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generateFunctionKey(ns, name, binds, pcodes);
        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingFunctionProcessing.findIndex((fp) => fp[0] === key) !== -1) {
            return key;
        }

        this.pendingFunctionProcessing.push([key, f, binds, pcodes, cinfo]);
        return key;
    }

    registerNamespaceOperatorCall(ns: string, name: string, opdecl: NamespaceOperatorDecl, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        xxxx;
    }

    registerStaticOperatorCall(containingType: OOPTypeDecl, name: string, opdecl: StaticOperatorDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        xxxx;
    }

    registerStaticCall(containingType: OOPTypeDecl, cbinds: Map<string, ResolvedType>, f: StaticFunctionDecl, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generateStaticKey(containingType, name, binds, pcodes);
        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingOOStaticProcessing.findIndex((sp) => sp[0] === key) !== -1) {
            return key;
        }

        this.pendingOOStaticProcessing.push([key, containingType, cbinds, f, binds, pcodes, cinfo]);
        return key;
    }

    registerMethodCall(containingType: OOPTypeDecl, m: MemberMethodDecl, cbinds: Map<string, ResolvedType>, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const vkey = MIRKeyGenerator.generateVirtualMethodKey(name, binds);
        const key = MIRKeyGenerator.generateMethodKey(containingType, name, binds, pcodes);
        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingOOMethodProcessing.findIndex((mp) => mp[1] === key) !== -1) {
            return key;
        }

        this.pendingOOMethodProcessing.push([vkey, key, containingType, cbinds, m, binds, pcodes, cinfo]);
        return key;
    }

    registerVirtualMethodCall(containingType: OOPTypeDecl, cbinds: Map<string, ResolvedType>, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRVirtualMethodKey {
        const key = MIRKeyGenerator.generateVirtualMethodKey(name, binds);
        const tkey = MIRKeyGenerator.generateTypeKey(containingType, binds);
        if (!this.emitEnabled || this.allVInvokes.findIndex((vi) => vi[0] === key && vi[1] === tkey) !== -1) {
            return key;
        }

        this.allVInvokes.push([key, tkey, containingType, cbinds, name, binds, pcodes, cinfo]);
        return key;
    }

    registerVirtualNamespaceOperatorCall(ns: string, name: string, opdecl: NamespaceOperatorDecl, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRVirtualMethodKey {
        xxxx;
    }

    registerVirtualStaticOperatorCall(containingType: OOPTypeDecl, name: string, opdecl: StaticOperatorDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRVirtualMethodKey {
        xxxx;
    }

    registerPCode(idecl: InvokeDecl, fsig: ResolvedFunctionType, binds: Map<string, ResolvedType>, cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generatePCodeKey(idecl);
        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingPCodeProcessing.findIndex((fp) => fp[0] === key) !== -1) {
            return key;
        }

        this.pendingPCodeProcessing.push([key, idecl, fsig, binds, cinfo]);
        return key;
    }

    registerTupleProjectToEphemeral(tt: ResolvedTupleAtomType, indecies: number[], epht: ResolvedEphemeralListType): MIRInvokeKey {
        xxxx;
    }

    registerTupleProjectToEphemeralVirtual(tt: ResolvedType, indecies: number[], epht: ResolvedEphemeralListType): MIRVirtualMethodKey {
        xxxx;
    }

    registerRecordProjectToEphemeral(tt: ResolvedRecordAtomType, properties: string[], epht: ResolvedEphemeralListType): MIRInvokeKey {
        xxxx;
    }

    registerRecordProjectToEphemeralVirtual(tt: ResolvedType, properties: string[], epht: ResolvedEphemeralListType): MIRVirtualMethodKey {
        xxxx;
    }

    registerEntityProjectToEphemeral(tt: ResolvedEntityAtomType, fields: MIRFieldKey[], epht: ResolvedEphemeralListType): MIRInvokeKey {
        xxxx;
    }

    registerOOTypeProjectToEphemeralVirtual(tt: ResolvedType, fields: MIRFieldKey[], epht: ResolvedEphemeralListType): MIRVirtualMethodKey {
        xxxx;
    }

    registerTupleUpdate(tt: ResolvedTupleAtomType, updates: [number, MIRType][]): MIRInvokeKey {
        xxxx;
    }

    registerTupleUpdateVirtual(tt: ResolvedType, updates: [number, MIRType][]): MIRVirtualMethodKey {
        xxxx;
    }

    registerRecordUpdate(tt: ResolvedRecordAtomType, updates: [string, MIRType][]): MIRInvokeKey {
        xxxx;
    }

    registerRecordUpdateVirtual(tt: ResolvedType, updates: [string, MIRType][]): MIRVirtualMethodKey {
        xxxx;
    }

    registerEntityUpdate(tt: ResolvedEntityAtomType, updates: [MIRFieldKey, MIRType][]): MIRInvokeKey {
        xxxx;
    }

    registerOOTypeUpdateVirtual(tt: ResolvedType, updates: [MIRFieldKey, MIRType][]): MIRVirtualMethodKey {
        xxxx;
    }

    private closeConceptDecl( cpt: MIRConceptTypeDecl) {
        cpt.provides.forEach((tkey) => {
            const ccdecl = this.masm.conceptDecls.get(tkey) as MIRConceptTypeDecl;
            this.closeConceptDecl(ccdecl);

            ccdecl.vcallMap.forEach((vcall, vcname) => {
                if (!cpt.vcallMap.has(vcname)) {
                    cpt.vcallMap.set(vcname, vcall);
                }
            });
        });
    }

    private closeEntityDecl(entity: MIREntityTypeDecl) {
        entity.provides.forEach((tkey) => {
            const ccdecl = this.masm.conceptDecls.get(tkey) as MIRConceptTypeDecl;
            this.closeConceptDecl(ccdecl);

            ccdecl.vcallMap.forEach((vcall, vcname) => {
                if (!entity.vcallMap.has(vcname)) {
                    entity.vcallMap.set(vcname, vcall);
                }
            });
        });
    }

    static generateMASM(pckge: PackageConfig, buildLevel: BuildLevel, validateLiteralStrings: boolean, functionalize: boolean, srcFiles: { relativePath: string, contents: string }[]): { masm: MIRAssembly | undefined, errors: string[] } {
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
        const emitter = new MIREmitter(assembly, masm);
        const checker = new TypeChecker(assembly, true, emitter, buildLevel, validateLiteralStrings);

        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Any") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialAnyConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Some") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialSomeConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Parsable") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialParsableConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Validator") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialValidatorConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::KeyType") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialKeyTypeConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::PODType") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialPODTypeConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::APIType") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialAPITypeConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::APIValue") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialAPIValueConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Truthy") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialTruthyConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Enum") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialEnumConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::IdKey") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialIdKeyConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Tuple") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialTupleConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Record") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialRecordConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Object") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialObjectConceptType());

        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::None") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialNoneType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Bool") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialBoolType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Int") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialIntType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::BigInt") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialBigIntType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Float64") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialFloat64Type());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::String") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialStringType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::BufferFormat") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialBufferFormatType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::BufferEncoding") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialBufferEncodingType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::BufferCompression") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialBufferCompressionType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::ByteBuffer") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialByteBufferType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::ISOTime") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialISOTimeType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::UUID") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialUUIDType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::LogicalTime") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialLogicalTimeType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::CryptoHash") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialCryptoHashType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Regex") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialRegexType());

        //get any entrypoint functions and initialize the checker there
        const nslist = assembly.getNamespaces();
        nslist.forEach((nsentry) => {
            nsentry.functions.forEach((f) => {
                if (f.attributes.indexOf("entrypoint") !== -1) {
                    emitter.registerFunctionCall(f.ns, f.name, f, new Map<string, ResolvedType>(), [], []);
                }
            });
        });

        ////////////////
        //While there is more to process get an item and run the checker on it
        try {
            let lastVCount = 0;
            while (true) {
                while (emitter.pendingOOProcessing.length !== 0 ||
                    emitter.pendingGlobalProcessing.length !== 0 || emitter.pendingConstProcessing.length !== 0 ||
                    emitter.pendingFunctionProcessing.length !== 0 || emitter.pendingPCodeProcessing.length !== 0 ||
                    emitter.pendingOOStaticProcessing.length !== 0 || emitter.pendingOOMethodProcessing.length !== 0) {

                    while (emitter.pendingOOProcessing.length !== 0) {
                        const tt = emitter.pendingOOProcessing.pop() as [MIRResolvedTypeKey, OOPTypeDecl, Map<string, ResolvedType>];
                        checker.processOOType(...tt);
                    }

                    while (emitter.pendingGlobalProcessing.length !== 0 || emitter.pendingConstProcessing.length !== 0) {
                        if (emitter.pendingGlobalProcessing.length !== 0) {
                            const pg = emitter.pendingGlobalProcessing.pop() as [MIRConstantKey, NamespaceConstDecl];
                            checker.processGlobal(...pg);
                        }
                        if (emitter.pendingConstProcessing.length !== 0) {
                            const pc = emitter.pendingConstProcessing.pop() as [MIRConstantKey, OOPTypeDecl, StaticMemberDecl, Map<string, ResolvedType>];
                            checker.processConst(...pc);
                        }
                    }

                    if (emitter.pendingFunctionProcessing.length !== 0) {
                        const pf = emitter.pendingFunctionProcessing.pop() as [MIRInvokeKey, NamespaceFunctionDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]];
                        checker.processNamespaceFunction(...pf);
                    }
                    else if (emitter.pendingPCodeProcessing.length !== 0) {
                        const lf = emitter.pendingPCodeProcessing.pop() as [MIRInvokeKey, InvokeDecl, ResolvedFunctionType, Map<string, ResolvedType>, [string, ResolvedType][]];
                        checker.processLambdaFunction(...lf);
                    }
                    else if (emitter.pendingOOStaticProcessing.length !== 0) {
                        const sf = emitter.pendingOOStaticProcessing.pop() as [MIRInvokeKey, OOPTypeDecl, Map<string, ResolvedType>, StaticFunctionDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]];
                        checker.processStaticFunction(...sf);
                    }
                    else if (emitter.pendingOOMethodProcessing.length !== 0) {
                        const mf = emitter.pendingOOMethodProcessing.pop() as [MIRVirtualMethodKey, MIRInvokeKey, OOPTypeDecl, Map<string, ResolvedType>, MemberMethodDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]];
                        checker.processMethodFunction(...mf);
                    }
                    else {
                        //nop
                    }
                }

                //make sure all vcall candidates are processed
                const vcgens = emitter.getVCallInstantiations(assembly);
                if (vcgens === undefined || vcgens.length === lastVCount) {
                    break;
                }
                lastVCount = vcgens.length;

                for (let i = 0; i < vcgens.length; ++i) {
                    checker.processMethodFunction(...vcgens[i]);
                }
            }

            if (checker.getErrorList().length === 0) {
                checker.processRegexInfo();
                checker.runFinalExhaustiveChecks();

                //compute closed field and vtable info
                masm.conceptDecls.forEach((cpt) => emitter.closeConceptDecl(cpt));
                masm.entityDecls.forEach((entity) => emitter.closeEntityDecl(entity));

                masm.invokeDecls.forEach((idecl) => {
                    const args = new Map<string, MIRType>();
                    idecl.params.forEach((param) => args.set(param.name, masm.typeMap.get(param.type) as MIRType));
                    computeVarTypesForInvoke(idecl.body, args, masm.typeMap.get(idecl.resultType) as MIRType, masm);
                });

                if (functionalize) {
                    functionalizeInvokes(masm);
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
