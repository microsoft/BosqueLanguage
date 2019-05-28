//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo, Parser } from "../ast/parser";
import { MIRTempRegister, MIROp, MIRLoadConst, MIRConstantNone, MIRConstantTrue, MIRConstantFalse, MIRConstantInt, MIRConstantString, MIRLoadConstTypedString, MIRTypeKey, MIRAccessNamespaceConstant, MIRAccessConstField, MIRConstKey, MIRAccessCapturedVariable, MIRAccessArgVariable, MIRAccessLocalVariable, MIRArgument, MIRLambdaKey, MIRFunctionKey, MIRStaticKey, MIRConstructorPrimary, MIRConstructorPrimaryCollectionSingletons, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionMixed, MIRMethodKey, MIRGlobalKey, MIRAccessFromIndex, MIRProjectFromIndecies, MIRProjectFromProperties, MIRProjectFromFields, MIRAccessFromProperty, MIRAccessFromField, MIRConstructorTuple, MIRConstructorRecord, MIRConstructorPrimaryCollectionEmpty, MIRResolvedTypeKey, MIRFieldKey, MIRLoadFieldDefaultValue, MIRConstructorLambda, MIRCallNamespaceFunction, MIRCallStaticFunction, MIRProjectFromTypeTuple, MIRProjectFromTypeRecord, MIRProjectFromTypeConcept, MIRModifyWithIndecies, MIRModifyWithProperties, MIRModifyWithFields, MIRStructuredExtendTuple, MIRStructuredExtendRecord, MIRStructuredExtendObject, MIRInvokeKnownTarget, MIRVirtualMethodKey, MIRInvokeVirtualTarget, MIRCallLambda, MIRJump, MIRJumpCond, MIRPrefixOp, MIRBinOp, MIRBinCmp, MIRBinEq, MIRRegAssign, MIRVarStore, MIRReturnAssign, MIRVarLifetimeStart, MIRVarLifetimeEnd, MIRBody, MIRBasicBlock, MIRTruthyConvert, MIRJumpNone, MIRDebug, MIRVarCaptured, MIRVarParameter, MIRVarLocal, MIRRegisterArgument, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRIsTypeOf, MIRLogicStore, MIRAbort } from "./mir_ops";
import { OOPTypeDecl, StaticFunctionDecl, MemberMethodDecl, InvokeDecl, Assembly, NamespaceFunctionDecl, NamespaceConstDecl, StaticMemberDecl, ConceptTypeDecl, EntityTypeDecl } from "../ast/assembly";
import { ResolvedType, ResolvedEntityAtomType, ResolvedConceptAtomType, ResolvedTupleAtomType, ResolvedRecordAtomType, ResolvedFunctionAtomType, ResolvedConceptAtomTypeEntry } from "../ast/resolved_type";
import { PackageConfig, MIRAssembly, MIRType, MIRTypeOption, MIRFunctionType, MIRFunctionParameter, MIREntityType, MIRConceptType, MIRTupleTypeEntry, MIRTupleType, MIRRecordTypeEntry, MIRRecordType } from "./mir_assembly";

import * as Crypto from "crypto";
import { TypeChecker } from "../type_checker/type_checker";
import { propagateTmpAssignForBody, removeDeadTempAssignsFromBody } from "./mir_cleanup";
import { convertBodyToSSA } from "./mir_ssa";

class MIRKeyGenerator {
    static computeBindsKeyInfo(binds: Map<string, ResolvedType>): string {
        let terms: string[] = [];
        binds.forEach((v, k) => terms.push(`${k}=${v.idStr}`));

        return `[${terms.sort().join(", ")}]`;
    }

    static generateTypeKey(t: OOPTypeDecl, binds: Map<string, ResolvedType>): MIRTypeKey {
        if (binds.size === 0) {
            return `${t.ns}::${t.name}`;
        }
        else {
            return `${t.ns}::${t.name}${MIRKeyGenerator.computeBindsKeyInfo(binds)}`;
        }
    }

    static generateGlobalKey(ns: string, name: string): MIRGlobalKey {
        return `${ns}::${name}`;
    }

    static generateConstKey(t: OOPTypeDecl, binds: Map<string, ResolvedType>, name: string): MIRConstKey {
        if (binds.size === 0) {
            return `${t.ns}::${t.name}::${name}`;
        }
        else {
            return `${t.ns}::${t.name}::${name}${MIRKeyGenerator.computeBindsKeyInfo(binds)}`;
        }
    }

    static generateFieldKey(t: OOPTypeDecl, binds: Map<string, ResolvedType>, name: string): MIRFieldKey {
        if (binds.size === 0) {
            return `${t.ns}::${t.name}::${name}`;
        }
        else {
            return `${t.ns}::${t.name}::${name}${MIRKeyGenerator.computeBindsKeyInfo(binds)}`;
        }
    }

    static generateLambdaKey(file: string, line: number, column: number, cpos: number, binds: Map<string, ResolvedType>): MIRLambdaKey {
        if (binds.size === 0) {
            return `${file}\$${line}\$${column}\$${cpos}`;
        }
        else {
            return `${file}\$${line}\$${column}\$${cpos}\$${MIRKeyGenerator.computeBindsKeyInfo(binds)}`;
        }
    }

    static generateFunctionKey(ns: string, name: string, binds: Map<string, ResolvedType>): MIRFunctionKey {
        if (binds.size === 0) {
            return `${ns}::${name}`;
        }
        else {
            return `${ns}::${name}${MIRKeyGenerator.computeBindsKeyInfo(binds)}`;
        }
    }

    static generateStaticKey(t: OOPTypeDecl, name: string, binds: Map<string, ResolvedType>): MIRStaticKey {
        if (binds.size === 0) {
            return `${t.ns}::${t.name}::${name}`;
        }
        else {
            return `${t.ns}::${t.name}::${name}${MIRKeyGenerator.computeBindsKeyInfo(binds)}`;
        }
    }

    static generateMethodKey(t: OOPTypeDecl, name: string, binds: Map<string, ResolvedType>): MIRMethodKey {
        if (binds.size === 0) {
            return `${t.ns}::${t.name}::${name}`;
        }
        else {
            return `${t.ns}::${t.name}::${name}${MIRKeyGenerator.computeBindsKeyInfo(binds)}`;
        }
    }

    static generateVirtualMethodKey(vname: string, binds: Map<string, ResolvedType>): MIRVirtualMethodKey {
        if (binds.size === 0) {
            return `${vname}`;
        }
        else {
            return `${vname}${MIRKeyGenerator.computeBindsKeyInfo(binds)}`;
        }
    }
}

class MIRBodyEmitter {
    private m_blockMap: Map<string, MIRBasicBlock> = new Map<string, MIRBasicBlock>();
    private m_currentBlock: MIROp[] = [];

    private m_tmpIDCtr = 0;

    initialize() {
        this.m_tmpIDCtr = 0;

        this.m_blockMap = new Map<string, MIRBasicBlock>();
        this.m_blockMap.set("entry", new MIRBasicBlock("entry", []));
        this.m_blockMap.set("exit", new MIRBasicBlock("exit", []));

        (this.m_blockMap.get("exit") as MIRBasicBlock).ops.push(new MIRVarStore(new SourceInfo(-1, 0, 0, 0), new MIRVarLocal("_ir_ret_"), new MIRVarLocal("_return_")));

        this.m_currentBlock = (this.m_blockMap.get("entry") as MIRBasicBlock).ops;
    }

    generateTmpRegister(): MIRTempRegister {
        return new MIRTempRegister(this.m_tmpIDCtr++);
    }

    createNewBlock(pfx: string): string {
        const name = `${pfx}_${this.m_blockMap.size}`;
        this.m_blockMap.set(name, new MIRBasicBlock(name, []));

        return name;
    }

    setActiveBlock(name: string) {
        this.m_currentBlock = (this.m_blockMap.get(name) as MIRBasicBlock).ops;
    }

    emitLoadConstNone(sinfo: SourceInfo, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantNone(), trgt));
    }

    emitLoadConstBool(sinfo: SourceInfo, bv: boolean, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRLoadConst(sinfo, bv ? new MIRConstantTrue() : new MIRConstantFalse(), trgt));
    }

    emitLoadConstInt(sinfo: SourceInfo, iv: string, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantInt(iv), trgt));
    }

    emitLoadConstString(sinfo: SourceInfo, sv: string, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantString(sv), trgt));
    }

    emitLoadConstTypedString(sinfo: SourceInfo, sv: string, tkey: MIRTypeKey, tskey: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRLoadConstTypedString(sinfo, sv, tkey, tskey, trgt));
    }

    emitAccessNamespaceConstant(sinfo: SourceInfo, gkey: MIRGlobalKey, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRAccessNamespaceConstant(sinfo, gkey, trgt));
    }

    emitAccessConstField(sinfo: SourceInfo, ckey: MIRConstKey, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRAccessConstField(sinfo, ckey, trgt));
    }

    emitLoadMemberFieldDefaultValue(sinfo: SourceInfo, ckey: MIRFieldKey, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRLoadFieldDefaultValue(sinfo, ckey, trgt));
    }

    emitAccessCapturedVariable(sinfo: SourceInfo, name: string, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRAccessCapturedVariable(sinfo, new MIRVarCaptured(name), trgt));
    }

    emitAccessArgVariable(sinfo: SourceInfo, name: string, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRAccessArgVariable(sinfo, new MIRVarParameter(name), trgt));
    }

    emitAccessLocalVariable(sinfo: SourceInfo, name: string, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRAccessLocalVariable(sinfo, new MIRVarLocal(name), trgt));
    }

    emitConstructorPrimary(sinfo: SourceInfo, tkey: MIRTypeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRConstructorPrimary(sinfo, tkey, args, trgt));
    }

    emitConstructorPrimaryCollectionEmpty(sinfo: SourceInfo, tkey: MIRTypeKey, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRConstructorPrimaryCollectionEmpty(sinfo, tkey, trgt));
    }

    emitConstructorPrimaryCollectionSingletons(sinfo: SourceInfo, tkey: MIRTypeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRConstructorPrimaryCollectionSingletons(sinfo, tkey, args, trgt));
    }

    emitConstructorPrimaryCollectionCopies(sinfo: SourceInfo, tkey: MIRTypeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRConstructorPrimaryCollectionCopies(sinfo, tkey, args, trgt));
    }

    emitConstructorPrimaryCollectionMixed(sinfo: SourceInfo, tkey: MIRTypeKey, args: [boolean, MIRArgument][], trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRConstructorPrimaryCollectionMixed(sinfo, tkey, args, trgt));
    }

    emitConstructorTuple(sinfo: SourceInfo, args: MIRArgument[], trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRConstructorTuple(sinfo, args, trgt));
    }

    emitConstructorRecord(sinfo: SourceInfo, args: [string, MIRArgument][], trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRConstructorRecord(sinfo, args, trgt));
    }

    emitConstructorLambda(sinfo: SourceInfo, lkey: MIRLambdaKey, lsigkey: MIRResolvedTypeKey, captured: Map<string, MIRRegisterArgument>, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRConstructorLambda(sinfo, lkey, lsigkey, captured, trgt));
    }

    emitCallNamespaceFunction(sinfo: SourceInfo, fkey: MIRFunctionKey, args: MIRArgument[], trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRCallNamespaceFunction(sinfo, fkey, args, trgt));
    }

    emitCallStaticFunction(sinfo: SourceInfo, skey: MIRStaticKey, args: MIRArgument[], trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRCallStaticFunction(sinfo, skey, args, trgt));
    }

    emitLoadTupleIndex(sinfo: SourceInfo, arg: MIRArgument, idx: number, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRAccessFromIndex(sinfo, arg, idx, trgt));
    }

    emitProjectTupleIndecies(sinfo: SourceInfo, arg: MIRArgument, indecies: number[], trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRProjectFromIndecies(sinfo, arg, indecies, trgt));
    }

    emitLoadProperty(sinfo: SourceInfo, arg: MIRArgument, pname: string, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRAccessFromProperty(sinfo, arg, pname, trgt));
    }

    emitLoadField(sinfo: SourceInfo, arg: MIRArgument, fname: string, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRAccessFromField(sinfo, arg, fname, trgt));
    }

    emitProjectProperties(sinfo: SourceInfo, arg: MIRArgument, properties: string[], trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRProjectFromProperties(sinfo, arg, properties, trgt));
    }

    emitProjectFields(sinfo: SourceInfo, arg: MIRArgument, fields: string[], trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRProjectFromFields(sinfo, arg, fields, trgt));
    }

    emitProjectFromTypeTuple(sinfo: SourceInfo, arg: MIRArgument, ptype: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRProjectFromTypeTuple(sinfo, arg, ptype, trgt));
    }

    emitProjectFromTypeRecord(sinfo: SourceInfo, arg: MIRArgument, ptype: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRProjectFromTypeRecord(sinfo, arg, ptype, trgt));
    }

    emitProjectFromTypeConcept(sinfo: SourceInfo, arg: MIRArgument, ctypes: MIRTypeKey[], trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRProjectFromTypeConcept(sinfo, arg, ctypes, trgt));
    }

    emitModifyWithIndecies(sinfo: SourceInfo, arg: MIRArgument, updates: [number, MIRArgument][], trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRModifyWithIndecies(sinfo, arg, updates, trgt));
    }

    emitModifyWithProperties(sinfo: SourceInfo, arg: MIRArgument, updates: [string, MIRArgument][], trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRModifyWithProperties(sinfo, arg, updates, trgt));
    }

    emitModifyWithFields(sinfo: SourceInfo, arg: MIRArgument, updates: [string, MIRArgument][], trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRModifyWithFields(sinfo, arg, updates, trgt));
    }

    emitStructuredExtendTuple(sinfo: SourceInfo, arg: MIRArgument, update: MIRArgument, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRStructuredExtendTuple(sinfo, arg, update, trgt));
    }

    emitStructuredExtendRecord(sinfo: SourceInfo, arg: MIRArgument, update: MIRArgument, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRStructuredExtendRecord(sinfo, arg, update, trgt));
    }

    emitStructuredExtendObject(sinfo: SourceInfo, arg: MIRArgument, update: MIRArgument, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRStructuredExtendObject(sinfo, arg, update, trgt));
    }

    emitInvokeKnownTarget(sinfo: SourceInfo, mkey: MIRMethodKey, args: MIRArgument[], trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRInvokeKnownTarget(sinfo, mkey, args, trgt));
    }

    emitInvokeVirtualTarget(sinfo: SourceInfo, vresolve: MIRVirtualMethodKey, args: MIRArgument[], trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRInvokeVirtualTarget(sinfo, vresolve, args, trgt));
    }

    emitCallLambda(sinfo: SourceInfo, lambda: MIRArgument, args: MIRArgument[], trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRCallLambda(sinfo, lambda, args, trgt));
    }

    emitPrefixOp(sinfo: SourceInfo, op: string, arg: MIRArgument, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRPrefixOp(sinfo, op, arg, trgt));
    }

    emitBinOp(sinfo: SourceInfo, lhs: MIRArgument, op: string, rhs: MIRArgument, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRBinOp(sinfo, lhs, op, rhs, trgt));
    }

    emitBinEq(sinfo: SourceInfo, lhs: MIRArgument, op: string, rhs: MIRArgument, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRBinEq(sinfo, lhs, op, rhs, trgt));
    }

    emitBinCmp(sinfo: SourceInfo, lhs: MIRArgument, op: string, rhs: MIRArgument, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRBinCmp(sinfo, lhs, op, rhs, trgt));
    }

    emitTypeOf(sinfo: SourceInfo, trgt: MIRTempRegister, chktype: MIRResolvedTypeKey, src: MIRArgument) {
        if (chktype === "NSCore::None") {
            this.m_currentBlock.push(new MIRIsTypeOfNone(sinfo, src, trgt));
        }
        else if (chktype === "NSCore::Some") {
            this.m_currentBlock.push(new MIRIsTypeOfSome(sinfo, src, trgt));
        }
        else {
            this.m_currentBlock.push(new MIRIsTypeOf(sinfo, src, chktype, trgt));
        }
    }

    emitRegAssign(sinfo: SourceInfo, src: MIRArgument, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRRegAssign(sinfo, src, trgt));
    }

    emitTruthyConversion(sinfo: SourceInfo, src: MIRTempRegister, trgt: MIRTempRegister) {
        this.m_currentBlock.push(new MIRTruthyConvert(sinfo, src, trgt));
    }

    emitLogicStore(sinfo: SourceInfo, trgt: MIRTempRegister, lhs: MIRArgument, op: string, rhs: MIRArgument) {
        this.m_currentBlock.push(new MIRLogicStore(sinfo, lhs, op, rhs, trgt));
    }

    localLifetimeStart(sinfo: SourceInfo, name: string, rtkey: MIRResolvedTypeKey) {
        this.m_currentBlock.push(new MIRVarLifetimeStart(sinfo, name, rtkey));
    }

    emitVarStore(sinfo: SourceInfo, src: MIRTempRegister, name: string) {
        this.m_currentBlock.push(new MIRVarStore(sinfo, src, new MIRVarLocal(name)));
    }

    localLifetimeEnd(sinfo: SourceInfo, name: string) {
        this.m_currentBlock.push(new MIRVarLifetimeEnd(sinfo, name));
    }

    emitReturnAssign(sinfo: SourceInfo, src: MIRArgument) {
        this.m_currentBlock.push(new MIRReturnAssign(sinfo, src));
    }

    emitAbort(sinfo: SourceInfo, releaseEnable: boolean, info: string) {
        this.m_currentBlock.push(new MIRAbort(sinfo, releaseEnable, info));
    }

    emitDebugBreak(sinfo: SourceInfo) {
        this.m_currentBlock.push(new MIRDebug(sinfo, undefined));
    }

    emitDebugPrint(sinfo: SourceInfo, value: MIRArgument) {
        this.m_currentBlock.push(new MIRDebug(sinfo, value));
    }

    emitDirectJump(sinfo: SourceInfo, blck: string) {
        this.m_currentBlock.push(new MIRJump(sinfo, blck));
    }

    emitBoolJump(sinfo: SourceInfo, arg: MIRTempRegister, trueblck: string, falseblck: string) {
        this.m_currentBlock.push(new MIRJumpCond(sinfo, arg, trueblck, falseblck));
    }

    emitNoneJump(sinfo: SourceInfo, arg: MIRTempRegister, noneblck: string, someblk: string, ) {
        this.m_currentBlock.push(new MIRJumpNone(sinfo, arg, noneblck, someblk));
    }

    getBody(file: string, sinfo: SourceInfo, args: string[], captured: string[]): MIRBody {
        let ibody = new MIRBody(file, sinfo, this.m_blockMap);

        propagateTmpAssignForBody(ibody);
        removeDeadTempAssignsFromBody(ibody);
        convertBodyToSSA(ibody, args, captured);

        return ibody;
    }
}

class MIREmitter {
    readonly masm: MIRAssembly;
    readonly bodyEmitter: MIRBodyEmitter = new MIRBodyEmitter();

    private readonly pendingOOProcessing: [MIRTypeKey, OOPTypeDecl, Map<string, ResolvedType>][] = [];

    private readonly pendingGlobalProcessing: [MIRGlobalKey, NamespaceConstDecl][] = [];
    private readonly pendingConstProcessing: [MIRConstKey, OOPTypeDecl, StaticMemberDecl, Map<string, ResolvedType>][] = [];

    private readonly pendingOOStaticProcessing: [MIRStaticKey, OOPTypeDecl, StaticFunctionDecl, Map<string, ResolvedType>][] = [];
    private readonly pendingOOMethodProcessing: [MIRVirtualMethodKey, MIRMethodKey, OOPTypeDecl, Map<string, ResolvedType>, MemberMethodDecl, Map<string, ResolvedType>][] = [];
    private readonly pendingFunctionProcessing: [MIRFunctionKey, NamespaceFunctionDecl, Map<string, ResolvedType>][] = [];
    private readonly pendingLambdaProcessing: [MIRLambdaKey, InvokeDecl, Map<string, ResolvedType>, Map<string, ResolvedType>, ResolvedFunctionAtomType][] = [];

    private readonly entityInstantiationInfo: [MIRTypeKey, OOPTypeDecl, Map<string, ResolvedType>][] = [];
    private readonly allVInvokes: [MIRVirtualMethodKey, MIRTypeKey, OOPTypeDecl, Map<string, ResolvedType>, string, Map<string, ResolvedType>][] = [];

    private constructor(masm: MIRAssembly) {
        this.masm = masm;
    }

    initializeBodyEmitter() {
        this.bodyEmitter.initialize();
    }

    getVCallInstantiations(assembly: Assembly): [MIRVirtualMethodKey, MIRMethodKey, OOPTypeDecl, Map<string, ResolvedType>, MemberMethodDecl, Map<string, ResolvedType>][] | undefined {
        if (this.allVInvokes.length === 0) {
            return undefined;
        }

        let resvi = new Map<string, [MIRVirtualMethodKey, MIRMethodKey, OOPTypeDecl, Map<string, ResolvedType>, MemberMethodDecl, Map<string, ResolvedType>]>();
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

                    if (!resvi.has(vinv[1])) {
                        resvi.set(vinv[1], [vinv[0], vinv[1], mcreate.contiainingType, mcreate.binds, mcreate.decl as MemberMethodDecl, binds as Map<string, ResolvedType>]);
                    }
                }
            }
        }

        let fres: [MIRVirtualMethodKey, MIRMethodKey, OOPTypeDecl, Map<string, ResolvedType>, MemberMethodDecl, Map<string, ResolvedType>][] = [];
        resvi.forEach((v, k) => fres.push(v));

        return fres;
    }

    registerTypeInstantiation(decl: OOPTypeDecl, binds: Map<string, ResolvedType>) {
        const key = MIRKeyGenerator.generateTypeKey(decl, binds);
        if (this.masm.conceptMap.has(key) || this.masm.entityMap.has(key) || this.pendingOOProcessing.findIndex((oop) => oop[0] === key) !== -1) {
            return;
        }

        this.pendingOOProcessing.push([key, decl, binds]);
        this.entityInstantiationInfo.push([key, decl, binds]);
    }

    registerResolvedTypeReference(t: ResolvedType): MIRType {
        if (t.options.length > 1) {
            const oopts = t.options.map((opt) => this.registerResolvedTypeReference(ResolvedType.createSingle(opt)).options);
            const ft = MIRType.create(([] as MIRTypeOption[]).concat(...oopts));

            this.masm.typeMap.set(ft.trkey, ft);
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
                rt = MIRTupleType.create(sopt.isOpen, tatoms);
            }
            else if (sopt instanceof ResolvedRecordAtomType) {
                const tatoms = sopt.entries.map((entry) => new MIRRecordTypeEntry(entry.name, this.registerResolvedTypeReference(entry.type), entry.isOptional));
                rt = MIRRecordType.create(sopt.isOpen, tatoms);
            }
            else {
                const fopt = (sopt as ResolvedFunctionAtomType);
                const params = fopt.params.map((p) => new MIRFunctionParameter(p.name, this.registerResolvedTypeReference(p.type), p.isOptional));
                const optRestName = fopt.optRestParamName;
                const optRestType = fopt.optRestParamType !== undefined ? this.registerResolvedTypeReference(fopt.optRestParamType) : undefined;
                const resultType = this.registerResolvedTypeReference(fopt.resultType);

                rt = MIRFunctionType.create(params, optRestName, optRestType, resultType);
            }

            const ft = MIRType.create([rt as MIRTypeOption]);
            this.masm.typeMap.set(ft.trkey, ft);
            return ft;
        }
    }

    registerPendingGlobalProcessing(decl: NamespaceConstDecl) {
        const key = MIRKeyGenerator.generateGlobalKey(decl.ns, decl.name);
        if (this.masm.globalDecls.has(key) || this.pendingGlobalProcessing.findIndex((gp) => gp[0] === key) !== -1) {
            return;
        }

        this.pendingGlobalProcessing.push([key, decl]);
    }

    registerPendingConstProcessing(containingType: OOPTypeDecl, decl: StaticMemberDecl, binds: Map<string, ResolvedType>) {
        const key = MIRKeyGenerator.generateConstKey(containingType, binds, decl.name);
        if (this.masm.constDecls.has(key) || this.pendingConstProcessing.findIndex((cp) => cp[0] === key) !== -1) {
            return;
        }

        this.pendingConstProcessing.push([key, containingType, decl, binds]);
    }

    registerFunctionCall(ns: string, name: string, f: NamespaceFunctionDecl, binds: Map<string, ResolvedType>) {
        const key = MIRKeyGenerator.generateFunctionKey(ns, name, binds);
        if (this.masm.functionDecls.has(key) || this.pendingFunctionProcessing.findIndex((fp) => fp[0] === key) !== -1) {
            return;
        }

        this.pendingFunctionProcessing.push([key, f, binds]);
    }

    registerStaticCall(containingType: OOPTypeDecl, f: StaticFunctionDecl, name: string, binds: Map<string, ResolvedType>) {
        const key = MIRKeyGenerator.generateStaticKey(containingType, name, binds);
        if (this.masm.staticDecls.has(key) || this.pendingOOStaticProcessing.findIndex((sp) => sp[0] === key) !== -1) {
            return;
        }

        this.pendingOOStaticProcessing.push([key, containingType, f, binds]);
    }

    registerMethodCall(containingType: OOPTypeDecl, m: MemberMethodDecl, cbinds: Map<string, ResolvedType>, name: string, binds: Map<string, ResolvedType>) {
        const vkey = MIRKeyGenerator.generateVirtualMethodKey(name, binds);
        const key = MIRKeyGenerator.generateMethodKey(containingType, name, binds);
        if (this.masm.methodDecls.has(key) || this.pendingOOMethodProcessing.findIndex((mp) => mp[0] === key) !== -1) {
            return;
        }

        this.pendingOOMethodProcessing.push([vkey, key, containingType, cbinds, m, binds]);
    }

    registerVirtualMethodCall(containingType: OOPTypeDecl, cbinds: Map<string, ResolvedType>, name: string, binds: Map<string, ResolvedType>) {
        const key = MIRKeyGenerator.generateVirtualMethodKey(name, binds);
        const tkey = MIRKeyGenerator.generateTypeKey(containingType, binds);
        if (this.allVInvokes.findIndex((vi) => vi[0] === key && vi[1] === tkey) !== -1) {
            return;
        }

        this.allVInvokes.push([key, tkey, containingType, cbinds, name, binds]);
    }

    registerLambda(lkey: MIRLambdaKey, capturedMap: Map<string, ResolvedType>, invoke: InvokeDecl, binds: Map<string, ResolvedType>, rsig: ResolvedFunctionAtomType) {
        if (this.masm.lambdaDecls.has(lkey) || this.pendingLambdaProcessing.findIndex((lp) => lp[0] === lkey) !== -1) {
            return;
        }

        this.pendingLambdaProcessing.push([lkey, invoke, capturedMap, binds, rsig]);
    }

    static generateMASM(pckge: PackageConfig, srcFiles: { relativePath: string, contents: string }[]): { masm: MIRAssembly | undefined, errors: string[] } {
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
            return { masm: undefined, errors: [...parseErrors] };
        }

        ////////////////
        //Compute the assembly hash and initialize representations
        const hash = Crypto.createHash("sha256");
        const data = [...srcFiles].sort((a, b) => a.relativePath.localeCompare(b.relativePath));
        data.forEach((sf) => {
            hash.update(sf.relativePath);
            hash.update(sf.contents);
        });

        const masm = new MIRAssembly(pckge, srcFiles, hash.digest("hex"));
        const emitter = new MIREmitter(masm);
        const checker = new TypeChecker(assembly, true, emitter);

        //get any entrypoint functions and initialize the checker there
        const nslist = assembly.getNamespaces();
        nslist.forEach((nsentry) => {
            nsentry.functions.forEach((f) => {
                if (f.attributes.indexOf("entrypoint") !== -1) {
                    emitter.registerFunctionCall(f.ns, f.name, f, new Map<string, ResolvedType>());
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
                    emitter.pendingFunctionProcessing.length !== 0 || emitter.pendingLambdaProcessing.length !== 0 ||
                    emitter.pendingOOStaticProcessing.length !== 0 || emitter.pendingOOMethodProcessing.length !== 0) {

                    while (emitter.pendingOOProcessing.length !== 0) {
                        const tt = emitter.pendingOOProcessing.pop() as [MIRTypeKey, OOPTypeDecl, Map<string, ResolvedType>];
                        checker.processOOType(...tt);
                    }

                    while (emitter.pendingGlobalProcessing.length !== 0 || emitter.pendingConstProcessing.length !== 0) {
                        if (emitter.pendingGlobalProcessing.length !== 0) {
                            const pg = emitter.pendingGlobalProcessing.pop() as [MIRGlobalKey, NamespaceConstDecl];
                            checker.processGlobal(...pg);
                        }
                        if (emitter.pendingConstProcessing.length !== 0) {
                            const pc = emitter.pendingConstProcessing.pop() as [MIRConstKey, OOPTypeDecl, StaticMemberDecl, Map<string, ResolvedType>];
                            checker.processConst(...pc);
                        }
                    }

                    if (emitter.pendingFunctionProcessing.length !== 0) {
                        const pf = emitter.pendingFunctionProcessing.pop() as [MIRFunctionKey, NamespaceFunctionDecl, Map<string, ResolvedType>];
                        checker.processNamespaceFunction(...pf);
                    }
                    else if (emitter.pendingLambdaProcessing.length !== 0) {
                        const lf = emitter.pendingLambdaProcessing.pop() as [MIRLambdaKey, InvokeDecl, Map<string, ResolvedType>, Map<string, ResolvedType>, ResolvedFunctionAtomType];
                        checker.processLambdaFunction(...lf);
                    }
                    else if (emitter.pendingOOStaticProcessing.length !== 0) {
                        const sf = emitter.pendingOOStaticProcessing.pop() as [MIRStaticKey, OOPTypeDecl, StaticFunctionDecl, Map<string, ResolvedType>];
                        checker.processStaticFunction(...sf);
                    }
                    else if (emitter.pendingOOMethodProcessing.length !== 0) {
                        const mf = emitter.pendingOOMethodProcessing.pop() as [MIRVirtualMethodKey, MIRMethodKey, OOPTypeDecl, Map<string, ResolvedType>, MemberMethodDecl, Map<string, ResolvedType>];
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

            //compute closed field and vtable info
            masm.conceptMap.forEach((cpt) => masm.closeConceptDecl(cpt));
            masm.entityMap.forEach((entity) => masm.closeEntityDecl(entity));
        }
        catch (ex) {
            //ignore
        }

        const tcerrors = checker.getErrorList();
        if (tcerrors.length !== 0) {
            return { masm: undefined, errors: tcerrors.map((err) => JSON.stringify(err)) };
        }
        else {
            return { masm: masm, errors: [] };
        }
    }
}

export { MIRKeyGenerator, MIRBodyEmitter, MIREmitter };
