"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const parser_1 = require("../ast/parser");
const mir_ops_1 = require("./mir_ops");
const assembly_1 = require("../ast/assembly");
const resolved_type_1 = require("../ast/resolved_type");
const mir_assembly_1 = require("./mir_assembly");
const Crypto = require("crypto");
const type_checker_1 = require("../type_checker/type_checker");
const mir_cleanup_1 = require("./mir_cleanup");
const mir_ssa_1 = require("./mir_ssa");
const mir_vartype_1 = require("./mir_vartype");
const functionalize_1 = require("./functionalize");
class MIRKeyGenerator {
    static computeBindsKeyInfo(binds) {
        if (binds.size === 0) {
            return "";
        }
        let terms = [];
        binds.forEach((v, k) => terms.push(`${k}=${v.idStr}`));
        return `<${terms.sort().join(", ")}>`;
    }
    static computePCodeKeyInfo(pcodes) {
        if (pcodes.length === 0) {
            return "";
        }
        return "[" + pcodes.map((pc) => `${pc.code.srcFile}%${pc.code.sourceLocation.line}%${pc.code.sourceLocation.column}`).join(",") + "]";
    }
    static generateTypeKey(t, binds) {
        return `${t.ns}::${t.name}${MIRKeyGenerator.computeBindsKeyInfo(binds)}`;
    }
    static generateGlobalKey(ns, name) {
        return `${ns}::${name}`;
    }
    static generateConstKey(t, binds, name) {
        return `${MIRKeyGenerator.generateTypeKey(t, binds)}::${name}`;
    }
    static generateFieldKey(t, binds, name) {
        return `${MIRKeyGenerator.generateTypeKey(t, binds)}.${name}`;
    }
    static generateFunctionKey(ns, name, binds, pcodes) {
        return `${ns}::${name}${MIRKeyGenerator.computeBindsKeyInfo(binds)}${MIRKeyGenerator.computePCodeKeyInfo(pcodes)}`;
    }
    static generateStaticKey(t, name, binds, pcodes) {
        return `${t.ns}::${t.name}::${name}${MIRKeyGenerator.computeBindsKeyInfo(binds)}${MIRKeyGenerator.computePCodeKeyInfo(pcodes)}`;
    }
    static generateMethodKey(t, name, binds, pcodes) {
        return `${t.ns}::${t.name}::${name}${MIRKeyGenerator.computeBindsKeyInfo(binds)}${MIRKeyGenerator.computePCodeKeyInfo(pcodes)}`;
    }
    static generateVirtualMethodKey(vname, binds) {
        return `${vname}${MIRKeyGenerator.computeBindsKeyInfo(binds)}`;
    }
    static generatePCodeKey(inv) {
        //
        //TODO: this might not be great as we leak build environment info into the assembly :(
        //      maybe we can do a hash of contents + basename (or something similar)?
        //
        return `fn--${inv.srcFile}%${inv.sourceLocation.line}%${inv.sourceLocation.column}`;
    }
}
exports.MIRKeyGenerator = MIRKeyGenerator;
class MIRBodyEmitter {
    constructor() {
        this.m_blockMap = new Map();
        this.m_currentBlock = [];
        this.m_tmpIDCtr = 0;
    }
    initialize() {
        this.m_tmpIDCtr = 0;
        this.m_blockMap = new Map();
        this.m_blockMap.set("entry", new mir_ops_1.MIRBasicBlock("entry", []));
        this.m_blockMap.set("returnassign", new mir_ops_1.MIRBasicBlock("returnassign", []));
        this.m_blockMap.set("exit", new mir_ops_1.MIRBasicBlock("exit", []));
        this.m_currentBlock = this.m_blockMap.get("entry").ops;
    }
    generateTmpRegister() {
        return new mir_ops_1.MIRTempRegister(this.m_tmpIDCtr++);
    }
    generateCapturedVarName(name) {
        return "__c_" + name;
    }
    createNewBlock(pfx) {
        const name = `${pfx}_${this.m_blockMap.size}`;
        this.m_blockMap.set(name, new mir_ops_1.MIRBasicBlock(name, []));
        return name;
    }
    setActiveBlock(name) {
        this.m_currentBlock = this.m_blockMap.get(name).ops;
    }
    emitLoadConstNone(sinfo, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRLoadConst(sinfo, new mir_ops_1.MIRConstantNone(), trgt));
    }
    emitLoadConstBool(sinfo, bv, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRLoadConst(sinfo, bv ? new mir_ops_1.MIRConstantTrue() : new mir_ops_1.MIRConstantFalse(), trgt));
    }
    emitLoadConstInt(sinfo, iv, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRLoadConst(sinfo, new mir_ops_1.MIRConstantInt(iv), trgt));
    }
    emitLoadConstBigInt(sinfo, iv, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRLoadConst(sinfo, new mir_ops_1.MIRConstantBigInt(iv), trgt));
    }
    emitLoadConstFloat(sinfo, fv, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRLoadConst(sinfo, new mir_ops_1.MIRConstantFloat64(fv), trgt));
    }
    emitLoadConstString(sinfo, sv, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRLoadConst(sinfo, new mir_ops_1.MIRConstantString(sv), trgt));
    }
    emitLoadLiteralRegex(sinfo, restr, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRLoadConstRegex(sinfo, restr, trgt));
    }
    emitLoadValidatedTypedString(sinfo, sv, tkey, tskey, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRLoadConstSafeString(sinfo, sv, tkey, tskey, trgt));
    }
    emitLoadConstTypedString(sinfo, sv, tkey, tskey, pfunckey, errtype, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRLoadConstTypedString(sinfo, sv, tkey, tskey, pfunckey, errtype, trgt));
    }
    emitAccessConstant(sinfo, gkey, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRAccessConstantValue(sinfo, gkey, trgt));
    }
    emitLoadMemberFieldDefaultValue(sinfo, ckey, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRLoadFieldDefaultValue(sinfo, ckey, trgt));
    }
    emitAccessArgVariable(sinfo, name, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRAccessArgVariable(sinfo, new mir_ops_1.MIRVariable(name), trgt));
    }
    emitAccessLocalVariable(sinfo, name, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRAccessLocalVariable(sinfo, new mir_ops_1.MIRVariable(name), trgt));
    }
    emitConstructorPrimary(sinfo, tkey, args, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRConstructorPrimary(sinfo, tkey, args, trgt));
    }
    emitInvokeInvariantCheckDirect(sinfo, ikey, tkey, rcvr, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRInvokeInvariantCheckDirect(sinfo, ikey, tkey, rcvr, trgt));
    }
    emitInvokeInvariantCheckVirtualTarget(sinfo, inferrcvr, rcvr, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRInvokeInvariantCheckVirtualTarget(sinfo, inferrcvr, rcvr, trgt));
    }
    emitConstructorPrimaryCollectionEmpty(sinfo, tkey, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRConstructorPrimaryCollectionEmpty(sinfo, tkey, trgt));
    }
    emitConstructorPrimaryCollectionSingletons(sinfo, tkey, args, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRConstructorPrimaryCollectionSingletons(sinfo, tkey, args, trgt));
    }
    emitConstructorPrimaryCollectionCopies(sinfo, tkey, args, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRConstructorPrimaryCollectionCopies(sinfo, tkey, args, trgt));
    }
    emitConstructorPrimaryCollectionMixed(sinfo, tkey, args, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRConstructorPrimaryCollectionMixed(sinfo, tkey, args, trgt));
    }
    emitConstructorTuple(sinfo, resultTupleType, args, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRConstructorTuple(sinfo, resultTupleType, args, trgt));
    }
    emitConstructorRecord(sinfo, resultRecordType, args, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRConstructorRecord(sinfo, resultRecordType, args, trgt));
    }
    emitConstructorValueList(sinfo, resultEphemeralType, args, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRConstructorEphemeralValueList(sinfo, resultEphemeralType, args, trgt));
    }
    emitLoadTupleIndex(sinfo, resultAccessType, arg, argInferType, idx, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRAccessFromIndex(sinfo, resultAccessType, arg, argInferType, idx, trgt));
    }
    emitProjectTupleIndecies(sinfo, resultProjectType, arg, argInferType, indecies, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRProjectFromIndecies(sinfo, resultProjectType, arg, argInferType, indecies, trgt));
    }
    emitLoadProperty(sinfo, resultAccessType, arg, argInferType, pname, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRAccessFromProperty(sinfo, resultAccessType, arg, argInferType, pname, trgt));
    }
    emitLoadField(sinfo, resultAccessType, arg, argInferType, fname, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRAccessFromField(sinfo, resultAccessType, arg, argInferType, fname, trgt));
    }
    emitProjectProperties(sinfo, resultProjectType, arg, argInferType, properties, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRProjectFromProperties(sinfo, resultProjectType, arg, argInferType, properties, trgt));
    }
    emitProjectFields(sinfo, resultProjectType, arg, argInferType, fields, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRProjectFromFields(sinfo, resultProjectType, arg, argInferType, fields, trgt));
    }
    emitProjectFromTypeTuple(sinfo, resultProjectType, arg, istry, argInferType, ptype, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRProjectFromTypeTuple(sinfo, resultProjectType, arg, istry, argInferType, ptype, trgt));
    }
    emitProjectFromTypeRecord(sinfo, resultProjectType, arg, istry, argInferType, ptype, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRProjectFromTypeRecord(sinfo, resultProjectType, arg, istry, argInferType, ptype, trgt));
    }
    emitProjectFromTypeNominal(sinfo, resultProjectType, arg, istry, argInferType, ptype, cfields, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRProjectFromTypeNominal(sinfo, resultProjectType, arg, istry, argInferType, ptype, cfields, trgt));
    }
    emitModifyWithIndecies(sinfo, resultTupleType, arg, argInferType, updates, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRModifyWithIndecies(sinfo, resultTupleType, arg, argInferType, updates, trgt));
    }
    emitModifyWithProperties(sinfo, resultRecordType, arg, argInferType, updates, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRModifyWithProperties(sinfo, resultRecordType, arg, argInferType, updates, trgt));
    }
    emitModifyWithFields(sinfo, resultNominalType, arg, argInferType, updates, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRModifyWithFields(sinfo, resultNominalType, arg, argInferType, updates, trgt));
    }
    emitStructuredExtendTuple(sinfo, resultTupleType, arg, argInferType, update, updateInferType, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRStructuredExtendTuple(sinfo, resultTupleType, arg, argInferType, update, updateInferType, trgt));
    }
    emitStructuredExtendRecord(sinfo, resultRecordType, arg, argInferType, update, updateInferType, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRStructuredExtendRecord(sinfo, resultRecordType, arg, argInferType, update, updateInferType, trgt));
    }
    emitStructuredExtendObject(sinfo, resultNominalType, arg, argInferType, update, updateInferType, fieldResolves, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRStructuredExtendObject(sinfo, resultNominalType, arg, argInferType, update, updateInferType, fieldResolves, trgt));
    }
    emitLoadFromEpehmeralList(sinfo, arg, argInferType, idx, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRLoadFromEpehmeralList(sinfo, arg, argInferType, idx, trgt));
    }
    emitInvokeFixedFunction(sinfo, ikey, args, retinfo, trgt) {
        if (retinfo[3].length === 0) {
            this.m_currentBlock.push(new mir_ops_1.MIRInvokeFixedFunction(sinfo, retinfo[0].trkey, ikey, args, trgt));
        }
        else {
            const rr = this.generateTmpRegister();
            this.m_currentBlock.push(new mir_ops_1.MIRInvokeFixedFunction(sinfo, retinfo[1].trkey, ikey, args, rr));
            if (retinfo[2] === -1) {
                this.m_currentBlock.push(new mir_ops_1.MIRLoadFromEpehmeralList(sinfo, rr, retinfo[1].trkey, 0, trgt));
            }
            else {
                this.m_currentBlock.push(new mir_ops_1.MIRPackSlice(sinfo, rr, retinfo[0].trkey, trgt));
            }
            for (let i = 0; i < retinfo[3].length; ++i) {
                const tr = this.generateTmpRegister();
                this.m_currentBlock.push(new mir_ops_1.MIRLoadFromEpehmeralList(sinfo, rr, retinfo[3][i][1].trkey, retinfo[2] + i, tr));
                this.m_currentBlock.push(new mir_ops_1.MIRVarStore(sinfo, tr, new mir_ops_1.MIRVariable(retinfo[3][i][0])));
            }
        }
    }
    emitInvokeVirtualTarget(sinfo, vresolve, args, thisInferType, retinfo, trgt) {
        if (retinfo[3].length === 0) {
            this.m_currentBlock.push(new mir_ops_1.MIRInvokeVirtualFunction(sinfo, retinfo[0].trkey, vresolve, args, thisInferType, trgt));
        }
        else {
            const rr = this.generateTmpRegister();
            this.m_currentBlock.push(new mir_ops_1.MIRInvokeVirtualFunction(sinfo, retinfo[1].trkey, vresolve, args, thisInferType, rr));
            if (retinfo[2] === -1) {
                this.m_currentBlock.push(new mir_ops_1.MIRLoadFromEpehmeralList(sinfo, rr, retinfo[1].trkey, 0, trgt));
            }
            else {
                this.m_currentBlock.push(new mir_ops_1.MIRPackSlice(sinfo, rr, retinfo[0].trkey, trgt));
            }
            for (let i = 0; i < retinfo[3].length; ++i) {
                const tr = this.generateTmpRegister();
                this.m_currentBlock.push(new mir_ops_1.MIRLoadFromEpehmeralList(sinfo, rr, retinfo[3][i][1].trkey, retinfo[2] + i, tr));
                this.m_currentBlock.push(new mir_ops_1.MIRVarStore(sinfo, tr, new mir_ops_1.MIRVariable(retinfo[3][i][0])));
            }
        }
    }
    emitPrefixNot(sinfo, op, isstrict, arg, trgt) {
        if (isstrict) {
            this.m_currentBlock.push(new mir_ops_1.MIRPrefixOp(sinfo, op, arg, trgt));
        }
        else {
            const tr = this.generateTmpRegister();
            this.m_currentBlock.push(new mir_ops_1.MIRTruthyConvert(sinfo, arg, tr));
            this.m_currentBlock.push(new mir_ops_1.MIRPrefixOp(sinfo, op, tr, trgt));
        }
    }
    emitPrefixOp(sinfo, op, arg, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRPrefixOp(sinfo, op, arg, trgt));
    }
    emitBinOp(sinfo, lhsInferType, lhs, op, rhsInferType, rhs, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRBinOp(sinfo, lhsInferType, lhs, op, rhsInferType, rhs, trgt));
    }
    emitBinEq(sinfo, lhsInferType, lhs, op, rhsInferType, rhs, trgt, relaxed) {
        this.m_currentBlock.push(new mir_ops_1.MIRBinEq(sinfo, lhsInferType, lhs, op, rhsInferType, rhs, trgt, relaxed));
    }
    emitBinLess(sinfo, lhsInferType, lhs, op, rhsInferType, rhs, trgt, relaxed) {
        this.m_currentBlock.push(new mir_ops_1.MIRBinLess(sinfo, lhsInferType, lhs, rhsInferType, rhs, trgt, relaxed));
    }
    emitBinCmp(sinfo, lhsInferType, lhs, op, rhsInferType, rhs, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRBinCmp(sinfo, lhsInferType, lhs, op, rhsInferType, rhs, trgt));
    }
    emitTypeOf(sinfo, trgt, chktype, srcInferType, src) {
        if (chktype === "NSCore::None") {
            this.m_currentBlock.push(new mir_ops_1.MIRIsTypeOfNone(sinfo, src, trgt));
        }
        else if (chktype === "NSCore::Some") {
            this.m_currentBlock.push(new mir_ops_1.MIRIsTypeOfSome(sinfo, src, trgt));
        }
        else {
            this.m_currentBlock.push(new mir_ops_1.MIRIsTypeOf(sinfo, srcInferType, src, chktype, trgt));
        }
    }
    emitRegAssign(sinfo, src, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRRegAssign(sinfo, src, trgt));
    }
    emitTruthyConversion(sinfo, src, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRTruthyConvert(sinfo, src, trgt));
    }
    localLifetimeStart(sinfo, name, rtkey) {
        this.m_currentBlock.push(new mir_ops_1.MIRVarLifetimeStart(sinfo, name, rtkey));
    }
    emitVarStore(sinfo, src, name) {
        this.m_currentBlock.push(new mir_ops_1.MIRVarStore(sinfo, src, new mir_ops_1.MIRVariable(name)));
    }
    emitArgVarStore(sinfo, src, name) {
        this.m_currentBlock.push(new mir_ops_1.MIRVarStore(sinfo, new mir_ops_1.MIRVariable(src), new mir_ops_1.MIRVariable(name)));
    }
    emitVarMove(sinfo, src, name) {
        this.m_currentBlock.push(new mir_ops_1.MIRVarStore(sinfo, new mir_ops_1.MIRVariable(src), new mir_ops_1.MIRVariable(name)));
    }
    emitMIRPackExtend(sinfo, basepack, ext, sltype, trgt) {
        this.m_currentBlock.push(new mir_ops_1.MIRPackExtend(sinfo, basepack, ext, sltype, trgt));
    }
    localLifetimeEnd(sinfo, name) {
        this.m_currentBlock.push(new mir_ops_1.MIRVarLifetimeEnd(sinfo, name));
    }
    emitReturnAssign(sinfo, src) {
        this.m_currentBlock.push(new mir_ops_1.MIRReturnAssign(sinfo, src));
    }
    emitAbort(sinfo, info) {
        this.m_currentBlock.push(new mir_ops_1.MIRAbort(sinfo, info));
    }
    emitDebugBreak(sinfo) {
        this.m_currentBlock.push(new mir_ops_1.MIRDebug(sinfo, undefined));
    }
    emitDebugPrint(sinfo, value) {
        this.m_currentBlock.push(new mir_ops_1.MIRDebug(sinfo, value));
    }
    emitDirectJump(sinfo, blck) {
        this.m_currentBlock.push(new mir_ops_1.MIRJump(sinfo, blck));
    }
    emitBoolJump(sinfo, arg, isstrict, trueblck, falseblck) {
        if (isstrict) {
            this.m_currentBlock.push(new mir_ops_1.MIRJumpCond(sinfo, arg, trueblck, falseblck));
        }
        else {
            const tr = this.generateTmpRegister();
            this.m_currentBlock.push(new mir_ops_1.MIRTruthyConvert(sinfo, arg, tr));
            this.m_currentBlock.push(new mir_ops_1.MIRJumpCond(sinfo, tr, trueblck, falseblck));
        }
    }
    emitNoneJump(sinfo, arg, noneblck, someblk) {
        this.m_currentBlock.push(new mir_ops_1.MIRJumpNone(sinfo, arg, noneblck, someblk));
    }
    getBody(file, sinfo, args) {
        let ibody = new mir_ops_1.MIRBody(file, sinfo, this.m_blockMap);
        mir_cleanup_1.propagateTmpAssignForBody(ibody);
        mir_cleanup_1.removeDeadTempAssignsFromBody(ibody);
        mir_ssa_1.convertBodyToSSA(ibody, args);
        return ibody;
    }
}
exports.MIRBodyEmitter = MIRBodyEmitter;
class MIREmitter {
    constructor(masm) {
        this.bodyEmitter = new MIRBodyEmitter();
        this.pendingOOProcessing = [];
        this.pendingGlobalProcessing = [];
        this.pendingConstProcessing = [];
        this.pendingOOStaticProcessing = [];
        this.pendingOOMethodProcessing = [];
        this.pendingFunctionProcessing = [];
        this.pendingPCodeProcessing = [];
        this.entityInstantiationInfo = [];
        this.allVInvokes = [];
        this.masm = masm;
    }
    initializeBodyEmitter() {
        this.bodyEmitter.initialize();
    }
    getVCallInstantiations(assembly) {
        if (this.allVInvokes.length === 0) {
            return undefined;
        }
        let resvi = new Map();
        for (let i = 0; i < this.allVInvokes.length; ++i) {
            const vinv = this.allVInvokes[i];
            const vcpt = resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedConceptAtomType.create([resolved_type_1.ResolvedConceptAtomTypeEntry.create(vinv[2], vinv[3])]));
            const impls = this.entityInstantiationInfo.filter((iinfo) => {
                if (iinfo[1] instanceof assembly_1.EntityTypeDecl) {
                    const etype = resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedEntityAtomType.create(iinfo[1], iinfo[2]));
                    return assembly.subtypeOf(etype, vcpt);
                }
                else {
                    const cpt = resolved_type_1.ResolvedConceptAtomType.create([resolved_type_1.ResolvedConceptAtomTypeEntry.create(iinfo[1], iinfo[2])]);
                    const ctype = resolved_type_1.ResolvedType.createSingle(cpt);
                    return assembly.subtypeOf(ctype, vcpt);
                }
            });
            for (let j = 0; j < impls.length; ++j) {
                const impl = impls[j];
                const itype = resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedEntityAtomType.create(impl[1], impl[2]));
                const mcreate = assembly.tryGetOOMemberDeclUnique(itype, "method", vinv[4]);
                if (mcreate !== undefined) {
                    const binds = new Map(mcreate.binds);
                    vinv[5].forEach((v, k) => binds.set(k, v));
                    const mkey = MIRKeyGenerator.generateMethodKey(mcreate.contiainingType, mcreate.decl.name, mcreate.binds, vinv[6]);
                    if (!resvi.has(mkey)) {
                        resvi.set(mkey, [vinv[0], mkey, mcreate.contiainingType, mcreate.binds, mcreate.decl, binds, vinv[6], vinv[7]]);
                    }
                }
            }
        }
        let fres = [];
        resvi.forEach((v, k) => fres.push(v));
        return fres;
    }
    registerTypeInstantiation(decl, binds) {
        const key = MIRKeyGenerator.generateTypeKey(decl, binds);
        if (this.masm.conceptDecls.has(key) || this.masm.entityDecls.has(key) || this.pendingOOProcessing.findIndex((oop) => oop[0] === key) !== -1) {
            return;
        }
        this.pendingOOProcessing.push([key, decl, binds]);
        this.entityInstantiationInfo.push([key, decl, binds]);
    }
    registerResolvedTypeReference(t) {
        if (t.options.length > 1) {
            const oopts = t.options.map((opt) => this.registerResolvedTypeReference(resolved_type_1.ResolvedType.createSingle(opt)).options);
            const ft = mir_assembly_1.MIRType.create([].concat(...oopts));
            this.masm.typeMap.set(ft.trkey, ft);
            return ft;
        }
        else {
            const sopt = t.options[0];
            let rt = undefined;
            if (sopt instanceof resolved_type_1.ResolvedEntityAtomType) {
                this.registerTypeInstantiation(sopt.object, sopt.binds);
                rt = mir_assembly_1.MIREntityType.create(MIRKeyGenerator.generateTypeKey(sopt.object, sopt.binds));
            }
            else if (sopt instanceof resolved_type_1.ResolvedConceptAtomType) {
                const natoms = sopt.conceptTypes.map((cpt) => {
                    this.registerTypeInstantiation(cpt.concept, cpt.binds);
                    return MIRKeyGenerator.generateTypeKey(cpt.concept, cpt.binds);
                });
                rt = mir_assembly_1.MIRConceptType.create(natoms);
            }
            else if (sopt instanceof resolved_type_1.ResolvedTupleAtomType) {
                const tatoms = sopt.types.map((entry) => new mir_assembly_1.MIRTupleTypeEntry(this.registerResolvedTypeReference(entry.type), entry.isOptional));
                rt = mir_assembly_1.MIRTupleType.create(tatoms);
            }
            else if (sopt instanceof resolved_type_1.ResolvedRecordAtomType) {
                const tatoms = sopt.entries.map((entry) => new mir_assembly_1.MIRRecordTypeEntry(entry.name, this.registerResolvedTypeReference(entry.type), entry.isOptional));
                rt = mir_assembly_1.MIRRecordType.create(tatoms);
            }
            else {
                const vpatoms = sopt.types.map((tt) => this.registerResolvedTypeReference(tt));
                rt = mir_assembly_1.MIREphemeralListType.create(vpatoms);
            }
            const ft = mir_assembly_1.MIRType.create([rt]);
            this.masm.typeMap.set(ft.trkey, ft);
            return ft;
        }
    }
    registerPendingGlobalProcessing(decl) {
        const key = MIRKeyGenerator.generateGlobalKey(decl.ns, decl.name);
        if (this.masm.constantDecls.has(key) || this.pendingGlobalProcessing.findIndex((gp) => gp[0] === key) !== -1) {
            return key;
        }
        this.pendingGlobalProcessing.push([key, decl]);
        return key;
    }
    registerPendingConstProcessing(containingType, decl, binds) {
        const key = MIRKeyGenerator.generateConstKey(containingType, binds, decl.name);
        if (this.masm.constantDecls.has(key) || this.pendingConstProcessing.findIndex((cp) => cp[0] === key) !== -1) {
            return key;
        }
        this.pendingConstProcessing.push([key, containingType, decl, binds]);
        return key;
    }
    registerFunctionCall(ns, name, f, binds, pcodes, cinfo) {
        const key = MIRKeyGenerator.generateFunctionKey(ns, name, binds, pcodes);
        if (this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingFunctionProcessing.findIndex((fp) => fp[0] === key) !== -1) {
            return key;
        }
        this.pendingFunctionProcessing.push([key, f, binds, pcodes, cinfo]);
        return key;
    }
    registerStaticCall(containingType, cbinds, f, name, binds, pcodes, cinfo) {
        const key = MIRKeyGenerator.generateStaticKey(containingType, name, binds, pcodes);
        if (this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingOOStaticProcessing.findIndex((sp) => sp[0] === key) !== -1) {
            return key;
        }
        this.pendingOOStaticProcessing.push([key, containingType, cbinds, f, binds, pcodes, cinfo]);
        return key;
    }
    registerMethodCall(containingType, m, cbinds, name, binds, pcodes, cinfo) {
        const vkey = MIRKeyGenerator.generateVirtualMethodKey(name, binds);
        const key = MIRKeyGenerator.generateMethodKey(containingType, name, binds, pcodes);
        if (this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingOOMethodProcessing.findIndex((mp) => mp[1] === key) !== -1) {
            return key;
        }
        this.pendingOOMethodProcessing.push([vkey, key, containingType, cbinds, m, binds, pcodes, cinfo]);
        return key;
    }
    registerVirtualMethodCall(containingType, cbinds, name, binds, pcodes, cinfo) {
        const key = MIRKeyGenerator.generateVirtualMethodKey(name, binds);
        const tkey = MIRKeyGenerator.generateTypeKey(containingType, binds);
        if (this.allVInvokes.findIndex((vi) => vi[0] === key && vi[1] === tkey) !== -1) {
            return key;
        }
        this.allVInvokes.push([key, tkey, containingType, cbinds, name, binds, pcodes, cinfo]);
        return key;
    }
    registerPCode(idecl, fsig, binds, cinfo) {
        const key = MIRKeyGenerator.generatePCodeKey(idecl);
        if (this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingPCodeProcessing.findIndex((fp) => fp[0] === key) !== -1) {
            return key;
        }
        this.pendingPCodeProcessing.push([key, idecl, fsig, binds, cinfo]);
        return key;
    }
    closeConceptDecl(cpt) {
        cpt.provides.forEach((tkey) => {
            const ccdecl = this.masm.conceptDecls.get(tkey);
            this.closeConceptDecl(ccdecl);
            ccdecl.fields.forEach((fd) => {
                if (cpt.fields.findIndex((ff) => ff.name === fd.name) === -1) {
                    cpt.fields.push(fd);
                }
            });
            ccdecl.vcallMap.forEach((vcall, vcname) => {
                if (!cpt.vcallMap.has(vcname)) {
                    cpt.vcallMap.set(vcname, vcall);
                }
            });
        });
    }
    closeEntityDecl(entity) {
        entity.provides.forEach((tkey) => {
            const ccdecl = this.masm.conceptDecls.get(tkey);
            this.closeConceptDecl(ccdecl);
            ccdecl.fields.forEach((fd) => {
                if (entity.fields.findIndex((ff) => ff.name === fd.name) === -1) {
                    entity.fields.push(fd);
                }
            });
            ccdecl.vcallMap.forEach((vcall, vcname) => {
                if (!entity.vcallMap.has(vcname)) {
                    entity.vcallMap.set(vcname, vcall);
                }
            });
        });
        entity.fields.sort((f1, f2) => f1.name.localeCompare(f2.name));
    }
    static generateMASM(pckge, buildLevel, validateLiteralStrings, functionalize, srcFiles) {
        ////////////////
        //Parse the contents and generate the assembly
        const assembly = new assembly_1.Assembly();
        let p = new parser_1.Parser(assembly);
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
            return { masm: undefined, errors: parseErrors.map((err) => JSON.stringify(err)) };
        }
        ////////////////
        //Compute the assembly hash and initialize representations
        const hash = Crypto.createHash("sha256");
        const data = [...srcFiles].sort((a, b) => a.relativePath.localeCompare(b.relativePath));
        data.forEach((sf) => {
            hash.update(sf.relativePath);
            hash.update(sf.contents);
        });
        const masm = new mir_assembly_1.MIRAssembly(pckge, srcFiles, hash.digest("hex"));
        const emitter = new MIREmitter(masm);
        const checker = new type_checker_1.TypeChecker(assembly, true, emitter, buildLevel, validateLiteralStrings);
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Any"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialAnyConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Some"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialSomeConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Convertable"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialConvertableConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Parsable"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialParsableConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Validator"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialValidatorConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::KeyType"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialKeyTypeConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::PODType"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialPODTypeConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::APIType"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialAPITypeConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::APIValue"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialAPIValueConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Truthy"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialTruthyConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Enum"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialEnumConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::IdKey"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialIdKeyConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Tuple"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialTupleConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Record"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialRecordConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Object"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialObjectConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::None"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialNoneType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Bool"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialBoolType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Int"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialIntType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::BigInt"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialBigIntType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Float64"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialFloat64Type());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::String"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialStringType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::BufferFormat"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialBufferFormatType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::BufferEncoding"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialBufferEncodingType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::BufferCompression"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialBufferCompressionType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::ByteBuffer"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialByteBufferType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::ISOTime"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialISOTimeType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::UUID"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialUUIDType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::LogicalTime"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialLogicalTimeType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::CryptoHash"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialCryptoHashType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Regex"), new Map());
        emitter.registerResolvedTypeReference(assembly.getSpecialRegexType());
        //get any entrypoint functions and initialize the checker there
        const nslist = assembly.getNamespaces();
        nslist.forEach((nsentry) => {
            nsentry.functions.forEach((f) => {
                if (f.attributes.indexOf("entrypoint") !== -1) {
                    emitter.registerFunctionCall(f.ns, f.name, f, new Map(), [], []);
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
                        const tt = emitter.pendingOOProcessing.pop();
                        checker.processOOType(...tt);
                    }
                    while (emitter.pendingGlobalProcessing.length !== 0 || emitter.pendingConstProcessing.length !== 0) {
                        if (emitter.pendingGlobalProcessing.length !== 0) {
                            const pg = emitter.pendingGlobalProcessing.pop();
                            checker.processGlobal(...pg);
                        }
                        if (emitter.pendingConstProcessing.length !== 0) {
                            const pc = emitter.pendingConstProcessing.pop();
                            checker.processConst(...pc);
                        }
                    }
                    if (emitter.pendingFunctionProcessing.length !== 0) {
                        const pf = emitter.pendingFunctionProcessing.pop();
                        checker.processNamespaceFunction(...pf);
                    }
                    else if (emitter.pendingPCodeProcessing.length !== 0) {
                        const lf = emitter.pendingPCodeProcessing.pop();
                        checker.processLambdaFunction(...lf);
                    }
                    else if (emitter.pendingOOStaticProcessing.length !== 0) {
                        const sf = emitter.pendingOOStaticProcessing.pop();
                        checker.processStaticFunction(...sf);
                    }
                    else if (emitter.pendingOOMethodProcessing.length !== 0) {
                        const mf = emitter.pendingOOMethodProcessing.pop();
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
                    const args = new Map();
                    idecl.params.forEach((param) => args.set(param.name, masm.typeMap.get(param.type)));
                    mir_vartype_1.computeVarTypesForInvoke(idecl.body, args, masm.typeMap.get(idecl.resultType), masm);
                });
                if (functionalize) {
                    functionalize_1.functionalizeInvokes(masm);
                }
            }
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
exports.MIREmitter = MIREmitter;
//# sourceMappingURL=mir_emitter.js.map