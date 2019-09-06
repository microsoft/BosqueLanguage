//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { MIROp, MIROpTag, MIRLoadConst, MIRArgument, MIRRegisterArgument, MIRAccessArgVariable, MIRAccessLocalVariable, MIRConstructorTuple, MIRAccessFromIndex, MIRConstantTrue, MIRConstantFalse, MIRConstantNone, MIRConstantInt, MIRConstantString, MIRPrefixOp, MIRConstantArgument, MIRBinOp, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRRegAssign, MIRTruthyConvert, MIRLogicStore, MIRVarStore, MIRReturnAssign, MIRAbort, MIRJumpCond, MIRJumpNone, MIRBinEq, MIRBinCmp, MIRModifyWithIndecies, MIRInvokeFixedFunction, MIRInvokeKey, MIRBasicBlock, MIRPhi, MIRJump, MIRConstructorPrimary, MIRAccessFromField, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionSingletons, extractMirBodyKeyPrefix, extractMirBodyKeyData, MIRNominalTypeKey, MIRConstantKey, MIRFieldKey, MIRBodyKey, MIRAccessConstantValue, MIRConstructorRecord, MIRAccessFromProperty, MIRModifyWithProperties, MIRModifyWithFields, MIRBody, MIRLoadFieldDefaultValue, MIRIsTypeOf } from "../../compiler/mir_ops";
import { MIRType, MIRAssembly, MIRTupleType, MIRTypeOption, MIREntityTypeDecl, MIREntityType, MIRRecordType, MIRInvokeDecl, MIRInvokeBodyDecl, MIRInvokePrimitiveDecl, MIRConstantDecl, MIRFieldDecl } from "../../compiler/mir_assembly";
import { constructCallGraphInfo } from "../../compiler/mir_callg";
import { BuiltinCalls, BuiltinCallEmit, smtsanizite } from "./builtins";
import { MIRKeyGenerator } from "../../compiler/mir_emitter";
import { SourceInfo } from "../../ast/parser";
import { SMTTypeGenerator } from "./typegen";
import { SMTExp, SMTValue, SMTLet, SMTCond, SMTFreeVar } from "./smtexp";

function NOT_IMPLEMENTED<T>(action: string): T {
    throw new Error(`Not Implemented: ${action}`);
}

const smt_header = `
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
`;

const smtlib_code = `
(declare-datatypes ( (ResultCode 0) ) (
    ( (result_error (error_id Int)) (result_bmc (bmc_id Int)) )
))

(declare-datatypes ( (BTerm 0) ) (
    (
      (bsq_term_none) (bsq_term_bool (bsq_term_bool_value Bool)) (bsq_term_int (bsq_term_int_value Int)) (bsq_term_string (bsq_term_string_value String))
      (bsq_term_tuple (bsq_term_tuple_size Int) (bsq_term_tuple_entries (Array Int BTerm)))
      (bsq_term_record (bsq_term_record_size Int) (bsq_term_record_entries (Array String BTerm)))
      (bsq_term_entity (bsq_term_entity_type String) (bsq_term_entity_entries (Array String BTerm)))
      (bsq_term_list (bsq_term_list_type String) (bsq_term_list_size Int) (bsq_term_list_entries (Array Int BTerm)))
    )
))
`;

class SMTLIBGenerator {
    readonly assembly: MIRAssembly;

    readonly typegen: SMTTypeGenerator;

    private cinvokeFile: string | undefined;
    private cinvokeResult: MIRType | undefined = undefined;

    private tmpvarctr = 0;

    readonly errormap: Map<number, [string, SourceInfo]> = new Map<number, [string, SourceInfo]>();

    constructor(assembly: MIRAssembly) {
        this.assembly = assembly;

        this.typegen = new SMTTypeGenerator(assembly);
    }

    registerError(sinfo: SourceInfo): number {
        this.errormap.set(this.errormap.size, [this.cinvokeFile as string, sinfo]);
        return this.errormap.size - 1;
    }

    getArgType(arg: MIRArgument, vtypes: Map<string, MIRType>): MIRType {
        if (arg instanceof MIRRegisterArgument) {
            return vtypes.get(arg.nameID) as MIRType;
        }
        else {
            if (arg instanceof MIRConstantNone) {
                return this.typegen.noneType;
            }
            else if (arg instanceof MIRConstantTrue || arg instanceof MIRConstantFalse) {
                return this.typegen.boolType;
            }
            else if (arg instanceof MIRConstantInt) {
                return this.typegen.intType;
            }
            else {
                return this.typegen.stringType;
            }
        }
    }

    invokenameToSMT2(ivk: MIRInvokeKey): string {
        return smtsanizite(ivk);
    }

    varNameToSMT2Name(varg: string): string {
        return varg;
    }

    varToSMT2Name(varg: MIRRegisterArgument): string {
        return this.varNameToSMT2Name(varg.nameID).replace(/#/g, "@");
    }

    argToSMT2Direct(arg: MIRArgument): SMTExp {
        if (arg instanceof MIRRegisterArgument) {
            return new SMTValue(this.varToSMT2Name(arg));
        }
        else {
            if (arg instanceof MIRConstantNone) {
                return new SMTValue("bsq_term_none");
            }
            else if (arg instanceof MIRConstantTrue) {
                return new SMTValue("true");
            }
            else if (arg instanceof MIRConstantFalse) {
                return new SMTValue("false");
            }
            else if (arg instanceof MIRConstantInt) {
                return new SMTValue(arg.value);
            }
            else {
                return new SMTValue((arg as MIRConstantString).value);
            }
        }
    }

    argToSMT2Coerce(arg: MIRArgument, from: MIRType | MIRTypeOption, into: MIRType | MIRTypeOption): SMTExp {
        if (arg instanceof MIRRegisterArgument) {
            const rval = new SMTValue(this.varToSMT2Name(arg));
            if (this.typegen.isTypeExact(into)) {
                return this.coerceUnBoxIfNeeded(rval, from, into);
            }
            else {
                return this.coerceBoxIfNeeded(rval, from, into);
            }
        }
        else {
            if (arg instanceof MIRConstantNone) {
                return new SMTValue("bsq_term_none");
            }
            else if (arg instanceof MIRConstantTrue) {
                return new SMTValue(this.typegen.isTypeExact(into) ? "true" : "(bsq_term_bool true)");
            }
            else if (arg instanceof MIRConstantFalse) {
                return new SMTValue(this.typegen.isTypeExact(into) ? "false" : "(bsq_term_bool false)");
            }
            else if (arg instanceof MIRConstantInt) {
                return new SMTValue(this.typegen.isTypeExact(into) ? arg.value : `(bsq_term_int ${arg.value})`);
            }
            else {
                return new SMTValue(this.typegen.isTypeExact(into) ? (arg as MIRConstantString).value : `(bsq_term_string ${(arg as MIRConstantString).value})`);
            }
        }
    }

    coerceBoxIfNeeded(arg: SMTExp, from: MIRType | MIRTypeOption, into: MIRType | MIRTypeOption): SMTExp {
        assert(!this.typegen.isTypeExact(into));

        if (!this.typegen.isTypeExact(from)) {
            return arg;
        }
        else {
            const fromtype = SMTTypeGenerator.getExactTypeFrom(from);
            if (fromtype instanceof MIREntityType) {
                const typedecl = this.assembly.entityDecls.get(fromtype.ekey) as MIREntityTypeDecl;
                if (typedecl.ns === "NSCore") {
                    if (typedecl.name === "None") {
                        return arg;
                    }
                    if (typedecl.name === "Bool") {
                        return new SMTValue(`bsq_term_bool ${arg.emit()}`);
                    }
                    if (typedecl.name === "Int") {
                        return new SMTValue(`(bsq_term_int ${arg.emit()})`);
                    }
                    if (typedecl.name === "String") {
                        return new SMTValue(`(bsq_term_string ${arg.emit()})`);
                    }
                }

                return NOT_IMPLEMENTED<SMTExp>("coerceBoxIfNeeded -- entity");
            }
            else if (fromtype instanceof MIRTupleType) {
                let entriesval = "((as const (Array Int BTerm)) bsq_term_none)";
                for (let i = 0; i < fromtype.entries.length; ++i) {
                    entriesval = `(store ${entriesval} ${i} (${this.typegen.typeToSMT2Constructor(fromtype)}@${i} ${arg}))`;
                }

                return new SMTValue(`(bsq_term_tuple ${fromtype.entries.length} ${entriesval})`);
            }
            else {
                assert(fromtype instanceof MIRRecordType);

                return NOT_IMPLEMENTED<SMTExp>("coerceBoxIfNeeded -- record");
            }
        }
    }

    coerceUnBoxIfNeeded(arg: SMTExp, from: MIRType | MIRTypeOption, into: MIRType | MIRTypeOption): SMTExp {
        assert(this.typegen.isTypeExact(into));

        if (this.typegen.isTypeExact(from)) {
            return arg;
        }
        else {
            const intotype = SMTTypeGenerator.getExactTypeFrom(into);
            if (intotype instanceof MIREntityType) {
                const typedecl = this.assembly.entityDecls.get(intotype.ekey) as MIREntityTypeDecl;
                if (typedecl.ns === "NSCore") {
                    if (typedecl.name === "None") {
                        return arg;
                    }
                    if (typedecl.name === "Bool") {
                        return new SMTValue(`(bsq_term_bool_value ${arg.emit()})`);
                    }
                    if (typedecl.name === "Int") {
                        return new SMTValue(`(bsq_term_int_value ${arg.emit()})`);
                    }
                    if (typedecl.name === "String") {
                        return new SMTValue(`(bsq_term_string_value ${arg.emit()})`);
                    }
                }

                return NOT_IMPLEMENTED<SMTExp>("coerceUnBoxIfNeeded -- entity");
            }
            else if (intotype instanceof MIRTupleType) {
                let entriesval = [];
                for (let i = 0; i < intotype.entries.length; ++i) {
                    entriesval.push(`(select ${arg} ${i})`);
                }

                return new SMTValue(`(${this.typegen.typeToSMT2Constructor(intotype)} ${entriesval.join(" ")})`);
            }
            else {
                assert(intotype instanceof MIRRecordType);

                return NOT_IMPLEMENTED<SMTExp>("coerceUnBoxIfNeeded -- record");
            }
        }
    }

    private generateTruthyConvert(arg: MIRArgument, vtypes: Map<string, MIRType>): SMTExp {
        const argtype = this.getArgType(arg, vtypes);

        if (this.assembly.subtypeOf(argtype, this.typegen.noneType)) {
            return new SMTValue("false");
        }
        else if (this.assembly.subtypeOf(argtype, this.typegen.boolType)) {
            return this.argToSMT2Coerce(arg, argtype, this.typegen.boolType);
        }
        else {
            return new SMTCond(new SMTValue(`(= ${this.argToSMT2Direct(arg).emit()} bsq_term_none)`), new SMTValue("false"), this.argToSMT2Coerce(arg, argtype, this.typegen.boolType));
        }
    }

    private generateMIRAccessConstantValue(cp: MIRAccessConstantValue, vtypes: Map<string, MIRType>): SMTExp {
        const cdecl = this.assembly.constantDecls.get(cp.ckey) as MIRConstantDecl;

        const tv = `@tmpvar@${this.tmpvarctr++}`;
        const crtype = "Result_" + this.typegen.typeToSMT2Type(this.assembly.typeMap.get(cdecl.declaredType) as MIRType);
        const resulttype = "Result_" + this.typegen.typeToSMT2Type(this.cinvokeResult as MIRType);

        const constexp = new SMTValue(this.invokenameToSMT2(cdecl.value.bkey));
        const checkerror = new SMTValue(`(is-${crtype}@result_with_code ${tv})`);
        const extracterror = new SMTValue(`(${resulttype}@result_with_code (${crtype}@result_code_value ${tv}))`);
        const normalassign = new SMTLet(this.varToSMT2Name(cp.trgt), new SMTValue(`(${crtype}@result_value ${tv})`), SMTFreeVar.generate());

        return new SMTLet(tv, constexp, new SMTCond(checkerror, extracterror, normalassign));
    }

    private generateMIRLoadFieldDefaultValue(ld: MIRLoadFieldDefaultValue, vtypes: Map<string, MIRType>): SMTExp {
        const fdecl = this.assembly.fieldDecls.get(ld.fkey) as MIRFieldDecl;

        const tv = `@tmpvar@${this.tmpvarctr++}`;
        const crtype = "Result_" + this.typegen.typeToSMT2Type(this.assembly.typeMap.get(fdecl.declaredType) as MIRType);
        const resulttype = "Result_" + this.typegen.typeToSMT2Type(this.cinvokeResult as MIRType);

        const fdexp = new SMTValue(this.invokenameToSMT2((fdecl.value as MIRBody).bkey));
        const checkerror = new SMTValue(`(is-${crtype}@result_with_code ${tv})`);
        const extracterror = new SMTValue(`(${resulttype}@result_with_code (${crtype}@result_code_value ${tv}))`);
        const normalassign = new SMTLet(this.varToSMT2Name(ld.trgt), new SMTValue(`(${crtype}@result_value ${tv})`), SMTFreeVar.generate());

        return new SMTLet(tv, fdexp, new SMTCond(checkerror, extracterror, normalassign));
    }

    private generateMIRConstructorPrimary(cp: MIRConstructorPrimary, vtypes: Map<string, MIRType>): SMTExp {
        const ctype = this.assembly.entityDecls.get(cp.tkey) as MIREntityTypeDecl;
        const fvals = cp.args.map((arg, i) => {
            const argtype = this.getArgType(arg, vtypes);
            const ftype = this.assembly.typeMap.get(ctype.fields[i].declaredType) as MIRType;
            return this.argToSMT2Coerce(arg, argtype, ftype).emit();
        });

        const smtctype = this.typegen.typeToSMT2Constructor(this.assembly.typeMap.get(cp.tkey) as MIRType);
        const cexp = new SMTValue(`(${smtctype} ${fvals.join(" ")})`);
        const bindexp = new SMTLet(this.varToSMT2Name(cp.trgt), cexp, SMTFreeVar.generate());
        if (ctype.invariants.length === 0) {
            return bindexp;
        }
        else {
            const testexp = new SMTValue(`(${smtctype}@invariant ${this.varToSMT2Name(cp.trgt)})`);
            const resulttype = "Result_" + this.typegen.typeToSMT2Type(this.cinvokeResult as MIRType);
            const errexp = new SMTValue(`(${resulttype}@result_with_code (result_error ${this.registerError(cp.sinfo)}))`);
            return bindexp.bind(new SMTCond(testexp, SMTFreeVar.generate(), errexp));
        }
    }

    private generateMIRConstructorPrimaryCollectionEmpty(cpce: MIRConstructorPrimaryCollectionEmpty, vtypes: Map<string, MIRType>): SMTExp {
        const ctype = this.assembly.entityDecls.get(((this.assembly.typeMap.get(cpce.tkey) as MIRType).options[0] as MIREntityType).ekey) as MIREntityTypeDecl;
        const smtctype = this.typegen.typeToSMT2Constructor(this.assembly.typeMap.get(cpce.tkey) as MIRType);
        if (ctype.name === "List") {
            if (this.typegen.isTypeExact(this.assembly.typeMap.get(cpce.tkey) as MIRType)) {
                return new SMTLet(this.varToSMT2Name(cpce.trgt), new SMTValue(`(${smtctype} 0 ${smtctype}@emptysingleton)`), SMTFreeVar.generate());
            }
            else {
                return new SMTLet(this.varToSMT2Name(cpce.trgt), new SMTValue(`(bsq_term_list "${smtsanizite(cpce.tkey)}" 0 ((as const (Array Int BTerm)) bsq_term_none))`), SMTFreeVar.generate());
            }
        }
        else if (ctype.name === "Set") {
            return NOT_IMPLEMENTED<SMTExp>("generateMIRConstructorPrimaryCollectionEmpty -- Set");
        }
        else {
            return NOT_IMPLEMENTED<SMTExp>("generateMIRConstructorPrimaryCollectionEmpty -- Map");
        }
    }

    private generateMIRConstructorPrimaryCollectionSingletons(cpcs: MIRConstructorPrimaryCollectionSingletons, vtypes: Map<string, MIRType>): SMTExp {
        const ctype = this.assembly.entityDecls.get(((this.assembly.typeMap.get(cpcs.tkey) as MIRType).options[0] as MIREntityType).ekey) as MIREntityTypeDecl;
        if (ctype.name === "List") {
            const contentstype = ctype.terms.get("T") as MIRType;
            if (this.typegen.isTypeExact(this.assembly.typeMap.get(cpcs.tkey) as MIRType)) {
                const smtctype = this.typegen.typeToSMT2Constructor(this.assembly.typeMap.get(cpcs.tkey) as MIRType);
                let entriesval = `${smtctype}@emptysingleton`;
                for (let i = 0; i < cpcs.args.length; ++i) {
                    entriesval = `(store ${entriesval} ${i} ${this.argToSMT2Coerce(cpcs.args[i], this.getArgType(cpcs.args[i], vtypes), contentstype).emit()})`;
                }

                return new SMTLet(this.varToSMT2Name(cpcs.trgt), new SMTValue(`(${smtctype} ${cpcs.args.length} ${entriesval})`), SMTFreeVar.generate());
            }
            else {
                let entriesval = `((as const (Array Int BTerm)) bsq_term_none)`;
                for (let i = cpcs.args.length - 1; i >= 0; --i) {
                    entriesval = `(store ${entriesval} ${i} ${this.argToSMT2Coerce(cpcs.args[i], this.getArgType(cpcs.args[i], vtypes), this.typegen.anyType).emit()})`;
                }

                return new SMTLet(this.varToSMT2Name(cpcs.trgt), new SMTValue(`(bsq_term_list "${smtsanizite(cpcs.tkey)}" ${cpcs.args.length} ${entriesval})`), SMTFreeVar.generate());
            }
        }
        else if (ctype.name === "Set") {
            return NOT_IMPLEMENTED<SMTExp>("generateMIRConstructorPrimaryCollectionSingletons -- Set");
        }
        else {
            return NOT_IMPLEMENTED<SMTExp>("generateMIRConstructorPrimaryCollectionSingletons -- Map");
        }
    }

    private generateMIRConstructorTuple(op: MIRConstructorTuple, vtypes: Map<string, MIRType>): SMTExp {
        const restype = (this.assembly.typeMap.get(op.resultTupleType) as MIRType);
        assert(restype.options.length === 1 && restype.options[0] instanceof MIRTupleType);

        const ttype = restype.options[0] as MIRTupleType;
        const exacttrgt = this.typegen.isTypeExact(ttype);
        let tentries: string[] = [];
        for (let i = 0; i < op.args.length; ++i) {
            const argt = this.getArgType(op.args[i], vtypes);
            const tt = (exacttrgt && i < ttype.entries.length) ? ttype.entries[i].type : this.typegen.anyType;
            tentries.push(this.argToSMT2Coerce(op.args[i], argt, tt).emit());
        }

        if (exacttrgt) {
            return new SMTLet(this.varToSMT2Name(op.trgt), new SMTValue(`(${this.typegen.typeToSMT2Constructor(ttype)} ${tentries.join(" ")})`), SMTFreeVar.generate());
        }
        else {
            let entriesval = "((as const (Array Int BTerm)) bsq_term_none)";
            for (let i = 0; i < tentries.length; ++i) {
                entriesval = `(store ${entriesval} ${i} ${tentries[i]})`;
            }

            return new SMTLet(this.varToSMT2Name(op.trgt), new SMTValue(`(bsq_term_tuple ${op.args.length} ${entriesval})`), SMTFreeVar.generate());
        }
    }

    private generateMIRConstructorRecord(op: MIRConstructorRecord, vtypes: Map<string, MIRType>): SMTExp {
        const restype = (this.assembly.typeMap.get(op.resultRecordType) as MIRType);
        assert(restype.options.length === 1 && restype.options[0] instanceof MIRRecordType);

        const ttype = restype.options[0] as MIRRecordType;
        const exacttrgt = this.typegen.isTypeExact(ttype);
        let tentries: string[] = [];
        for (let i = 0; i < op.args.length; ++i) {
            const argt = this.getArgType(op.args[i][1], vtypes);
            const tt = (exacttrgt && i < ttype.entries.length) ? ttype.entries[i].type : this.typegen.anyType;
            tentries.push(this.argToSMT2Coerce(op.args[i][1], argt, tt).emit());
        }

        if (exacttrgt) {
            return new SMTLet(this.varToSMT2Name(op.trgt), new SMTValue(`(${this.typegen.typeToSMT2Constructor(ttype)} ${tentries.join(" ")})`), SMTFreeVar.generate());
        }
        else {
            let entriesval = "((as const (Array String BTerm)) bsq_term_none)";
            for (let i = 0; i < tentries.length; ++i) {
                entriesval = `(store ${entriesval} "${ttype.entries[i].name}" ${tentries[i]})`;
            }

            return new SMTLet(this.varToSMT2Name(op.trgt), new SMTValue(`(bsq_term_record ${op.args.length} ${entriesval})`), SMTFreeVar.generate());
        }
    }

    generateMIRAccessFromIndex(op: MIRAccessFromIndex, resultAccessType: MIRType, vtypes: Map<string, MIRType>): SMTExp {
        const argtype = this.getArgType(op.arg, vtypes);

        if (this.typegen.isTypeExact(argtype)) {
            const tupinfo = argtype.options[0] as MIRTupleType;

            if (op.idx >= tupinfo.entries.length) {
                return new SMTLet(this.varToSMT2Name(op.trgt), new SMTValue("bsq_term_none"), SMTFreeVar.generate());
            }
            else {
                const fromtype = tupinfo.entries[op.idx].type;
                let access: SMTExp = new SMTValue(`(${this.typegen.typeToSMT2Constructor(argtype)}@${op.idx} ${this.varToSMT2Name(op.arg as MIRRegisterArgument)})`);

                if (this.typegen.isTypeExact(resultAccessType)) {
                    return new SMTLet(this.varToSMT2Name(op.trgt), access, SMTFreeVar.generate());
                }
                else {
                    return new SMTLet(this.varToSMT2Name(op.trgt), this.coerceBoxIfNeeded(access, fromtype, resultAccessType), SMTFreeVar.generate());
                }
            }
        }
        else {
            const access = new SMTValue(`(select (bsq_term_tuple_entries ${this.varToSMT2Name(op.arg as MIRRegisterArgument)}) ${op.idx})`);
            if (!this.typegen.isTypeExact(resultAccessType)) {
                return new SMTLet(this.varToSMT2Name(op.trgt), access, SMTFreeVar.generate());
            }
            else {
                return new SMTLet(this.varToSMT2Name(op.trgt), this.coerceUnBoxIfNeeded(access, this.typegen.anyType, resultAccessType), SMTFreeVar.generate());
            }
        }
    }

    generateMIRAccessFromProperty(op: MIRAccessFromProperty, resultAccessType: MIRType, vtypes: Map<string, MIRType>): SMTExp {
        const argtype = this.getArgType(op.arg, vtypes);

        if (this.typegen.isTypeExact(argtype)) {
            const recinfo = argtype.options[0] as MIRRecordType;

            const pidx = recinfo.entries.findIndex((e) => e.name === op.property);
            if (pidx === -1) {
                return new SMTLet(this.varToSMT2Name(op.trgt), new SMTValue("bsq_term_none"), SMTFreeVar.generate());
            }
            else {
                const fromtype = recinfo.entries[pidx].type;
                let access: SMTExp = new SMTValue(`(${this.typegen.typeToSMT2Constructor(argtype)}@${op.property} ${this.varToSMT2Name(op.arg as MIRRegisterArgument)})`);

                if (this.typegen.isTypeExact(resultAccessType)) {
                    return new SMTLet(this.varToSMT2Name(op.trgt), access, SMTFreeVar.generate());
                }
                else {
                    return new SMTLet(this.varToSMT2Name(op.trgt), this.coerceBoxIfNeeded(access, fromtype, resultAccessType), SMTFreeVar.generate());
                }
            }
        }
        else {
            const access = new SMTValue(`(select (bsq_term_record_entries ${this.varToSMT2Name(op.arg as MIRRegisterArgument)}) "${op.property}")`);
            if (!this.typegen.isTypeExact(resultAccessType)) {
                return new SMTLet(this.varToSMT2Name(op.trgt), access, SMTFreeVar.generate());
            }
            else {
                return new SMTLet(this.varToSMT2Name(op.trgt), this.coerceUnBoxIfNeeded(access, this.typegen.anyType, resultAccessType), SMTFreeVar.generate());
            }
        }
    }

    generateMIRAccessFromField(op: MIRAccessFromField, resultAccessType: MIRType, vtypes: Map<string, MIRType>): SMTExp {
        const argtype = this.getArgType(op.arg, vtypes);

        if (this.typegen.isTypeExact(argtype)) {
            const tpfx = this.typegen.typeToSMT2Constructor(argtype);
            return new SMTLet(this.varToSMT2Name(op.trgt), new SMTValue(`(${tpfx}@${op.field} ${this.varToSMT2Name(op.arg as MIRRegisterArgument)})`), SMTFreeVar.generate());
        }
        else {
            const access = new SMTValue(`(select (bsq_term_entity_entries ${this.varToSMT2Name(op.arg as MIRRegisterArgument)}) "${op.field}")`);
            if (this.typegen.isTypeExact(resultAccessType)) {
                return new SMTLet(this.varToSMT2Name(op.trgt), this.coerceUnBoxIfNeeded(access, this.typegen.anyType, resultAccessType), SMTFreeVar.generate());
            }
            else {
                return new SMTLet(this.varToSMT2Name(op.trgt), access, SMTFreeVar.generate());
            }
        }
    }

    generateMIRModifyWithIndecies(mi: MIRModifyWithIndecies, vtypes: Map<string, MIRType>): SMTExp {
        const argtype = this.getArgType(mi.arg, vtypes);
        const restype = this.assembly.typeMap.get(mi.resultTupleType) as MIRType;

        if (this.typegen.isTypeExact(argtype) && this.typegen.isTypeExact(restype)) {
            const atinfo = argtype.options[0] as MIRTupleType;
            const rtinfo = restype.options[0] as MIRTupleType;

            let vals: string[] = [];
            for (let i = 0; i < rtinfo.entries.length; ++i) {
                const upd = mi.updates.find((up) => up[0] === i);
                if (upd !== undefined) {
                    vals.push(this.argToSMT2Coerce(upd[1], this.getArgType(upd[1], vtypes), rtinfo.entries[i].type).emit());
                }
                else if (i < atinfo.entries.length) {
                    vals.push(`(${this.typegen.typeToSMT2Constructor(argtype)}@${i} ${this.varToSMT2Name(mi.arg as MIRRegisterArgument)})`);
                }
                else {
                    vals.push("bsq_term_none");
                }
            }

            return new SMTLet(this.varToSMT2Name(mi.trgt), new SMTValue(`(${this.typegen.typeToSMT2Constructor(rtinfo)} ${vals.join(" ")})`), SMTFreeVar.generate());
        }
        else {
            return NOT_IMPLEMENTED<SMTExp>("generateMIRModifyWithIndecies -- not type exact case");
        }
    }

    generateMIRModifyWithProperties(mp: MIRModifyWithProperties, vtypes: Map<string, MIRType>): SMTExp {
        const argtype = this.getArgType(mp.arg, vtypes);
        const restype = this.assembly.typeMap.get(mp.resultRecordType) as MIRType;

        if (this.typegen.isTypeExact(argtype) && this.typegen.isTypeExact(restype)) {
            const rrinfo = restype.options[0] as MIRRecordType;

            let vals: string[] = [];
            for (let i = 0; i < rrinfo.entries.length; ++i) {
                const upd = mp.updates.find((up) => up[0] === rrinfo.entries[i].name);
                if (upd !== undefined) {
                    vals.push(this.argToSMT2Coerce(upd[1], this.getArgType(upd[1], vtypes), rrinfo.entries[i].type).emit());
                }
                else {
                    vals.push(`(${this.typegen.typeToSMT2Constructor(argtype)}@${rrinfo.entries[i].name} ${this.varToSMT2Name(mp.arg as MIRRegisterArgument)})`);
                }
            }

            return new SMTLet(this.varToSMT2Name(mp.trgt), new SMTValue(`(${this.typegen.typeToSMT2Constructor(rrinfo)} ${vals.join(" ")})`), SMTFreeVar.generate());
        }
        else {
            return NOT_IMPLEMENTED<SMTExp>("generateMIRModifyWithProperties -- not type exact case");
        }
    }

    generateMIRModifyWithFields(mf: MIRModifyWithFields, vtypes: Map<string, MIRType>): SMTExp {
        const argtype = this.getArgType(mf.arg, vtypes);
        const restype = this.assembly.typeMap.get(mf.resultNominalType) as MIRType;

        if (this.typegen.isTypeExact(argtype) && this.typegen.isTypeExact(restype)) {
            const reinfo = restype.options[0] as MIREntityType;
            const redecl = this.assembly.entityDecls.get(reinfo.ekey) as MIREntityTypeDecl;

            let vals: string[] = [];
            for (let i = 0; i < redecl.fields.length; ++i) {
                const upd = mf.updates.find((up) => up[0] === redecl.fields[i].name);
                if (upd !== undefined) {
                    vals.push(this.argToSMT2Coerce(upd[1], this.getArgType(upd[1], vtypes), this.assembly.typeMap.get(redecl.fields[i].declaredType) as MIRType).emit());
                }
                else {
                    vals.push(`(${this.typegen.typeToSMT2Constructor(argtype)}@${redecl.fields[i].name} ${this.varToSMT2Name(mf.arg as MIRRegisterArgument)})`);
                }
            }

            return new SMTLet(this.varToSMT2Name(mf.trgt), new SMTValue(`(${this.typegen.typeToSMT2Constructor(reinfo)} ${vals.join(" ")})`), SMTFreeVar.generate());

        }
        else {
            return NOT_IMPLEMENTED<SMTExp>("generateMIRModifyWithFields -- not type exact case");
        }
    }

    generateMIRInvokeFixedFunction(ivop: MIRInvokeFixedFunction, vtypes: Map<string, MIRType>): SMTExp {
        let vals: string[] = [];
        const idecl = (this.assembly.invokeDecls.get(ivop.mkey) || this.assembly.primitiveInvokeDecls.get(ivop.mkey)) as MIRInvokeDecl;

        for (let i = 0; i < ivop.args.length; ++i) {
            vals.push(this.argToSMT2Coerce(ivop.args[i], this.getArgType(ivop.args[i], vtypes), this.assembly.typeMap.get(idecl.params[i].type) as MIRType).emit());
        }

        const tv = `@tmpvar@${this.tmpvarctr++}`;
        const ivrtype = "Result_" + this.typegen.typeToSMT2Type(this.assembly.typeMap.get((idecl as MIRInvokeDecl).resultType) as MIRType);
        const resulttype = "Result_" + this.typegen.typeToSMT2Type(this.cinvokeResult as MIRType);

        const invokeexp = new SMTValue( vals.length !== 0 ? `(${this.invokenameToSMT2(ivop.mkey)} ${vals.join(" ")})` : this.invokenameToSMT2(ivop.mkey));
        const checkerror = new SMTValue(`(is-${ivrtype}@result_with_code ${tv})`);
        const extracterror = new SMTValue(`(${resulttype}@result_with_code (${ivrtype}@result_code_value ${tv}))`);
        const normalassign = new SMTLet(this.varToSMT2Name(ivop.trgt), new SMTValue(`(${ivrtype}@result_value ${tv})`), SMTFreeVar.generate());

        return new SMTLet(tv, invokeexp, new SMTCond(checkerror, extracterror, normalassign));
    }

    generateSMTScope(op: MIROp, vtypes: Map<string, MIRType>, fromblck: string): SMTExp | undefined {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = (op as MIRLoadConst);
                vtypes.set(lcv.trgt.nameID, this.getArgType(lcv.src, vtypes));
                return new SMTLet(this.varToSMT2Name(lcv.trgt), this.argToSMT2Direct(lcv.src), SMTFreeVar.generate());
            }
            case MIROpTag.MIRLoadConstTypedString:  {
                return NOT_IMPLEMENTED<SMTExp>("MIRLoadConstTypedString");
            }
            case MIROpTag.MIRAccessConstantValue: {
                const acv = (op as MIRAccessConstantValue);
                vtypes.set(acv.trgt.nameID, this.assembly.typeMap.get((this.assembly.constantDecls.get(acv.ckey) as MIRConstantDecl).declaredType) as MIRType);
                return this.generateMIRAccessConstantValue(acv, vtypes);
            }
            case MIROpTag.MIRLoadFieldDefaultValue: {
                const ldv = (op as MIRLoadFieldDefaultValue);
                vtypes.set(ldv.trgt.nameID, this.assembly.typeMap.get((this.assembly.fieldDecls.get(ldv.fkey) as MIRFieldDecl).declaredType) as MIRType);
                return this.generateMIRLoadFieldDefaultValue(ldv, vtypes);
            }
            case MIROpTag.MIRAccessArgVariable: {
                const lav = (op as MIRAccessArgVariable);
                vtypes.set(lav.trgt.nameID, this.getArgType(lav.name, vtypes));
                return new SMTLet(this.varToSMT2Name(lav.trgt), this.argToSMT2Direct(lav.name), SMTFreeVar.generate());
            }
            case MIROpTag.MIRAccessLocalVariable: {
                const llv = (op as MIRAccessLocalVariable);
                vtypes.set(llv.trgt.nameID, this.getArgType(llv.name, vtypes));
                return new SMTLet(this.varToSMT2Name(llv.trgt), this.argToSMT2Direct(llv.name), SMTFreeVar.generate());
            }
            case MIROpTag.MIRConstructorPrimary: {
                const cp = op as MIRConstructorPrimary;
                vtypes.set(cp.trgt.nameID, this.assembly.typeMap.get(cp.tkey) as MIRType);
                return this.generateMIRConstructorPrimary(cp, vtypes);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
                const cpce = op as MIRConstructorPrimaryCollectionEmpty;
                vtypes.set(cpce.trgt.nameID, this.assembly.typeMap.get(cpce.tkey) as MIRType);
                return this.generateMIRConstructorPrimaryCollectionEmpty(cpce, vtypes);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                const cpcs = op as MIRConstructorPrimaryCollectionSingletons;
                vtypes.set(cpcs.trgt.nameID, this.assembly.typeMap.get(cpcs.tkey) as MIRType);
                return this.generateMIRConstructorPrimaryCollectionSingletons(cpcs, vtypes);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
                return NOT_IMPLEMENTED<SMTExp>("MIRConstructorPrimaryCollectionCopies");
            }
            case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                return NOT_IMPLEMENTED<SMTExp>("MIRConstructorPrimaryCollectionMixed");
            }
            case MIROpTag.MIRConstructorTuple: {
                const tc = op as MIRConstructorTuple;
                vtypes.set(tc.trgt.nameID, this.assembly.typeMap.get(tc.resultTupleType) as MIRType);
                return this.generateMIRConstructorTuple(tc, vtypes);
            }
            case MIROpTag.MIRConstructorRecord: {
                const tr = op as MIRConstructorRecord;
                vtypes.set(tr.trgt.nameID, this.assembly.typeMap.get(tr.resultRecordType) as MIRType);
                return this.generateMIRConstructorRecord(tr, vtypes);
            }
            case MIROpTag.MIRAccessFromIndex: {
                const ai = op as MIRAccessFromIndex;
                vtypes.set(ai.trgt.nameID, this.assembly.typeMap.get(ai.resultAccessType) as MIRType);
                return this.generateMIRAccessFromIndex(ai, this.assembly.typeMap.get(ai.resultAccessType) as MIRType, vtypes);
            }
            case MIROpTag.MIRProjectFromIndecies: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromIndecies");
            }
            case MIROpTag.MIRAccessFromProperty: {
                const ap = op as MIRAccessFromProperty;
                vtypes.set(ap.trgt.nameID, this.assembly.typeMap.get(ap.resultAccessType) as MIRType);
                return this.generateMIRAccessFromProperty(ap, this.assembly.typeMap.get(ap.resultAccessType) as MIRType, vtypes);
            }
            case MIROpTag.MIRProjectFromProperties: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromProperties");
            }
            case MIROpTag.MIRAccessFromField: {
                const af = op as MIRAccessFromField;
                vtypes.set(af.trgt.nameID, this.assembly.typeMap.get(af.resultAccessType) as MIRType);
                return this.generateMIRAccessFromField(af, this.assembly.typeMap.get(af.resultAccessType) as MIRType, vtypes);
            }
            case MIROpTag.MIRProjectFromFields: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromFields");
            }
            case MIROpTag.MIRProjectFromTypeTuple: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromTypeTuple");
            }
            case MIROpTag.MIRProjectFromTypeRecord: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromTypeRecord");
            }
            case MIROpTag.MIRProjectFromTypeConcept: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromTypeConcept");
            }
            case MIROpTag.MIRModifyWithIndecies: {
                const mi = op as MIRModifyWithIndecies;
                vtypes.set(mi.trgt.nameID, this.assembly.typeMap.get(mi.resultTupleType) as MIRType);
                return this.generateMIRModifyWithIndecies(mi, vtypes);
            }
            case MIROpTag.MIRModifyWithProperties: {
                const mp = op as MIRModifyWithProperties;
                vtypes.set(mp.trgt.nameID, this.assembly.typeMap.get(mp.resultRecordType) as MIRType);
                return this.generateMIRModifyWithProperties(mp, vtypes);
            }
            case MIROpTag.MIRModifyWithFields: {
                const mf = op as MIRModifyWithFields;
                vtypes.set(mf.trgt.nameID, this.assembly.typeMap.get(mf.resultNominalType) as MIRType);
                return this.generateMIRModifyWithFields(mf, vtypes);
            }
            case MIROpTag.MIRStructuredExtendTuple: {
                return NOT_IMPLEMENTED<SMTExp>("MIRStructuredExtendTuple");
            }
            case MIROpTag.MIRStructuredExtendRecord: {
                return NOT_IMPLEMENTED<SMTExp>("MIRStructuredExtendRecord");
            }
            case MIROpTag.MIRStructuredExtendObject: {
                return NOT_IMPLEMENTED<SMTExp>("MIRStructuredExtendObject");
            }
            case MIROpTag.MIRInvokeFixedFunction: {
                const invk = op as MIRInvokeFixedFunction;
                vtypes.set(invk.trgt.nameID, this.assembly.typeMap.get(((this.assembly.invokeDecls.get(invk.mkey) || this.assembly.primitiveInvokeDecls.get(invk.mkey)) as MIRInvokeDecl).resultType) as MIRType);
                return this.generateMIRInvokeFixedFunction(invk, vtypes);
            }
            case MIROpTag.MIRInvokeVirtualTarget: {
                return NOT_IMPLEMENTED<SMTExp>("MIRInvokeVirtualTarget");
            }
            case MIROpTag.MIRPrefixOp: {
                const pfx = op as MIRPrefixOp;
                const argtype = this.getArgType(pfx.arg, vtypes);
                if (pfx.op === "!") {
                    vtypes.set(pfx.trgt.nameID, this.typegen.boolType);

                    const smttest = this.generateTruthyConvert(pfx.arg, vtypes);
                    return new SMTLet(this.varToSMT2Name(pfx.trgt), new SMTValue(`(not ${smttest.emit()})`), SMTFreeVar.generate());
                }
                else {
                    vtypes.set(pfx.trgt.nameID, this.typegen.intType);

                    if (pfx.op === "-") {
                        return new SMTLet(this.varToSMT2Name(pfx.trgt), new SMTValue(`(* ${this.argToSMT2Coerce(pfx.arg, argtype, this.typegen.intType).emit()} -1)`), SMTFreeVar.generate());
                    }
                    else {
                        return new SMTLet(this.varToSMT2Name(pfx.trgt), this.argToSMT2Coerce(pfx.arg, argtype, this.typegen.intType), SMTFreeVar.generate());
                    }
                }
            }
            case MIROpTag.MIRBinOp: {
                const bop = op as MIRBinOp;
                vtypes.set(bop.trgt.nameID, this.typegen.intType);

                const lhvtype = this.getArgType(bop.lhs, vtypes);
                const lhv = this.argToSMT2Coerce(bop.lhs, lhvtype, this.typegen.intType).emit();

                const rhvtype = this.getArgType(bop.rhs, vtypes);
                const rhv = this.argToSMT2Coerce(bop.rhs, rhvtype, this.typegen.intType).emit();

                switch (bop.op) {
                    case "+":
                        return new SMTLet(this.varToSMT2Name(bop.trgt), new SMTValue(`(+ ${lhv} ${rhv})`), SMTFreeVar.generate());
                    case "-":
                        return new SMTLet(this.varToSMT2Name(bop.trgt), new SMTValue(`(- ${lhv} ${rhv})`), SMTFreeVar.generate());
                    case "*": {
                        if (bop.lhs instanceof MIRConstantArgument || bop.rhs instanceof MIRConstantArgument) {
                            return new SMTLet(this.varToSMT2Name(bop.trgt), new SMTValue(`(* ${lhv} ${rhv})`), SMTFreeVar.generate());
                        }
                        else {
                            return NOT_IMPLEMENTED<SMTExp>("BINOP -- nonlinear *");
                        }
                    }
                    case "/":
                            return NOT_IMPLEMENTED<SMTExp>("BINOP -- nonlinear /");
                    default:
                            return NOT_IMPLEMENTED<SMTExp>("BINOP -- nonlinear %");
                }
            }
            case MIROpTag.MIRBinEq: {
                const beq = op as MIRBinEq;
                vtypes.set(beq.trgt.nameID, this.typegen.boolType);

                const lhvtype = this.getArgType(beq.lhs, vtypes);
                const rhvtype = this.getArgType(beq.rhs, vtypes);
                if (this.typegen.isTypeExact(lhvtype) && this.typegen.isTypeExact(rhvtype)) {
                    if ((lhvtype.trkey === "NSCore::None" && rhvtype.trkey === "NSCore::None")
                        || (lhvtype.trkey === "NSCore::Bool" && rhvtype.trkey === "NSCore::Bool")
                        || (lhvtype.trkey === "NSCore::Int" && rhvtype.trkey === "NSCore::Int")
                        || (lhvtype.trkey === "NSCore::String" && rhvtype.trkey === "NSCore::String")) {
                            const smv = `(= ${this.argToSMT2Coerce(beq.lhs, lhvtype, lhvtype).emit()} ${this.argToSMT2Coerce(beq.rhs, rhvtype, rhvtype).emit()})`;
                            return new SMTLet(this.varToSMT2Name(beq.trgt), new SMTValue(beq.op === "!=" ? `(not ${smv})` : smv), SMTFreeVar.generate());
                    }
                    else {
                        return NOT_IMPLEMENTED<SMTExp>("BINEQ -- nonprimitive values");
                    }
                }
                else {
                    const larg = this.argToSMT2Coerce(beq.lhs, lhvtype, this.typegen.anyType).emit();
                    const rarg = this.argToSMT2Coerce(beq.rhs, rhvtype, this.typegen.anyType).emit();

                    let tops: SMTExp[] = [];
                    if (this.assembly.subtypeOf(this.typegen.noneType, lhvtype) && this.assembly.subtypeOf(this.typegen.noneType, lhvtype)) {
                        tops.push(new SMTCond(new SMTValue(`(and (= ${larg} bsq_term_none) (= ${rarg} bsq_term_none))`), new SMTValue("true"), SMTFreeVar.generate()));
                    }

                    if (this.assembly.subtypeOf(this.typegen.boolType, lhvtype) && this.assembly.subtypeOf(this.typegen.boolType, lhvtype)) {
                        tops.push(new SMTCond(new SMTValue(`(and (is-bsq_term_bool ${larg}) (is-bsq_term_bool ${rarg}) (= (bsq_term_bool_value ${larg}) (bsq_term_bool_value ${rarg})))`), new SMTValue("true"), SMTFreeVar.generate()));
                    }

                    if (this.assembly.subtypeOf(this.typegen.intType, lhvtype) && this.assembly.subtypeOf(this.typegen.intType, lhvtype)) {
                        tops.push(new SMTCond(new SMTValue(`(and (is-bsq_term_int ${larg}) (is-bsq_term_int ${rarg}) (= (bsq_term_int_value ${larg}) (bsq_term_int_value ${rarg})))`), new SMTValue("true"), SMTFreeVar.generate()));
                    }

                    if (this.assembly.subtypeOf(this.typegen.stringType, lhvtype) && this.assembly.subtypeOf(this.typegen.stringType, lhvtype)) {
                        tops.push(new SMTCond(new SMTValue(`(and (is-bsq_term_string ${larg}) (is-bsq_term_string ${rarg}) (= (bsq_term_string_value ${larg}) (bsq_term_string_value ${rarg})))`), new SMTValue("true"), SMTFreeVar.generate()));
                    }

                    //
                    //TODO: handle the other types here
                    //

                    let rexp: SMTExp = new SMTValue("false");
                    for (let i = tops.length - 1; i >= 0; --i) {
                        rexp = tops[i].bind(rexp);
                    }

                    return new SMTLet(this.varToSMT2Name(beq.trgt), new SMTValue(beq.op === "!=" ? `(not ${rexp.emit()})` : rexp.emit()), SMTFreeVar.generate());
                }
            }
            case MIROpTag.MIRBinCmp: {
                const bcmp = op as MIRBinCmp;
                vtypes.set(bcmp.trgt.nameID, this.typegen.boolType);

                const lhvtype = this.getArgType(bcmp.lhs, vtypes);
                const rhvtype = this.getArgType(bcmp.rhs, vtypes);

                if (this.typegen.isTypeExact(lhvtype) && this.typegen.isTypeExact(rhvtype)) {
                    if (lhvtype.trkey === "NSCore::Int" && rhvtype.trkey === "NSCore::Int") {
                        return new SMTLet(this.varToSMT2Name(bcmp.trgt), new SMTValue(`(${bcmp.op} ${this.argToSMT2Coerce(bcmp.lhs, lhvtype, lhvtype).emit()} ${this.argToSMT2Coerce(bcmp.rhs, rhvtype, rhvtype).emit()})`), SMTFreeVar.generate());
                    }
                    else {
                        return NOT_IMPLEMENTED<SMTExp>("BINCMP -- string");
                    }
                }
                else {
                    const trgttype = (this.assembly.subtypeOf(this.typegen.intType, lhvtype) && this.assembly.subtypeOf(this.typegen.intType, rhvtype)) ? this.typegen.intType : this.typegen.stringType;

                    const tvl = `@tmpl@${this.tmpvarctr++}`;
                    const tvr = `@tmpr@${this.tmpvarctr++}`;

                    const lets = new SMTLet(tvl, this.typegen.isTypeExact(lhvtype) ? this.argToSMT2Direct(bcmp.lhs) : this.argToSMT2Coerce(bcmp.lhs, lhvtype, trgttype), new SMTLet(tvr, this.typegen.isTypeExact(rhvtype) ? this.argToSMT2Direct(bcmp.rhs) : this.argToSMT2Coerce(bcmp.rhs, rhvtype, trgttype), SMTFreeVar.generate()));
                    if (trgttype.trkey === "NSCore::Int") {
                        return lets.bind(new SMTLet(this.varToSMT2Name(bcmp.trgt), new SMTValue(`(${bcmp.op} ${tvl} ${tvr})`), SMTFreeVar.generate()));
                    }
                    else {
                        return NOT_IMPLEMENTED<SMTExp>("BINCMP -- string");
                    }
                }
            }
            case MIROpTag.MIRIsTypeOfNone: {
                const ton = op as MIRIsTypeOfNone;
                vtypes.set(ton.trgt.nameID, this.typegen.boolType);

                const argtype = this.getArgType(ton.arg, vtypes);
                if (this.typegen.isTypeExact(argtype)) {
                    return new SMTLet(this.varToSMT2Name(ton.trgt), new SMTValue(this.assembly.subtypeOf(argtype, this.typegen.noneType) ? "true" : "false"), SMTFreeVar.generate());
                }
                else {
                    return new SMTLet(this.varToSMT2Name(ton.trgt), new SMTValue(`(= ${this.argToSMT2Direct(ton.arg).emit()} bsq_term_none)`), SMTFreeVar.generate());
                }
            }
            case MIROpTag.MIRIsTypeOfSome: {
                const tos = op as MIRIsTypeOfSome;
                vtypes.set(tos.trgt.nameID, this.assembly.typeMap.get("NSCore::Bool") as MIRType);

                const argtype = this.getArgType(tos.arg, vtypes);
                if (this.typegen.isTypeExact(argtype)) {
                    return new SMTLet(this.varToSMT2Name(tos.trgt), new SMTValue(this.assembly.subtypeOf(argtype, this.typegen.noneType) ? "false" : "true"), SMTFreeVar.generate());
                }
                else {
                    return new SMTLet(this.varToSMT2Name(tos.trgt), new SMTValue(`(not (= ${this.argToSMT2Direct(tos.arg).emit()} bsq_term_none))`), SMTFreeVar.generate());
                }
            }
            case MIROpTag.MIRIsTypeOf: {
                const tof = op as MIRIsTypeOf;
                vtypes.set(tof.trgt.nameID, this.assembly.typeMap.get("NSCore::Bool") as MIRType);

                const argtype = this.getArgType(tof.arg, vtypes);
                const oftype = this.assembly.typeMap.get(tof.oftype) as MIRType;
                if (this.typegen.isTypeExact(argtype)) {
                    return new SMTLet(this.varToSMT2Name(tof.trgt), new SMTValue(this.assembly.subtypeOf(argtype, oftype) ? "false" : "true"), SMTFreeVar.generate());
                }
                else {
                    const tcheck = this.typegen.generateTypeOfCall(this.argToSMT2Direct(tof.arg).emit(), argtype, oftype);
                    return new SMTLet(this.varToSMT2Name(tof.trgt), new SMTValue(tcheck), SMTFreeVar.generate());
                }
            }
            case MIROpTag.MIRRegAssign: {
                const regop = op as MIRRegAssign;
                vtypes.set(regop.trgt.nameID, this.getArgType(regop.src, vtypes));

                return new SMTLet(this.varToSMT2Name(regop.trgt), this.argToSMT2Direct(regop.src), SMTFreeVar.generate());
            }
            case MIROpTag.MIRTruthyConvert: {
                const tcop = op as MIRTruthyConvert;
                vtypes.set(tcop.trgt.nameID, this.typegen.boolType);

                const smttest = this.generateTruthyConvert(tcop.src, vtypes);
                return new SMTLet(this.varToSMT2Name(tcop.trgt), smttest, SMTFreeVar.generate());
            }
            case MIROpTag.MIRLogicStore: {
                const llop = op as MIRLogicStore;
                vtypes.set(llop.trgt.nameID, this.typegen.boolType);

                const lhvtype = this.getArgType(llop.lhs, vtypes);
                const lhv = this.argToSMT2Coerce(llop.lhs, lhvtype, this.typegen.boolType).emit();

                const rhvtype = this.getArgType(llop.rhs, vtypes);
                const rhv = this.argToSMT2Coerce(llop.rhs, rhvtype, this.typegen.boolType).emit();

                if (llop.op === "&") {
                    return new SMTLet(this.varToSMT2Name(llop.trgt), new SMTValue(`(and ${lhv} ${rhv})`), SMTFreeVar.generate());
                }
                else {
                    return new SMTLet(this.varToSMT2Name(llop.trgt), new SMTValue(`(or ${lhv} ${rhv})`), SMTFreeVar.generate());
                }
            }
            case MIROpTag.MIRVarStore: {
                const vsop = op as MIRVarStore;
                vtypes.set(vsop.name.nameID, this.getArgType(vsop.src, vtypes));

                return new SMTLet(this.varToSMT2Name(vsop.name), this.argToSMT2Direct(vsop.src), SMTFreeVar.generate());
            }
            case MIROpTag.MIRReturnAssign: {
                const raop = op as MIRReturnAssign;
                vtypes.set(raop.name.nameID, this.cinvokeResult as MIRType);

                const totype = vtypes.get(raop.name.nameID) as MIRType;
                const fromtype = this.getArgType(raop.src, vtypes);
                return new SMTLet(this.varToSMT2Name(raop.name), this.argToSMT2Coerce(raop.src, fromtype, totype), SMTFreeVar.generate());
            }
            case MIROpTag.MIRAbort: {
                const aop = op as MIRAbort;
                const resulttype = "Result_" + this.typegen.typeToSMT2Type(this.cinvokeResult as MIRType);
                return new SMTValue(`(${resulttype}@result_with_code (result_error ${this.registerError(aop.sinfo)}))`);
            }
            case MIROpTag.MIRDebug: {
                return undefined;
            }
            case MIROpTag.MIRJump: {
                return undefined;
            }
            case MIROpTag.MIRJumpCond: {
                const cjop = op as MIRJumpCond;
                const smttest = this.generateTruthyConvert(cjop.arg, vtypes);
                return new SMTCond(smttest, SMTFreeVar.generate("#true_trgt#"), SMTFreeVar.generate("#false_trgt#"));
            }
            case MIROpTag.MIRJumpNone: {
                const njop = op as MIRJumpNone;
                const argtype = this.getArgType(njop.arg, vtypes);
                if (this.typegen.isTypeExact(argtype)) {
                    return new SMTCond(new SMTValue(this.assembly.subtypeOf(argtype, this.typegen.noneType) ? "true" : "false"), SMTFreeVar.generate("#true_trgt#"), SMTFreeVar.generate("#false_trgt#"));
                }
                else {
                    return new SMTCond(new SMTValue(`(= ${this.argToSMT2Direct(njop.arg).emit()} bsq_term_none)`), SMTFreeVar.generate("#true_trgt#"), SMTFreeVar.generate("#false_trgt#"));
                }
            }
            case MIROpTag.MIRPhi: {
                const pop = op as MIRPhi;
                const uvar = pop.src.get(fromblck) as MIRRegisterArgument;
                vtypes.set(pop.trgt.nameID, this.getArgType(uvar, vtypes));

                return new SMTLet(this.varToSMT2Name(pop.trgt), this.argToSMT2Direct(uvar), SMTFreeVar.generate());
            }
            case MIROpTag.MIRVarLifetimeStart:
            case MIROpTag.MIRVarLifetimeEnd: {
                return undefined;
            }
            default:
                assert(false);
                return undefined;
        }
    }

    private generateSMTBlockExps(block: MIRBasicBlock, fromblock: string, blocks: Map<string, MIRBasicBlock>, vtypes: Map<string, MIRType>): SMTExp {
        const exps: SMTExp[] = [];
        for (let i = 0; i < block.ops.length; ++i) {
            const exp = this.generateSMTScope(block.ops[i], vtypes, fromblock);
            if (exp !== undefined) {
                exps.push(exp);
            }
        }

        if (block.label === "exit") {
            const resulttype = "Result_" + this.typegen.typeToSMT2Type(this.cinvokeResult as MIRType);
            let rexp = new SMTValue(`(${resulttype}@result_success _return_)`) as SMTExp;
            for (let i = exps.length - 1; i >= 0; --i) {
                rexp = exps[i].bind(rexp, "#body#");
            }

            return rexp;
        }
        else {
            const jop = block.ops[block.ops.length - 1];
            if (jop.tag === MIROpTag.MIRJump) {
                let rexp = this.generateSMTBlockExps(blocks.get((jop as MIRJump).trgtblock) as MIRBasicBlock, block.label, blocks, vtypes);
                for (let i = exps.length - 1; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }

                return rexp;
            }
            else {
                assert(jop.tag === MIROpTag.MIRJumpCond || jop.tag === MIROpTag.MIRJumpNone);

                let tblock = ((jop.tag === MIROpTag.MIRJumpCond) ? blocks.get((jop as MIRJumpCond).trueblock) : blocks.get((jop as MIRJumpNone).noneblock)) as MIRBasicBlock;
                let texp = this.generateSMTBlockExps(tblock, block.label, blocks, new Map<string, MIRType>(vtypes));

                let fblock = ((jop.tag === MIROpTag.MIRJumpCond) ? blocks.get((jop as MIRJumpCond).falseblock) : blocks.get((jop as MIRJumpNone).someblock)) as MIRBasicBlock;
                let fexp = this.generateSMTBlockExps(fblock, block.label, blocks, new Map<string, MIRType>(vtypes));

                let rexp = exps[exps.length - 1].bind(texp, "#true_trgt#").bind(fexp, "#false_trgt#");
                for (let i = exps.length - 2; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }

                return rexp;
            }
        }
    }

    generateSMTInvoke(idecl: MIRInvokeDecl): string {
        this.cinvokeFile = idecl.srcFile;
        this.cinvokeResult = this.assembly.typeMap.get(idecl.resultType) as MIRType;

        let argvars = new Map<string, MIRType>();
        idecl.params.forEach((arg) => argvars.set(arg.name, this.assembly.typeMap.get(arg.type) as MIRType));

        const args = idecl.params.map((arg) => `(${this.varNameToSMT2Name(arg.name)} ${this.typegen.typeToSMT2Type(this.assembly.typeMap.get(arg.type) as MIRType)})`);
        const restype = this.typegen.typeToSMT2Type(this.assembly.typeMap.get(idecl.resultType) as MIRType);
        const decl = `(define-fun ${this.invokenameToSMT2(idecl.key)} (${args.join(" ")}) Result_${restype}`;

        if (idecl instanceof MIRInvokeBodyDecl) {
            const blocks = (idecl as MIRInvokeBodyDecl).body.body;
            const body = this.generateSMTBlockExps(blocks.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocks, argvars);

            if (idecl.preconditions.length === 0 && idecl.postconditions.length === 0) {
                return `${decl} \n${body.emit("  ")})`;
            }
            else {
                let cbody = body;

                if (idecl.postconditions.length !== 0) {
                    //
                    //TODO -- ref parms don't get expanded correctly here -- need to coordinate with def and call here
                    //
                    const tbody = `@tmpbody@${this.tmpvarctr++}`;
                    const tpostcheck = `@tmppostcheck@${this.tmpvarctr++}`;
                    const postinvoke = this.invokenameToSMT2(MIRKeyGenerator.generateBodyKey("post", idecl.key));
                    const callpost = new SMTValue(`(${postinvoke} ${idecl.params.map((arg) => this.varNameToSMT2Name(arg.name)).join(" ")} ${tbody})`);
                    cbody = new SMTLet(tbody, new SMTValue(cbody.emit("  ")), new SMTCond(
                        (new SMTLet(tpostcheck, callpost, new SMTValue(`(and (is-Result_Bool@result_success ${tpostcheck}) (Result_Bool@result_value ${tpostcheck}))`))),
                        new SMTValue(tbody),
                        new SMTValue(`(Result_${restype}@result_with_code (result_error ${this.registerError(idecl.sourceLocation)}))`)
                    ));
                }

                if (idecl.preconditions.length !== 0) {
                    const tprecheck = `@tmpprecheck@${this.tmpvarctr++}`;
                    const preinvoke = this.invokenameToSMT2(MIRKeyGenerator.generateBodyKey("pre", idecl.key));
                    const callpre = new SMTValue(idecl.params.length !== 0 ? `(${preinvoke} ${idecl.params.map((arg) => this.varNameToSMT2Name(arg.name)).join(" ")})` : preinvoke);
                    cbody = new SMTCond(
                        new SMTLet(tprecheck, callpre, new SMTValue(`(and (is-Result_Bool@result_success ${tprecheck}) (Result_Bool@result_value ${tprecheck}))`)),
                        cbody,
                        new SMTValue(`(Result_${restype}@result_with_code (result_error ${this.registerError(idecl.sourceLocation)}))`)
                    );
                }

                return `${decl} \n${cbody.emit("  ")})`;
            }
        }
        else {
            assert(idecl instanceof MIRInvokePrimitiveDecl);

            return (BuiltinCalls.get(((idecl as MIRInvokePrimitiveDecl).implkey)) as BuiltinCallEmit)(this, idecl as MIRInvokePrimitiveDecl, decl);
        }
    }

    generateSMTPre(prekey: MIRBodyKey, idecl: MIRInvokeDecl): string {
        this.cinvokeFile = idecl.srcFile;
        this.cinvokeResult = this.typegen.boolType;

        let argvars = new Map<string, MIRType>();
        idecl.params.forEach((arg) => argvars.set(arg.name, this.assembly.typeMap.get(arg.type) as MIRType));

        const args = idecl.params.map((arg) => `(${this.varNameToSMT2Name(arg.name)} ${this.typegen.typeToSMT2Type(this.assembly.typeMap.get(arg.type) as MIRType)})`);
        const decl = `(define-fun ${this.invokenameToSMT2(prekey)} (${args.join(" ")}) Result_Bool`;

        if (idecl.preconditions.length === 1) {
            const blocks = idecl.preconditions[0][0].body;
            const body = this.generateSMTBlockExps(blocks.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocks, argvars);
            return `${decl} \n${body.emit("  ")})`;
        }
        else {
            const decls = idecl.preconditions.map((pc, i) => {
                const blocksi = pc[0].body;
                const bodyi = this.generateSMTBlockExps(blocksi.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocksi, argvars);
                const decli = `(define-fun ${this.invokenameToSMT2(prekey)}${i} (${args.join(" ")}) Result_Bool \n${bodyi.emit("  ")})`;
                const calli = (`(${this.invokenameToSMT2(prekey)}${i} ${idecl.params.map((arg) => this.varNameToSMT2Name(arg.name)).join(" ")})`);

                return [decli, calli];
            });

            const declsand = decls.map((cc) => {
                const tv = `@tmpvarda@${this.tmpvarctr++}`;
                return new SMTLet(tv, new SMTValue(cc[1]), new SMTValue(`(and (is-Result_Bool@result_success ${tv}) (Result_Bool@result_value ${tv}))`)).emit();
            });

            return `${decls.map((cc) => cc[0]).join("\n")}\n\n${decl} \n(Result_Bool@result_success (and ${declsand.join(" ")})))`;
        }
    }

    generateSMTPost(postkey: MIRBodyKey, idecl: MIRInvokeDecl): string {
        this.cinvokeFile = idecl.srcFile;
        this.cinvokeResult = this.typegen.boolType;
        const restype = this.assembly.typeMap.get(idecl.resultType) as MIRType;

        let argvars = new Map<string, MIRType>();
        idecl.params.forEach((arg) => argvars.set(arg.name, this.assembly.typeMap.get(arg.type) as MIRType));
        argvars.set("__result__", restype);

        const args = idecl.params.map((arg) => `(${this.varNameToSMT2Name(arg.name)} ${this.typegen.typeToSMT2Type(this.assembly.typeMap.get(arg.type) as MIRType)})`);
        args.push(`(__result__ ${this.typegen.typeToSMT2Type(restype)})`);
        const decl = `(define-fun ${this.invokenameToSMT2(postkey)} (${args.join(" ")}) Result_Bool`;

        if (idecl.postconditions.length === 1) {
            const blocks = idecl.postconditions[0].body;
            const body = this.generateSMTBlockExps(blocks.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocks, argvars);
            return `${decl} \n${body.emit("  ")})`;
        }
        else {
            const decls = idecl.postconditions.map((pc, i) => {
                const blocksi = pc.body;
                const bodyi = this.generateSMTBlockExps(blocksi.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocksi, argvars);
                const decli = `(define-fun ${this.invokenameToSMT2(postkey)}${i} (${args.join(" ")}) Result_Bool \n${bodyi.emit("  ")})`;
                const calli = (`(${this.invokenameToSMT2(postkey)}${i} ${[idecl.params.map((arg) => this.varNameToSMT2Name(arg.name)), "__result__"].join(" ")})`);

                return [decli, calli];
            });

            const declsand = decls.map((cc) => {
                const tv = `@tmpvarda@${this.tmpvarctr++}`;
                return new SMTLet(tv, new SMTValue(cc[1]), new SMTValue(`(and (is-Result_Bool@result_success ${tv}) (Result_Bool@result_value ${tv}))`)).emit();
            });

            return `${decls.map((cc) => cc[0]).join("\n")}\n\n${decl} \n(Result_Bool@result_success (and ${declsand.join(" ")})))`;
        }
    }

    generateSMTInv(invkey: MIRBodyKey, idecl: MIREntityTypeDecl): string {
        this.cinvokeFile = idecl.srcFile;
        this.cinvokeResult = this.typegen.boolType;

        let argvars = new Map<string, MIRType>().set("this", this.assembly.typeMap.get(idecl.tkey) as MIRType);

        const args = `(this ${this.typegen.typeToSMT2Type(this.assembly.typeMap.get(idecl.tkey) as MIRType)})`;
        const decl = `(define-fun ${this.invokenameToSMT2(invkey)} (${args}) Result_Bool`;

        if (idecl.invariants.length === 1) {
            const blocks = idecl.invariants[0].body;
            const body = this.generateSMTBlockExps(blocks.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocks, argvars);
            return `${decl} \n${body.emit("  ")})`;
        }
        else {
            const decls = idecl.invariants.map((pc, i) => {
                const blocksi = pc.body;
                const bodyi = this.generateSMTBlockExps(blocksi.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocksi, argvars);
                const decli = `(define-fun ${this.invokenameToSMT2(invkey)}${i} (${args}) Result_Bool \n${bodyi.emit("  ")})`;
                const calli = (`(${this.invokenameToSMT2(invkey)}${i} this)`);

                return [decli, calli];
            });

            const declsand = decls.map((cc) => {
                const tv = `@tmpvarda@${this.tmpvarctr++}`;
                return new SMTLet(tv, new SMTValue(cc[1]), new SMTValue(`(and (is-Result_Bool@result_success ${tv}) (Result_Bool@result_value ${tv}))`)).emit();
            });

            return `${decls.map((cc) => cc[0]).join("\n")}\n\n${decl} \n(Result_Bool@result_success (and ${declsand.join(" ")})))`;
        }
    }

    generateSMTConst(constkey: MIRBodyKey, cdecl: MIRConstantDecl): string {
        this.cinvokeFile = cdecl.srcFile;
        this.cinvokeResult = this.assembly.typeMap.get(cdecl.declaredType) as MIRType;

        const restype = this.typegen.typeToSMT2Type(this.assembly.typeMap.get(cdecl.declaredType) as MIRType);
        const decl = `(define-fun ${this.invokenameToSMT2(constkey)} () Result_${restype}`;
        const blocks = cdecl.value.body;
        const body = this.generateSMTBlockExps(blocks.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocks, new Map<string, MIRType>());
        return `${decl} \n${body.emit("  ")})`;
    }

    generateSMTFDefault(fdkey: MIRBodyKey, fdecl: MIRFieldDecl): string {
        this.cinvokeFile = fdecl.srcFile;
        this.cinvokeResult = this.assembly.typeMap.get(fdecl.declaredType) as MIRType;

        const restype = this.typegen.typeToSMT2Type(this.assembly.typeMap.get(fdecl.declaredType) as MIRType);
        const decl = `(define-fun ${this.invokenameToSMT2(fdkey)} () Result_${restype}`;
        const blocks = (fdecl.value as MIRBody).body;
        const body = this.generateSMTBlockExps(blocks.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocks, new Map<string, MIRType>());
        return `${decl} \n${body.emit("  ")})`;
    }

    generateSMTAssembly(): string {
        const typedecls: string[] = [];
        const consdecls: [string, string?][] = [];
        this.assembly.typeMap.forEach((type) => {
            this.typegen.generateTypeDecl(type, typedecls, consdecls);
        });

        const cginfo = constructCallGraphInfo(this.assembly.entryPoints, this.assembly);
        assert(cginfo.recursive.length === 0, "TODO: we need to support recursion here");

        const invokedecls: string[] = [];
        const resultset = new Set<string>();
        const bupcg = [...cginfo.topologicalOrder].reverse();
        for (let i = 0; i < bupcg.length; ++i) {
            const bbup = bupcg[i];
            const tag = extractMirBodyKeyPrefix(bbup.invoke);
            if (tag === "invoke") {
                const ikey = extractMirBodyKeyData(bbup.invoke) as MIRInvokeKey;
                const idcl = (this.assembly.invokeDecls.get(ikey) || this.assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
                invokedecls.push(this.generateSMTInvoke(idcl));

                resultset.add(this.typegen.typeToSMT2Type(this.assembly.typeMap.get(idcl.resultType) as MIRType));
            }
            else if (tag === "pre") {
                const ikey = extractMirBodyKeyData(bbup.invoke) as MIRInvokeKey;
                const idcl = (this.assembly.invokeDecls.get(ikey) || this.assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
                invokedecls.push(this.generateSMTPre(bbup.invoke, idcl));
            }
            else if (tag === "post") {
                const ikey = extractMirBodyKeyData(bbup.invoke) as MIRInvokeKey;
                const idcl = (this.assembly.invokeDecls.get(ikey) || this.assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
                invokedecls.push(this.generateSMTPost(bbup.invoke, idcl));
            }
            else if (tag === "invariant") {
                const edcl = this.assembly.entityDecls.get(extractMirBodyKeyData(bbup.invoke) as MIRNominalTypeKey) as MIREntityTypeDecl;
                invokedecls.push(this.generateSMTInv(bbup.invoke, edcl));
            }
            else if (tag === "const") {
                const cdcl = this.assembly.constantDecls.get(extractMirBodyKeyData(bbup.invoke) as MIRConstantKey) as MIRConstantDecl;
                invokedecls.push(this.generateSMTConst(bbup.invoke, cdcl));

                resultset.add(this.typegen.typeToSMT2Type(this.assembly.typeMap.get(cdcl.declaredType) as MIRType));
            }
            else {
                assert(tag === "fdefault");
                const fdcl = this.assembly.fieldDecls.get(extractMirBodyKeyData(bbup.invoke) as MIRFieldKey) as MIRFieldDecl;
                invokedecls.push(this.generateSMTFDefault(bbup.invoke, fdcl));

                resultset.add(this.typegen.typeToSMT2Type(this.assembly.typeMap.get(fdcl.declaredType) as MIRType));
            }
        }

        const resultarr = [...resultset];
        const resultdecls = resultarr.map((rd) => `(Result_${rd} 0)`);
        const resultcons = resultarr.map((rd) => `( (Result_${rd}@result_with_code (Result_${rd}@result_code_value ResultCode)) (Result_${rd}@result_success (Result_${rd}@result_value ${rd})) )`);

        const nominaltypechecks = this.typegen.generateNominalTypeDecls();
        const structuraltypechecks = this.typegen.generateStructuralTypeDecls();

        return smt_header
        + "\n\n"
        + smtlib_code
        + "\n\n"
        + `(declare-datatypes (${typedecls.join("\n")}) (\n${consdecls.map((cd) => cd[0]).join("\n")}\n))`
        + "\n\n"
        + `(declare-datatypes (${resultdecls.join("\n")}) (\n${resultcons.join("\n")}\n))`
        + "\n\n"
        + `${consdecls.map((cd) => cd[1]).filter((d) => d !== undefined).join("\n")}`
        + "\n\n"
        + nominaltypechecks
        + "\n\n"
        + structuraltypechecks
        + "\n\n"
        + invokedecls.join("\n\n")
        + "\n\n";
    }
}

export {
    SMTLIBGenerator
};
