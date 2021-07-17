//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIREntityType, MIREntityTypeDecl, MIREphemeralListType, MIRInvokeDecl, MIROOTypeDecl, MIRRecordType, MIRSpecialTypeCategory, MIRTupleType, MIRType } from "../../compiler/mir_assembly";
import { MIRFieldKey, MIRResolvedTypeKey } from "../../compiler/mir_ops";
import { SMTCallGeneral, SMTCallSimple, SMTConst, SMTExp, SMTType, VerifierOptions } from "./smt_exp";

import * as assert from "assert";
import { BSQRegex } from "../../ast/bsqregex";

enum APIEmitTypeTag
{
    NoneTag = 0x0,
    BoolTag,
    NatTag,
    IntTag,
    BigNatTag,
    BigIntTag,
    RationalTag,
    FloatTag,
    DecimalTag,
    StringTag,
    StringOfTag,
    NumberOfTag,
    DataStringTag,
    ByteBufferTag,
    BufferTag,
    DataBufferTag,
    ISOTag,
    LogicalTag,
    UUIDTag,
    ContentHashTag,
    TupleTag,
    RecordTag,
    ListTag,
    EnumTag,
    UnionTag
};

class SMTTypeEmitter {
    readonly assembly: MIRAssembly;
    readonly vopts: VerifierOptions;

    private mangledNameMap: Map<string, string> = new Map<string, string>();

    constructor(assembly: MIRAssembly, vopts: VerifierOptions, mangledNameMap?: Map<string, string>) {
        this.assembly = assembly;
        this.vopts = vopts;

        this.mangledNameMap = mangledNameMap || new Map<string, string>();
    }

    mangle(name: string): string {
        if (!this.mangledNameMap.has(name)) {
            const cleanname = name.replace(/\W/g, "_").toLowerCase() + "I" + this.mangledNameMap.size + "I";
            this.mangledNameMap.set(name, cleanname);
        }

        return this.mangledNameMap.get(name) as string;
    }

    getMIRType(tkey: MIRResolvedTypeKey): MIRType {
        return this.assembly.typeMap.get(tkey) as MIRType;
    }

    isType(tt: MIRType, tkey: string): boolean {
        return tt.trkey === tkey;
    }

    isUniqueTupleType(tt: MIRType): boolean {
        return tt.options.length === 1 && (tt.options[0] instanceof MIRTupleType) && !(tt.options[0] as MIRTupleType).entries.some((entry) => entry.isOptional);
    }

    isUniqueRecordType(tt: MIRType): boolean {
        return tt.options.length === 1 && (tt.options[0] instanceof MIRRecordType) && !(tt.options[0] as MIRRecordType).entries.some((entry) => entry.isOptional);
    }

    isUniqueEntityType(tt: MIRType): boolean {
        return tt.options.length === 1 && (tt.options[0] instanceof MIREntityType);
    }

    isUniqueEphemeralType(tt: MIRType): boolean {
        return tt.options.length === 1 && (tt.options[0] instanceof MIREphemeralListType);
    }

    isUniqueType(tt: MIRType): boolean {
        return this.isUniqueTupleType(tt) || this.isUniqueRecordType(tt) || this.isUniqueEntityType(tt) || this.isUniqueEphemeralType(tt);
    }

    private getSMTTypeForEntity(tt: MIREntityTypeDecl): SMTType {
        if(tt.specialDecls.has(MIRSpecialTypeCategory.StringOfDecl)) {
            return new SMTType("BString");
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.DataStringDecl)) {
            return new SMTType("BString");
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.TypeDeclNumeric) || tt.specialDecls.has(MIRSpecialTypeCategory.TypeDeclDecl)) {
            const dkind = (tt.specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[])[0].tkind;

            return this.getSMTTypeFor(this.getMIRType(dkind));
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.EnumTypeDecl)) {
            const dkind = (tt.specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[])[0].tkind;

            return this.getSMTTypeFor(this.getMIRType(dkind));
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.BufferDecl)) {
            //
            //TODO: implement this representation in the C++ interpreter etc.
            //
            assert(false, "Buffer is not implemented yet");
            return new SMTType(this.mangle(tt.tkey));
        }
        else if(tt.specialDecls.has(MIRSpecialTypeCategory.DataBufferDecl)) {
            //
            //TODO: implement this representation in the C++ interpreter etc.
            //
            assert(false, "Buffer is not implemented yet");
            return new SMTType(this.mangle(tt.tkey));
        }
        else {
            return new SMTType(this.mangle(tt.tkey));
        }
    }

    getSMTTypeFor(tt: MIRType): SMTType {
        if (this.isType(tt, "NSCore::None")) {
            return new SMTType("bsq_none");
        }
        else if (this.isType(tt, "NSCore::Bool")) {
            return new SMTType("Bool");
        }
        else if (this.isType(tt, "NSCore::Int")) {
            return new SMTType("BInt");
        }
        else if (this.isType(tt, "NSCore::Nat")) {
            return new SMTType("BNat");
        }
        else if (this.isType(tt, "NSCore::BigInt")) {
            return new SMTType("BBigInt");
        }
        else if (this.isType(tt, "NSCore::BigNat")) {
            return new SMTType("BBigNat");
        }
        else if (this.isType(tt, "NSCore::Float")) {
            return new SMTType("BFloat");
        }
        else if (this.isType(tt, "NSCore::Decimal")) {
            return new SMTType("BDecimal");
        }
        else if (this.isType(tt, "NSCore::Rational")) {
            return new SMTType("BRational");
        }
        else if (this.isType(tt, "NSCore::StringPos")) {
            return new SMTType("Int");
        }
        else if (this.isType(tt, "NSCore::String")) {
            return new SMTType("BString");
        }
        else if (this.isType(tt, "NSCore::ByteBuffer")) {
            return new SMTType("BByteBuffer");
        }
        else if(this.isType(tt, "NSCore::ISOTime")) {
            return new SMTType("Int");
        }
        else if(this.isType(tt, "NSCore::LogicalTime")) {
            return new SMTType("Int");
        }
        else if(this.isType(tt, "NSCore::UUID")) {
            return new SMTType("String");
        }
        else if(this.isType(tt, "NSCore::ContentHash")) {
            return new SMTType("Int");
        }
        else if (this.isType(tt, "NSCore::Regex")) {
            return new SMTType("bsq_regex");
        }
        else if (this.isType(tt, "NSCore::ISequence")) {
            return new SMTType("ISequence");
        }
        else if(this.isUniqueTupleType(tt)) {
            return new SMTType(this.mangle(tt.trkey));
        }
        else if(this.isUniqueRecordType(tt)) {
            return new SMTType(this.mangle(tt.trkey));
        }
        else if(this.isUniqueEntityType(tt)) {
            return this.getSMTTypeForEntity(this.assembly.entityDecls.get(tt.trkey) as MIREntityTypeDecl);
        }
        else if (this.isUniqueEphemeralType(tt)) {
            return new SMTType(this.mangle(tt.trkey));
        }
        else if(this.assembly.subtypeOf(tt, this.getMIRType("NSCore::KeyType"))) {
            return new SMTType("BKey");
        }
        else {
            return new SMTType("BTerm");
        }
    }

    getSMTTypeTag(tt: MIRType): string {
        if (this.isType(tt, "NSCore::None")) {
            return "TypeTag_None";
        }
        else if (this.isType(tt, "NSCore::Bool")) {
            return "TypeTag_Bool";
        }
        else if (this.isType(tt, "NSCore::Int")) {
            return "TypeTag_Int";
        }
        else if (this.isType(tt, "NSCore::Nat")) {
            return "TypeTag_Nat";
        }
        else if (this.isType(tt, "NSCore::BigInt")) {
            return "TypeTag_BigInt";
        }
        else if (this.isType(tt, "NSCore::BigNat")) {
            return "TypeTag_BigNat";
        }
        else if (this.isType(tt, "NSCore::Float")) {
            return "TypeTag_Float";
        }
        else if (this.isType(tt, "NSCore::Decimal")) {
            return "TypeTag_Decimal";
        }
        else if (this.isType(tt, "NSCore::Rational")) {
            return "TypeTag_Rational";
        }
        else if (this.isType(tt, "NSCore::StringPos")) {
            return "TypeTag_StringPos";
        }
        else if (this.isType(tt, "NSCore::String")) {
            return "TypeTag_String";
        }
        else if (this.isType(tt, "NSCore::ByteBuffer")) {
            return "TypeTag_ByteBuffer";
        }
        else if(this.isType(tt, "NSCore::ISOTime")) {
            return "TypeTag_ISOTime";
        }
        else if(this.isType(tt, "NSCore::LogicalTime")) {
            return "TypeTag_LogicalTime";
        }
        else if(this.isType(tt, "NSCore::UUID")) {
            return "TypeTag_UUID";
        }
        else if(this.isType(tt, "NSCore::ContentHash")) {
            return "TypeTag_ContentHash";
        }
        else if (this.isType(tt, "NSCore::Regex")) {
            return "TypeTag_Regex";
        }
        else if (this.isUniqueTupleType(tt)) {
            return `TypeTag_${this.mangle(tt.trkey)}`;
        }
        else if (this.isUniqueRecordType(tt)) {
            return `TypeTag_${this.mangle(tt.trkey)}`;
        }
        else {
            assert(this.isUniqueEntityType(tt), "Should not be other options")
            return `TypeTag_${this.mangle(tt.trkey)}`;
        }
    }

    getSMTConstructorName(tt: MIRType): { cons: string, box: string, bfield: string } {
        const kfix = this.assembly.subtypeOf(tt, this.getMIRType("NSCore::KeyType")) ? "bsqkey_" : "bsqobject_"
        if (this.isUniqueTupleType(tt)) {
            return { cons: `${this.mangle(tt.trkey)}@cons`, box: `${this.mangle(tt.trkey)}@box`, bfield: `${kfix}${this.mangle(tt.trkey)}_value` };
        }
        else if (this.isUniqueRecordType(tt)) {
            return { cons: `${this.mangle(tt.trkey)}@cons`, box: `${this.mangle(tt.trkey)}@box`, bfield: `${kfix}${this.mangle(tt.trkey)}_value` };
        }
        else if (this.isUniqueEntityType(tt)) {
            return { cons: `${this.mangle(tt.trkey)}@cons`, box: `${this.mangle(tt.trkey)}@box`, bfield: `${kfix}${this.mangle(tt.trkey)}_value` };
        }
        else {
            assert(this.isUniqueEphemeralType(tt), "should not be other options")
            return { cons: `${this.mangle(tt.trkey)}@cons`, box: `${this.mangle(tt.trkey)}@box`, bfield: `${kfix}${this.mangle(tt.trkey)}_value` };
        }
    }

    private coerceFromAtomicToKey(exp: SMTExp, from: MIRType): SMTExp  {
        assert(this.assembly.subtypeOf(from, this.getMIRType("NSCore::KeyType")));

        if (from.trkey === "NSCore::None") {
            return new SMTConst("BKey@none");
        }
        else {
            let objval: SMTExp | undefined = undefined;
            let typetag = "[NOT SET]";

            if (this.isType(from, "NSCore::Bool")) {
                objval = new SMTCallSimple("bsqkey_bool@box", [exp]);
                typetag = "TypeTag_Bool";
            }
            else if (this.isType(from, "NSCore::Int")) {
                objval = new SMTCallSimple("bsqkey_int@box", [exp]);
                typetag = "TypeTag_Int";
            }
            else if (this.isType(from, "NSCore::Nat")) {
                objval = new SMTCallSimple("bsqkey_nat@box", [exp]);
                typetag = "TypeTag_Nat";
            }
            else if (this.isType(from, "NSCore::BigInt")) {
                objval = new SMTCallSimple("bsqkey_bigint@box", [exp]);
                typetag = "TypeTag_BigInt";
            }
            else if (this.isType(from, "NSCore::BigNat")) {
                objval = new SMTCallSimple("bsqkey_bignat@box", [exp]);
                typetag = "TypeTag_BigNat";
            }
            else if (this.isType(from, "NSCore::String")) {
                objval = new SMTCallSimple("bsqkey_string@box", [exp]);
                typetag = "TypeTag_String";
            }
            else if(this.isType(from, "NSCore::LogicalTime")) {
                objval = new SMTCallSimple("bsqkey_logicaltime@box", [exp]);
                typetag = "TypeTag_LogicalTime";
            }
            else if(this.isType(from, "NSCore::UUID")) {
                objval = new SMTCallSimple("bsqkey_uuid@box", [exp]);
                typetag = "TypeTag_UUID";
            }
            else if(this.isType(from, "NSCore::ContentHash")) {
                objval = new SMTCallSimple("bsqkey_contenthash@box", [exp]);
                typetag = "TypeTag_ContentHash";
            }
            else if (this.isUniqueTupleType(from)) {
                objval = new SMTCallSimple(this.getSMTConstructorName(from).box, [exp]);
                typetag = this.getSMTTypeTag(from);
            }
            else if (this.isUniqueRecordType(from)) {
                objval = new SMTCallSimple(this.getSMTConstructorName(from).box, [exp]);
                typetag = this.getSMTTypeTag(from);
            }
            else {
                assert(this.isUniqueEntityType(from));

                objval = new SMTCallSimple(this.getSMTConstructorName(from).box, [exp]);
                typetag = this.getSMTTypeTag(from);
            }

            return new SMTCallSimple("BKey@box", [new SMTConst(typetag), objval as SMTExp]);
        }
    }

    private coerceFromAtomicToTerm(exp: SMTExp, from: MIRType): SMTExp {
        if (from.trkey === "NSCore::None") {
            return new SMTConst(`BTerm@none`);
        }
        else {
            if(this.assembly.subtypeOf(from, this.getMIRType("NSCore::KeyType"))) {
                return new SMTCallSimple("BTerm@keybox", [this.coerceFromAtomicToKey(exp, from)]);
            }
            else {
                let objval: SMTExp | undefined = undefined;
                let typetag = "[NOT SET]";

                if (this.isType(from, "NSCore::Float")) {
                    objval = new SMTCallSimple("bsq_float@box", [exp]);
                    typetag = "TypeTag_Float";
                }
                else if (this.isType(from, "NSCore::Decimal")) {
                    objval = new SMTCallSimple("bsq_decimal@box", [exp]);
                    typetag = "TypeTag_Decimal";
                }
                else if (this.isType(from, "NSCore::Rational")) {
                    objval = new SMTCallSimple("bsq_rational@box", [exp]);
                    typetag = "TypeTag_Rational";
                }
                else if (this.isType(from, "NSCore::StringPos")) {
                    objval = new SMTCallSimple("bsq_stringpos@box", [exp]);
                    typetag = "TypeTag_StringPos";
                }
                else if (this.isType(from, "NSCore::ByteBuffer")) {
                    objval = new SMTCallSimple("bsq_bytebuffer@box", [exp]);
                    typetag = "TypeTag_ByteBuffer";
                }
                else if(this.isType(from, "NSCore::ISOTime")) {
                    objval = new SMTCallSimple("bsq_isotime@box", [exp]);
                    typetag = "TypeTag_ISOTime";
                }
                else if (this.isType(from, "NSCore::Regex")) {
                    objval = new SMTCallSimple("bsq_regex@box", [exp]);
                    typetag = "TypeTag_Regex";
                }
                else if (this.isUniqueTupleType(from)) {
                    objval = new SMTCallSimple(this.getSMTConstructorName(from).box, [exp]);
                    typetag = this.getSMTTypeTag(from);
                }
                else if (this.isUniqueRecordType(from)) {
                    objval = new SMTCallSimple(this.getSMTConstructorName(from).box, [exp]);
                    typetag = this.getSMTTypeTag(from);
                }
                else {
                    assert(this.isUniqueEntityType(from));

                    objval = new SMTCallSimple(this.getSMTConstructorName(from).box, [exp]);
                    typetag = this.getSMTTypeTag(from);
                }

                return new SMTCallSimple("BTerm@termbox", [new SMTConst(typetag), objval as SMTExp]);
            }
        }
    }

    private coerceKeyIntoAtomic(exp: SMTExp, into: MIRType): SMTExp {
        if (this.isType(into, "NSCore::None")) {
            return new SMTConst("bsq_none@literal");
        }
        else {
            const oexp = new SMTCallSimple("BKey_value", [exp]);

            if (this.isType(into, "NSCore::Bool")) {
                return new SMTCallSimple("bsqkey_bool_value", [oexp]);
            }
            else if (this.isType(into, "NSCore::Int")) {
                return new SMTCallSimple("bsqkey_int_value", [oexp]);
            }
            else if (this.isType(into, "NSCore::Nat")) {
                return new SMTCallSimple("bsqkey_nat_value", [oexp]);
            }
            else if (this.isType(into, "NSCore::BigInt")) {
                return new SMTCallSimple("bsqkey_bigint_value", [oexp]);
            }
            else if (this.isType(into, "NSCore::BigNat")) {
                return new SMTCallSimple("bsqkey_bignat_value", [oexp]);
            }
            else if (this.isType(into, "NSCore::String")) {
                return new SMTCallSimple("bsqkey_string_value", [oexp]);
            }
            else if(this.isType(into, "NSCore::LogicalTime")) {
                return new SMTCallSimple("bsqkey_logicaltime_value", [oexp]);
            }
            else if(this.isType(into, "NSCore::UUID")) {
                return new SMTCallSimple("bsqkey_uuid_value", [oexp]);
            }
            else if(this.isType(into, "NSCore::ContentHash")) {
                return new SMTCallSimple("bsqkey_contenthash_value", [oexp]);
            }
            else if (this.isUniqueTupleType(into)) {
                return new SMTCallSimple(this.getSMTConstructorName(into).bfield, [oexp]);
            }
            else if (this.isUniqueRecordType(into)) {
                return new SMTCallSimple(this.getSMTConstructorName(into).bfield, [oexp]);
            }
            else {
                assert(this.isUniqueEntityType(into));

                return new SMTCallSimple(this.getSMTConstructorName(into).bfield, [oexp]);
            }
        }
    }

    private coerceTermIntoAtomic(exp: SMTExp, into: MIRType): SMTExp {
        if (this.isType(into, "NSCore::None")) {
            return new SMTConst("bsq_none@literal");
        }
        else {
            if(this.assembly.subtypeOf(into, this.getMIRType("NSCore::KeyType"))) {
                return this.coerceKeyIntoAtomic(new SMTCallSimple("BTerm_keyvalue", [exp]), into)
            }
            else {
                const oexp = new SMTCallSimple("BTerm_termvalue", [exp]);

                if (this.isType(into, "NSCore::Float")) {
                    return new SMTCallSimple("bsqobject_float_value", [oexp]);
                }
                else if (this.isType(into, "NSCore::Decimal")) {
                    return new SMTCallSimple("bsqobject_decimal_value", [oexp]);
                }
                else if (this.isType(into, "NSCore::Rational")) {
                    return new SMTCallSimple("bsqobject_rational_value", [oexp]);
                }
                else if (this.isType(into, "NSCore::StringPos")) {
                    return new SMTCallSimple("bsqobject_stringpos_value", [oexp]);
                }
                else if (this.isType(into, "NSCore::ByteBuffer")) {
                    return new SMTCallSimple("bsqobject_bytebuffer_value", [oexp]);
                }
                else if(this.isType(into, "NSCore::ISOTime")) {
                    return new SMTCallSimple("bsqobject_isotime_value", [oexp]);
                }
                else if (this.isType(into, "NSCore::Regex")) {
                    return new SMTCallSimple("bsqobject_regex_value", [oexp]);
                }
                else if (this.isUniqueTupleType(into)) {
                    return new SMTCallSimple(this.getSMTConstructorName(into).bfield, [oexp]);
                }
                else if (this.isUniqueRecordType(into)) {
                    return new SMTCallSimple(this.getSMTConstructorName(into).bfield, [oexp]);
                }
                else {
                    assert(this.isUniqueEntityType(into));

                    return new SMTCallSimple(this.getSMTConstructorName(into).bfield, [oexp]);
                }
            }
        }
    }

    coerce(exp: SMTExp, from: MIRType, into: MIRType): SMTExp {
        const smtfrom = this.getSMTTypeFor(from);
        const smtinto = this.getSMTTypeFor(into);

        if (smtfrom.name === smtinto.name) {
            return exp;
        }
        else if (smtinto.name === "BKey") {
            if(smtfrom.name === "BTerm") {
                return new SMTCallSimple("BTerm_keyvalue", [exp]);
            }
            else {
                return this.coerceFromAtomicToKey(exp, from);
            }
        }
        else if (smtinto.name === "BTerm") {
            if(smtfrom.name === "BKey") {
                return new SMTCallSimple("BTerm@keybox", [exp]);
            }
            else {
                return this.coerceFromAtomicToTerm(exp, from);
            }
        }
        else {
            if (smtfrom.name === "BKey") {
                return this.coerceKeyIntoAtomic(exp, into);
            }
            else {
                assert(smtfrom.name === "BTerm");

                return this.coerceTermIntoAtomic(exp, into);
            }
        }
    }

    coerceToKey(exp: SMTExp, from: MIRType): SMTExp {
        const smtfrom = this.getSMTTypeFor(from);

        if (smtfrom.name === "BKey") {
            return exp;
        }
        else {
            if(smtfrom.name === "BTerm") {
                return new SMTCallSimple("BTerm_keyvalue", [exp]);
            }
            else {
                return this.coerceFromAtomicToKey(exp, from);
            }
        }
    }

    generateTupleIndexGetFunction(tt: MIRTupleType, idx: number): string {
        return `${this.mangle(tt.trkey)}@_${idx}`;
    } 

    generateRecordPropertyGetFunction(tt: MIRRecordType, pname: string): string {
        return `${this.mangle(tt.trkey)}@_${pname}`;
    }

    generateEntityFieldGetFunction(tt: MIREntityTypeDecl, field: MIRFieldKey): string {
        return `${this.mangle(tt.tkey)}@_${this.mangle(field)}`;
    }

    generateEphemeralListGetFunction(tt: MIREphemeralListType, idx: number): string {
        return `${this.mangle(tt.trkey)}@_${idx}`;
    }

    generateResultType(ttype: MIRType): SMTType {
        return new SMTType(`$Result_${this.getSMTTypeFor(ttype).name}`);
    }

    generateResultTypeConstructorSuccess(ttype: MIRType, val: SMTExp): SMTExp {
        return new SMTCallSimple(`$Result_${this.getSMTTypeFor(ttype).name}@success`, [val]);
    }

    generateResultTypeConstructorError(ttype: MIRType, err: SMTExp): SMTExp {
        return new SMTCallSimple(`$Result_${this.getSMTTypeFor(ttype).name}@error`, [err]);
    }

    generateErrorResultAssert(rtype: MIRType): SMTExp {
        return this.generateResultTypeConstructorError(rtype, new SMTConst("ErrorID_AssumeCheck"));
    }

    generateResultIsSuccessTest(ttype: MIRType, exp: SMTExp): SMTExp {
        return new SMTCallSimple(`(_ is $Result_${this.getSMTTypeFor(ttype).name}@success)`, [exp]);
    }

    generateResultIsErrorTest(ttype: MIRType, exp: SMTExp): SMTExp {
        return new SMTCallSimple(`(_ is $Result_${this.getSMTTypeFor(ttype).name}@error)`, [exp]);
    }

    generateResultGetSuccess(ttype: MIRType, exp: SMTExp): SMTExp {
        return new SMTCallSimple(`$Result_${this.getSMTTypeFor(ttype).name}@success_value`, [exp]);
    }

    generateResultGetError(ttype: MIRType, exp: SMTExp): SMTExp {
        return new SMTCallSimple(`$Result_${this.getSMTTypeFor(ttype).name}@error_value`, [exp]);
    }
    
    generateAccessWithSetGuardResultType(ttype: MIRType): SMTType {
        return new SMTType(`$GuardResult_${this.getSMTTypeFor(ttype).name}`);
    }

    generateAccessWithSetGuardResultTypeConstructorLoad(ttype: MIRType, value: SMTExp, flag: boolean): SMTExp {
        return new SMTCallSimple(`$GuardResult_${this.getSMTTypeFor(ttype).name}@cons`, [value, new SMTConst(flag ? "true" : "false")]);
    }

    generateAccessWithSetGuardResultGetValue(ttype: MIRType, exp: SMTExp): SMTExp {
        return new SMTCallSimple(`$GuardResult_${this.getSMTTypeFor(ttype).name}@result`, [exp]);
    }

    generateAccessWithSetGuardResultGetFlag(ttype: MIRType, exp: SMTExp): SMTExp {
        return new SMTCallSimple(`$GuardResult_${this.getSMTTypeFor(ttype).name}@flag`, [exp]);
    }

    private havocTypeInfoGen(tt: MIRType): [string, boolean] {
        if (this.isType(tt, "NSCore::None")) {
            return ["BNone@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::Bool")) {
            return ["BBool@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::Int")) {
            return ["BInt@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::Nat")) {
            return ["BNat@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::BigInt")) {
            return ["BBigInt@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::BigNat")) {
            return ["BBigNat@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::Float")) {
            return ["BFloat@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::Decimal")) {
            return ["BDecimal@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::ISOTime")) {
            return ["BISOTime@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::LogicalTime")) {
            return ["BLogicalTime@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::UUID")) {
            return ["BUUID@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::ContentHash")) {
            return ["BContentHash@UFCons_API", false];
        }
        else {
            return [`_@@cons_${this.getSMTTypeFor(tt).name}_entrypoint`, true];
        }
    }

    isKnownSafeHavocConstructorType(tt: MIRType): boolean {
        return !this.havocTypeInfoGen(tt)[1];
    }

    generateHavocConstructorName(tt: MIRType): string {
        return this.havocTypeInfoGen(tt)[0];
    }

    generateHavocConstructorPathExtend(path: SMTExp, step: SMTExp): SMTExp {
        return new SMTCallSimple("seq.++", [path, new SMTCallSimple("Ctx@MakeStep", [step])]);
    }

    generateHavocConstructorCall(tt: MIRType, path: SMTExp, step: SMTExp): SMTExp {
        if(this.isKnownSafeHavocConstructorType(tt)) {
            return this.generateResultTypeConstructorSuccess(tt, new SMTCallSimple(this.generateHavocConstructorName(tt), [this.generateHavocConstructorPathExtend(path, step)]));
        }
        else {
            return new SMTCallGeneral(this.generateHavocConstructorName(tt), [this.generateHavocConstructorPathExtend(path, step)]);
        }
    }

    private getJSONApiBase(tt: MIRType): {name: string, smtname: string} {
        return {name: tt.trkey, smtname: this.getSMTTypeFor(tt).name};
    }

    private getJSONApiStd(tt: MIRType): {name: string, smtname: string, smttypetag: string} {
        return {...this.getJSONApiBase(tt), smttypetag: this.getSMTTypeTag(tt)};
    }

    getAPITypeFor(tt: MIRType): object {
        if (this.isType(tt, "NSCore::None")) {
            return {tag: APIEmitTypeTag.NoneTag, ...this.getJSONApiStd(tt), boxfunc: "[SPECIAL_BOX]", unboxfunc: "[SPECIAL_UNBOX]"};
        }
        else if (this.isType(tt, "NSCore::Bool")) {
            return {tag: APIEmitTypeTag.BoolTag, ...this.getJSONApiStd(tt), boxfunc: "bsqkey_bool@box", unboxfunc: "bsqkey_bool_value"};
        }
        else if (this.isType(tt, "NSCore::Int")) {
            return {tag: APIEmitTypeTag.IntTag, ...this.getJSONApiStd(tt), boxfunc: "bsqkey_int@box", unboxfunc: "bsqkey_int_value"};
        }
        else if (this.isType(tt, "NSCore::Nat")) {
            return {tag: APIEmitTypeTag.NatTag, ...this.getJSONApiStd(tt), boxfunc: "bsqkey_nat@box", unboxfunc: "bsqkey_nat_value"};
        }
        else if (this.isType(tt, "NSCore::BigInt")) {
            return {tag: APIEmitTypeTag.BigIntTag, ...this.getJSONApiStd(tt), boxfunc: "bsqkey_bigint@box", unboxfunc: "bsqkey_bigint_value"};
        }
        else if (this.isType(tt, "NSCore::BigNat")) {
            return {tag: APIEmitTypeTag.BigNatTag, ...this.getJSONApiStd(tt), boxfunc: "bsqkey_bignat@box", unboxfunc: "bsqkey_bignat_value"};
        }
        else if (this.isType(tt, "NSCore::Float")) {
            return {tag: APIEmitTypeTag.FloatTag, ...this.getJSONApiStd(tt), boxfunc: "bsq_float@box", unboxfunc: "bsqobject_float_value"};
        }
        else if (this.isType(tt, "NSCore::Decimal")) {
            return {tag: APIEmitTypeTag.DecimalTag, ...this.getJSONApiStd(tt), boxfunc: "bsq_decimal@box", unboxfunc: "bsqobject_decimal_value"};
        }
        else if (this.isType(tt, "NSCore::Rational")) {
            return {tag: APIEmitTypeTag.RationalTag, ...this.getJSONApiStd(tt), boxfunc: "bsq_rational@box", unboxfunc: "bsqobject_rational_value"};
        }
        else if (this.isType(tt, "NSCore::String")) {
            return {tag: APIEmitTypeTag.StringTag, ...this.getJSONApiStd(tt), boxfunc: "bsqkey_string@box", unboxfunc: "bsqkey_string_value"};
        }
        else if (this.isType(tt, "NSCore::ByteBuffer")) {
            return {tag: APIEmitTypeTag.ByteBufferTag, ...this.getJSONApiStd(tt), boxfunc: "bsqkey_bytebuffer@box", unboxfunc: "bsqobject_bytebuffer_value"};
        }
        else if(this.isType(tt, "NSCore::ISOTime")) {
            return {tag: APIEmitTypeTag.ISOTag, ...this.getJSONApiStd(tt), boxfunc: "bsq_isotime@box", unboxfunc: "bsqobject_isotime_value"};
        }
        else if(this.isType(tt, "NSCore::LogicalTime")) {
            return {tag: APIEmitTypeTag.LogicalTag, ...this.getJSONApiStd(tt), boxfunc: "bsqkey_logicaltime@box", unboxfunc: "bsqkey_logicaltime_value"};
        }
        else if(this.isType(tt, "NSCore::UUID")) {
            return {tag: APIEmitTypeTag.UUIDTag, ...this.getJSONApiStd(tt), boxfunc: "bsqkey_uuid@box", unboxfunc: "bsqkey_uuid_value"};
        }
        else if(this.isType(tt, "NSCore::ContentHash")) {
            return {tag: APIEmitTypeTag.ContentHashTag, ...this.getJSONApiStd(tt), boxfunc: "bsqkey_contenthash@box", unboxfunc: "bsqkey_contenthash_value"};
        }
        else if(this.isUniqueTupleType(tt)) {
            const tdecl = this.assembly.tupleDecls.get(tt.trkey) as MIRTupleType;

            const iskey = tdecl.grounded && this.assembly.subtypeOf(tt, this.getMIRType("NSCore::KeyType"));
            const bbufuncs = this.getSMTConstructorName(tt);

            let ttypes: string[] = [];
            let smtaccessors: string[] = [];
            for(let i = 0; i < tdecl.entries.length; ++i)
            {
                const mirtt = tdecl.entries[i].type;

                ttypes.push(this.getSMTTypeFor(mirtt).name);
                smtaccessors.push(this.generateTupleIndexGetFunction(tdecl, i));
            }

            return {tag: APIEmitTypeTag.TupleTag, ...this.getJSONApiStd(tt), iskey: iskey, boxfunc: bbufuncs.box, unboxfunc: bbufuncs.bfield, isvalue: tdecl.isvalue, ttypes: ttypes, smtaccessors: smtaccessors};
        }
        else if(this.isUniqueRecordType(tt)) {
            const rdecl = this.assembly.tupleDecls.get(tt.trkey) as MIRRecordType;

            const iskey = rdecl.grounded && this.assembly.subtypeOf(tt, this.getMIRType("NSCore::KeyType"));
            const bbufuncs = this.getSMTConstructorName(tt);

            let props: string[] = [];
            let ttypes: string[] = [];
            let smtaccessors: string[] = [];
            for(let i = 0; i < rdecl.entries.length; ++i)
            {
                const prop = rdecl.entries[i].name;
                const mirtt = rdecl.entries[i].type;

                props.push(prop);
                ttypes.push(this.getSMTTypeFor(mirtt).name);
                smtaccessors.push(this.generateRecordPropertyGetFunction(rdecl, prop));
            }

            return {tag: APIEmitTypeTag.RecordTag, ...this.getJSONApiStd(tt), iskey: iskey, boxfunc: bbufuncs.box, unboxfunc: bbufuncs.bfield, isvalue: rdecl.isvalue, props: props, ttypes: ttypes, smtaccessors: smtaccessors};
        }
        else if(this.isUniqueEntityType(tt)) {
            const edecl = this.assembly.entityDecls.get(tt.trkey) as MIREntityTypeDecl;
            const bbufuncs = this.getSMTConstructorName(tt);

            if(edecl.specialDecls.has(MIRSpecialTypeCategory.StringOfDecl)) {
                const vtype = ((edecl.specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[]).find((tke) => tke.tname === "T") as { tname: string, tkind: MIRResolvedTypeKey }).tkind;
        
                const vre = this.assembly.validatorRegexs.get(vtype) as BSQRegex;
                const lre = vre.compileToSMTValidator(this.vopts.StringOpt === "ASCII");

                return {tag: APIEmitTypeTag.StringOfTag, ...this.getJSONApiStd(tt), boxfunc: bbufuncs.box, unboxfunc: bbufuncs.bfield, validator: vtype, re_validate: lre};
            }
            else if(edecl.specialDecls.has(MIRSpecialTypeCategory.TypeDeclNumeric)) {
                const oftype = (edecl.specialTemplateInfo as {tname: string, tkind: MIRResolvedTypeKey}[])[0].tkind;
                //
                //TODO: we are dropping the invariant call info here ... we need to get it here, and probably, some other places
                //

                return {tag: APIEmitTypeTag.NumberOfTag, ...this.getJSONApiStd(tt), boxfunc: bbufuncs.box, unboxfunc: bbufuncs.bfield, primitive: oftype, oftype: oftype, smtinvcall: null, cppinvcall: null};
            }
            else if(edecl.specialDecls.has(MIRSpecialTypeCategory.DataStringDecl)) {
                const oftype = (edecl.specialTemplateInfo as {tname: string, tkind: MIRResolvedTypeKey}[])[0].tkind;
                const ofdecl = (this.assembly.entityDecls.get(oftype) || this.assembly.conceptDecls.get(oftype)) as MIROOTypeDecl; 
                const sdecl = this.assembly.invokeDecls.get(`${oftype}::parse`) as MIRInvokeDecl;
                
                const isvalue = ofdecl.attributes.includes("struct");

                return {tag: APIEmitTypeTag.DataStringTag, ...this.getJSONApiStd(tt), boxfunc: bbufuncs.box, unboxfunc: bbufuncs.bfield, oftype: oftype, isvalue: isvalue, smtinvcall: this.mangle(sdecl.key), cppinvcall: sdecl.key};
            }
            else if(edecl.specialDecls.has(MIRSpecialTypeCategory.BufferDecl)) {
                return {tag: APIEmitTypeTag.BufferTag, ...this.getJSONApiStd(tt), boxfunc: bbufuncs.box, unboxfunc: bbufuncs.bfield};
            }
            else if(edecl.specialDecls.has(MIRSpecialTypeCategory.DataBufferDecl)) {
                return {tag: APIEmitTypeTag.DataBufferTag, ...this.getJSONApiStd(tt), boxfunc: bbufuncs.box, unboxfunc: bbufuncs.bfield};
            }
            else if(edecl.specialDecls.has(MIRSpecialTypeCategory.ListTypeDecl)) {
                const ltype = this.getSMTTypeFor(tt);
                const oftype = (edecl.specialTemplateInfo as {tname: string, tkind: MIRResolvedTypeKey}[])[0].tkind;

                const smtsize = `${ltype.name}@size`;
                const smtget = `_@@desop_${ltype.name}_get`;

                let smtconsfunc_k: string[] = [];
                for(let i = 1; i <= 3; ++i) {
                    smtconsfunc_k.push(`_@@cons_${ltype.name}__${i}`);
                }

                return {tag: APIEmitTypeTag.ListTag, ...this.getJSONApiStd(tt), boxfunc: bbufuncs.box, unboxfunc: bbufuncs.bfield, oftype: oftype, smtsizefunc: smtsize, smtgetfunc: smtget, smtconsfunc_k: smtconsfunc_k};
            }
            else {
                const oftype = (edecl.specialTemplateInfo as {tname: string, tkind: MIRResolvedTypeKey}[])[0].tkind;
                const smttagfunc = this.mangle(`${tt.trkey}::nameof`);
                const smtselectfunc = "[UNDEF_SELECT]";
                
                const ddcls = [...this.assembly.constantDecls].filter((cdcl) => cdcl[1].enclosingDecl !== undefined && cdcl[1].enclosingDecl === tt.trkey);
                const enuminvs = ddcls.map((cdcl) => [cdcl[1].gkey, this.mangle(cdcl[1].value)] as [string, string]);
                            

                return {tag: APIEmitTypeTag.EnumTag, ...this.getJSONApiStd(tt), boxfunc: bbufuncs.box, unboxfunc: bbufuncs.bfield, underlying: oftype, smttagfunc, smtselectfunc: smtselectfunc, enuminvs: enuminvs};
            }
        }
        else {
            const smttype = this.getSMTTypeFor(tt);
            const opts: string[] = tt.options.map((opt) => tt.trkey);
            
            return {tag: APIEmitTypeTag.EnumTag, ...this.getJSONApiBase(tt), iskey: smttype.isGeneralKeyType(), opts: opts};
        }
    }
}

export {
    SMTTypeEmitter
};
