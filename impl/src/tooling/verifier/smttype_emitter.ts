//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRConceptType, MIRConstructableEntityTypeDecl, MIRConstructableInternalEntityTypeDecl, MIREntityType, MIREntityTypeDecl, MIREnumEntityTypeDecl, MIREphemeralListType, MIRFieldDecl, MIRInternalEntityTypeDecl, MIRObjectEntityTypeDecl, MIRPrimitiveCollectionEntityTypeDecl, MIRPrimitiveInternalEntityTypeDecl, MIRPrimitiveListEntityTypeDecl, MIRPrimitiveMapEntityTypeDecl, MIRPrimitiveQueueEntityTypeDecl, MIRPrimitiveSetEntityTypeDecl, MIRPrimitiveStackEntityTypeDecl, MIRRecordType, MIRTupleType, MIRType } from "../../compiler/mir_assembly";
import { MIRGlobalKey, MIRInvokeKey, MIRResolvedTypeKey } from "../../compiler/mir_ops";
import { SMTCallGeneral, SMTCallSimple, SMTConst, SMTExp, SMTType, VerifierOptions } from "./smt_exp";

import * as assert from "assert";
import { BSQRegex } from "../../ast/bsqregex";

enum APIEmitTypeTag
{
    NoneTag = 0x0,
    NothingTag,
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
    PrimitiveOfTag,
    DataStringTag,
    ByteBufferTag,
    BufferOfTag,
    DataBufferTag,
    ISOTag,
    LogicalTag,
    UUIDTag,
    ContentHashTag,
    TupleTag,
    RecordTag,
    SomethingTag,
    OkTag,
    ErrTag,
    ListTag,
    StackTag,
    QueueTag,
    SetTag,
    MapTag,
    EnumTag,
    EntityTag,
    UnionTag,
    ConceptTag
};

class SMTTypeEmitter {
    readonly assembly: MIRAssembly;
    readonly vopts: VerifierOptions;

    private namectr: number = 0;
    private mangledTypeNameMap: Map<string, string> = new Map<string, string>();
    private mangledFunctionNameMap: Map<string, string> = new Map<string, string>();
    private mangledGlobalNameMap: Map<string, string> = new Map<string, string>();

    constructor(assembly: MIRAssembly, vopts: VerifierOptions, namectr?: number, mangledTypeNameMap?: Map<string, string>, mangledFunctionNameMap?: Map<string, string>, mangledGlobalNameMap?: Map<string, string>) {
        this.assembly = assembly;
        this.vopts = vopts;

        this.namectr = namectr || 0;
        this.mangledTypeNameMap = mangledTypeNameMap || new Map<string, string>();
        this.mangledFunctionNameMap = mangledFunctionNameMap || new Map<string, string>();
        this.mangledGlobalNameMap = mangledGlobalNameMap || new Map<string, string>();
    }

    internTypeName(keyid: MIRResolvedTypeKey, shortname: string) {
        if (!this.mangledTypeNameMap.has(keyid)) {
            const cleanname = shortname.replace(/[<>, \[\]:]/g, "_") + "$" + this.namectr++;
            this.mangledTypeNameMap.set(keyid, cleanname);
        }
    }

    lookupTypeName(keyid: MIRResolvedTypeKey): string {
        assert(this.mangledTypeNameMap.has(keyid));

        return this.mangledTypeNameMap.get(keyid) as string;
    }

    internFunctionName(keyid: MIRInvokeKey, shortname: string) {
        if (!this.mangledFunctionNameMap.has(keyid)) {
            const cleanname = shortname.replace(/[<>, \[\]:]/g, "_") + "$" + this.namectr++;
            this.mangledFunctionNameMap.set(keyid, cleanname);
        }
    }

    lookupFunctionName(keyid: MIRInvokeKey): string {
        assert(this.mangledFunctionNameMap.has(keyid));

        return this.mangledFunctionNameMap.get(keyid) as string;
    }

    internGlobalName(keyid: MIRGlobalKey, shortname: string) {
        if (!this.mangledGlobalNameMap.has(keyid)) {
            const cleanname = shortname.replace(/[<>, \[\]:]/g, "_") + "$" + this.namectr++;
            this.mangledGlobalNameMap.set(keyid, cleanname);
        }
    }

    lookupGlobalName(keyid: MIRGlobalKey): string {
        assert(this.mangledGlobalNameMap.has(keyid));

        return this.mangledGlobalNameMap.get(keyid) as string;
    }

    getMIRType(tkey: MIRResolvedTypeKey): MIRType {
        return this.assembly.typeMap.get(tkey) as MIRType;
    }

    isType(tt: MIRType, tkey: MIRResolvedTypeKey): boolean {
        return tt.typeID === tkey;
    }

    isUniqueTupleType(tt: MIRType): boolean {
        return tt.options.length === 1 && (tt.options[0] instanceof MIRTupleType);
    }

    isUniqueRecordType(tt: MIRType): boolean {
        return tt.options.length === 1 && (tt.options[0] instanceof MIRRecordType);
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

    private getSMTTypeForEntity(tt: MIRType, entity: MIREntityTypeDecl): SMTType {
        if(entity instanceof MIRInternalEntityTypeDecl) {
            if(entity instanceof MIRPrimitiveInternalEntityTypeDecl) {
                if (this.isType(tt, "NSCore::None")) {
                    return new SMTType("bsq_none", "TypeTag_None", entity.tkey);
                }
                else if (this.isType(tt, "NSCore::Nothing")) {
                    return new SMTType("bsq_nothing", "TypeTag_Nothing", entity.tkey);
                }
                else if (this.isType(tt, "NSCore::Bool")) {
                    return new SMTType("Bool", "TypeTag_Bool", entity.tkey);
                }
                else if (this.isType(tt, "NSCore::Int")) {
                    return new SMTType("BInt", "TypeTag_Int", entity.tkey);
                }
                else if (this.isType(tt, "NSCore::Nat")) {
                    return new SMTType("BNat", "TypeTag_Nat", entity.tkey);
                }
                else if (this.isType(tt, "NSCore::BigInt")) {
                    return new SMTType("BBigInt", "TypeTag_BigInt", entity.tkey);
                }
                else if (this.isType(tt, "NSCore::BigNat")) {
                    return new SMTType("BBigNat", "TypeTag_BigInt", entity.tkey);
                }
                else if (this.isType(tt, "NSCore::Float")) {
                    return new SMTType("BFloat", "TypeTag_Float", entity.tkey);
                }
                else if (this.isType(tt, "NSCore::Decimal")) {
                    return new SMTType("BDecimal", "TypeTag_Decimal", entity.tkey);
                }
                else if (this.isType(tt, "NSCore::Rational")) {
                    return new SMTType("BRational", "TypeTag_Rational", entity.tkey);
                }
                else if (this.isType(tt, "NSCore::StringPos")) {
                    return new SMTType("BStringPos", "TypeTag_StringPos", entity.tkey);
                }
                else if (this.isType(tt, "NSCore::String")) {
                    return new SMTType("BString", "TypeTag_String", entity.tkey);
                }
                else if (tt.typeID.startsWith("NSCore::ByteBuffer")) {
                    return new SMTType("BByteBuffer", "TypeTag_ByteBuffer", entity.tkey);
                }
                else if(this.isType(tt, "NSCore::ISOTime")) {
                    return new SMTType("BISOTime", "TypeTag_ISOTime", entity.tkey);
                }
                else if(this.isType(tt, "NSCore::LogicalTime")) {
                    return new SMTType("BLogicalTime", "TypeTag_LogicalTime", entity.tkey);
                }
                else if(this.isType(tt, "NSCore::UUID")) {
                    return new SMTType("BUUID", "TypeTag_UUID", entity.tkey);
                }
                else if(this.isType(tt, "NSCore::ContentHash")) {
                    return new SMTType("BHash", "TypeTag_ContentHash", entity.tkey);
                }
                else if(this.isType(tt, "NSCore::Regex")) {
                    return new SMTType("bsq_regex", "TypeTag_Regex", entity.tkey);
                }
                else if (this.isType(tt, "NSCore::ISequence")) {
                    return new SMTType("ISequence", "TypeTag_ISequence", entity.tkey);
                }
                else if (this.isType(tt, "NSCore::JSequence")) {
                    return new SMTType("JSequence", "TypeTag_JSequence", entity.tkey);
                }
                else if (this.isType(tt, "NSCore::SSequence")) {
                    return new SMTType("SSequence", "TypeTag_SSequence", entity.tkey);
                }
                else if (this.isType(tt, "NSCore::HavocSequence")) {
                    return new SMTType("HavocSequence", "TypeTag_HavocSequence", entity.tkey);
                }
                else {
                    assert(false);
                    return new SMTType("[UNKNOWN MIRPrimitiveInternalEntityTypeDecl]", "[UNKNOWN]", entity.tkey);
                }
            }
            else if (entity instanceof MIRConstructableInternalEntityTypeDecl) {
                if (tt.typeID.startsWith("NSCore::StringOf")) {
                    return new SMTType("BString", `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
                }
                else if (tt.typeID.startsWith("NSCore::DataString")) {
                    return new SMTType("BString", `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
                }
                else if (tt.typeID.startsWith("NSCore::BufferOf")) {
                    return new SMTType("BByteBuffer", `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
                }
                else if (tt.typeID.startsWith("NSCore::DataBuffer")) {
                    return new SMTType("BByteBuffer", `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
                }
                else if (tt.typeID.startsWith("NSCore::Something")) {
                    const sof = this.getSMTTypeFor(this.getMIRType(entity.fromtype as MIRResolvedTypeKey));
                    return new SMTType(sof.name, `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
                }
                else if (tt.typeID.startsWith("NSCore::Result::Ok")) {
                    const sof = this.getSMTTypeFor(this.getMIRType(entity.fromtype as MIRResolvedTypeKey));
                    return new SMTType(sof.name, `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
                }
                else {
                    assert(tt.typeID.startsWith("NSCore::Result::Err"));
                    const sof = this.getSMTTypeFor(this.getMIRType(entity.fromtype as MIRResolvedTypeKey));
                    return new SMTType(sof.name, `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
                }
            }
            else {
                assert(entity instanceof MIRPrimitiveCollectionEntityTypeDecl);

                return new SMTType(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
            }
        }
        else if (entity instanceof MIRConstructableEntityTypeDecl) {
            const sof = this.getSMTTypeFor(this.getMIRType(entity.fromtype as MIRResolvedTypeKey));
            return new SMTType(sof.name, `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
        }
        else if (entity instanceof MIREnumEntityTypeDecl) {
            const sof = this.getSMTTypeFor(this.getMIRType("NSCore::Nat"));
            return new SMTType(sof.name, `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
        }
        else {
            return new SMTType(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
        }
    }

    getSMTTypeFor(tt: MIRType): SMTType {
        this.internTypeName(tt.typeID, tt.shortname);

        if(this.isUniqueTupleType(tt)) {
            return new SMTType(this.lookupTypeName(tt.typeID), `TypeTag_${this.lookupTypeName(tt.typeID)}`, tt.typeID);
        }
        else if(this.isUniqueRecordType(tt)) {
            return new SMTType(this.lookupTypeName(tt.typeID), `TypeTag_${this.lookupTypeName(tt.typeID)}`, tt.typeID);
        }
        else if(this.isUniqueEntityType(tt)) {
            return this.getSMTTypeForEntity(tt, this.assembly.entityDecls.get(tt.typeID) as MIREntityTypeDecl);
        }
        else if (this.isUniqueEphemeralType(tt)) {
            return new SMTType(this.lookupTypeName(tt.typeID), `TypeTag_${this.lookupTypeName(tt.typeID)}`, tt.typeID);
        }
        else if(this.assembly.subtypeOf(tt, this.getMIRType("NSCore::KeyType"))) {
            return new SMTType("BKey", "[BKEY]", tt.typeID);
        }
        else {
            return new SMTType("BTerm", "[BTERM]", tt.typeID);
        }
    }

    getSMTConstructorName(tt: MIRType): { cons: string, box: string, bfield: string } {
        assert(tt.options.length === 0);
        this.internTypeName(tt.typeID, tt.shortname);

        const kfix = this.assembly.subtypeOf(tt, this.getMIRType("NSCore::KeyType")) ? "bsqkey_" : "bsqobject_"
        if (this.isUniqueTupleType(tt)) {
            return { cons: `${this.lookupTypeName(tt.typeID)}@cons`, box: `${this.lookupTypeName(tt.typeID)}@box`, bfield: `${kfix}${this.lookupTypeName(tt.typeID)}_value` };
        }
        else if (this.isUniqueRecordType(tt)) {
            return { cons: `${this.lookupTypeName(tt.typeID)}@cons`, box: `${this.lookupTypeName(tt.typeID)}@box`, bfield: `${kfix}${this.lookupTypeName(tt.typeID)}_value` };
        }
        else if (this.isUniqueEntityType(tt)) {
            assert(!(this.assembly.entityDecls.get(tt.typeID) instanceof MIRInternalEntityTypeDecl));

            return { cons: `${this.lookupTypeName(tt.typeID)}@cons`, box: `${this.lookupTypeName(tt.typeID)}@box`, bfield: `${kfix}${this.lookupTypeName(tt.typeID)}_value` };
        }
        else {
            assert(this.isUniqueEphemeralType(tt), "should not be other options")
            return { cons: `${this.lookupTypeName(tt.typeID)}@cons`, box: "[UNDEF_EPHEMERAL_BOX]", bfield: "[UNDEF_EPHEMERAL_BOX]" };
        }
    }

    private coerceFromAtomicToKey(exp: SMTExp, from: MIRType): SMTExp  {
        assert(this.assembly.subtypeOf(from, this.getMIRType("NSCore::KeyType")));

        if (from.typeID === "NSCore::None") {
            return new SMTConst("BKey@none");
        }
        else if(from.typeID === "NSCore::Nothing") {
            return new SMTConst("BKey@nothing");
        }
        else {
            const smtfrom = this.getSMTTypeFor(from);
            let objval: SMTExp | undefined = undefined;

            if (this.isType(from, "NSCore::Bool")) {
                objval = new SMTCallSimple("bsqkey_bool@box", [exp]);
            }
            else if (this.isType(from, "NSCore::Int")) {
                objval = new SMTCallSimple("bsqkey_int@box", [exp]);
            }
            else if (this.isType(from, "NSCore::Nat")) {
                objval = new SMTCallSimple("bsqkey_nat@box", [exp]);
            }
            else if (this.isType(from, "NSCore::BigInt")) {
                objval = new SMTCallSimple("bsqkey_bigint@box", [exp]);
            }
            else if (this.isType(from, "NSCore::BigNat")) {
                objval = new SMTCallSimple("bsqkey_bignat@box", [exp]);
            }
            else if (this.isType(from, "NSCore::String")) {
                objval = new SMTCallSimple("bsqkey_string@box", [exp]);
            }
            else if(this.isType(from, "NSCore::LogicalTime")) {
                objval = new SMTCallSimple("bsqkey_logicaltime@box", [exp]);
            }
            else if(this.isType(from, "NSCore::UUID")) {
                objval = new SMTCallSimple("bsqkey_uuid@box", [exp]);
            }
            else if(this.isType(from, "NSCore::ContentHash")) {
                objval = new SMTCallSimple("bsqkey_contenthash@box", [exp]);
            }
            else {
                assert(this.isUniqueEntityType(from));

                objval = new SMTCallSimple(this.getSMTConstructorName(from).box, [exp]);
            }

            return new SMTCallSimple("BKey@box", [new SMTConst(smtfrom.smttypetag), objval as SMTExp]);
        }
    }

    private coerceFromAtomicToTerm(exp: SMTExp, from: MIRType): SMTExp {
        if (from.typeID === "NSCore::None") {
            return new SMTConst(`BTerm@none`);
        }
        else if (from.typeID === "NSCore::None") {
            return new SMTConst(`BTerm@nothing`);
        }
        else {
            if(this.assembly.subtypeOf(from, this.getMIRType("NSCore::KeyType"))) {
                return new SMTCallSimple("BTerm@keybox", [this.coerceFromAtomicToKey(exp, from)]);
            }
            else {
                const smtfrom = this.getSMTTypeFor(from);
                let objval: SMTExp | undefined = undefined;

                if (this.isType(from, "NSCore::Float")) {
                    objval = new SMTCallSimple("bsq_float@box", [exp]);
                }
                else if (this.isType(from, "NSCore::Decimal")) {
                    objval = new SMTCallSimple("bsq_decimal@box", [exp]);
                }
                else if (this.isType(from, "NSCore::Rational")) {
                    objval = new SMTCallSimple("bsq_rational@box", [exp]);
                }
                else if (this.isType(from, "NSCore::StringPos")) {
                    objval = new SMTCallSimple("bsq_stringpos@box", [exp]);
                }
                else if (this.isType(from, "NSCore::ByteBuffer")) {
                    objval = new SMTCallSimple("bsq_bytebuffer@box", [exp]);
                }
                else if(this.isType(from, "NSCore::ISOTime")) {
                    objval = new SMTCallSimple("bsq_isotime@box", [exp]);
                }
                else if (this.isType(from, "NSCore::Regex")) {
                    objval = new SMTCallSimple("bsq_regex@box", [exp]);
                }
                else if (this.isUniqueTupleType(from)) {
                    objval = new SMTCallSimple(this.getSMTConstructorName(from).box, [exp]);
                }
                else if (this.isUniqueRecordType(from)) {
                    objval = new SMTCallSimple(this.getSMTConstructorName(from).box, [exp]);
                }
                else {
                    assert(this.isUniqueEntityType(from));

                    objval = new SMTCallSimple(this.getSMTConstructorName(from).box, [exp]);
                }

                return new SMTCallSimple("BTerm@termbox", [new SMTConst(smtfrom.smttypetag), objval as SMTExp]);
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
        this.internTypeName(tt.typeID, tt.shortname);
        return `${this.lookupTypeName(tt.typeID)}@_${idx}`;
    } 

    generateRecordPropertyGetFunction(tt: MIRRecordType, pname: string): string {
        this.internTypeName(tt.typeID, tt.shortname);
        return `${this.lookupTypeName(tt.typeID)}@_${pname}`;
    }

    generateEntityFieldGetFunction(tt: MIREntityTypeDecl, field: MIRFieldDecl): string {
        this.internTypeName(tt.tkey, tt.shortname);
        return `${this.lookupTypeName(tt.tkey)}@_${field.fname}`;
    }

    generateEphemeralListGetFunction(tt: MIREphemeralListType, idx: number): string {
        this.internTypeName(tt.typeID, tt.shortname);
        return `${this.lookupTypeName(tt.typeID)}@_${idx}`;
    }

    generateResultType(ttype: MIRType): SMTType {
        return new SMTType(`$Result_${this.getSMTTypeFor(ttype).name}`, "[INTERNAL RESULT]", "[INTERNAL RESULT]");
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
        return new SMTType(`$GuardResult_${this.getSMTTypeFor(ttype).name}`, "[INTERNAL GUARD RESULT]", "[INTERNAL GUARD RESULT]");
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
            return ["bsq_none@literal", false];
        }
        else if (this.isType(tt, "NSCore::Nothing")) {
            return ["bsq_nothing@literal", false];
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
        else if (this.isType(tt, "NSCore::Float")) {
            return ["BFloat@UFCons_API", false];
        }
        else if (this.isType(tt, "NSCore::Decimal")) {
            return ["BDecimal@UFCons_API", false];
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
        return new SMTCallSimple("seq.++", [path, new SMTCallSimple("seq.unit", [step])]);
    }

    generateHavocConstructorCall(tt: MIRType, path: SMTExp, step: SMTExp): SMTExp {
        if(this.isKnownSafeHavocConstructorType(tt)) {
            return this.generateResultTypeConstructorSuccess(tt, new SMTCallSimple(this.generateHavocConstructorName(tt), [this.generateHavocConstructorPathExtend(path, step)]));
        }
        else {
            return new SMTCallGeneral(this.generateHavocConstructorName(tt), [this.generateHavocConstructorPathExtend(path, step)]);
        }
    }

    private getAPITypeForEntity(tt: MIRType, entity: MIREntityTypeDecl): object {
        if(entity instanceof MIRInternalEntityTypeDecl) {
            if(entity instanceof MIRPrimitiveInternalEntityTypeDecl) {
                if (this.isType(tt, "NSCore::None")) {
                    return {tag: APIEmitTypeTag.NoneTag, name: tt.typeID};
                }
                else if (this.isType(tt, "NSCore::Nothing")) {
                    return {tag: APIEmitTypeTag.NothingTag, name: tt.typeID};
                }
                else if (this.isType(tt, "NSCore::Bool")) {
                    return {tag: APIEmitTypeTag.BoolTag, name: tt.typeID};
                }
                else if (this.isType(tt, "NSCore::Int")) {
                    return {tag: APIEmitTypeTag.IntTag, name: tt.typeID};
                }
                else if (this.isType(tt, "NSCore::Nat")) {
                    return {tag: APIEmitTypeTag.NatTag, name: tt.typeID};
                }
                else if (this.isType(tt, "NSCore::BigInt")) {
                    return {tag: APIEmitTypeTag.BigIntTag, name: tt.typeID};
                }
                else if (this.isType(tt, "NSCore::BigNat")) {
                    return {tag: APIEmitTypeTag.BigNatTag, name: tt.typeID};
                }
                else if (this.isType(tt, "NSCore::Float")) {
                    return {tag: APIEmitTypeTag.FloatTag, name: tt.typeID};
                }
                else if (this.isType(tt, "NSCore::Decimal")) {
                    return {tag: APIEmitTypeTag.DecimalTag, name: tt.typeID};
                }
                else if (this.isType(tt, "NSCore::Rational")) {
                    return {tag: APIEmitTypeTag.RationalTag, name: tt.typeID};
                }
                else if (this.isType(tt, "NSCore::String")) {
                    return {tag: APIEmitTypeTag.StringTag, name: tt.typeID};
                }
                else if (this.isType(tt, "NSCore::ByteBuffer")) {
                    return {tag: APIEmitTypeTag.ByteBufferTag, name: tt.typeID};
                }
                else if(this.isType(tt, "NSCore::ISOTime")) {
                    return {tag: APIEmitTypeTag.ISOTag, name: tt.typeID};
                }
                else if(this.isType(tt, "NSCore::LogicalTime")) {
                    return {tag: APIEmitTypeTag.LogicalTag, name: tt.typeID};
                }
                else if(this.isType(tt, "NSCore::UUID")) {
                    return {tag: APIEmitTypeTag.UUIDTag, name: tt.typeID};
                }
                else if(this.isType(tt, "NSCore::ContentHash")) {
                    return {tag: APIEmitTypeTag.ContentHashTag, name: tt.typeID};
                }
                else {
                    assert(false);
                    return {tag: APIEmitTypeTag.NoneTag, name: "[UNKNOWN API TYPE]"};
                }
            }
            else if (entity instanceof MIRConstructableInternalEntityTypeDecl) {
                if (tt.typeID.startsWith("NSCore::StringOf")) {
                    const vre = this.assembly.validatorRegexs.get(entity.fromtype as MIRResolvedTypeKey) as BSQRegex;
                    return {tag: APIEmitTypeTag.StringOfTag, name: tt.typeID, oftype: (entity.fromtype as MIRResolvedTypeKey), re_validate: vre.jemit()};
                }
                else if (tt.typeID.startsWith("NSCore::DataString")) {
                    return {tag: APIEmitTypeTag.DataStringTag, name: tt.typeID, oftype: (entity.fromtype as MIRResolvedTypeKey)};
                }
                else if (tt.typeID.startsWith("NSCore::BufferOf")) {
                    return {tag: APIEmitTypeTag.BufferOfTag, name: tt.typeID, oftype: (entity.fromtype as MIRResolvedTypeKey)};
                }
                else if (tt.typeID.startsWith("NSCore::DataBuffer")) {
                    return {tag: APIEmitTypeTag.DataBufferTag, name: tt.typeID, oftype: (entity.fromtype as MIRResolvedTypeKey)};
                }
                else if (tt.typeID.startsWith("NSCore::Something")) {
                    return {tag: APIEmitTypeTag.SomethingTag, name: tt.typeID, oftype: (entity.fromtype as MIRResolvedTypeKey)};
                }
                else if (tt.typeID.startsWith("NSCore::Result::Ok")) {
                    return {tag: APIEmitTypeTag.OkTag, name: tt.typeID, oftype: (entity.fromtype as MIRResolvedTypeKey)};
                }
                else {
                    assert(tt.typeID.startsWith("NSCore::Result::Err"));
                    return {tag: APIEmitTypeTag.ErrTag, name: tt.typeID, oftype: (entity.fromtype as MIRResolvedTypeKey)};
                }
            }
            else {
                assert(entity instanceof MIRPrimitiveCollectionEntityTypeDecl);

                if(entity instanceof MIRPrimitiveListEntityTypeDecl) {
                    return {tag: APIEmitTypeTag.ListTag, name: tt.typeID, oftype: entity.oftype};
                }
                else if(entity instanceof MIRPrimitiveStackEntityTypeDecl) {
                    return {tag: APIEmitTypeTag.StackTag, name: tt.typeID, oftype: entity.oftype, ultype: entity.ultype};
                }
                else if(entity instanceof MIRPrimitiveQueueEntityTypeDecl) {
                    return {tag: APIEmitTypeTag.QueueTag, name: tt.typeID, oftype: entity.oftype, ultype: entity.ultype};
                }
                else if(entity instanceof MIRPrimitiveSetEntityTypeDecl) {
                    return {tag: APIEmitTypeTag.SetTag, name: tt.typeID, oftype: entity.oftype, ultype: entity.ultype, unqchkinv: entity.unqchkinv, unqconvinv: entity.unqconvinv};
                }
                else {
                    const mentity = entity as MIRPrimitiveMapEntityTypeDecl;
                    return {tag: APIEmitTypeTag.MapTag, name: tt.typeID, oftype: mentity.oftype, ultype: mentity.ultype, unqchkinv: mentity.unqchkinv};
                }
            }
        }
        else if(entity instanceof MIRConstructableEntityTypeDecl) {
            return {tag: APIEmitTypeTag.PrimitiveOfTag, name: tt.typeID, oftype: entity.fromtype, usinginv: entity.usingcons};
        }
        else if(entity instanceof MIREnumEntityTypeDecl) {
            return {tag: APIEmitTypeTag.EnumTag, name: tt.typeID, usinginv: entity.usingcons, enums: entity.enums};
        }
        else {
            const oentity = entity as MIRObjectEntityTypeDecl;
            
            let fields: string[] = [];
            let ttypes: string[] = [];
            for(let i = 0; i < oentity.consfuncfields.length; ++i)
            {
                const ff = oentity.consfuncfields[i];
                const mirtt = this.assembly.fieldDecls.get(ff) as MIRFieldDecl;

                fields.push(ff);
                ttypes.push(mirtt.declaredType);
            }

            return {tag: APIEmitTypeTag.EntityTag, name: tt.typeID, fields: fields, ttypes: ttypes};
        }
    }

    getAPITypeFor(tt: MIRType): object {
        this.internTypeName(tt.typeID, tt.shortname);

        if(this.isUniqueTupleType(tt)) {
            const tdecl = this.assembly.tupleDecls.get(tt.typeID) as MIRTupleType;

            let ttypes: string[] = [];
            for(let i = 0; i < tdecl.entries.length; ++i)
            {
                const mirtt = tdecl.entries[i];
                ttypes.push(mirtt.typeID);
            }

            return {tag: APIEmitTypeTag.TupleTag, name: tt.typeID, ttypes: ttypes};
        }
        else if(this.isUniqueRecordType(tt)) {
            const rdecl = this.assembly.recordDecls.get(tt.typeID) as MIRRecordType;

            let props: string[] = [];
            let ttypes: string[] = [];
            for(let i = 0; i < rdecl.entries.length; ++i)
            {
                const prop = rdecl.entries[i].pname;
                const mirtt = rdecl.entries[i].ptype;

                props.push(prop);
                ttypes.push(mirtt.typeID);
            }

            return {tag: APIEmitTypeTag.RecordTag, name: tt.typeID, props: props, ttypes: ttypes};
        }
        else if(this.isUniqueEntityType(tt)) {
            return this.getAPITypeForEntity(tt, this.assembly.entityDecls.get(tt.typeID) as MIREntityTypeDecl);
        }
        else if(tt instanceof MIRConceptType) {
            const etypes = [...this.assembly.entityDecls].filter((edi) => this.assembly.subtypeOf(this.getMIRType(edi[1].tkey), this.getMIRType(tt.typeID)));
            const opts: string[] = etypes.map((opt) => opt[1].tkey);

            return {tag: APIEmitTypeTag.ConceptTag, name: tt.typeID, opts: opts};
        }
        else {
            const opts: string[] = tt.options.map((opt) => opt.typeID);
            
            return {tag: APIEmitTypeTag.UnionTag, name: tt.typeID, opts: opts};
        }
    }
}

export {
    SMTTypeEmitter
};
