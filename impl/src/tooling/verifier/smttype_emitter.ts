//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRConceptType, MIRConstructableEntityTypeDecl, MIRConstructableInternalEntityTypeDecl, MIREntityType, MIREntityTypeDecl, MIREnumEntityTypeDecl, MIREphemeralListType, MIRFieldDecl, MIRHavocEntityTypeDecl, MIRInternalEntityTypeDecl, MIRObjectEntityTypeDecl, MIRPrimitiveCollectionEntityTypeDecl, MIRPrimitiveInternalEntityTypeDecl, MIRPrimitiveListEntityTypeDecl, MIRPrimitiveMapEntityTypeDecl, MIRPrimitiveQueueEntityTypeDecl, MIRPrimitiveSetEntityTypeDecl, MIRPrimitiveStackEntityTypeDecl, MIRRecordType, MIRTupleType, MIRType } from "../../compiler/mir_assembly";
import { MIRGlobalKey, MIRInvokeKey, MIRResolvedTypeKey } from "../../compiler/mir_ops";
import { SMTCallGeneral, SMTCallSimple, SMTConst, SMTExp, SMTTypeInfo, VerifierOptions } from "./smt_exp";

import * as assert from "assert";

class SMTTypeEmitter {
    readonly assembly: MIRAssembly;
    readonly vopts: VerifierOptions;

    private namectr: number = 0;
    private allshortnames = new Set<string>();
    private mangledTypeNameMap: Map<string, string> = new Map<string, string>();
    private mangledFunctionNameMap: Map<string, string> = new Map<string, string>();
    private mangledGlobalNameMap: Map<string, string> = new Map<string, string>();

    private typeDataMap: Map<MIRResolvedTypeKey, SMTTypeInfo> = new Map<MIRResolvedTypeKey, SMTTypeInfo>();

    constructor(assembly: MIRAssembly, vopts: VerifierOptions, namectr?: number, mangledTypeNameMap?: Map<string, string>, mangledFunctionNameMap?: Map<string, string>, mangledGlobalNameMap?: Map<string, string>) {
        this.assembly = assembly;
        this.vopts = vopts;

        this.namectr = namectr || 0;
        this.mangledTypeNameMap = mangledTypeNameMap || new Map<string, string>();
        this.mangledFunctionNameMap = mangledFunctionNameMap || new Map<string, string>();
        this.mangledGlobalNameMap = mangledGlobalNameMap || new Map<string, string>();

        this.allshortnames = new Set<string>();
        this.mangledTypeNameMap.forEach((sn) => this.allshortnames.add(sn));
        this.mangledFunctionNameMap.forEach((sn) => this.allshortnames.add(sn));
        this.mangledGlobalNameMap.forEach((sn) => this.allshortnames.add(sn));
    }

    internTypeName(keyid: MIRResolvedTypeKey) {
        if (!this.mangledTypeNameMap.has(keyid)) {
            let cleanname = keyid.replace(/:/g, ".").replace(/[<>, \[\]\{\}\(\)\\\/\#\=\|]/g, "_");
            if(this.allshortnames.has(cleanname)) {
                cleanname = cleanname + "$" + this.namectr++;
            }

            this.mangledTypeNameMap.set(keyid, cleanname);
            this.allshortnames.add(cleanname);
        }
    }

    lookupTypeName(keyid: MIRResolvedTypeKey): string {
        assert(this.mangledTypeNameMap.has(keyid));

        return this.mangledTypeNameMap.get(keyid) as string;
    }

    internFunctionName(keyid: MIRInvokeKey, shortname: string) {
        if (!this.mangledFunctionNameMap.has(keyid)) {
            let cleanname = shortname.replace(/:/g, ".").replace(/[<>, \[\]\{\}\(\)\\\/\#\=\|]/g, "_");
            if(this.allshortnames.has(cleanname)) {
                cleanname = cleanname + "$" + this.namectr++;
            }

            this.mangledFunctionNameMap.set(keyid, cleanname);
            this.allshortnames.add(cleanname);
        }
    }

    lookupFunctionName(keyid: MIRInvokeKey): string {
        assert(this.mangledFunctionNameMap.has(keyid), `Missing -- ${keyid}`);

        return this.mangledFunctionNameMap.get(keyid) as string;
    }

    internGlobalName(keyid: MIRGlobalKey, shortname: string) {
        if (!this.mangledGlobalNameMap.has(keyid)) {
            let cleanname = shortname.replace(/:/g, ".").replace(/[<>, \[\]\{\}\(\)\\\/\#\=\|]/g, "_");
            if(this.allshortnames.has(cleanname)) {
                cleanname = cleanname + "$" + this.namectr++;
            }

            this.mangledGlobalNameMap.set(keyid, cleanname);
            this.allshortnames.add(cleanname);
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

    getSMTTypeFor(tt: MIRType): SMTTypeInfo {
        if(this.typeDataMap.has(tt.typeID)) {
            return this.typeDataMap.get(tt.typeID) as SMTTypeInfo;
        }

        this.internTypeName(tt.typeID);
        if(this.isUniqueTupleType(tt)) {
            return new SMTTypeInfo(this.lookupTypeName(tt.typeID), `TypeTag_${this.lookupTypeName(tt.typeID)}`, tt.typeID);
        }
        else if(this.isUniqueRecordType(tt)) {
            return new SMTTypeInfo(this.lookupTypeName(tt.typeID), `TypeTag_${this.lookupTypeName(tt.typeID)}`, tt.typeID);
        }
        else if(this.isUniqueEntityType(tt)) {
            return this.getSMTTypeInfoForEntity(tt, this.assembly.entityDecls.get(tt.typeID) as MIREntityTypeDecl);
        }
        else if (this.isUniqueEphemeralType(tt)) {
            return new SMTTypeInfo(this.lookupTypeName(tt.typeID), `TypeTag_${this.lookupTypeName(tt.typeID)}`, tt.typeID);
        }
        else if(this.assembly.subtypeOf(tt, this.getMIRType("KeyType"))) {
            return new SMTType("BKey", "[BKEY]", tt.typeID);
        }
        else {
            return new SMTType("BTerm", "[BTERM]", tt.typeID);
        }
    }

    private getSMTTypeInfoForEntity(tt: MIRType, entity: MIREntityTypeDecl): SMTTypeInfo {
        if(entity instanceof MIRInternalEntityTypeDecl) {
            if(entity instanceof MIRPrimitiveInternalEntityTypeDecl) {
                if (this.isType(tt, "None")) {
                    return new SMTTypeInfo("bsq_none", "TypeTag_None", entity.tkey);
                }
                else if (this.isType(tt, "Nothing")) {
                    return new SMTTypeInfo("bsq_nothing", "TypeTag_Nothing", entity.tkey);
                }
                else if (this.isType(tt, "Bool")) {
                    return new SMTTypeInfo("Bool", "TypeTag_Bool", entity.tkey);
                }
                else if (this.isType(tt, "Int")) {
                    return new SMTTypeInfo("BInt", "TypeTag_Int", entity.tkey);
                }
                else if (this.isType(tt, "Nat")) {
                    return new SMTTypeInfo("BNat", "TypeTag_Nat", entity.tkey);
                }
                else if (this.isType(tt, "BigInt")) {
                    return new SMTTypeInfo("BBigInt", "TypeTag_BigInt", entity.tkey);
                }
                else if (this.isType(tt, "BigNat")) {
                    return new SMTTypeInfo("BBigNat", "TypeTag_BigInt", entity.tkey);
                }
                else if (this.isType(tt, "Float")) {
                    return new SMTTypeInfo("BFloat", "TypeTag_Float", entity.tkey);
                }
                else if (this.isType(tt, "Decimal")) {
                    return new SMTTypeInfo("BDecimal", "TypeTag_Decimal", entity.tkey);
                }
                else if (this.isType(tt, "Rational")) {
                    return new SMTTypeInfo("BRational", "TypeTag_Rational", entity.tkey);
                }
                else if (this.isType(tt, "String")) {
                    return new SMTTypeInfo("BString", "TypeTag_String", entity.tkey);
                }
                else if (this.isType(tt, "ByteBuffer")) {
                    return new SMTTypeInfo("BByteBuffer", "TypeTag_ByteBuffer", entity.tkey);
                }
                else if(this.isType(tt, "DateTime")) {
                    return new SMTTypeInfo("BDateTime", "TypeTag_DateTime", entity.tkey);
                }
                else if(this.isType(tt, "TickTime")) {
                    return new SMTTypeInfo("BTickTime", "TypeTag_TickTime", entity.tkey);
                }
                else if(this.isType(tt, "LogicalTime")) {
                    return new SMTTypeInfo("BLogicalTime", "TypeTag_LogicalTime", entity.tkey);
                }
                else if(this.isType(tt, "UUID")) {
                    return new SMTTypeInfo("BUUID", "TypeTag_UUID", entity.tkey);
                }
                else if(this.isType(tt, "ContentHash")) {
                    return new SMTTypeInfo("BContentHash", "TypeTag_ContentHash", entity.tkey);
                }
                else if(this.isType(tt, "Regex")) {
                    return new SMTTypeInfo("bsq_regex", "TypeTag_Regex", entity.tkey);
                }
                else {
                    assert(false, "Unknown primitive internal entity");
                    return new SMTTypeInfo("[UNKNOWN_TYPE]", "TypeTag_[UNKNOWN_TYPE]", entity.tkey);
                }
            }
            else if (entity instanceof MIRHavocEntityTypeDecl) {
                return new SMTTypeInfo("HavocSequence", "TypeTag_HavocSequence", entity.tkey);
            }
            else if (entity instanceof MIRConstructableInternalEntityTypeDecl) {
                return new SMTTypeInfo(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
            }
            else {
                assert(entity instanceof MIRPrimitiveCollectionEntityTypeDecl, "Should be a collection type");

                return new SMTTypeInfo(entity.tkey, `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
            }
        }
        else if (entity instanceof MIREnumEntityTypeDecl) {
            return new SMTTypeInfo(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
        }
        else if (entity instanceof MIRConstructableEntityTypeDecl) {
            return new SMTTypeInfo(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
        }
        else {
            return new SMTTypeInfo(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
        }
    }

    getSMTConstructorName(tt: MIRType): { cons: string, box: string, bfield: string } {
        assert(tt.options.length === 1);
        this.internTypeName(tt.typeID, tt.shortname);

        const kfix = this.assembly.subtypeOf(tt, this.getMIRType("KeyType")) ? "bsqkey_" : "bsqobject_"
        if (this.isUniqueTupleType(tt)) {
            return { cons: `${this.lookupTypeName(tt.typeID)}@cons`, box: `${this.lookupTypeName(tt.typeID)}@box`, bfield: `${kfix}${this.lookupTypeName(tt.typeID)}_value` };
        }
        else if (this.isUniqueRecordType(tt)) {
            return { cons: `${this.lookupTypeName(tt.typeID)}@cons`, box: `${this.lookupTypeName(tt.typeID)}@box`, bfield: `${kfix}${this.lookupTypeName(tt.typeID)}_value` };
        }
        else if (this.isUniqueEntityType(tt)) {
            return { cons: `${this.lookupTypeName(tt.typeID)}@cons`, box: `${this.lookupTypeName(tt.typeID)}@box`, bfield: `${kfix}${this.lookupTypeName(tt.typeID)}_value` };
        }
        else {
            assert(this.isUniqueEphemeralType(tt), "should not be other options")
            return { cons: `${this.lookupTypeName(tt.typeID)}@cons`, box: "[UNDEF_EPHEMERAL_BOX]", bfield: "[UNDEF_EPHEMERAL_BOX]" };
        }
    }

    private coerceFromAtomicToKey(exp: SMTExp, from: MIRType): SMTExp  {
        assert(this.assembly.subtypeOf(from, this.getMIRType("KeyType")));

        if (from.typeID === "None") {
            return new SMTConst("BKey@none");
        }
        else if(from.typeID === "Nothing") {
            return new SMTConst("BKey@nothing");
        }
        else {
            const smtfrom = this.getSMTTypeFor(from);
            let objval: SMTExp | undefined = undefined;

            if (this.isType(from, "Bool")) {
                objval = new SMTCallSimple("bsqkey_bool@box", [exp]);
            }
            else if (this.isType(from, "Int")) {
                objval = new SMTCallSimple("bsqkey_int@box", [exp]);
            }
            else if (this.isType(from, "Nat")) {
                objval = new SMTCallSimple("bsqkey_nat@box", [exp]);
            }
            else if (this.isType(from, "BigInt")) {
                objval = new SMTCallSimple("bsqkey_bigint@box", [exp]);
            }
            else if (this.isType(from, "BigNat")) {
                objval = new SMTCallSimple("bsqkey_bignat@box", [exp]);
            }
            else if (this.isType(from, "String")) {
                objval = new SMTCallSimple("bsqkey_string@box", [exp]);
            }
            else if(this.isType(from, "LogicalTime")) {
                objval = new SMTCallSimple("bsqkey_logicaltime@box", [exp]);
            }
            else if(this.isType(from, "UUID")) {
                objval = new SMTCallSimple("bsqkey_uuid@box", [exp]);
            }
            else if(this.isType(from, "ContentHash")) {
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
        if (from.typeID === "None") {
            return new SMTConst(`BTerm@none`);
        }
        else if (from.typeID === "Nothing") {
            return new SMTConst(`BTerm@nothing`);
        }
        else {
            if(this.assembly.subtypeOf(from, this.getMIRType("KeyType"))) {
                return new SMTCallSimple("BTerm@keybox", [this.coerceFromAtomicToKey(exp, from)]);
            }
            else {
                const smtfrom = this.getSMTTypeFor(from);
                let objval: SMTExp | undefined = undefined;

                if (this.isType(from, "Float")) {
                    objval = new SMTCallSimple("bsq_float@box", [exp]);
                }
                else if (this.isType(from, "Decimal")) {
                    objval = new SMTCallSimple("bsq_decimal@box", [exp]);
                }
                else if (this.isType(from, "Rational")) {
                    objval = new SMTCallSimple("bsq_rational@box", [exp]);
                }
                else if (this.isType(from, "ByteBuffer")) {
                    objval = new SMTCallSimple("bsq_bytebuffer@box", [exp]);
                }
                else if(this.isType(from, "ISOTime")) {
                    objval = new SMTCallSimple("bsq_isotime@box", [exp]);
                }
                else if (this.isType(from, "Regex")) {
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
        if (this.isType(into, "None")) {
            return new SMTConst("bsq_none@literal");
        }
        else {
            const oexp = new SMTCallSimple("BKey_value", [exp]);

            if (this.isType(into, "Bool")) {
                return new SMTCallSimple("bsqkey_bool_value", [oexp]);
            }
            else if (this.isType(into, "Int")) {
                return new SMTCallSimple("bsqkey_int_value", [oexp]);
            }
            else if (this.isType(into, "Nat")) {
                return new SMTCallSimple("bsqkey_nat_value", [oexp]);
            }
            else if (this.isType(into, "BigInt")) {
                return new SMTCallSimple("bsqkey_bigint_value", [oexp]);
            }
            else if (this.isType(into, "BigNat")) {
                return new SMTCallSimple("bsqkey_bignat_value", [oexp]);
            }
            else if (this.isType(into, "String")) {
                return new SMTCallSimple("bsqkey_string_value", [oexp]);
            }
            else if(this.isType(into, "LogicalTime")) {
                return new SMTCallSimple("bsqkey_logicaltime_value", [oexp]);
            }
            else if(this.isType(into, "UUID")) {
                return new SMTCallSimple("bsqkey_uuid_value", [oexp]);
            }
            else if(this.isType(into, "ContentHash")) {
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
        if (this.isType(into, "None")) {
            return new SMTConst("bsq_none@literal");
        }
        else if (this.isType(into, "Nothing")) {
            return new SMTConst("bsq_nothing@literal");
        }
        else {
            if(this.assembly.subtypeOf(into, this.getMIRType("KeyType"))) {
                return this.coerceKeyIntoAtomic(new SMTCallSimple("BTerm_keyvalue", [exp]), into)
            }
            else {
                const oexp = new SMTCallSimple("BTerm_termvalue", [exp]);

                if (this.isType(into, "Float")) {
                    return new SMTCallSimple("bsqobject_float_value", [oexp]);
                }
                else if (this.isType(into, "Decimal")) {
                    return new SMTCallSimple("bsqobject_decimal_value", [oexp]);
                }
                else if (this.isType(into, "Rational")) {
                    return new SMTCallSimple("bsqobject_rational_value", [oexp]);
                }
                else if (this.isType(into, "ByteBuffer")) {
                    return new SMTCallSimple("bsqobject_bytebuffer_value", [oexp]);
                }
                else if(this.isType(into, "ISOTime")) {
                    return new SMTCallSimple("bsqobject_isotime_value", [oexp]);
                }
                else if (this.isType(into, "Regex")) {
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
        if (this.isType(tt, "None")) {
            return ["BNone@UFCons_API", false];
        }
        else if (this.isType(tt, "Nothing")) {
            return ["BNothing@UFCons_API", false];
        }
        else if (this.isType(tt, "Bool")) {
            return ["BBool@UFCons_API", false];
        }
        else if (this.isType(tt, "Int")) {
            return ["BInt@UFCons_API", false];
        }
        else if (this.isType(tt, "Nat")) {
            return ["BNat@UFCons_API", false];
        }
        else if (this.isType(tt, "BigInt")) {
            return ["BBigInt@UFCons_API", false];
        }
        else if (this.isType(tt, "Float")) {
            return ["BFloat@UFCons_API", false];
        }
        else if (this.isType(tt, "Decimal")) {
            return ["BDecimal@UFCons_API", false];
        }
        else if (this.isType(tt, "ContentHash")) {
            return ["BContentHash@UFCons_API", false];
        }
        else {
            return [`_@@cons_${this.lookupTypeName(tt.typeID)}_entrypoint`, true];
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
                if (this.isType(tt, "None")) {
                    return {tag: APIEmitTypeTag.NoneTag, name: tt.typeID};
                }
                else if (this.isType(tt, "Nothing")) {
                    return {tag: APIEmitTypeTag.NothingTag, name: tt.typeID};
                }
                else if (this.isType(tt, "Bool")) {
                    return {tag: APIEmitTypeTag.BoolTag, name: tt.typeID};
                }
                else if (this.isType(tt, "Int")) {
                    return {tag: APIEmitTypeTag.IntTag, name: tt.typeID};
                }
                else if (this.isType(tt, "Nat")) {
                    return {tag: APIEmitTypeTag.NatTag, name: tt.typeID};
                }
                else if (this.isType(tt, "BigInt")) {
                    return {tag: APIEmitTypeTag.BigIntTag, name: tt.typeID};
                }
                else if (this.isType(tt, "BigNat")) {
                    return {tag: APIEmitTypeTag.BigNatTag, name: tt.typeID};
                }
                else if (this.isType(tt, "Float")) {
                    return {tag: APIEmitTypeTag.FloatTag, name: tt.typeID};
                }
                else if (this.isType(tt, "Decimal")) {
                    return {tag: APIEmitTypeTag.DecimalTag, name: tt.typeID};
                }
                else if (this.isType(tt, "Rational")) {
                    return {tag: APIEmitTypeTag.RationalTag, name: tt.typeID};
                }
                else if (this.isType(tt, "String")) {
                    return {tag: APIEmitTypeTag.StringTag, name: tt.typeID};
                }
                else if (this.isType(tt, "ByteBuffer")) {
                    return {tag: APIEmitTypeTag.ByteBufferTag, name: tt.typeID};
                }
                else if(this.isType(tt, "ISOTime")) {
                    return {tag: APIEmitTypeTag.ISOTag, name: tt.typeID};
                }
                else if(this.isType(tt, "LogicalTime")) {
                    return {tag: APIEmitTypeTag.LogicalTag, name: tt.typeID};
                }
                else if(this.isType(tt, "UUID")) {
                    return {tag: APIEmitTypeTag.UUIDTag, name: tt.typeID};
                }
                else if(this.isType(tt, "ContentHash")) {
                    return {tag: APIEmitTypeTag.ContentHashTag, name: tt.typeID};
                }
                else {
                    assert(false);
                    return {tag: APIEmitTypeTag.NoneTag, name: "[UNKNOWN API TYPE]"};
                }
            }
            else if (entity instanceof MIRConstructableInternalEntityTypeDecl) {
                if (tt.typeID.startsWith("StringOf")) {
                    return {tag: APIEmitTypeTag.StringOfTag, name: tt.typeID, validator: (entity.fromtype as MIRResolvedTypeKey)};
                }
                else if (tt.typeID.startsWith("DataString")) {
                    return {tag: APIEmitTypeTag.DataStringTag, name: tt.typeID, oftype: (entity.fromtype as MIRResolvedTypeKey)};
                }
                else if (tt.typeID.startsWith("DataBuffer")) {
                    return {tag: APIEmitTypeTag.DataBufferTag, name: tt.typeID, oftype: (entity.fromtype as MIRResolvedTypeKey)};
                }
                else if (tt.typeID.startsWith("Something")) {
                    return {tag: APIEmitTypeTag.SomethingTag, name: tt.typeID, oftype: (entity.fromtype as MIRResolvedTypeKey)};
                }
                else if (tt.typeID.startsWith("Result::Ok")) {
                    return {tag: APIEmitTypeTag.OkTag, name: tt.typeID, oftype: (entity.fromtype as MIRResolvedTypeKey)};
                }
                else {
                    assert(tt.typeID.startsWith("Result::Err"));
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
            return {tag: APIEmitTypeTag.ConstructableOfType, name: tt.typeID, oftype: entity.fromtype, usinginv: entity.usingcons || null};
        }
        else if(entity instanceof MIREnumEntityTypeDecl) {
            return {tag: APIEmitTypeTag.EnumTag, name: tt.typeID, enums: entity.enums};
        }
        else {
            const oentity = entity as MIRObjectEntityTypeDecl;
            
            let fields: string[] = [];
            let ttypes: string[] = [];
            for(let i = 0; i < oentity.consfuncfields.length; ++i)
            {
                const ff = oentity.consfuncfields[i];
                const mirff = this.assembly.fieldDecls.get(ff) as MIRFieldDecl;

                fields.push(mirff.fname);
                ttypes.push(mirff.declaredType);
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
