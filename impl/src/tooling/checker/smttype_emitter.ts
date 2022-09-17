//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRConstructableEntityTypeDecl, MIRConstructableInternalEntityTypeDecl, MIRDataBufferInternalEntityTypeDecl, MIRDataStringInternalEntityTypeDecl, MIREntityType, MIREntityTypeDecl, MIREnumEntityTypeDecl, MIREphemeralListType, MIRFieldDecl, MIRHavocEntityTypeDecl, MIRInternalEntityTypeDecl, MIRPrimitiveCollectionEntityTypeDecl, MIRPrimitiveInternalEntityTypeDecl, MIRPrimitiveListEntityTypeDecl, MIRPrimitiveMapEntityTypeDecl, MIRRecordType, MIRStringOfInternalEntityTypeDecl, MIRTupleType, MIRType } from "../../compiler/mir_assembly";
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

    lookupFunctionMangledName(keyid: MIRInvokeKey): string {
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

    getSMTTypeFor(tt: MIRType, fordecl?: boolean): SMTTypeInfo {
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
            return this.getSMTTypeInfoForEntity(tt, this.assembly.entityDecls.get(tt.typeID) as MIREntityTypeDecl, fordecl || false);
        }
        else if (this.isUniqueEphemeralType(tt)) {
            return new SMTTypeInfo(this.lookupTypeName(tt.typeID), `TypeTag_${this.lookupTypeName(tt.typeID)}`, tt.typeID);
        }
        else if(this.assembly.subtypeOf(tt, this.getMIRType("KeyType"))) {
            return new SMTTypeInfo("BKey", "[BKEY]", tt.typeID);
        }
        else {
            return new SMTTypeInfo("BTerm", "[BTERM]", tt.typeID);
        }
    }

    private getSMTTypeInfoForEntity(tt: MIRType, entity: MIREntityTypeDecl, fordecl: boolean): SMTTypeInfo {
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
                else if(this.isType(tt, "UTCDateTime")) {
                    return new SMTTypeInfo("BUTCDateTime", "TypeTag_UTCDateTime", entity.tkey);
                }
                else if(this.isType(tt, "CalendarDate")) {
                    return new SMTTypeInfo("BCalendarDate", "TypeTag_CalendarDate", entity.tkey);
                }
                else if(this.isType(tt, "TickTime")) {
                    return new SMTTypeInfo("BTickTime", "TypeTag_TickTime", entity.tkey);
                }
                else if(this.isType(tt, "LogicalTime")) {
                    return new SMTTypeInfo("BLogicalTime", "TypeTag_LogicalTime", entity.tkey);
                }
                else if(this.isType(tt, "ISOTimeStamp")) {
                    return new SMTTypeInfo("BISOTimeStamp", "TypeTag_ISOTimeStamp", entity.tkey);
                }
                else if(this.isType(tt, "UUID4")) {
                    return new SMTTypeInfo("BUUID4", "TypeTag_UUID4", entity.tkey);
                }
                else if(this.isType(tt, "UUID7")) {
                    return new SMTTypeInfo("BUUID7", "TypeTag_UUID7", entity.tkey);
                }
                else if(this.isType(tt, "SHAContentHash")) {
                    return new SMTTypeInfo("BSHAContentHash", "TypeTag_SHAContentHash", entity.tkey);
                }
                else if(this.isType(tt, "LatLongCoordinate")) {
                    return new SMTTypeInfo("BLatLongCoordinate", "TypeTag_LatLongCoordinate", entity.tkey);
                }
                else if(this.isType(tt, "Regex")) {
                    return new SMTTypeInfo("bsq_regex", "TypeTag_Regex", entity.tkey);
                }
                else {
                    if(entity.name === "SeqList") {
                        return new SMTTypeInfo(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
                    }
                    else if (entity.name === "SeqMap") {
                        return new SMTTypeInfo(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
                    }
                    else {
                        assert(false, "Unknown primitive internal entity");

                        return (undefined as any) as SMTTypeInfo;
                    }
                }
            }
            else if (entity instanceof MIRHavocEntityTypeDecl) {
                return new SMTTypeInfo("HavocSequence", "TypeTag_HavocSequence", entity.tkey);
            }
            else if (entity instanceof MIRStringOfInternalEntityTypeDecl) {
                return new SMTTypeInfo(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
            }
            else if (entity instanceof MIRDataStringInternalEntityTypeDecl) {
                return new SMTTypeInfo(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
            }
            else if (entity instanceof MIRDataBufferInternalEntityTypeDecl) {
                return new SMTTypeInfo(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
            }
            else if (entity instanceof MIRConstructableInternalEntityTypeDecl) {
                //Convert all refs of the type into refs to the underlying type
                const ulltype = this.getSMTTypeFor(this.getMIRType(entity.fromtype), fordecl);
                return new SMTTypeInfo(ulltype.smttypename, `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
            }
            else {
                assert(entity instanceof MIRPrimitiveCollectionEntityTypeDecl, "Should be a collection type");

                if(fordecl) {
                    return new SMTTypeInfo("BTerm", "[BTERM]", tt.typeID);
                }
                else {
                    if (entity instanceof MIRPrimitiveListEntityTypeDecl) {
                        return new SMTTypeInfo(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
                    }
                    else {
                        assert(entity instanceof MIRPrimitiveMapEntityTypeDecl);

                        return new SMTTypeInfo(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
                    }
                }
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
        this.internTypeName(tt.typeID);

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
        else {
            const smtfrom = this.getSMTTypeFor(from);
            let oftypetag = "[UNDEFINED]";
            let objval: SMTExp | undefined = undefined;

            if (this.isType(from, "Bool")) {
                oftypetag = smtfrom.smttypetag;
                objval = new SMTCallSimple("bsqkey_bool@box", [exp]);
            }
            else if (this.isType(from, "Int")) {
                oftypetag = smtfrom.smttypetag;
                objval = new SMTCallSimple("bsqkey_int@box", [exp]);
            }
            else if (this.isType(from, "Nat")) {
                oftypetag = smtfrom.smttypetag;
                objval = new SMTCallSimple("bsqkey_nat@box", [exp]);
            }
            else if (this.isType(from, "BigInt")) {
                oftypetag = smtfrom.smttypetag;
                objval = new SMTCallSimple("bsqkey_bigint@box", [exp]);
            }
            else if (this.isType(from, "BigNat")) {
                oftypetag = smtfrom.smttypetag;
                objval = new SMTCallSimple("bsqkey_bignat@box", [exp]);
            }
            else if (this.isType(from, "String")) {
                oftypetag = smtfrom.smttypetag;
                objval = new SMTCallSimple("bsqkey_string@box", [exp]);
            }
            else if(this.isType(from, "UTCDateTime")) {
                oftypetag = smtfrom.smttypetag;
                objval = new SMTCallSimple("bsqkey_utcdatetime@box", [exp]);
            }
            else if(this.isType(from, "CalendarDate")) {
                oftypetag = smtfrom.smttypetag;
                objval = new SMTCallSimple("bsqkey_calendardate@box", [exp]);
            }
            else if(this.isType(from, "TickTime")) {
                oftypetag = smtfrom.smttypetag;
                objval = new SMTCallSimple("bsqkey_ticktime@box", [exp]);
            }
            else if(this.isType(from, "LogicalTime")) {
                oftypetag = smtfrom.smttypetag;
                objval = new SMTCallSimple("bsqkey_logicaltime@box", [exp]);
            }
            else if(this.isType(from, "ISOTimeStamp")) {
                oftypetag = smtfrom.smttypetag;
                objval = new SMTCallSimple("bsqkey_isotimestamp@box", [exp]);
            }
            else if(this.isType(from, "UUID4")) {
                oftypetag = smtfrom.smttypetag;
                objval = new SMTCallSimple("bsqkey_uuid4@box", [exp]);
            }
            else if(this.isType(from, "UUID7")) {
                oftypetag = smtfrom.smttypetag;
                objval = new SMTCallSimple("bsqkey_uuid7@box", [exp]);
            }
            else if(this.isType(from, "SHAContentHash")) {
                oftypetag = smtfrom.smttypetag;
                objval = new SMTCallSimple("bsqkey_shacontenthash@box", [exp]);
            }
            else {
                const entity = this.assembly.entityDecls.get(from.typeID) as MIREntityTypeDecl;

                if (entity instanceof MIRStringOfInternalEntityTypeDecl) {
                    oftypetag = this.getSMTTypeFor(this.getMIRType("String")).smttypetag;
                    objval = new SMTCallSimple("bsqkey_string@box", [exp]);
                }
                else if (entity instanceof MIRDataStringInternalEntityTypeDecl) {
                    oftypetag = this.getSMTTypeFor(this.getMIRType("String")).smttypetag;
                    objval = new SMTCallSimple("bsqkey_string@box", [exp]);
                }
                else if (entity instanceof MIRConstructableInternalEntityTypeDecl) {
                    oftypetag = this.getSMTTypeFor(this.getMIRType(entity.fromtype)).smttypetag;
                    objval = new SMTCallSimple(this.getSMTConstructorName(this.getMIRType(entity.fromtype)).box, [exp]);
                }
                else if (entity instanceof MIREnumEntityTypeDecl) {
                    oftypetag = this.getSMTTypeFor(this.getMIRType("Nat")).smttypetag;
                    objval = new SMTCallSimple("bsqkey_nat@box", [exp]);
                }
                else if (entity instanceof MIRConstructableEntityTypeDecl) {
                    oftypetag = this.getSMTTypeFor(this.getMIRType(entity.basetype)).smttypetag;
                    objval = new SMTCallSimple(this.getSMTConstructorName(this.getMIRType(entity.basetype)).box, [exp]);
                }
                else {
                    assert(this.isUniqueEntityType(from));
                    oftypetag = smtfrom.smttypetag;
                    objval = new SMTCallSimple(this.getSMTConstructorName(from).box, [exp]);
                }
            }

            return new SMTCallSimple("BKey@box", [new SMTConst(smtfrom.smttypetag), new SMTConst(oftypetag), objval as SMTExp]);
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
                    objval = new SMTCallSimple("bsqobject_float@box", [exp]);
                }
                else if (this.isType(from, "Decimal")) {
                    objval = new SMTCallSimple("bsqobject_decimal@box", [exp]);
                }
                else if (this.isType(from, "Rational")) {
                    objval = new SMTCallSimple("bsqobject_rational@box", [exp]);
                }
                else if (this.isType(from, "ByteBuffer")) {
                    objval = new SMTCallSimple("bsqobject_bytebuffer@box", [exp]);
                }
                else if(this.isType(from, "DateTime")) {
                    objval = new SMTCallSimple("bsqobject_datetime@box", [exp]);
                }
                else if(this.isType(from, "LatLongCoordinate")) {
                    objval = new SMTCallSimple("bsqobject_latlongcoordinate@box", [exp]);
                }
                else if (this.isType(from, "Regex")) {
                    objval = new SMTCallSimple("bsqobject_regex@box", [exp]);
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
            else if(this.isType(into, "UTCDateTime")) {
                return new SMTCallSimple("bsqkey_utcdatetime_value", [oexp]);
            }
            else if(this.isType(into, "CalendarDate")) {
                return new SMTCallSimple("bsqkey_calendardate_value", [oexp]);
            }
            else if(this.isType(into, "TickTime")) {
                return new SMTCallSimple("bsqkey_ticktime_value", [oexp]);
            }
            else if(this.isType(into, "LogicalTime")) {
                return new SMTCallSimple("bsqkey_logicaltime_value", [oexp]);
            }
            else if(this.isType(into, "ISOTimeStamp")) {
                return new SMTCallSimple("bsqkey_isotimestamp_value", [oexp]);
            }
            else if(this.isType(into, "UUID4")) {
                return new SMTCallSimple("bsqkey_uuid4_value", [oexp]);
            }
            else if(this.isType(into, "UUID7")) {
                return new SMTCallSimple("bsqkey_uuid7_value", [oexp]);
            }
            else if(this.isType(into, "SHAContentHash")) {
                return new SMTCallSimple("bsqkey_shacontenthash_value", [oexp]);
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
                else if(this.isType(into, "DateTime")) {
                    return new SMTCallSimple("bsqobject_datetime_value", [oexp]);
                }
                else if(this.isType(into, "LatLongCoordinate")) {
                    return new SMTCallSimple("bsqobject_latlongcoordinate_value", [oexp]);
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

        if(smtfrom.smttypename === smtinto.smttypename) {
            return exp;
        }

        if (smtinto.isGeneralKeyType()) {
            if(smtfrom.isGeneralKeyType()) {
                return exp;
            }
            if(smtfrom.isGeneralTermType()) {
                return new SMTCallSimple("BTerm_keyvalue", [exp]);
            }
            else {
                return this.coerceFromAtomicToKey(exp, from);
            }
        }
        else if (smtinto.isGeneralTermType()) {
            if(smtfrom.isGeneralTermType()) {
                return exp;
            }
            else if(smtfrom.isGeneralKeyType()) {
                return new SMTCallSimple("BTerm@keybox", [exp]);
            }
            else {
                return this.coerceFromAtomicToTerm(exp, from);
            }
        }
        else {
            if (smtfrom.isGeneralKeyType()) {
                return this.coerceKeyIntoAtomic(exp, into);
            }
            else {
                assert(smtfrom.isGeneralTermType());

                return this.coerceTermIntoAtomic(exp, into);
            }
        }
    }

    coerceToKey(exp: SMTExp, from: MIRType): SMTExp {
        const smtfrom = this.getSMTTypeFor(from);

        if (smtfrom.isGeneralKeyType()) {
            return exp;
        }
        else {
            if(smtfrom.isGeneralTermType()) {
                return new SMTCallSimple("BTerm_keyvalue", [exp]);
            }
            else {
                return this.coerceFromAtomicToKey(exp, from);
            }
        }
    }

    coerceContainerAtomIntoTermRepresentation(exp: SMTExp, from: MIRType): SMTExp {
        return this.coerceFromAtomicToTerm(exp, from);
    }

    generateTupleIndexGetFunction(tt: MIRTupleType, idx: number): string {
        this.internTypeName(tt.typeID);
        return `${this.lookupTypeName(tt.typeID)}@_${idx}`;
    } 

    generateRecordPropertyGetFunction(tt: MIRRecordType, pname: string): string {
        this.internTypeName(tt.typeID);
        return `${this.lookupTypeName(tt.typeID)}@_${pname}`;
    }

    generateEntityFieldGetFunction(tt: MIREntityTypeDecl, field: MIRFieldDecl): string {
        this.internTypeName(tt.tkey);
        return `${this.lookupTypeName(tt.tkey)}@_${field.fname}`;
    }

    generateEphemeralListGetFunction(tt: MIREphemeralListType, idx: number): string {
        this.internTypeName(tt.typeID);
        return `${this.lookupTypeName(tt.typeID)}@_${idx}`;
    }

    generateResultType(ttype: MIRType): SMTTypeInfo {
        return new SMTTypeInfo(`$Result_${this.getSMTTypeFor(ttype).smttypename}`, "[INTERNAL RESULT]", "[INTERNAL RESULT]");
    }

    generateResultTypeConstructorSuccess(ttype: MIRType, val: SMTExp): SMTExp {
        return new SMTCallSimple(`$Result_${this.getSMTTypeFor(ttype).smttypename}@success`, [val]);
    }

    generateResultTypeConstructorError(ttype: MIRType, err: SMTExp): SMTExp {
        return new SMTCallSimple(`$Result_${this.getSMTTypeFor(ttype).smttypename}@error`, [err]);
    }

    generateErrorResultAssert(rtype: MIRType): SMTExp {
        return this.generateResultTypeConstructorError(rtype, new SMTConst("ErrorID_AssumeCheck"));
    }

    generateResultIsSuccessTest(ttype: MIRType, exp: SMTExp): SMTExp {
        return new SMTCallSimple(`(_ is $Result_${this.getSMTTypeFor(ttype).smttypename}@success)`, [exp]);
    }

    generateResultIsErrorTest(ttype: MIRType, exp: SMTExp): SMTExp {
        return new SMTCallSimple(`(_ is $Result_${this.getSMTTypeFor(ttype).smttypename}@error)`, [exp]);
    }

    generateResultGetSuccess(ttype: MIRType, exp: SMTExp): SMTExp {
        return new SMTCallSimple(`$Result_${this.getSMTTypeFor(ttype).smttypename}@success_value`, [exp]);
    }

    generateResultGetError(ttype: MIRType, exp: SMTExp): SMTExp {
        return new SMTCallSimple(`$Result_${this.getSMTTypeFor(ttype).smttypename}@error_value`, [exp]);
    }
    
    generateAccessWithSetGuardResultType(ttype: MIRType): SMTTypeInfo {
        return new SMTTypeInfo(`$GuardResult_${this.getSMTTypeFor(ttype).smttypename}`, "[INTERNAL GUARD RESULT]", "[INTERNAL GUARD RESULT]");
    }

    generateAccessWithSetGuardResultTypeConstructorLoad(ttype: MIRType, value: SMTExp, flag: boolean): SMTExp {
        return new SMTCallSimple(`$GuardResult_${this.getSMTTypeFor(ttype).smttypename}@cons`, [value, new SMTConst(flag ? "true" : "false")]);
    }

    generateAccessWithSetGuardResultGetValue(ttype: MIRType, exp: SMTExp): SMTExp {
        return new SMTCallSimple(`$GuardResult_${this.getSMTTypeFor(ttype).smttypename}@result`, [exp]);
    }

    generateAccessWithSetGuardResultGetFlag(ttype: MIRType, exp: SMTExp): SMTExp {
        return new SMTCallSimple(`$GuardResult_${this.getSMTTypeFor(ttype).smttypename}@flag`, [exp]);
    }

    generateSeqListTypeConsInfoSeq(ttype: MIRType): {cons: string, seqf: string} {
        return {cons: `${this.getSMTTypeFor(ttype).smttypename}@cons`, seqf: `${this.getSMTTypeFor(ttype).smttypename}_seq`};
    }

    generateSeqListTypeConstructorSeq(ttype: MIRType, seq: SMTExp): SMTExp {
        const consinfo = this.generateSeqListTypeConsInfoSeq(ttype);
        return new SMTCallSimple(consinfo.cons, [seq]);
    }

    generateSeqListTypeGetData(ttype: MIRType, ll: SMTExp): SMTExp {
        return new SMTCallSimple(this.generateSeqListTypeConsInfoSeq(ttype).seqf, [ll]);
    }

    generateSeqListTypeGetLength(ttype: MIRType, ll: SMTExp): SMTExp {
        return new SMTCallSimple("seq.len", [this.generateSeqListTypeGetData(ttype, ll)]);
    }

    generateSeqListTypeGetLengthMinus1(ttype: MIRType, ll: SMTExp): SMTExp {
        const len = this.generateSeqListTypeGetLength(ttype, ll);
        return new SMTCallSimple("-", [len, new SMTConst("1")]);
    }

    generateSeqMapEntryType(ttype: MIRType): SMTTypeInfo {
        return new SMTTypeInfo(`$MapEntry_${this.getSMTTypeFor(ttype).smttypename}`, "[INTERNAL RESULT]", "[INTERNAL RESULT]");
    }

    generateSeqMapEntryTypeConsInfo(ttype: MIRType): {cons: string, keyf: string, valf: string} {
        return {cons: `$MapEntry_${this.getSMTTypeFor(ttype).smttypename}@cons`, keyf: `$MapEntry_${this.getSMTTypeFor(ttype).smttypename}_key`, valf: `$MapEntry_${this.getSMTTypeFor(ttype).smttypename}_value`};
    }

    generateSeqMapEntryTypeConstructor(ttype: MIRType, key: SMTExp, val: SMTExp): SMTExp {
        const consinfo = this.generateSeqMapEntryTypeConsInfo(ttype);
        return new SMTCallSimple(consinfo.cons, [key, val]);
    }

    generateSeqMapEntryTypeGetKey(ttype: MIRType, entry: SMTExp): SMTExp {
        const consinfo = this.generateSeqMapEntryTypeConsInfo(ttype);
        return new SMTCallSimple(consinfo.keyf, [entry]);
    }

    generateSeqMapEntryTypeGetValue(ttype: MIRType, entry: SMTExp): SMTExp {
        const consinfo = this.generateSeqMapEntryTypeConsInfo(ttype);
        return new SMTCallSimple(consinfo.valf, [entry]);
    }

    generateSeqMapTypeConsInfo(ttype: MIRType): {cons: string, seqf: string} {
        return {cons: `${this.getSMTTypeFor(ttype).smttypename}@cons`, seqf: `${this.getSMTTypeFor(ttype).smttypename}_seq`};
    }

    generateSeqMapTypeConstructor(ttype: MIRType, seq: SMTExp): SMTExp {
        const consinfo = this.generateSeqMapTypeConsInfo(ttype);
        return new SMTCallSimple(consinfo.cons, [seq]);
    }

    generateSeqMapTypeGetData(ttype: MIRType, mm: SMTExp): SMTExp {
        return new SMTCallSimple(this.generateSeqMapTypeConsInfo(ttype).seqf, [mm]);
    }

    generateSeqMapTypeGetLength(ttype: MIRType, mm: SMTExp): SMTExp {
        return new SMTCallSimple("seq.len", [this.generateSeqMapTypeGetData(ttype, mm)]);
    }

    generateSeqMapTypeGetLengthMinus1(ttype: MIRType, mm: SMTExp): SMTExp {
        return new SMTCallSimple("-", [new SMTCallSimple("seq.len", [this.generateSeqMapTypeGetData(ttype, mm)]), new SMTConst("1")]);
    }

    generateHavocConstructorName(tt: MIRType): string {
        return `_@@cons_${this.lookupTypeName(tt.typeID)}_entrypoint`;
    }

    generateHavocConstructorPathExtend(path: SMTExp, step: SMTExp): SMTExp {
        return new SMTCallSimple("seq.++", [path, new SMTCallSimple("seq.unit", [step])]);
    }

    generateHavocConstructorCall(tt: MIRType, path: SMTExp, step: SMTExp): SMTExp {
        return new SMTCallGeneral(this.generateHavocConstructorName(tt), [this.generateHavocConstructorPathExtend(path, step)]);
    }

    generateHavocConstructorCall_PassThrough(tt: MIRType, path: SMTExp): SMTExp {
        return new SMTCallGeneral(this.generateHavocConstructorName(tt), [path]);
    }
}

export {
    SMTTypeEmitter
};
