//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRConstructableEntityTypeDecl, MIRConstructableInternalEntityTypeDecl, MIRDataBufferInternalEntityTypeDecl, MIRDataStringInternalEntityTypeDecl, MIREntityType, MIREntityTypeDecl, MIREnumEntityTypeDecl, MIREphemeralListType, MIRInternalEntityTypeDecl, MIRPrimitiveCollectionEntityTypeDecl, MIRPrimitiveInternalEntityTypeDecl, MIRPrimitiveListEntityTypeDecl, MIRPrimitiveMapEntityTypeDecl, MIRFieldDecl, MIRRecordType, MIRStringOfInternalEntityTypeDecl, MIRTupleType, MIRType } from "../../../compiler/mir_assembly";
import { MIRGlobalKey, MIRInvokeKey, MIRResolvedTypeKey } from "../../../compiler/mir_ops";
import { MorphirCallSimple, MorphirConst, MorphirExp, MorphirTypeInfo } from "./morphir_exp";
import { SourceInfo } from "../../../ast/parser";

import * as assert from "assert";

class MorphirTypeEmitter {
    readonly assembly: MIRAssembly;

    private namectr: number = 0;
    private allshortnames = new Set<string>();
    private mangledTypeNameMap: Map<string, string> = new Map<string, string>();
    private mangledFunctionNameMap: Map<string, string> = new Map<string, string>();
    private mangledGlobalNameMap: Map<string, string> = new Map<string, string>();

    private typeDataMap: Map<MIRResolvedTypeKey, MorphirTypeInfo> = new Map<MIRResolvedTypeKey, MorphirTypeInfo>();

    constructor(assembly: MIRAssembly, namectr?: number, mangledTypeNameMap?: Map<string, string>, mangledFunctionNameMap?: Map<string, string>, mangledGlobalNameMap?: Map<string, string>) {
        this.assembly = assembly;

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

    getMorphirTypeFor(tt: MIRType): MorphirTypeInfo {
        if(this.typeDataMap.has(tt.typeID)) {
            return this.typeDataMap.get(tt.typeID) as MorphirTypeInfo;
        }

        this.internTypeName(tt.typeID);
        if(this.isUniqueTupleType(tt)) {
            return new MorphirTypeInfo(this.lookupTypeName(tt.typeID), `TypeTag_${this.lookupTypeName(tt.typeID)}`, tt.typeID);
        }
        else if(this.isUniqueRecordType(tt)) {
            return new MorphirTypeInfo(this.lookupTypeName(tt.typeID), `TypeTag_${this.lookupTypeName(tt.typeID)}`, tt.typeID);
        }
        else if(this.isUniqueEntityType(tt)) {
            return this.getMorphirTypeInfoForEntity(tt, this.assembly.entityDecls.get(tt.typeID) as MIREntityTypeDecl);
        }
        else if (this.isUniqueEphemeralType(tt)) {
            return new MorphirTypeInfo(this.lookupTypeName(tt.typeID), `TypeTag_${this.lookupTypeName(tt.typeID)}`, tt.typeID);
        }
        else if(this.assembly.subtypeOf(tt, this.getMIRType("KeyType"))) {
            return new MorphirTypeInfo("BKey", "[BKEY]", tt.typeID);
        }
        else {
            return new MorphirTypeInfo("BTerm", "[BTERM]", tt.typeID);
        }
    }

    private getMorphirTypeInfoForEntity(tt: MIRType, entity: MIREntityTypeDecl): MorphirTypeInfo {
        if(entity instanceof MIRInternalEntityTypeDecl) {
            if(entity instanceof MIRPrimitiveInternalEntityTypeDecl) {
                if (this.isType(tt, "None")) {
                    return new MorphirTypeInfo("BNone", "TypeTag_None", entity.tkey);
                }
                else if (this.isType(tt, "Nothing")) {
                    return new MorphirTypeInfo("BNothing", "TypeTag_Nothing", entity.tkey);
                }
                else if (this.isType(tt, "Bool")) {
                    return new MorphirTypeInfo("Bool", "TypeTag_Bool", entity.tkey);
                }
                else if (this.isType(tt, "Int")) {
                    return new MorphirTypeInfo("BInt", "TypeTag_Int", entity.tkey);
                }
                else if (this.isType(tt, "Nat")) {
                    return new MorphirTypeInfo("BNat", "TypeTag_Nat", entity.tkey);
                }
                else if (this.isType(tt, "BigInt")) {
                    return new MorphirTypeInfo("BBigInt", "TypeTag_BigInt", entity.tkey);
                }
                else if (this.isType(tt, "BigNat")) {
                    return new MorphirTypeInfo("BBigNat", "TypeTag_BigInt", entity.tkey);
                }
                else if (this.isType(tt, "Float")) {
                    return new MorphirTypeInfo("BFloat", "TypeTag_Float", entity.tkey);
                }
                else if (this.isType(tt, "Decimal")) {
                    return new MorphirTypeInfo("BDecimal", "TypeTag_Decimal", entity.tkey);
                }
                else if (this.isType(tt, "Rational")) {
                    return new MorphirTypeInfo("BRational", "TypeTag_Rational", entity.tkey);
                }
                else if (this.isType(tt, "String")) {
                    return new MorphirTypeInfo("BString", "TypeTag_String", entity.tkey);
                }
                else if (this.isType(tt, "ByteBuffer")) {
                    return new MorphirTypeInfo("BByteBuffer", "TypeTag_ByteBuffer", entity.tkey);
                }
                else if(this.isType(tt, "DateTime")) {
                    return new MorphirTypeInfo("BDateTime", "TypeTag_DateTime", entity.tkey);
                }
                else if(this.isType(tt, "UTCDateTime")) {
                    return new MorphirTypeInfo("BUTCDateTime", "TypeTag_UTCDateTime", entity.tkey);
                }
                else if(this.isType(tt, "CalendarDate")) {
                    return new MorphirTypeInfo("BCalendarDate", "TypeTag_CalendarDate", entity.tkey);
                }
                else if(this.isType(tt, "RelativeTime")) {
                    return new MorphirTypeInfo("BRelativeTime", "TypeTag_RelativeTime", entity.tkey);
                }
                else if(this.isType(tt, "TickTime")) {
                    return new MorphirTypeInfo("BTickTime", "TypeTag_TickTime", entity.tkey);
                }
                else if(this.isType(tt, "LogicalTime")) {
                    return new MorphirTypeInfo("BLogicalTime", "TypeTag_LogicalTime", entity.tkey);
                }
                else if(this.isType(tt, "ISOTimeStamp")) {
                    return new MorphirTypeInfo("BISOTimeStamp", "TypeTag_ISOTimeStamp", entity.tkey);
                }
                else if(this.isType(tt, "UUID4")) {
                    return new MorphirTypeInfo("BUUID4", "TypeTag_UUID4", entity.tkey);
                }
                else if(this.isType(tt, "UUID7")) {
                    return new MorphirTypeInfo("BUUID7", "TypeTag_UUID7", entity.tkey);
                }
                else if(this.isType(tt, "SHAContentHash")) {
                    return new MorphirTypeInfo("BSHAContentHash", "TypeTag_SHAContentHash", entity.tkey);
                }
                else if(this.isType(tt, "LatLongCoordinate")) {
                    return new MorphirTypeInfo("BLatLongCoordinate", "TypeTag_LatLongCoordinate", entity.tkey);
                }
                else if(this.isType(tt, "Regex")) {
                    return new MorphirTypeInfo("BRegex", "TypeTag_Regex", entity.tkey);
                }
                else {
                    assert(false, "Unknown primitive internal entity");
                }
            }
            else if (entity instanceof MIRStringOfInternalEntityTypeDecl) {
                return new MorphirTypeInfo(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
            }
            else if (entity instanceof MIRDataStringInternalEntityTypeDecl) {
                return new MorphirTypeInfo(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
            }
            else if (entity instanceof MIRDataBufferInternalEntityTypeDecl) {
                return new MorphirTypeInfo(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
            }
            else if (entity instanceof MIRConstructableInternalEntityTypeDecl) {
                //Convert all refs of the type into refs to the underlying type
                const ulltype = this.getMorphirTypeFor(this.getMIRType(entity.fromtype));
                return new MorphirTypeInfo(ulltype.morphirtypename, `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
            }
            else {
                assert(entity instanceof MIRPrimitiveCollectionEntityTypeDecl, "Should be a collection type");

                if(entity instanceof MIRPrimitiveListEntityTypeDecl) {
                    return new MorphirTypeInfo(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
                }
                else {
                    assert(entity instanceof MIRPrimitiveMapEntityTypeDecl);

                    return new MorphirTypeInfo(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
                }
            }
        }
        else if (entity instanceof MIREnumEntityTypeDecl) {
            return new MorphirTypeInfo(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
        }
        else if (entity instanceof MIRConstructableEntityTypeDecl) {
            return new MorphirTypeInfo(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
        }
        else {
            return new MorphirTypeInfo(this.lookupTypeName(entity.tkey), `TypeTag_${this.lookupTypeName(entity.tkey)}`, entity.tkey);
        }
    }

    getMorphirConstructorName(tt: MIRType): { cons: string, box: string, bfield: string } {
        assert(tt.options.length === 1);
        this.internTypeName(tt.typeID);

        const kfix = this.assembly.subtypeOf(tt, this.getMIRType("KeyType")) ? "bkey_" : "bobject_"
        if (this.isUniqueTupleType(tt)) {
            return { cons: `${this.lookupTypeName(tt.typeID)}__cons`, box: `${this.lookupTypeName(tt.typeID)}__box`, bfield: `${kfix}${this.lookupTypeName(tt.typeID)}__value` };
        }
        else if (this.isUniqueRecordType(tt)) {
            return { cons: `${this.lookupTypeName(tt.typeID)}__cons`, box: `${this.lookupTypeName(tt.typeID)}__box`, bfield: `${kfix}${this.lookupTypeName(tt.typeID)}__value` };
        }
        else if (this.isUniqueEntityType(tt)) {
            return { cons: `${this.lookupTypeName(tt.typeID)}__cons`, box: `${this.lookupTypeName(tt.typeID)}__box`, bfield: `${kfix}${this.lookupTypeName(tt.typeID)}__value` };
        }
        else {
            assert(this.isUniqueEphemeralType(tt), "should not be other options")
            return { cons: `${this.lookupTypeName(tt.typeID)}__cons`, box: "[UNDEF_EPHEMERAL_BOX]", bfield: "[UNDEF_EPHEMERAL_BOX]" };
        }
    }

    private coerceFromAtomicToKey(exp: MorphirExp, from: MIRType): MorphirExp  {
        assert(this.assembly.subtypeOf(from, this.getMIRType("KeyType")));

        if (from.typeID === "None") {
            return new MorphirConst("bkey__none");
        }
        else {
            const smtfrom = this.getMorphirTypeFor(from);
            let oftypetag = "[UNDEFINED]";
            let objval: MorphirExp | undefined = undefined;

            if (this.isType(from, "Bool")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("BSQKey_bool__box", [exp]);
            }
            else if (this.isType(from, "Int")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("bsqkey_int__box", [exp]);
            }
            else if (this.isType(from, "Nat")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("bsqkey_nat__box", [exp]);
            }
            else if (this.isType(from, "BigInt")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("bsqkey_bigint__box", [exp]);
            }
            else if (this.isType(from, "BigNat")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("bsqkey_bignat__box", [exp]);
            }
            else if (this.isType(from, "String")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("bsqkey_string__box", [exp]);
            }
            else if(this.isType(from, "UTCDateTime")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("bsqkey_utcdatetime__box", [exp]);
            }
            else if(this.isType(from, "CalendarDate")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("bsqkey_calendardate__box", [exp]);
            }
            else if(this.isType(from, "RelativeTime")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("bsqkey_relativetimetime__box", [exp]);
            }
            else if(this.isType(from, "TickTime")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("bsqkey_ticktime__box", [exp]);
            }
            else if(this.isType(from, "LogicalTime")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("bsqkey_logicaltime__box", [exp]);
            }
            else if(this.isType(from, "ISOTimeStamp")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("bsqkey_isotimestamp__box", [exp]);
            }
            else if(this.isType(from, "UUID4")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("bsqkey_uuid4__box", [exp]);
            }
            else if(this.isType(from, "UUID7")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("bsqkey_uuid7__box", [exp]);
            }
            else if(this.isType(from, "SHAContentHash")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("bsqkey_shacontenthash__box", [exp]);
            }
            else {
                const entity = this.assembly.entityDecls.get(from.typeID) as MIREntityTypeDecl;

                if (entity instanceof MIRStringOfInternalEntityTypeDecl) {
                    oftypetag = this.getMorphirTypeFor(this.getMIRType("String")).morphirtypetag;
                    objval = new MorphirCallSimple("bsqkey_string__box", [exp]);
                }
                else if (entity instanceof MIRDataStringInternalEntityTypeDecl) {
                    oftypetag = this.getMorphirTypeFor(this.getMIRType("String")).morphirtypetag;
                    objval = new MorphirCallSimple("bsqkey_string__box", [exp]);
                }
                else if (entity instanceof MIRConstructableInternalEntityTypeDecl) {
                    oftypetag = this.getMorphirTypeFor(this.getMIRType(entity.fromtype)).morphirtypetag;
                    objval = new MorphirCallSimple(this.getMorphirConstructorName(this.getMIRType(entity.fromtype)).box, [exp]);
                }
                else if (entity instanceof MIREnumEntityTypeDecl) {
                    oftypetag = this.getMorphirTypeFor(this.getMIRType("Nat")).morphirtypetag;
                    objval = new MorphirCallSimple("bsqkey_nat__box", [exp]);
                }
                else if (entity instanceof MIRConstructableEntityTypeDecl) {
                    oftypetag = this.getMorphirTypeFor(this.getMIRType(entity.basetype)).morphirtypetag;
                    objval = new MorphirCallSimple(this.getMorphirConstructorName(this.getMIRType(entity.basetype)).box, [exp]);
                }
                else {
                    assert(this.isUniqueEntityType(from));
                    oftypetag = smtfrom.morphirtypetag;
                    objval = new MorphirCallSimple(this.getMorphirConstructorName(from).box, [exp]);
                }
            }

            return new MorphirCallSimple("BKey__box", [new MorphirConst(smtfrom.morphirtypetag), new MorphirConst(oftypetag), objval as MorphirExp]);
        }
    }

    private coerceFromAtomicToTerm(exp: MorphirExp, from: MIRType): MorphirExp {
        if (from.typeID === "None") {
            return new MorphirConst(`BTerm__none`);
        }
        else if (from.typeID === "Nothing") {
            return new MorphirConst(`BTerm__nothing`);
        }
        else {
            if(this.assembly.subtypeOf(from, this.getMIRType("KeyType"))) {
                return new MorphirCallSimple("BTerm__keybox", [this.coerceFromAtomicToKey(exp, from)]);
            }
            else {
                const smtfrom = this.getMorphirTypeFor(from);
                let objval: MorphirExp | undefined = undefined;

                if (this.isType(from, "Float")) {
                    objval = new MorphirCallSimple("bsqobject_float__box", [exp]);
                }
                else if (this.isType(from, "Decimal")) {
                    objval = new MorphirCallSimple("bsqobject_decimal__box", [exp]);
                }
                else if (this.isType(from, "Rational")) {
                    objval = new MorphirCallSimple("bsqobject_rational__box", [exp]);
                }
                else if (this.isType(from, "ByteBuffer")) {
                    objval = new MorphirCallSimple("bsqobject_bytebuffer__box", [exp]);
                }
                else if(this.isType(from, "DateTime")) {
                    objval = new MorphirCallSimple("bsqobject_datetime__box", [exp]);
                }
                else if(this.isType(from, "LatLongCoordinate")) {
                    objval = new MorphirCallSimple("bsqobject_latlongcoordinate__box", [exp]);
                }
                else if (this.isType(from, "Regex")) {
                    objval = new MorphirCallSimple("bsqobject_regex__box", [exp]);
                }
                else if (this.isUniqueTupleType(from)) {
                    objval = new MorphirCallSimple(this.getMorphirConstructorName(from).box, [exp]);
                }
                else if (this.isUniqueRecordType(from)) {
                    objval = new MorphirCallSimple(this.getMorphirConstructorName(from).box, [exp]);
                }
                else {
                    assert(this.isUniqueEntityType(from));
    
                    objval = new MorphirCallSimple(this.getMorphirConstructorName(from).box, [exp]);
                }

                return new MorphirCallSimple("BTerm__termbox", [new MorphirConst(smtfrom.morphirtypetag), objval as MorphirExp]);
            }
        }
    }

    private coerceKeyIntoAtomic(exp: MorphirExp, into: MIRType): MorphirExp {
        if (this.isType(into, "None")) {
            return new MorphirConst("bsq_none__literal");
        }
        else {
            const oexp = new MorphirCallSimple("BKey_value", [exp]);

            if (this.isType(into, "Bool")) {
                return new MorphirCallSimple("bsqkey_bool_value", [oexp]);
            }
            else if (this.isType(into, "Int")) {
                return new MorphirCallSimple("bsqkey_int_value", [oexp]);
            }
            else if (this.isType(into, "Nat")) {
                return new MorphirCallSimple("bsqkey_nat_value", [oexp]);
            }
            else if (this.isType(into, "BigInt")) {
                return new MorphirCallSimple("bsqkey_bigint_value", [oexp]);
            }
            else if (this.isType(into, "BigNat")) {
                return new MorphirCallSimple("bsqkey_bignat_value", [oexp]);
            }
            else if (this.isType(into, "String")) {
                return new MorphirCallSimple("bsqkey_string_value", [oexp]);
            }
            else if(this.isType(into, "UTCDateTime")) {
                return new MorphirCallSimple("bsqkey_utcdatetime_value", [oexp]);
            }
            else if(this.isType(into, "CalendarDate")) {
                return new MorphirCallSimple("bsqkey_calendardate_value", [oexp]);
            }
            else if(this.isType(into, "RelativeTime")) {
                return new MorphirCallSimple("bsqkey_relativetime_value", [oexp]);
            }
            else if(this.isType(into, "TickTime")) {
                return new MorphirCallSimple("bsqkey_ticktime_value", [oexp]);
            }
            else if(this.isType(into, "LogicalTime")) {
                return new MorphirCallSimple("bsqkey_logicaltime_value", [oexp]);
            }
            else if(this.isType(into, "ISOTimeStamp")) {
                return new MorphirCallSimple("bsqkey_isotimestamp_value", [oexp]);
            }
            else if(this.isType(into, "UUID4")) {
                return new MorphirCallSimple("bsqkey_uuid4_value", [oexp]);
            }
            else if(this.isType(into, "UUID7")) {
                return new MorphirCallSimple("bsqkey_uuid7_value", [oexp]);
            }
            else if(this.isType(into, "SHAContentHash")) {
                return new MorphirCallSimple("bsqkey_shacontenthash_value", [oexp]);
            }
            else {
                assert(this.isUniqueEntityType(into));

                return new MorphirCallSimple(this.getMorphirConstructorName(into).bfield, [oexp]);
            }
        }
    }

    private coerceTermIntoAtomic(exp: MorphirExp, into: MIRType): MorphirExp {
        if (this.isType(into, "None")) {
            return new MorphirConst("bsq_none__literal");
        }
        else if (this.isType(into, "Nothing")) {
            return new MorphirConst("bsq_nothing__literal");
        }
        else {
            if(this.assembly.subtypeOf(into, this.getMIRType("KeyType"))) {
                return this.coerceKeyIntoAtomic(new MorphirCallSimple("BTerm_keyvalue", [exp]), into)
            }
            else {
                const oexp = new MorphirCallSimple("BTerm_termvalue", [exp]);

                if (this.isType(into, "Float")) {
                    return new MorphirCallSimple("bsqobject_float_value", [oexp]);
                }
                else if (this.isType(into, "Decimal")) {
                    return new MorphirCallSimple("bsqobject_decimal_value", [oexp]);
                }
                else if (this.isType(into, "Rational")) {
                    return new MorphirCallSimple("bsqobject_rational_value", [oexp]);
                }
                else if (this.isType(into, "ByteBuffer")) {
                    return new MorphirCallSimple("bsqobject_bytebuffer_value", [oexp]);
                }
                else if(this.isType(into, "DateTime")) {
                    return new MorphirCallSimple("bsqobject_datetime_value", [oexp]);
                }
                else if(this.isType(into, "LatLongCoordinate")) {
                    return new MorphirCallSimple("bsqobject_latlongcoordinate_value", [oexp]);
                }
                else if (this.isType(into, "Regex")) {
                    return new MorphirCallSimple("bsqobject_regex_value", [oexp]);
                }
                else if (this.isUniqueTupleType(into)) {
                    return new MorphirCallSimple(this.getMorphirConstructorName(into).bfield, [oexp]);
                }
                else if (this.isUniqueRecordType(into)) {
                    return new MorphirCallSimple(this.getMorphirConstructorName(into).bfield, [oexp]);
                }
                else {
                    assert(this.isUniqueEntityType(into));

                    return new MorphirCallSimple(this.getMorphirConstructorName(into).bfield, [oexp]);
                }
            }
        }
    }

    coerce(exp: MorphirExp, from: MIRType, into: MIRType): MorphirExp {
        const smtfrom = this.getMorphirTypeFor(from);
        const smtinto = this.getMorphirTypeFor(into);

        if(smtfrom.morphirtypename === smtinto.morphirtypename) {
            return exp;
        }

        if (smtinto.isGeneralKeyType()) {
            if(smtfrom.isGeneralKeyType()) {
                return exp;
            }
            if(smtfrom.isGeneralTermType()) {
                return new MorphirCallSimple("BTerm_keyvalue", [exp]);
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
                return new MorphirCallSimple("BTerm__keybox", [exp]);
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

    coerceToKey(exp: MorphirExp, from: MIRType): MorphirExp {
        const smtfrom = this.getMorphirTypeFor(from);

        if (smtfrom.isGeneralKeyType()) {
            return exp;
        }
        else {
            if(smtfrom.isGeneralTermType()) {
                return new MorphirCallSimple("BTerm_keyvalue", [exp]);
            }
            else {
                return this.coerceFromAtomicToKey(exp, from);
            }
        }
    }

    generateTupleIndexGetFunction(tt: MIRTupleType, idx: number): string {
        this.internTypeName(tt.typeID);
        return `${this.lookupTypeName(tt.typeID)}__${idx}`;
    } 

    generateRecordPropertyGetFunction(tt: MIRRecordType, pname: string): string {
        this.internTypeName(tt.typeID);
        return `${this.lookupTypeName(tt.typeID)}__${pname}`;
    }

    generateEntityFieldGetFunction(tt: MIREntityTypeDecl, field: MIRFieldDecl): string {
        this.internTypeName(tt.tkey);
        return `${this.lookupTypeName(tt.tkey)}__${field.fname}`;
    }

    generateEphemeralListGetFunction(tt: MIREphemeralListType, idx: number): string {
        this.internTypeName(tt.typeID);
        return `${this.lookupTypeName(tt.typeID)}__${idx}`;
    }

    generateResultType(ttype: MIRType): MorphirTypeInfo {
        return new MorphirTypeInfo(`Result ${this.getMorphirTypeFor(ttype).morphirtypename} String`, "[INTERNAL RESULT]", "[INTERNAL RESULT]");
    }

    generateResultTypeConstructorSuccess(ttype: MIRType, val: MorphirExp): MorphirExp {
        return new MorphirCallSimple("Ok", [val]);
    }

    generateResultTypeConstructorError(ttype: MIRType, err: MorphirExp): MorphirExp {
        return new MorphirCallSimple("Err", [err]);
    }

    generateErrorResultAssert(rtype: MIRType, file: string, sinfo: SourceInfo): MorphirExp {
        return this.generateResultTypeConstructorError(rtype, new MorphirConst(`"${file}::${sinfo.line}"`));
    }

    generateResultIsSuccessTest(ttype: MIRType, exp: MorphirExp): MorphirExp {
        return new MorphirCallSimple("Result__is__success", [exp]);
    }

    generateResultIsErrorTest(ttype: MIRType, exp: MorphirExp): MorphirExp {
        return new MorphirCallSimple("Result__is__error", [exp]);
    }

    generateResultGetSuccess(ttype: MIRType, exp: MorphirExp): MorphirExp {
        const ufcname = `${this.getMorphirTypeFor(ttype).morphirtypename}@uicons_UF`;
        return new MorphirCallSimple("Result__success__get__value", [exp, new MorphirConst(ufcname)]);
    }

    generateResultGetError(ttype: MIRType, exp: MorphirExp): MorphirExp {
        return new MorphirCallSimple("Result__error__get__value", [exp]);
    }
    
    generateAccessWithSetGuardResultType(ttype: MIRType): MorphirTypeInfo {
        return new MorphirTypeInfo(`GuardResult__${this.getMorphirTypeFor(ttype).morphirtypename}`, "[INTERNAL GUARD RESULT]", "[INTERNAL GUARD RESULT]");
    }

    generateAccessWithSetGuardResultTypeConstructorLoad(ttype: MIRType, value: MorphirExp, flag: boolean): MorphirExp {
        return new MorphirCallSimple(`GuardResult__${this.getMorphirTypeFor(ttype).morphirtypename}__cons`, [value, new MorphirConst(flag ? "true" : "false")]);
    }

    generateAccessWithSetGuardResultGetValue(ttype: MIRType, exp: MorphirExp): MorphirExp {
        const ufcname = `${this.getMorphirTypeFor(ttype).morphirtypename}@uicons_UF`;
        return new MorphirCallSimple(`GuardResult__${this.getMorphirTypeFor(ttype).morphirtypename}__result`, [exp, new MorphirConst(ufcname)]);
    }

    generateAccessWithSetGuardResultGetFlag(ttype: MIRType, exp: MorphirExp): MorphirExp {
        return new MorphirCallSimple(`GuardResult__${this.getMorphirTypeFor(ttype).morphirtypename}__flag`, [exp]);
    }

    generateListTypeConsInfoSeq(ttype: MIRType): {cons: string, seqf: string} {
        return {cons: `${this.getMorphirTypeFor(ttype).morphirtypename}__cons`, seqf: `${this.getMorphirTypeFor(ttype).morphirtypename}_seq`};
    }

    generateListTypeConstructorSeq(ttype: MIRType, seq: MorphirExp): MorphirExp {
        const consinfo = this.generateListTypeConsInfoSeq(ttype);
        return new MorphirCallSimple(consinfo.cons, [seq]);
    }

    generateListTypeGetData(ttype: MIRType, ll: MorphirExp): MorphirExp {
        return new MorphirCallSimple(this.generateListTypeConsInfoSeq(ttype).seqf, [ll]);
    }

    generateListTypeGetLength(ttype: MIRType, ll: MorphirExp): MorphirExp {
        return new MorphirCallSimple("length", [this.generateListTypeGetData(ttype, ll)]);
    }

    generateListTypeGetLengthMinus1(ttype: MIRType, ll: MorphirExp): MorphirExp {
        const len = this.generateListTypeGetLength(ttype, ll);
        return new MorphirCallSimple("-", [len, new MorphirConst("1")], true);
    }

    generateMapEntryType(ttype: MIRType): MorphirTypeInfo {
        return new MorphirTypeInfo(`MapEntry__${this.getMorphirTypeFor(ttype).morphirtypename}`, "[INTERNAL RESULT]", "[INTERNAL RESULT]");
    }

    generateMapEntryTypeConsInfo(ttype: MIRType): {cons: string, keyf: string, valf: string} {
        return {cons: `MapEntry__${this.getMorphirTypeFor(ttype).morphirtypename}__cons`, keyf: `MapEntry__${this.getMorphirTypeFor(ttype).morphirtypename}_key`, valf: `MapEntry__${this.getMorphirTypeFor(ttype).morphirtypename}_value`};
    }

    generateMapEntryTypeConstructor(ttype: MIRType, key: MorphirExp, val: MorphirExp): MorphirExp {
        const consinfo = this.generateMapEntryTypeConsInfo(ttype);
        return new MorphirCallSimple(consinfo.cons, [key, val]);
    }

    generateMapEntryTypeGetKey(ttype: MIRType, entry: MorphirExp): MorphirExp {
        const consinfo = this.generateMapEntryTypeConsInfo(ttype);
        return new MorphirCallSimple(consinfo.keyf, [entry]);
    }

    generateMapEntryTypeGetValue(ttype: MIRType, entry: MorphirExp): MorphirExp {
        const consinfo = this.generateMapEntryTypeConsInfo(ttype);
        return new MorphirCallSimple(consinfo.valf, [entry]);
    }

    generateMapTypeConsInfo(ttype: MIRType): {cons: string, seqf: string} {
        return {cons: `${this.getMorphirTypeFor(ttype).morphirtypename}__cons`, seqf: `${this.getMorphirTypeFor(ttype).morphirtypename}_seq`};
    }

    generateMapTypeConstructor(ttype: MIRType, seq: MorphirExp): MorphirExp {
        const consinfo = this.generateMapTypeConsInfo(ttype);
        return new MorphirCallSimple(consinfo.cons, [seq]);
    }

    generateMapTypeGetData(ttype: MIRType, mm: MorphirExp): MorphirExp {
        return new MorphirCallSimple(this.generateMapTypeConsInfo(ttype).seqf, [mm]);
    }

    generateMapTypeGetLength(ttype: MIRType, mm: MorphirExp): MorphirExp {
        return new MorphirCallSimple("length", [this.generateMapTypeGetData(ttype, mm)]);
    }
}

export {
    MorphirTypeEmitter
};
