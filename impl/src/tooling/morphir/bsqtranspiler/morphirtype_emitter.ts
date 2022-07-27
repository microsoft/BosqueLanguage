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
            let cleanname = keyid.replace(/:/g, "_").replace(/[<>, \[\]\{\}\(\)\\\/\#\=\|]/g, "_");
            if(this.allshortnames.has(cleanname)) {
                cleanname = cleanname + "__" + this.namectr++;
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
            let cleanname = shortname.replace(/:/g, "_").replace(/[<>, \[\]\{\}\(\)\\\/\#\=\|]/g, "_");
            
            if(/[A-Z]/.test(cleanname[0])) {
                cleanname = cleanname[0].toLowerCase() + cleanname.slice(1);
            }

            if(this.allshortnames.has(cleanname)) {
                cleanname = cleanname + "__" + this.namectr++;
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
            let cleanname = shortname.replace(/:/g, "_").replace(/[<>, \[\]\{\}\(\)\\\/\#\=\|]/g, "_");
            
            if(/[A-Z]/.test(cleanname[0])) {
                cleanname = cleanname[0].toLowerCase() + cleanname.slice(1);
            }

            if(this.allshortnames.has(cleanname)) {
                cleanname = cleanname + "__" + this.namectr++;
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

    getMorphirConstructorName(tt: MIRType): { cons: string, box: string, unbox: string, default: string } {
        assert(tt.options.length === 1);
        this.internTypeName(tt.typeID);

        const mname = this.lookupTypeName(tt.typeID);
        const kfix = this.assembly.subtypeOf(tt, this.getMIRType("KeyType")) ? "BKey" : "BObject"

        if (this.isUniqueTupleType(tt)) {
            return { cons: `${mname}`, box: `${mname}_box`, unbox: `unbox_${kfix}${mname}`, default: `bsq${mname.toLowerCase()}_default`};
        }
        else if (this.isUniqueRecordType(tt)) {
            return { cons: `${this.lookupTypeName(tt.typeID)}`, box: `${this.lookupTypeName(tt.typeID)}_box`, unbox: `unbox_${kfix}${mname}`, default: `bsq${mname.toLowerCase()}_default` };
        }
        else if (this.isUniqueEntityType(tt)) {
            return { cons: `${this.lookupTypeName(tt.typeID)}`, box: `${this.lookupTypeName(tt.typeID)}_box`, unbox: `unbox_${kfix}${mname}`, default: `bsq${mname.toLowerCase()}_default` };
        }
        else {
            assert(this.isUniqueEphemeralType(tt), "should not be other options")
            return { cons: `${this.lookupTypeName(tt.typeID)}_cons`, box: "[UNDEF_EPHEMERAL_BOX]", unbox: "[UNDEF_EPHEMERAL_BOX]", default: "[UNDEF_EPHEMERAL_DEFAULT]" };
        }
    }

    private coerceFromAtomicToKey(exp: MorphirExp, from: MIRType): MorphirExp  {
        assert(this.assembly.subtypeOf(from, this.getMIRType("KeyType")));

        if (from.typeID === "None") {
            return new MorphirConst("bkey_none");
        }
        else {
            const smtfrom = this.getMorphirTypeFor(from);
            let oftypetag = "[UNDEFINED]";
            let objval: MorphirExp | undefined = undefined;

            if (this.isType(from, "Bool")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("BKeyBool_box", [exp]);
            }
            else if (this.isType(from, "Int")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("BKeyBInt_box", [exp]);
            }
            else if (this.isType(from, "Nat")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("BKeyBNat_box", [exp]);
            }
            else if (this.isType(from, "BigInt")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("BKeyBBigInt_box", [exp]);
            }
            else if (this.isType(from, "BigNat")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("BKeyBBigNat_box", [exp]);
            }
            else if (this.isType(from, "String")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("BKeyBString_box", [exp]);
            }
            else if(this.isType(from, "UTCDateTime")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("BKeyBUTCDateTime_box", [exp]);
            }
            else if(this.isType(from, "CalendarDate")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("BKeyBCalendarDate_box", [exp]);
            }
            else if(this.isType(from, "RelativeTime")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("BKeyBRelativeTime_box", [exp]);
            }
            else if(this.isType(from, "TickTime")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("BKeyBTickTime_box", [exp]);
            }
            else if(this.isType(from, "LogicalTime")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("BKeyBLogicalTime_box", [exp]);
            }
            else if(this.isType(from, "ISOTimeStamp")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("BKeyBISOTimeStamp_box", [exp]);
            }
            else if(this.isType(from, "UUID4")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("BKeyBUUID4_box", [exp]);
            }
            else if(this.isType(from, "UUID7")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("BKeyBUUID7_box", [exp]);
            }
            else if(this.isType(from, "SHAContentHash")) {
                oftypetag = smtfrom.morphirtypetag;
                objval = new MorphirCallSimple("BKeyBSHAContentHash_box", [exp]);
            }
            else {
                const entity = this.assembly.entityDecls.get(from.typeID) as MIREntityTypeDecl;

                if (entity instanceof MIRStringOfInternalEntityTypeDecl) {
                    oftypetag = this.getMorphirTypeFor(this.getMIRType("String")).morphirtypetag;
                    objval = new MorphirCallSimple("BKeyBString_box", [exp]);
                }
                else if (entity instanceof MIRDataStringInternalEntityTypeDecl) {
                    oftypetag = this.getMorphirTypeFor(this.getMIRType("String")).morphirtypetag;
                    objval = new MorphirCallSimple("BKeyBString_box", [exp]);
                }
                else if (entity instanceof MIRConstructableInternalEntityTypeDecl) {
                    oftypetag = this.getMorphirTypeFor(this.getMIRType(entity.fromtype)).morphirtypetag;
                    objval = new MorphirCallSimple(this.getMorphirConstructorName(this.getMIRType(entity.fromtype)).box, [exp]);
                }
                else if (entity instanceof MIREnumEntityTypeDecl) {
                    oftypetag = this.getMorphirTypeFor(this.getMIRType("Nat")).morphirtypetag;
                    objval = new MorphirCallSimple("BKeyBNat_box", [exp]);
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

            return new MorphirCallSimple("BKey", [new MorphirConst(smtfrom.morphirtypetag), new MorphirConst(oftypetag), objval as MorphirExp]);
        }
    }

    private coerceFromAtomicToTerm(exp: MorphirExp, from: MIRType): MorphirExp {
        if (from.typeID === "None") {
            return new MorphirConst(`bterm_none`);
        }
        else if (from.typeID === "Nothing") {
            return new MorphirConst(`bterm_nothing`);
        }
        else {
            if(this.assembly.subtypeOf(from, this.getMIRType("KeyType"))) {
                return new MorphirCallSimple("BKeyObject", [this.coerceFromAtomicToKey(exp, from)]);
            }
            else {
                const smtfrom = this.getMorphirTypeFor(from);
                let objval: MorphirExp | undefined = undefined;

                if (this.isType(from, "Float")) {
                    objval = new MorphirCallSimple("BObjectBFloat_box", [exp]);
                }
                else if (this.isType(from, "Decimal")) {
                    objval = new MorphirCallSimple("BObjectBRational_box", [exp]);
                }
                else if (this.isType(from, "Rational")) {
                    objval = new MorphirCallSimple("BObjectBRational_box", [exp]);
                }
                else if (this.isType(from, "ByteBuffer")) {
                    objval = new MorphirCallSimple("BObjectBByteBuffer_box", [exp]);
                }
                else if(this.isType(from, "DateTime")) {
                    objval = new MorphirCallSimple("BObjectBDateTime_box", [exp]);
                }
                else if(this.isType(from, "LatLongCoordinate")) {
                    objval = new MorphirCallSimple("BObjectBLatLongCoordinate_box", [exp]);
                }
                else if (this.isType(from, "Regex")) {
                    objval = new MorphirCallSimple("BObjectRegex_box", [exp]);
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

                return new MorphirCallSimple("BTermObject", [new MorphirConst(smtfrom.morphirtypetag), objval as MorphirExp]);
            }
        }
    }

    private coerceKeyIntoAtomic(exp: MorphirExp, into: MIRType): MorphirExp {
        if (this.isType(into, "None")) {
            return new MorphirConst("bsqnone_literal");
        }
        else {
            const oexp = new MorphirCallSimple("bkey_extract_value", [exp]);

            if (this.isType(into, "Bool")) {
                return new MorphirCallSimple("unbox_BKeyBool", [oexp]);
            }
            else if (this.isType(into, "Int")) {
                return new MorphirCallSimple("unbox_BKeyBInt", [oexp]);
            }
            else if (this.isType(into, "Nat")) {
                return new MorphirCallSimple("unbox_BKeyBNat", [oexp]);
            }
            else if (this.isType(into, "BigInt")) {
                return new MorphirCallSimple("unbox_BKeyBBigInt", [oexp]);
            }
            else if (this.isType(into, "BigNat")) {
                return new MorphirCallSimple("unbox_BKeyBBigNat", [oexp]);
            }
            else if (this.isType(into, "String")) {
                return new MorphirCallSimple("unbox_BKeyBString", [oexp]);
            }
            else if(this.isType(into, "UTCDateTime")) {
                return new MorphirCallSimple("unbox_BKeyBUTCDateTime", [oexp]);
            }
            else if(this.isType(into, "CalendarDate")) {
                return new MorphirCallSimple("unbox_BKeyBCalendarDate", [oexp]);
            }
            else if(this.isType(into, "RelativeTime")) {
                return new MorphirCallSimple("unbox_BKeyBRelativeTime", [oexp]);
            }
            else if(this.isType(into, "TickTime")) {
                return new MorphirCallSimple("unbox_BKeyBTickTime", [oexp]);
            }
            else if(this.isType(into, "LogicalTime")) {
                return new MorphirCallSimple("unbox_BKeyBLogicalTime", [oexp]);
            }
            else if(this.isType(into, "ISOTimeStamp")) {
                return new MorphirCallSimple("unbox_BKeyBISOTimeStamp", [oexp]);
            }
            else if(this.isType(into, "UUID4")) {
                return new MorphirCallSimple("unbox_BKeyBUUID4", [oexp]);
            }
            else if(this.isType(into, "UUID7")) {
                return new MorphirCallSimple("unbox_BKeyBUUID7", [oexp]);
            }
            else if(this.isType(into, "SHAContentHash")) {
                return new MorphirCallSimple("unbox_BKeyBSHAContentHash", [oexp]);
            }
            else {
                assert(this.isUniqueEntityType(into));

                return new MorphirCallSimple(this.getMorphirConstructorName(into).unbox, [oexp]);
            }
        }
    }

    private coerceTermIntoAtomic(exp: MorphirExp, into: MIRType): MorphirExp {
        if (this.isType(into, "None")) {
            return new MorphirConst("bterm_none");
        }
        else if (this.isType(into, "Nothing")) {
            return new MorphirConst("bterm_nothing");
        }
        else {
            if(this.assembly.subtypeOf(into, this.getMIRType("KeyType"))) {
                return this.coerceKeyIntoAtomic(new MorphirCallSimple("getTermObj_BKey", [exp]), into)
            }
            else {
                const oexp = new MorphirCallSimple("getTermObj_BTerm", [exp]);

                if (this.isType(into, "Float")) {
                    return new MorphirCallSimple("unbox_BObjectBFloat", [oexp]);
                }
                else if (this.isType(into, "Decimal")) {
                    return new MorphirCallSimple("unbox_BObjectBDecimal", [oexp]);
                }
                else if (this.isType(into, "Rational")) {
                    return new MorphirCallSimple("unbox_BObjectBRational", [oexp]);
                }
                else if (this.isType(into, "ByteBuffer")) {
                    return new MorphirCallSimple("unbox_BObjectByteBuffer", [oexp]);
                }
                else if(this.isType(into, "DateTime")) {
                    return new MorphirCallSimple("unbox_BObjectBDateTime", [oexp]);
                }
                else if(this.isType(into, "LatLongCoordinate")) {
                    return new MorphirCallSimple("unbox_BObjectBLatLongCoordinate", [oexp]);
                }
                else if (this.isType(into, "Regex")) {
                    return new MorphirCallSimple("unbox_BObjectRegex", [oexp]);
                }
                else if (this.isUniqueTupleType(into)) {
                    return new MorphirCallSimple(this.getMorphirConstructorName(into).unbox, [oexp]);
                }
                else if (this.isUniqueRecordType(into)) {
                    return new MorphirCallSimple(this.getMorphirConstructorName(into).unbox, [oexp]);
                }
                else {
                    assert(this.isUniqueEntityType(into));

                    return new MorphirCallSimple(this.getMorphirConstructorName(into).unbox, [oexp]);
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
                return new MorphirCallSimple("getTermObj_BKey", [exp]);
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
                return new MorphirCallSimple("BKeyObject", [exp]);
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
                return new MorphirCallSimple("getTermObj_BKey", [exp]);
            }
            else {
                return this.coerceFromAtomicToKey(exp, from);
            }
        }
    }

    generateTupleIndexGetFunction(tt: MIRTupleType, idx: number): string {
        this.internTypeName(tt.typeID);
        return `${this.lookupTypeName(tt.typeID)}_${idx}`;
    } 

    generateRecordPropertyGetFunction(tt: MIRRecordType, pname: string): string {
        this.internTypeName(tt.typeID);
        return `${this.lookupTypeName(tt.typeID)}_${pname}`;
    }

    generateEntityFieldGetFunction(tt: MIREntityTypeDecl, field: MIRFieldDecl): string {
        this.internTypeName(tt.tkey);
        return `${this.lookupTypeName(tt.tkey)}_${field.fname}`;
    }

    generateEphemeralListGetFunction(tt: MIREphemeralListType, idx: number): string {
        this.internTypeName(tt.typeID);
        return `${this.lookupTypeName(tt.typeID)}_${idx}`;
    }

    generateResultType(ttype: MIRType): MorphirTypeInfo {
        return new MorphirTypeInfo(`Result String ${this.getMorphirTypeFor(ttype).morphirtypename}`, "[INTERNAL RESULT]", "[INTERNAL RESULT]");
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
        return new MorphirCallSimple("result_is_success", [exp]);
    }

    generateResultIsErrorTest(ttype: MIRType, exp: MorphirExp): MorphirExp {
        return new MorphirCallSimple("result_is_error", [exp]);
    }

    generateResultGetSuccess(ttype: MIRType, exp: MorphirExp): MorphirExp {
        const ufcname = `${this.getMorphirTypeFor(ttype).morphirtypename}@uicons_UF`;
        return new MorphirCallSimple("result_success_get_value", [exp, new MorphirConst(ufcname)]);
    }

    generateResultGetError(ttype: MIRType, exp: MorphirExp): MorphirExp {
        return new MorphirCallSimple("result_error_get_value", [exp]);
    }
    
    generateAccessWithSetGuardResultType(ttype: MIRType): MorphirTypeInfo {
        return new MorphirTypeInfo(`GuardResult_${this.getMorphirTypeFor(ttype).morphirtypename}`, "[INTERNAL GUARD RESULT]", "[INTERNAL GUARD RESULT]");
    }

    generateAccessWithSetGuardResultTypeConstructorLoad(ttype: MIRType, value: MorphirExp, flag: boolean): MorphirExp {
        return new MorphirCallSimple(`GuardResult_${this.getMorphirTypeFor(ttype).morphirtypename}_cons`, [value, new MorphirConst(flag ? "true" : "false")]);
    }

    generateAccessWithSetGuardResultGetValue(ttype: MIRType, exp: MorphirExp): MorphirExp {
        const ufcname = `${this.getMorphirTypeFor(ttype).morphirtypename}@uicons_UF`;
        return new MorphirCallSimple(`guard_result_${this.getMorphirTypeFor(ttype).morphirtypename}_result`, [exp, new MorphirConst(ufcname)]);
    }

    generateAccessWithSetGuardResultGetFlag(ttype: MIRType, exp: MorphirExp): MorphirExp {
        return new MorphirCallSimple(`guard_result_${this.getMorphirTypeFor(ttype).morphirtypename}_flag`, [exp]);
    }

    generateListTypeGetLength(ttype: MIRType, ll: MorphirExp): MorphirExp {
        return new MorphirCallSimple("length", [ll]);
    }

    generateListTypeGetLengthMinus1(ttype: MIRType, ll: MorphirExp): MorphirExp {
        const len = this.generateListTypeGetLength(ttype, ll);
        return new MorphirCallSimple("-", [len, new MorphirConst("1")], true);
    }

    generateMapTypeGetLength(ttype: MIRType, mm: MorphirExp): MorphirExp {
        return new MorphirCallSimple("length", [mm]);
    }
}

export {
    MorphirTypeEmitter
};
