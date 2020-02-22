//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIREntityTypeDecl, MIRInvokeDecl, MIRTupleType, MIRRecordType, MIREntityType, MIRConceptType, MIREphemeralListType, MIRRecordTypeEntry } from "../../compiler/mir_assembly";
import { MIRResolvedTypeKey, MIRNominalTypeKey } from "../../compiler/mir_ops";

import * as assert from "assert";

class CPPTypeEmitter {
    readonly assembly: MIRAssembly;

    readonly anyType: MIRType;

    readonly noneType: MIRType;
    readonly boolType: MIRType;
    readonly intType: MIRType;
    readonly stringType: MIRType;

    readonly keyType: MIRType;
    readonly validatorType: MIRType;
    readonly podType: MIRType;
    readonly apiType: MIRType;
    readonly tupleType: MIRType;
    readonly recordType: MIRType;

    readonly enumtype: MIRType;
    readonly idkeytype: MIRType;
    readonly guididkeytype: MIRType;
    readonly logicaltimeidkeytype: MIRType;
    readonly contenthashidkeytype: MIRType;    

    private mangledNameMap: Map<string, string> = new Map<string, string>();

    conceptSubtypeRelation: Map<MIRNominalTypeKey, MIRNominalTypeKey[]> = new Map<MIRNominalTypeKey, MIRNominalTypeKey[]>();

    constructor(assembly: MIRAssembly) {
        this.assembly = assembly;

        this.anyType = assembly.typeMap.get("NSCore::Any") as MIRType;

        this.noneType = assembly.typeMap.get("NSCore::None") as MIRType;
        this.boolType = assembly.typeMap.get("NSCore::Bool") as MIRType;
        this.intType = assembly.typeMap.get("NSCore::Int") as MIRType;
        this.stringType = assembly.typeMap.get("NSCore::String") as MIRType;

        this.keyType = assembly.typeMap.get("NSCore::KeyType") as MIRType;
        this.validatorType = assembly.typeMap.get("NSCore::Validator") as MIRType;
        this.podType = assembly.typeMap.get("NSCore::PODType") as MIRType;
        this.apiType = assembly.typeMap.get("NSCore::APIType") as MIRType;
        this.tupleType = assembly.typeMap.get("NSCore::Tuple") as MIRType;
        this.recordType = assembly.typeMap.get("NSCore::Record") as MIRType;

        this.enumtype = assembly.typeMap.get("NSCore::Enum") as MIRType;
        this.idkeytype = assembly.typeMap.get("NSCore::IdKey") as MIRType;
        this.guididkeytype = assembly.typeMap.get("NSCore::GUIDIdKey") as MIRType;
        this.logicaltimeidkeytype = assembly.typeMap.get("NSCore::LogicalTimeIdKey") as MIRType;
        this.contenthashidkeytype = assembly.typeMap.get("NSCore::ContentHashIdKey") as MIRType;
    }

    mangleStringForCpp(name: string): string {
        if (!this.mangledNameMap.has(name)) {
            const cleanname = name.replace(/\W/g, "_").toLowerCase() + "I" + this.mangledNameMap.size + "I";
            this.mangledNameMap.set(name, cleanname);
        }

        return this.mangledNameMap.get(name) as string;
    }

    getMIRType(tkey: MIRResolvedTypeKey): MIRType {
        return this.assembly.typeMap.get(tkey) as MIRType;
    }

    typecheckIsName(tt: MIRType, oftype: RegExp, match?: "exact" | "may"): boolean {
        match = match || "exact";
        if(match === "exact") {
            return tt.options.length === 1 && (tt.options[0] instanceof MIREntityType) && oftype.test(tt.options[0].trkey);
        }
        else {
            return tt.options.some((opt) => (opt instanceof MIREntityType) && oftype.test(opt.trkey));
        }
    }

    typecheckEntityAndProvidesName(tt: MIRType, oftype: MIRType, match?: "exact" | "may"): boolean {
        match = match || "exact";
        if(match === "exact") {
            return tt.options.length === 1 && (tt.options[0] instanceof MIREntityType) && this.assembly.subtypeOf(tt, oftype);
        }
        else {
            return tt.options.some((opt) => (opt instanceof MIREntityType) && this.assembly.subtypeOf(MIRType.createSingle(opt), oftype));
        }
    }

    typecheckTuple(tt: MIRType, match?: "known" | "tuple"): boolean {
        match = match || "tuple";
        if(match === "known") {
            return tt.options.length === 1 && (tt.options[0] instanceof MIRTupleType) && !(tt.options[0] as MIRTupleType).entries.some((entry) => entry.isOptional);
        }
        else {
            return tt.options.every((opt) => opt instanceof MIRTupleType);
        }
    }

    typecheckRecord(tt: MIRType, match?: "known" | "record"): boolean {
        match = match || "record";
        if(match === "known") {
            return tt.options.length === 1 && (tt.options[0] instanceof MIRRecordType) && !(tt.options[0] as MIRRecordType).entries.some((entry) => entry.isOptional);
        }
        else {
            return tt.options.every((opt) => opt instanceof MIRRecordType);
        }
    }

    typecheckUEntity(tt: MIRType, match?: "exact" | "may"): boolean {
        match = match || "exact";
        if(match === "exact") {
            return tt.options.length === 1 && (tt.options[0] instanceof MIREntityType) && tt.options[0].trkey !== "NSCore::None";
        }
        else {
            return tt.options.some((opt) => (opt instanceof MIREntityType) && opt.trkey !== "NSCore::None");
        }
    }

    typecheckAllKeys(tt: MIRType): boolean {
        return tt.options.every((opt) => this.assembly.subtypeOf(MIRType.createSingle(opt), this.keyType));
    }

    typecheckEphemeral(tt: MIRType): boolean {
        return tt.options.length === 1 && tt.options[0] instanceof MIREphemeralListType;
    }
    
    typecheckIsNoneable(tt: MIRType): boolean {
        return tt.options.some((opt) => (opt instanceof MIREntityType) && opt.trkey === "NSCore::None");
    }

    typecheckIsPOD_Always(tt: MIRType): boolean {
        return this.assembly.subtypeOf(tt, this.podType);
    }

    typecheckIsPOD_Never(tt: MIRType): boolean {
        return tt.options.every((opt) => {
            if(opt instanceof MIREntityType) {
                return !this.assembly.subtypeOf(this.getMIRType(opt.trkey), this.podType);
            }
            else if (opt instanceof MIRConceptType) {
                return false; //TODO: this is very conservative -- we could do better by enumerating possible entities 
            }
            else if (opt instanceof MIRTupleType) {
                return opt.entries.some((entry) => !entry.isOptional && this.typecheckIsPOD_Never(entry.type));
            }
            else if (opt instanceof MIRRecordType) {
                return opt.entries.some((entry) => !entry.isOptional && this.typecheckIsPOD_Never(entry.type));
            }
            else {
                return false;
            }
        });
    }

    typecheckIsAPI_Always(tt: MIRType): boolean {
        return this.assembly.subtypeOf(tt, this.apiType);
    }

    typecheckIsAPI_Never(tt: MIRType): boolean {
        return tt.options.every((opt) => {
            if(opt instanceof MIREntityType) {
                return !this.assembly.subtypeOf(this.getMIRType(opt.trkey), this.apiType);
            }
            else if (opt instanceof MIRConceptType) {
                return false; //TODO: this is very conservative -- we could do better by enumerating possible entities 
            }
            else if (opt instanceof MIRTupleType) {
                return opt.entries.some((entry) => !entry.isOptional && this.typecheckIsAPI_Never(entry.type));
            }
            else if (opt instanceof MIRRecordType) {
                return opt.entries.some((entry) => !entry.isOptional && this.typecheckIsAPI_Never(entry.type));
            }
            else {
                return false;
            }
        });
    }

    generateInitialDataKindFlag(tt: MIRType): string {
        if(this.typecheckIsPOD_Always(tt)) {
            return "DATA_KIND_POD_FLAG";
        }

        if(this.typecheckIsAPI_Always(tt)) {
            return "DATA_KIND_API_FLAG";
        }

        if(this.typecheckIsAPI_Never(tt) && this.typecheckIsPOD_Never(tt)) {
            return "DATA_KIND_CLEAR_FLAG";
        }

        return "DATA_KIND_UNKNOWN_FLAG";
    }

    getCPPTypeFor(tt: MIRType, declspec: "base" | "parameter" | "return" | "storage"): string {
        if (this.typecheckIsName(tt, /^NSCore::Bool$/)) {
            return "bool";
        }
        else if (this.typecheckIsName(tt, /^NSCore::Int$/)) {
            return "IntValue";
        }
        else if (this.typecheckIsName(tt, /^NSCore::String$/)) {
            return "BSQString" + (declspec !== "base" ? "*" : "");
        }
        else if (this.typecheckIsName(tt, /^NSCore::SafeString<.*>$/)) {
            return "BSQSafeString" + (declspec !== "base" ? "*" : "");
        }
        else if (this.typecheckIsName(tt, /^NSCore::StringOf<.*>$/)) {
            return "BSQStringOf" + (declspec !== "base" ? "*" : "");
        }
        else if (this.typecheckIsName(tt, /^NSCore::GUID$/)) {
            return "BSQGUID" + (declspec !== "base" ? "*" : "");
        }
        else if (this.typecheckIsName(tt, /^NSCore::LogicalTime$/)) {
            return "BSQLogicalTime";
        }
        else if (this.typecheckIsName(tt, /^NSCore::DataHash$/)) {
            return "BSQDataHash";
        }
        else if (this.typecheckIsName(tt, /^NSCore::CryptoHash$/)) {
            return "BSQCryptoHash" + (declspec !== "base" ? "*" : "");
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.enumtype)) {
            return "BSQEnum";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.idkeytype)) {
            return "BSQIdKey" + (declspec !== "base" ? "*" : "");
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.guididkeytype)) {
            return "BSQGUIDIdKey" + (declspec !== "base" ? "*" : "");
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.logicaltimeidkeytype)) {
            return "BSQLogicalTimeIdKey";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.contenthashidkeytype)) {
            return "BSQContentHashIdKey" + (declspec !== "base" ? "*" : "");
        }
        else {
            if (this.typecheckAllKeys(tt)) {
                return "KeyValue";
            }
            else if (this.typecheckIsName(tt, /^NSCore::Buffer<.*>$/)) {
                return "BSQBuffer" + (declspec !== "base" ? "*" : "");
            }
            else if (this.typecheckIsName(tt, /^NSCore::ISOTime$/)) {
                return "BSQISOTime" + (declspec !== "base" ? "*" : "");
            }
            else if (this.typecheckIsName(tt, /^NSCore::Regex$/)) {
                return "BSQRegex" + (declspec !== "base" ? "*" : "");
            }
            else if (this.typecheckTuple(tt)) {
                return "BSQTuple" + (declspec !== "base" ? "*" : "");
            }
            else if (this.typecheckRecord(tt)) {
                return "BSQRecord" + (declspec !== "base" ? "*" : "");
            }
            else if(this.typecheckUEntity(tt)) {
                return this.mangleStringForCpp(tt.trkey) + (declspec !== "base" ? "*" : "");
            }
            else if(this.typecheckEphemeral(tt)) {
                return this.mangleStringForCpp(tt.trkey);
            }
            else {
                return "Value";
            }
        }
    }

    private coerceFromAtomicKey(exp: string, from: MIRType): string {
        const scope = this.mangleStringForCpp("$scope$");
        if (from.trkey === "NSCore::None") {
            return "BSQ_VALUE_NONE";
        }
        else if (this.typecheckIsName(from, /^NSCore::Bool$/)) {
            return `BSQ_ENCODE_VALUE_BOOL(${exp})`;
        }
        else if (this.typecheckIsName(from, /^NSCore::LogicalTime$/)) {
            return `BSQ_NEW_ADD_SCOPE(${scope}, BSQLogicalTime, ${exp})`;
        }
        else if (this.typecheckIsName(from, /^NSCore::DataHash$/)) {
            return `BSQ_NEW_ADD_SCOPE(${scope}, BSQDataHash, ${exp})`;
        }
        else if (this.typecheckEntityAndProvidesName(from, this.enumtype)) {
            return `BSQ_NEW_ADD_SCOPE(${scope}, BSQEnum, ${exp})`;
        }
        else if (this.typecheckEntityAndProvidesName(from, this.logicaltimeidkeytype)) {
            return `BSQ_NEW_ADD_SCOPE(${scope}, BSQLogicalTimeIdKey, ${exp})`;
        }
        else {
            return exp;
        }
    }

    private coerceFromOptionsKey(exp: string, into: MIRType): string {
        if (this.typecheckIsName(into, /^NSCore::Bool$/)) {
            return `BSQ_GET_VALUE_BOOL(${exp})`;
        }
        else if (this.typecheckIsName(into, /^NSCore::LogicalTime$/)) {
            return `*BSQ_GET_VALUE_PTR(${exp}, BSQLogicalTime)`;
        }
        else if (this.typecheckIsName(into, /^NSCore::DataHash$/)) {
            return `*BSQ_GET_VALUE_PTR(${exp}, BSQDataHash)`;
        }
        else if (this.typecheckEntityAndProvidesName(into, this.enumtype)) {
            return `*BSQ_GET_VALUE_PTR(${exp}, BSQEnum)`;
        }
        else if (this.typecheckEntityAndProvidesName(into, this.logicaltimeidkeytype)) {
            return `*BSQ_GET_VALUE_PTR(${exp}, BSQLogicalTimeIdKey)`;
        }
        else {
            return `BSQ_GET_VALUE_PTR(${exp}, ${this.getCPPTypeFor(into, "base")})`;
        }
    }

    private coerceIntoAtomicKey(exp: string, into: MIRType): string {
        if (this.typecheckIsName(into, /^NSCore::Bool$/)) {
            return `BSQ_GET_VALUE_BOOL(${exp})`;
        }
        else if (this.typecheckIsName(into, /^NSCore::LogicalTime$/)) {
            return `*BSQ_GET_VALUE_PTR(${exp}, BSQLogicalTime)`;
        }
        else if (this.typecheckIsName(into, /^NSCore::DataHash$/)) {
            return `*BSQ_GET_VALUE_PTR(${exp}, BSQDataHash)`;
        }
        else if (this.typecheckEntityAndProvidesName(into, this.enumtype)) {
            return `*BSQ_GET_VALUE_PTR(${exp}, BSQEnum)`;
        }
        else if (this.typecheckEntityAndProvidesName(into, this.logicaltimeidkeytype)) {
            return `*BSQ_GET_VALUE_PTR(${exp}, BSQLogicalTimeIdKey)`;
        }
        else {
            return `BSQ_GET_VALUE_PTR(${exp}, ${this.getCPPTypeFor(into, "base")})`;
        }
    }

    private coerceIntoAtomicTerm(exp: string, into: MIRType): string {
        if (this.typecheckIsName(into, /^NSCore::Buffer<.*>$/) || this.typecheckIsName(into, /^NSCore::ISOTime$/) || this.typecheckIsName(into, /^NSCore::Regex$/)) {
            return `BSQ_GET_VALUE_PTR(${exp}, ${this.getCPPTypeFor(into, "base")})`;
        }
        else if (this.typecheckTuple(into)) {
            return `BSQ_GET_VALUE_PTR(${exp}, BSQTuple)`;
        }
        else if (this.typecheckRecord(into)) {
            return `BSQ_GET_VALUE_PTR(${exp}, BSQRecord)`;
        }
        else {
            return `BSQ_GET_VALUE_PTR(${exp}, ${this.getCPPTypeFor(into, "base")})`;
        }
    }

    coerce(exp: string, from: MIRType, into: MIRType): string {
        if (this.getCPPTypeFor(from, "base") === this.getCPPTypeFor(into, "base")) {
            return exp;
        }

        if (from.trkey === "NSCore::None") {
            return this.coerceFromAtomicKey(exp, from);
        }
        else if (this.typecheckIsName(from, /^NSCore::Bool$/) || this.typecheckIsName(from, /^NSCore::Int$/) || this.typecheckIsName(from, /^NSCore::String$/)) {
            return this.coerceFromAtomicKey(exp, from);
        }
        else if (this.typecheckIsName(from, /^NSCore::SafeString<.*>$/) || this.typecheckIsName(from, /^NSCore::StringOf<.*>$/) 
            || this.typecheckIsName(from, /^NSCore::GUID$/) || this.typecheckIsName(from, /^NSCore::LogicalTime$/)
            || this.typecheckIsName(from, /^NSCore::DataHash$/) || this.typecheckIsName(from, /^NSCore::CryptoHash$/)) {
            return this.coerceFromAtomicKey(exp, from);
        }
        else if (this.typecheckEntityAndProvidesName(from, this.enumtype) || this.typecheckEntityAndProvidesName(from, this.idkeytype) || this.typecheckEntityAndProvidesName(from, this.guididkeytype)
            || this.typecheckEntityAndProvidesName(from, this.logicaltimeidkeytype) || this.typecheckEntityAndProvidesName(from, this.contenthashidkeytype)) {
            return this.coerceFromAtomicKey(exp, from);
        }
        else if (this.typecheckAllKeys(from)) {
            const intotype = this.getCPPTypeFor(into, "base");
            if(intotype === "Value") {
                return exp;
            }
            else {
                return this.coerceFromOptionsKey(exp, into);
            }
        }
        else if (this.typecheckIsName(from, /^NSCore::Buffer<.*>$/) || this.typecheckIsName(from, /^NSCore::ISOTime$/) || this.typecheckIsName(from, /^NSCore::Regex$/)
            || this.typecheckTuple(from) || this.typecheckRecord(from)) {
            return exp;
        }
        else if (this.typecheckUEntity(from)) {
            return exp;
        }
        else {
           //now from must be Bterm so we are projecting down
           assert(this.getCPPTypeFor(from, "base") === "Value");

           if (into.trkey === "NSCore::None") {
               return this.coerceIntoAtomicKey(exp, into);
           }
           else if (this.typecheckIsName(into, /^NSCore::Bool$/) || this.typecheckIsName(into, /^NSCore::Int$/) || this.typecheckIsName(into, /^NSCore::String$/)) {
               return this.coerceIntoAtomicKey(exp, into);
           }
           else if (this.typecheckIsName(from, /^NSCore::SafeString<.*>$/) || this.typecheckIsName(into, /^NSCore::StringOf<.*>$/) 
                || this.typecheckIsName(into, /^NSCore::GUID$/) || this.typecheckIsName(into, /^NSCore::LogicalTime$/)
                || this.typecheckIsName(into, /^NSCore::DataHash$/) || this.typecheckIsName(into, /^NSCore::CryptoHash$/)) {
               return this.coerceIntoAtomicKey(exp, into);
           }
           else if (this.typecheckEntityAndProvidesName(into, this.enumtype) || this.typecheckEntityAndProvidesName(into, this.idkeytype) || this.typecheckEntityAndProvidesName(into, this.guididkeytype)
                || this.typecheckEntityAndProvidesName(into, this.logicaltimeidkeytype) || this.typecheckEntityAndProvidesName(into, this.contenthashidkeytype)) {
                return this.coerceIntoAtomicKey(exp, into);
           }
           else if (this.typecheckAllKeys(into)) {
                return `((KeyValue)${exp})`;
           }
           else if (this.typecheckIsName(into, /^NSCore::Buffer<.*>$/) || this.typecheckIsName(into, /^NSCore::ISOTime$/) || this.typecheckIsName(into, /^NSCore::Regex$/)) {
                return this.coerceIntoAtomicTerm(exp, into);
           }
           else if (this.typecheckTuple(into) || this.typecheckRecord(into)) {
                return this.coerceIntoAtomicTerm(exp, into);
           }
           else {
                assert(this.typecheckUEntity(into));

                return this.coerceIntoAtomicTerm(exp, into);
           }
        }
    }

    getKeyProjectedTypeFrom(ktype: MIRType): MIRType {
        if(this.typecheckAllKeys(ktype)) {
            return ktype;
        }
        else {
            assert(false);
            return ktype;
        }
    }
    
    getKeyFrom(arg: string, atype: MIRType): string {
        if(this.typecheckAllKeys(atype)) {
            return arg;
        }
        else {
            assert(false);
            return "[NOT IMPLEMENTED]";
        }
    }

    tupleHasIndex(tt: MIRType, idx: number): "yes" | "no" | "maybe" {
        if(tt.options.every((opt) => opt instanceof MIRTupleType && idx < opt.entries.length && !opt.entries[idx].isOptional)) {
            return "yes";
        }
        else if(tt.options.every((opt) => opt instanceof MIRTupleType && opt.entries.length <= idx)) {
            return "no";
        }
        else {
            return "maybe";
        }
    }

    getMaxTupleLength(tt: MIRType): number {
        const lens = tt.options.map((opt) => (opt as MIRTupleType).entries.length);
        return Math.max(...lens);
    }

    recordHasField(tt: MIRType, pname: string): "yes" | "no" | "maybe" {
        if(tt.options.every((opt) => opt instanceof MIRRecordType && opt.entries.find((entry) => entry.name === pname) !== undefined && !(opt.entries.find((entry) => entry.name === pname) as MIRRecordTypeEntry).isOptional)) {
            return "yes";
        }
        else if(tt.options.every((opt) => opt instanceof MIRRecordType && opt.entries.find((entry) => entry.name === pname) === undefined)) {
            return "no";
        }
        else {
            return "maybe";
        }
    }
    
    getMaxPropertySet(tt: MIRType): string[] {
        let props = new Set<string>();
        tt.options.forEach((opt) => (opt as MIRRecordType).entries.forEach((entry) => props.add(entry.name)));

        return [...props].sort();
    }

    getEntityEKey(tt: MIRType): MIRNominalTypeKey {
        return (tt.options[0] as MIREntityType).ekey;
    }
    
    getRefCountableStatus(tt: MIRType): "no" | "int" | "direct" | "checked" | "special" {
        if (this.typecheckIsName(tt, /^NSCore::None$/) || this.typecheckIsName(tt, /^NSCore::Bool$/)) {
            return "no";
        }
        else if (this.typecheckIsName(tt, /^NSCore::Int$/)) {
            return "int";
        }
        else if (this.typecheckIsName(tt, /^NSCore::String$/) || this.typecheckIsName(tt, /^NSCore::SafeString<.*>$/) || this.typecheckIsName(tt, /^NSCore::StringOf<.*>$/)) {
            return "direct";
        }
        else if (this.typecheckIsName(tt, /^NSCore::GUID$/) || this.typecheckIsName(tt, /^NSCore::CryptoHash$/)) {
            return "direct";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.idkeytype) || this.typecheckEntityAndProvidesName(tt, this.guididkeytype) || this.typecheckEntityAndProvidesName(tt, this.contenthashidkeytype)) {
            return "direct";
        }
        else if (this.typecheckIsName(tt, /^NSCore::LogicalTime$/) || this.typecheckIsName(tt, /^NSCore::DataHash$/)) {
            return "no";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.enumtype) || this.typecheckEntityAndProvidesName(tt, this.logicaltimeidkeytype)) {
            return "no";
        }
        else {
            if (this.typecheckAllKeys(tt)) {
                return "checked";
            }
            else if (this.typecheckIsName(tt, /^NSCore::Buffer<.*>$/) || this.typecheckIsName(tt, /^NSCore::ISOTime$/) || this.typecheckIsName(tt, /^NSCore::Regex$/)) {
                return "direct";
            }
            else if (this.typecheckTuple(tt) || this.typecheckRecord(tt)) {
                return "direct";
            }
            else if(this.typecheckUEntity(tt)) {
                return "direct";
            }
            else if(this.typecheckEphemeral(tt)) {
                return "special";
            }
            else {
                return "checked";
            }
        }
    }

    getIncOpForType(tt: MIRType, arg: string): string {
        const rcinfo = this.getRefCountableStatus(tt);
        if (rcinfo === "no") {
            return arg;
        }
        else {
            const btype = this.getCPPTypeFor(tt, "base");

            if (rcinfo === "int") {
                return `INC_REF_CHECK(${btype}, ${arg})`;
            }
            else if (rcinfo === "direct") {
                return `INC_REF_DIRECT(${btype}, ${arg})`;
            }
            else if (rcinfo === "checked") {
                return `INC_REF_CHECK(${btype}, ${arg})`;
            }
            else {
                assert(false); //only option right now is ephemeral lists but we should't be doing this with them
                return "[INVALID]"
            }
        }
    }

    getDecOpForType(tt: MIRType, arg: string): string {
        const rcinfo = this.getRefCountableStatus(tt);
        if (rcinfo === "no") {
            return "";
        }
        else if (rcinfo === "int") {
            return `BSQRef::decrementChecked(${arg})`;
        }
        else if (rcinfo === "direct") {
            return `BSQRef::decrementDirect(${arg})`;
        }
        else if (rcinfo === "checked") {
            return `BSQRef::decrementChecked(${arg})`;
        }
        else {
            assert(false); //only option right now is ephemeral lists but we should't be doing this with them
            return "[INVALID]"
        }
    }

    getGetKeyOpForType(tt: MIRType, arg: string): string {
        if(this.typecheckAllKeys(tt)) {
            return arg;
        }
        else {
            assert(false);
            return "[INVALID]"
        }
    }

    getGetCMPOpsForKeyType(tt: MIRType): { hash: string, eq: string, cmp: string } {
        const tval = this.getCPPTypeFor(tt, "base");
        const hf = `HashFunctor_${tval}{}`;
        const eqf = `EqualFunctor_${tval}{}`;
        const cmpf = `LessFunctor_${tval}`;

        return { hash: hf, eq: eqf, cmp: cmpf };
    }

    isSpecialReprEntity(tt: MIRType): boolean {
        if (this.typecheckIsName(tt, /^NSCore::None$/) || this.typecheckIsName(tt, /^NSCore::Bool$/) || this.typecheckIsName(tt, /^NSCore::Int$/) || this.typecheckIsName(tt, /^NSCore::String$/)) {
            return true;
        }
        else if (this.typecheckIsName(tt, /^NSCore::SafeString<.*>$/) || this.typecheckIsName(tt, /^NSCore::StringOf<.*>$/)) {
            return true;
        }
        else if (this.typecheckIsName(tt, /^NSCore::GUID$/) || this.typecheckIsName(tt, /^NSCore::LogicalTime$/) || this.typecheckIsName(tt, /^NSCore::DataHash$/) || this.typecheckIsName(tt, /^NSCore::CryptoHash$/)) {
            return true;
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.enumtype) || this.typecheckEntityAndProvidesName(tt, this.idkeytype) || this.typecheckEntityAndProvidesName(tt, this.guididkeytype)
            || this.typecheckEntityAndProvidesName(tt, this.logicaltimeidkeytype) || this.typecheckEntityAndProvidesName(tt, this.contenthashidkeytype)) {
           return true;
        }
        else {
            if (this.typecheckIsName(tt, /^NSCore::Buffer<.*>$/) || this.typecheckIsName(tt, /^NSCore::ISOTime$/) || this.typecheckIsName(tt, /^NSCore::Regex$/)) {
                return true;
            }
            else {
                return false;
            }
        }
    }

    typeToCPPDefaultValue(ttype: MIRType): string {
        if ( this.typecheckIsName(ttype, /^NSCore::Bool$/)) {
            return "false"
        }
        else if (this.typecheckIsName(ttype, /^NSCore::Int$/)) {
            return "BSQ_VALUE_0";
        }
        else if (this.typecheckIsName(ttype, /^NSCore::LogicalTime$/) || this.typecheckIsName(ttype, /^NSCore::DataHash$/)) {
            return `${this.getCPPTypeFor(ttype, "storage")}{}`;
        }
        else if (this.typecheckEntityAndProvidesName(ttype, this.enumtype) || this.typecheckEntityAndProvidesName(ttype, this.logicaltimeidkeytype)) {
            return `${this.getCPPTypeFor(ttype, "storage")}{}`;
        }
        else {
            return "nullptr";
        }
    }

    initializeConceptSubtypeRelation(): void {
        this.assembly.conceptDecls.forEach((tt) => {
            const cctype = this.getMIRType(tt.tkey);
            const est = [...this.assembly.entityDecls].map((edecl) => this.getMIRType(edecl[0])).filter((et) => this.assembly.subtypeOf(et, cctype));
            const keyarray = est.map((et) => et.trkey).sort();

            this.conceptSubtypeRelation.set(tt.tkey, keyarray);
        });
    }

    getSubtypesArrayCount(ckey: MIRNominalTypeKey): number {
        return (this.conceptSubtypeRelation.get(ckey) as string[]).length;
    }

    generateConstructorArgInc(argtype: MIRType, arg: string): string {
        const rcinfo = this.getRefCountableStatus(argtype);
        if (rcinfo === "no") {
            return arg;
        }

        return this.getIncOpForType(argtype, arg);
    }

    generateListCPPEntity(entity: MIREntityTypeDecl, templatefile: string): { fwddecl: string, fulldecl: string } {
        const tt = this.getMIRType(entity.tkey);
        const declname = this.getCPPTypeFor(tt, "base");

        const typet = entity.terms.get("T") as MIRType;

        const decl = `#define Ty ${declname}\n`
        + `#define T ${this.getCPPTypeFor(typet, "storage")}\n`
        + `#define INC_RC_T(X) ${this.getIncOpForType(typet, "X")}\n`
        + `#define DEC_RC_T(X) ${this.getDecOpForType(typet, "X")}\n`
        + `#define FDisplay(X) diagnostic_format(${this.coerce("X", typet, this.anyType)})\n`
        + "\n"
        + `#include ${templatefile}\n`;

        return { fwddecl: `class ${declname};`, fulldecl: decl };
    }

    generateSetCPPEntity(entity: MIREntityTypeDecl, templatefile: string): { fwddecl: string, fulldecl: string } {
        const tt = this.getMIRType(entity.tkey);
        const declname = this.getCPPTypeFor(tt, "base");

        const typet = entity.terms.get("T") as MIRType;
        const typekp = this.getKeyProjectedTypeFrom(typet);
        const typekl = ([...this.assembly.entityDecls].find((e) => e[1].ns === "NSCore" && e[1].name === "KeyList" && (e[1].terms.get("K") as MIRType).trkey === typekp.trkey) as [string, MIREntityTypeDecl]);

        const decl = `#define Ty ${declname}\n`
        + `#define T ${this.getCPPTypeFor(typet, "storage")}\n`
        + `#define INC_RC_T(X) ${this.getIncOpForType(typet, "X")}\n`
        + `#define DEC_RC_T(X) ${this.getDecOpForType(typet, "X")}\n`
        + `#define T_GET_KEY(X) ${this.getGetKeyOpForType(typet, "X")}\n`
        + `#define K ${this.getCPPTypeFor(typekp, "storage")}\n`
        + `#define INC_RC_K(X) ${this.getIncOpForType(typekp, "X")}\n`
        + `#define DEC_RC_K(X) ${this.getDecOpForType(typekp, "X")}\n`
        + `#define K_LIST ${this.getCPPTypeFor(this.getMIRType(typekl[0]), "base")}\n`
        + `#define KLCONS(K, KL) ${this.mangleStringForCpp(typekl[0])}$cons(K, KL)\n`
        + `#define K_CMP ${this.getGetCMPOpsForKeyType(typekp).cmp}\n`
        + `#define K_EQ(X, Y) ${this.getGetCMPOpsForKeyType(typekp).eq}(X, Y)\n`
        + `#define FDisplay(X) diagnostic_format(${this.coerce("X", typet, this.anyType)})\n`
        + "\n"
        + `#include ${templatefile}\n`;

        return { fwddecl: `class ${declname};`, fulldecl: decl };
    }

    generateMapCPPEntity(entity: MIREntityTypeDecl, templatefile: string): { fwddecl: string, fulldecl: string } {
        const tt = this.getMIRType(entity.tkey);
        const declname = this.getCPPTypeFor(tt, "base");

        const typet = entity.terms.get("K") as MIRType;
        const typeu = entity.terms.get("V") as MIRType;
        const typekp = this.getKeyProjectedTypeFrom(typet);
        const typekl = ([...this.assembly.entityDecls].find((e) => e[1].ns === "NSCore" && e[1].name === "KeyList" && (e[1].terms.get("K") as MIRType).trkey === typekp.trkey) as [string, MIREntityTypeDecl])[1];

        const decl = `#define Ty ${declname}\n`
        + `#define T ${this.getCPPTypeFor(typet, "storage")}\n`
        + `#define INC_RC_T(X) ${this.getIncOpForType(typet, "X")}\n`
        + `#define DEC_RC_T(X) ${this.getDecOpForType(typet, "X")}\n`
        + `#define T_GET_KEY(X) ${this.getGetKeyOpForType(typet, "X")}\n`

        + `#define U ${this.getCPPTypeFor(typeu, "storage")}\n`
        + `#define INC_RC_U(X) ${this.getIncOpForType(typeu, "X")}\n`
        + `#define DEC_RC_U(X) ${this.getDecOpForType(typeu, "X")}\n`

        + `#define K ${this.getCPPTypeFor(typekp, "storage")}\n`
        + `#define INC_RC_K(X) ${this.getIncOpForType(typekp, "X")}\n`
        + `#define DEC_RC_K(X) ${this.getDecOpForType(typekp, "X")}\n`
        + `#define K_LIST ${this.getCPPTypeFor(this.getMIRType(typekl.tkey), "base")}\n`
        + `#define KLCONS(K, KL) ${this.mangleStringForCpp(typekl.tkey)}$cons(K, KL)\n`
        + `#define K_CMP ${this.getGetCMPOpsForKeyType(typekp).cmp}\n`
        + `#define K_EQ(X, Y) ${this.getGetCMPOpsForKeyType(typekp).eq}(X, Y)\n`
        + `#define TDisplay(X) diagnostic_format(${this.coerce("X", typet, this.anyType)})\n`
        + `#define UDisplay(X) diagnostic_format(${this.coerce("X", typeu, this.anyType)})\n`
        + "\n"
        + `#include ${templatefile}\n`;

        return { fwddecl: `class ${declname};`, fulldecl: decl };
    }

    generateCPPEntity(entity: MIREntityTypeDecl, specialReps: Map<string, string>): { fwddecl: string, fulldecl: string } | undefined {
        const tt = this.getMIRType(entity.tkey);

        if(this.isSpecialReprEntity(tt)) {
            return undefined;
        }

        if(this.typecheckIsName(tt, /^NSCore::List<.*>$/)) {
            return this.generateListCPPEntity(entity, specialReps.get("list") as string);
        }
        else if(this.typecheckIsName(tt, /^NSCore::Set<.*>$/)) {
            return this.generateSetCPPEntity(entity, specialReps.get("set") as string);
        }
        else if(this.typecheckIsName(tt, /^NSCore::Map<.*>$/)) {
            return this.generateMapCPPEntity(entity, specialReps.get("map") as string);
        }
        else {
            const constructor_args = entity.fields.map((fd) => {
                return `${this.getCPPTypeFor(this.getMIRType(fd.declaredType), "parameter")} ${fd.name}`;
            });

            const constructor_initializer = entity.fields.map((fd) => {
                return `${this.mangleStringForCpp(fd.fkey)}(${fd.name})`;
            });

            const destructor_list = entity.fields.map((fd) => {
                const rcinfo = this.getRefCountableStatus(this.getMIRType(fd.declaredType));
                if (rcinfo === "no") {
                    return undefined;
                }

                const arg = `this->${this.mangleStringForCpp(fd.fkey)}`;
                return `${this.getDecOpForType(this.getMIRType(fd.declaredType), arg)};`;
            })
            .filter((fd) => fd !== undefined);

            const fields = entity.fields.map((fd) => {
                return `${this.getCPPTypeFor(this.getMIRType(fd.declaredType), "storage")} ${this.mangleStringForCpp(fd.fkey)};`;
            });

            const vfield_accessors = entity.fields.map((fd) => {
                if (fd.enclosingDecl === entity.tkey) {
                    return "NA";
                }
                else {
                    const fn = `this->${this.mangleStringForCpp(fd.fkey)}`;
                    return `${this.getCPPTypeFor(this.getMIRType(fd.declaredType), "return")} get$${this.mangleStringForCpp(fd.fkey)}() { return ${fn}; };`;
                }
            });

            const vcalls = [...entity.vcallMap].map((callp) => {
                const rcall = (this.assembly.invokeDecls.get(callp[1]) || this.assembly.primitiveInvokeDecls.get(callp[1])) as MIRInvokeDecl;
                if (rcall.enclosingDecl === entity.tkey) {
                    return "NA";
                }
                else {
                    const resulttype = this.getMIRType(rcall.resultType);
                    const rtype = this.getCPPTypeFor(resulttype, "return");

                    const vargs = rcall.params.slice(1).map((fp) => `${this.getCPPTypeFor(this.getMIRType(fp.type), "parameter")} ${fp.name}`);
                    const cargs = rcall.params.map((fp) => fp.name);

                    if (this.getRefCountableStatus(resulttype) !== "no") {
                        vargs.push("BSQRefScope& $callerscope$");
                        cargs.push("$callerscope$")
                    }

                    return `${rtype} ${this.mangleStringForCpp(callp[0])}(${vargs.join(", ")})\n`
                        + "    {\n"
                        + `        return ${this.mangleStringForCpp(callp[1])}(${cargs.join(", ")});\n`
                        + "    }\n";
                }
            });

            const faccess = entity.fields.map((f) => this.coerce(`this->${this.mangleStringForCpp(f.fkey)}`, this.getMIRType(f.declaredType), this.anyType));
            const fjoins = faccess.length !== 0 ? faccess.map((fa) => `diagnostic_format(${fa})`).join(" + std::u32string(U\", \") + ") : "U\" \"";
            const display = "std::u32string display() const\n"
                + "    {\n"
                + `        BSQRefScope ${this.mangleStringForCpp("$scope$")};\n`
                + `        return std::u32string(U"${entity.tkey}{ ") + ${fjoins} + std::u32string(U" }");\n`
                + "    }";

            return {
                fwddecl: `class ${this.mangleStringForCpp(entity.tkey)};`,
                fulldecl: `class ${this.mangleStringForCpp(entity.tkey)} : public BSQObject, public BSQVable\n`
                    + "{\n"
                    + "public:\n"
                    + `    ${fields.join("\n    ")}\n\n`
                    + `    ${this.mangleStringForCpp(entity.tkey)}(${constructor_args.join(", ")}) : BSQObject(MIRNominalTypeEnum::${this.mangleStringForCpp(entity.tkey)})${constructor_initializer.length !== 0 ? ", " : ""}${constructor_initializer.join(", ")} { ; }\n`
                    + `    virtual ~${this.mangleStringForCpp(entity.tkey)}() { ; }\n\n`
                    + `    virtual void destroy() { ${destructor_list.join(" ")} }\n\n`
                    + `    ${display}\n\n`
                    + `    ${vfield_accessors.filter((vacf) => vacf !== "NA").join("\n    ")}\n\n`
                    + `    ${vcalls.filter((vc) => vc !== "NA").join("\n    ")}\n`
                    + "};"
            };
        }
    }

    generateCPPEphemeral(tt: MIREphemeralListType): string {        
        let fields: string[] = [];
        let displayvals: string[] = [];
        let callretops: string[] = [];
        let constructor_args: string[] = [];
        let constructor_default: string[] = [];
        let constructor_initializer: string[] = [];

        for(let i = 0; i < tt.entries.length; ++i) {
            fields.push(`${this.getCPPTypeFor(tt.entries[i], "storage")} entry_${i};`);
            
            const rctype = this.getRefCountableStatus(tt.entries[i]);
            if (rctype === "int") {
                callretops.push(`scope.processReturnChecked(this->entry_${i});`);
            }
            else if (rctype === "direct") {
                callretops.push(`scope.callReturnDirect(this->entry_${i});`);
            }
            else if (rctype === "checked") {
                callretops.push(`scope.processReturnChecked(this->entry_${i});`);
            }
            else {
                // nothing needs to be done
            }

            displayvals.push(this.coerce(`this->entry_${i}`, tt.entries[i], this.anyType));

            constructor_args.push(`${this.getCPPTypeFor(tt.entries[i], "parameter")} e${i}`);
            constructor_default.push(`entry_${i}(${this.typeToCPPDefaultValue(tt.entries[i])})`);
            constructor_initializer.push(`entry_${i}(e${i})`);
        }

        const fjoins = displayvals.map((dv) => `diagnostic_format(${dv})`).join(" + std::u32string(U\", \") + ");
        const display = "std::u32string display() const\n"
            + "    {\n"
            + `        BSQRefScope ${this.mangleStringForCpp("$scope$")};\n`
            + `        return std::u32string(U"(|) ") + ${fjoins} + std::u32string(U" |)");\n`
            + "    }";

        const processForCallReturn = "void processForCallReturn(BSQRefScope& scope)\n"
            + "    {\n"
            + `        ${callretops.join("\n        ")}`
            + "    }";

        return `class ${this.mangleStringForCpp(tt.trkey)}\n`
            + "{\n"
            + "public:\n"
            + `    ${fields.join("\n    ")}\n\n`
            + `    ${this.mangleStringForCpp(tt.trkey)}() : ${constructor_default.join(", ")} { ; }\n\n`
            + `    ${this.mangleStringForCpp(tt.trkey)}(${constructor_args.join(", ")}) : ${constructor_initializer.join(", ")} { ; }\n\n`
            + `    ${display}\n\n`
            + `    ${processForCallReturn}\n`
            + "};"
    }
}

export {
    CPPTypeEmitter
};
