"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const mir_assembly_1 = require("../../compiler/mir_assembly");
const assert = require("assert");
class CPPTypeEmitter {
    constructor(assembly) {
        this.mangledNameMap = new Map();
        this.conceptSubtypeRelation = new Map();
        this.assembly = assembly;
        this.anyType = assembly.typeMap.get("NSCore::Any");
        this.noneType = assembly.typeMap.get("NSCore::None");
        this.boolType = assembly.typeMap.get("NSCore::Bool");
        this.intType = assembly.typeMap.get("NSCore::Int");
        this.stringType = assembly.typeMap.get("NSCore::String");
        this.keyType = assembly.typeMap.get("NSCore::KeyType");
        this.validatorType = assembly.typeMap.get("NSCore::Validator");
        this.podType = assembly.typeMap.get("NSCore::PODType");
        this.apiType = assembly.typeMap.get("NSCore::APIType");
        this.tupleType = assembly.typeMap.get("NSCore::Tuple");
        this.recordType = assembly.typeMap.get("NSCore::Record");
        this.enumtype = assembly.typeMap.get("NSCore::Enum");
        this.idkeytype = assembly.typeMap.get("NSCore::IdKey");
        this.guididkeytype = assembly.typeMap.get("NSCore::GUIDIdKey");
        this.logicaltimeidkeytype = assembly.typeMap.get("NSCore::LogicalTimeIdKey");
        this.contenthashidkeytype = assembly.typeMap.get("NSCore::ContentHashIdKey");
    }
    mangleStringForCpp(name) {
        if (!this.mangledNameMap.has(name)) {
            const cleanname = name.replace(/\W/g, "_").toLowerCase() + "I" + this.mangledNameMap.size + "I";
            this.mangledNameMap.set(name, cleanname);
        }
        return this.mangledNameMap.get(name);
    }
    getMIRType(tkey) {
        return this.assembly.typeMap.get(tkey);
    }
    typecheckIsName(tt, oftype, match) {
        match = match || "exact";
        if (match === "exact") {
            return tt.options.length === 1 && (tt.options[0] instanceof mir_assembly_1.MIREntityType) && oftype.test(tt.options[0].trkey);
        }
        else {
            return tt.options.some((opt) => (opt instanceof mir_assembly_1.MIREntityType) && oftype.test(opt.trkey));
        }
    }
    typecheckEntityAndProvidesName(tt, oftype, match) {
        match = match || "exact";
        if (match === "exact") {
            return tt.options.length === 1 && (tt.options[0] instanceof mir_assembly_1.MIREntityType) && this.assembly.subtypeOf(tt, oftype);
        }
        else {
            return tt.options.some((opt) => (opt instanceof mir_assembly_1.MIREntityType) && this.assembly.subtypeOf(mir_assembly_1.MIRType.createSingle(opt), oftype));
        }
    }
    typecheckTuple(tt, match) {
        match = match || "tuple";
        if (match === "known") {
            return tt.options.length === 1 && (tt.options[0] instanceof mir_assembly_1.MIRTupleType) && !tt.options[0].entries.some((entry) => entry.isOptional);
        }
        else {
            return tt.options.every((opt) => opt instanceof mir_assembly_1.MIRTupleType);
        }
    }
    typecheckRecord(tt, match) {
        match = match || "record";
        if (match === "known") {
            return tt.options.length === 1 && (tt.options[0] instanceof mir_assembly_1.MIRRecordType) && !tt.options[0].entries.some((entry) => entry.isOptional);
        }
        else {
            return tt.options.every((opt) => opt instanceof mir_assembly_1.MIRRecordType);
        }
    }
    typecheckUEntity(tt, match) {
        match = match || "exact";
        if (match === "exact") {
            return tt.options.length === 1 && (tt.options[0] instanceof mir_assembly_1.MIREntityType) && tt.options[0].trkey !== "NSCore::None";
        }
        else {
            return tt.options.some((opt) => (opt instanceof mir_assembly_1.MIREntityType) && opt.trkey !== "NSCore::None");
        }
    }
    typecheckAllKeys(tt) {
        return tt.options.every((opt) => this.assembly.subtypeOf(mir_assembly_1.MIRType.createSingle(opt), this.keyType));
    }
    typecheckEphemeral(tt) {
        return tt.options.length === 1 && tt.options[0] instanceof mir_assembly_1.MIREphemeralListType;
    }
    typecheckIsNoneable(tt) {
        return tt.options.some((opt) => (opt instanceof mir_assembly_1.MIREntityType) && opt.trkey === "NSCore::None");
    }
    typecheckIsPOD_Always(tt) {
        return this.assembly.subtypeOf(tt, this.podType);
    }
    typecheckIsPOD_Never(tt) {
        return tt.options.every((opt) => {
            if (opt instanceof mir_assembly_1.MIREntityType) {
                return !this.assembly.subtypeOf(this.getMIRType(opt.trkey), this.podType);
            }
            else if (opt instanceof mir_assembly_1.MIRConceptType) {
                return false; //TODO: this is very conservative -- we could do better by enumerating possible entities 
            }
            else if (opt instanceof mir_assembly_1.MIRTupleType) {
                return opt.entries.some((entry) => !entry.isOptional && this.typecheckIsPOD_Never(entry.type));
            }
            else if (opt instanceof mir_assembly_1.MIRRecordType) {
                return opt.entries.some((entry) => !entry.isOptional && this.typecheckIsPOD_Never(entry.type));
            }
            else {
                return false;
            }
        });
    }
    typecheckIsAPI_Always(tt) {
        return this.assembly.subtypeOf(tt, this.apiType);
    }
    typecheckIsAPI_Never(tt) {
        return tt.options.every((opt) => {
            if (opt instanceof mir_assembly_1.MIREntityType) {
                return !this.assembly.subtypeOf(this.getMIRType(opt.trkey), this.apiType);
            }
            else if (opt instanceof mir_assembly_1.MIRConceptType) {
                return false; //TODO: this is very conservative -- we could do better by enumerating possible entities 
            }
            else if (opt instanceof mir_assembly_1.MIRTupleType) {
                return opt.entries.some((entry) => !entry.isOptional && this.typecheckIsAPI_Never(entry.type));
            }
            else if (opt instanceof mir_assembly_1.MIRRecordType) {
                return opt.entries.some((entry) => !entry.isOptional && this.typecheckIsAPI_Never(entry.type));
            }
            else {
                return false;
            }
        });
    }
    generateInitialDataKindFlag(tt) {
        if (this.typecheckIsPOD_Always(tt)) {
            return "DATA_KIND_POD_FLAG";
        }
        if (this.typecheckIsAPI_Always(tt)) {
            return "DATA_KIND_API_FLAG";
        }
        if (this.typecheckIsAPI_Never(tt) && this.typecheckIsPOD_Never(tt)) {
            return "DATA_KIND_CLEAR_FLAG";
        }
        return "DATA_KIND_UNKNOWN_FLAG";
    }
    getCPPTypeFor(tt, declspec) {
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
            else if (this.typecheckUEntity(tt)) {
                return this.mangleStringForCpp(tt.trkey) + (declspec !== "base" ? "*" : "");
            }
            else if (this.typecheckEphemeral(tt)) {
                return this.mangleStringForCpp(tt.trkey);
            }
            else {
                return "Value";
            }
        }
    }
    coerceFromAtomicKey(exp, from) {
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
    coerceFromOptionsKey(exp, into) {
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
    coerceIntoAtomicKey(exp, into) {
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
    coerceIntoAtomicTerm(exp, into) {
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
    coerce(exp, from, into) {
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
            if (intotype === "Value") {
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
    getKeyProjectedTypeFrom(ktype) {
        if (this.typecheckAllKeys(ktype)) {
            return ktype;
        }
        else {
            assert(false);
            return ktype;
        }
    }
    getKeyFrom(arg, atype) {
        if (this.typecheckAllKeys(atype)) {
            return arg;
        }
        else {
            assert(false);
            return "[NOT IMPLEMENTED]";
        }
    }
    tupleHasIndex(tt, idx) {
        if (tt.options.every((opt) => opt instanceof mir_assembly_1.MIRTupleType && idx < opt.entries.length && !opt.entries[idx].isOptional)) {
            return "yes";
        }
        else if (tt.options.every((opt) => opt instanceof mir_assembly_1.MIRTupleType && opt.entries.length <= idx)) {
            return "no";
        }
        else {
            return "maybe";
        }
    }
    getMaxTupleLength(tt) {
        const lens = tt.options.map((opt) => opt.entries.length);
        return Math.max(...lens);
    }
    recordHasField(tt, pname) {
        if (tt.options.every((opt) => opt instanceof mir_assembly_1.MIRRecordType && opt.entries.find((entry) => entry.name === pname) !== undefined && !opt.entries.find((entry) => entry.name === pname).isOptional)) {
            return "yes";
        }
        else if (tt.options.every((opt) => opt instanceof mir_assembly_1.MIRRecordType && opt.entries.find((entry) => entry.name === pname) === undefined)) {
            return "no";
        }
        else {
            return "maybe";
        }
    }
    getMaxPropertySet(tt) {
        let props = new Set();
        tt.options.forEach((opt) => opt.entries.forEach((entry) => props.add(entry.name)));
        return [...props].sort();
    }
    getEntityEKey(tt) {
        return tt.options[0].ekey;
    }
    getRefCountableStatus(tt) {
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
            else if (this.typecheckUEntity(tt)) {
                return "direct";
            }
            else if (this.typecheckEphemeral(tt)) {
                return "special";
            }
            else {
                return "checked";
            }
        }
    }
    getIncOpForType(tt, arg) {
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
                return "[INVALID]";
            }
        }
    }
    getDecOpForType(tt, arg) {
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
            return "[INVALID]";
        }
    }
    getGetKeyOpForType(tt, arg) {
        if (this.typecheckAllKeys(tt)) {
            return arg;
        }
        else {
            assert(false);
            return "[INVALID]";
        }
    }
    getGetCMPOpsForKeyType(tt) {
        const tval = this.getCPPTypeFor(tt, "base");
        const hf = `HashFunctor_${tval}{}`;
        const eqf = `EqualFunctor_${tval}{}`;
        const cmpf = `LessFunctor_${tval}`;
        return { hash: hf, eq: eqf, cmp: cmpf };
    }
    isSpecialReprEntity(tt) {
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
    typeToCPPDefaultValue(ttype) {
        if (this.typecheckIsName(ttype, /^NSCore::Bool$/)) {
            return "false";
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
    initializeConceptSubtypeRelation() {
        this.assembly.conceptDecls.forEach((tt) => {
            const cctype = this.getMIRType(tt.tkey);
            const est = [...this.assembly.entityDecls].map((edecl) => this.getMIRType(edecl[0])).filter((et) => this.assembly.subtypeOf(et, cctype));
            const keyarray = est.map((et) => et.trkey).sort();
            this.conceptSubtypeRelation.set(tt.tkey, keyarray);
        });
    }
    getSubtypesArrayCount(ckey) {
        return this.conceptSubtypeRelation.get(ckey).length;
    }
    generateConstructorArgInc(argtype, arg) {
        const rcinfo = this.getRefCountableStatus(argtype);
        if (rcinfo === "no") {
            return arg;
        }
        return this.getIncOpForType(argtype, arg);
    }
    generateListCPPEntity(entity, templatefile) {
        const tt = this.getMIRType(entity.tkey);
        const declname = this.getCPPTypeFor(tt, "base");
        const typet = entity.terms.get("T");
        const decl = `#define Ty ${declname}\n`
            + `#define T ${this.getCPPTypeFor(typet, "storage")}\n`
            + `#define INC_RC_T(X) ${this.getIncOpForType(typet, "X")}\n`
            + `#define DEC_RC_T(X) ${this.getDecOpForType(typet, "X")}\n`
            + `#define BSCOPE ${this.mangleStringForCpp("$scope$")}\n`
            + `#define FDisplay(X) diagnostic_format(${this.coerce("X", typet, this.anyType)})\n`
            + "\n"
            + `#include ${templatefile}\n`;
        return { fwddecl: `class ${declname};`, fulldecl: decl };
    }
    generateSetCPPEntity(entity, templatefile) {
        const tt = this.getMIRType(entity.tkey);
        const declname = this.getCPPTypeFor(tt, "base");
        const typet = entity.terms.get("T");
        const typekp = this.getKeyProjectedTypeFrom(typet);
        const typekl = [...this.assembly.entityDecls].find((e) => e[1].ns === "NSCore" && e[1].name === "KeyList" && e[1].terms.get("K").trkey === typekp.trkey);
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
            + `#define BSCOPE ${this.mangleStringForCpp("$scope$")}\n`
            + `#define FDisplay(X) diagnostic_format(${this.coerce("X", typet, this.anyType)})\n`
            + "\n"
            + `#include ${templatefile}\n`;
        return { fwddecl: `class ${declname};`, fulldecl: decl };
    }
    generateMapCPPEntity(entity, templatefile) {
        const tt = this.getMIRType(entity.tkey);
        const declname = this.getCPPTypeFor(tt, "base");
        const typet = entity.terms.get("K");
        const typeu = entity.terms.get("V");
        const typekp = this.getKeyProjectedTypeFrom(typet);
        const typekl = [...this.assembly.entityDecls].find((e) => e[1].ns === "NSCore" && e[1].name === "KeyList" && e[1].terms.get("K").trkey === typekp.trkey)[1];
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
            + `#define BSCOPE ${this.mangleStringForCpp("$scope$")}\n`
            + `#define TDisplay(X) diagnostic_format(${this.coerce("X", typet, this.anyType)})\n`
            + `#define UDisplay(X) diagnostic_format(${this.coerce("X", typeu, this.anyType)})\n`
            + "\n"
            + `#include ${templatefile}\n`;
        return { fwddecl: `class ${declname};`, fulldecl: decl };
    }
    generateCPPEntity(entity, specialReps) {
        const tt = this.getMIRType(entity.tkey);
        if (this.isSpecialReprEntity(tt)) {
            return undefined;
        }
        if (this.typecheckIsName(tt, /^NSCore::List<.*>$/)) {
            return this.generateListCPPEntity(entity, specialReps.get("list"));
        }
        else if (this.typecheckIsName(tt, /^NSCore::Set<.*>$/)) {
            return this.generateSetCPPEntity(entity, specialReps.get("set"));
        }
        else if (this.typecheckIsName(tt, /^NSCore::Map<.*>$/)) {
            return this.generateMapCPPEntity(entity, specialReps.get("map"));
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
                const rcall = (this.assembly.invokeDecls.get(callp[1]) || this.assembly.primitiveInvokeDecls.get(callp[1]));
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
                        cargs.push("$callerscope$");
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
    generateCPPEphemeral(tt) {
        let fields = [];
        let displayvals = [];
        let callretops = [];
        let constructor_args = [];
        let constructor_default = [];
        let constructor_initializer = [];
        for (let i = 0; i < tt.entries.length; ++i) {
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
            + "};";
    }
}
exports.CPPTypeEmitter = CPPTypeEmitter;
//# sourceMappingURL=cpptype_emitter.js.map