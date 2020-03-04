"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const mir_assembly_1 = require("../../compiler/mir_assembly");
const smt_exp_1 = require("./smt_exp");
const assert = require("assert");
class SMTTypeEmitter {
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
    mangleStringForSMT(name) {
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
            return "3";
        }
        if (this.typecheckIsAPI_Always(tt)) {
            return "1";
        }
        if (this.typecheckIsAPI_Never(tt) && this.typecheckIsPOD_Never(tt)) {
            return "0";
        }
        return "unknown";
    }
    getSMTTypeFor(tt) {
        if (this.typecheckIsName(tt, /^NSCore::Bool$/)) {
            return "Bool";
        }
        else if (this.typecheckIsName(tt, /^NSCore::Int$/)) {
            return "Int";
        }
        else if (this.typecheckIsName(tt, /^NSCore::String$/)) {
            return "String";
        }
        else if (this.typecheckIsName(tt, /^NSCore::SafeString<.*>$/)) {
            return "bsq_safestring";
        }
        else if (this.typecheckIsName(tt, /^NSCore::StringOf<.*>$/)) {
            return "bsq_stringof";
        }
        else if (this.typecheckIsName(tt, /^NSCore::GUID$/)) {
            return "bsq_guid";
        }
        else if (this.typecheckIsName(tt, /^NSCore::LogicalTime$/)) {
            return "bsq_logicaltime";
        }
        else if (this.typecheckIsName(tt, /^NSCore::DataHash$/)) {
            return "bsq_datahash";
        }
        else if (this.typecheckIsName(tt, /^NSCore::CryptoHash$/)) {
            return "bsq_cryptohash";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.enumtype)) {
            return "bsq_enum";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.idkeytype)) {
            return "bsq_idkey";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.guididkeytype)) {
            return "bsq_idkey_guid";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.logicaltimeidkeytype)) {
            return "bsq_idkey_logicaltime";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.contenthashidkeytype)) {
            return "bsq_idkey_cryptohash";
        }
        else {
            if (this.typecheckAllKeys(tt)) {
                return "BKeyValue";
            }
            else if (this.typecheckIsName(tt, /^NSCore::Buffer<.*>$/)) {
                return "bsq_buffer";
            }
            else if (this.typecheckIsName(tt, /^NSCore::ISOTime$/)) {
                return "bsq_isotime";
            }
            else if (this.typecheckIsName(tt, /^NSCore::Regex$/)) {
                return "bsq_regex";
            }
            else if (this.typecheckTuple(tt)) {
                return "bsq_tuple";
            }
            else if (this.typecheckRecord(tt)) {
                return "bsq_record";
            }
            else if (this.typecheckUEntity(tt)) {
                return this.mangleStringForSMT(tt.trkey);
            }
            else if (this.typecheckEphemeral(tt)) {
                return this.mangleStringForSMT(tt.trkey);
            }
            else {
                return "BTerm";
            }
        }
    }
    coerceFromAtomicKey(exp, from, into) {
        const intotype = this.getSMTTypeFor(into);
        if (from.trkey === "NSCore::None") {
            return (intotype === "BKeyValue") ? new smt_exp_1.SMTValue("bsqkey_none") : new smt_exp_1.SMTValue(`bsqterm_none`);
        }
        else {
            let ctoval = "[NOT SET]";
            if (this.typecheckIsName(from, /^NSCore::Bool$/)) {
                ctoval = `(bsqkey_bool ${exp.emit()})`;
            }
            else if (this.typecheckIsName(from, /^NSCore::Int$/)) {
                ctoval = `(bsqkey_int ${exp.emit()})`;
            }
            else if (this.typecheckIsName(from, /^NSCore::String$/)) {
                ctoval = `(bsqkey_string ${exp.emit()})`;
            }
            else if (this.typecheckIsName(from, /^NSCore:<.*>$/)) {
                ctoval = `(bsq_safestring ${exp.emit()})`;
            }
            else if (this.typecheckIsName(from, /^NSCore::StringOf<.*>$/)) {
                ctoval = `(bsqkey_stringof ${exp.emit()})`;
            }
            else if (this.typecheckIsName(from, /^NSCore::GUID$/)) {
                ctoval = `(bsqkey_guid ${exp.emit()})`;
            }
            else if (this.typecheckIsName(from, /^NSCore::LogicalTime$/)) {
                ctoval = `(bsqkey_logicaltime ${exp.emit()})`;
            }
            else if (this.typecheckIsName(from, /^NSCore::DataHash$/)) {
                ctoval = `(bsqkey_datahash ${exp.emit()})`;
            }
            else if (this.typecheckIsName(from, /^NSCore::CryptoHash$/)) {
                ctoval = `(bsqkey_cryptohash ${exp.emit()})`;
            }
            else if (this.typecheckEntityAndProvidesName(from, this.enumtype)) {
                ctoval = `(bsqkey_enum ${exp.emit()})`;
            }
            else if (this.typecheckEntityAndProvidesName(from, this.idkeytype)) {
                ctoval = `(bsqkey_idkey ${exp.emit()})`;
            }
            else if (this.typecheckEntityAndProvidesName(from, this.guididkeytype)) {
                ctoval = `(bsqkey_idkey_guid ${exp.emit()})`;
            }
            else if (this.typecheckEntityAndProvidesName(from, this.logicaltimeidkeytype)) {
                ctoval = `(bsqkey_idkey_logicaltime ${exp.emit()})`;
            }
            else {
                ctoval = `(bsqkey_idkey_cryptohash ${exp.emit()})`;
            }
            return (intotype === "BKeyValue") ? new smt_exp_1.SMTValue(ctoval) : new smt_exp_1.SMTValue(`(bsqterm_key ${ctoval})`);
        }
    }
    coerceFromOptionsKey(exp, into) {
        if (this.typecheckIsName(into, /^NSCore::Bool$/)) {
            return new smt_exp_1.SMTValue(`(bsqkey_bool_value ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::Int$/)) {
            return new smt_exp_1.SMTValue(`(bsqkey_int_value ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::String$/)) {
            return new smt_exp_1.SMTValue(`(bsqkey_string_value ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::SafeString<.*>$/)) {
            return new smt_exp_1.SMTValue(`(bsqkey_safestring_value ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::StringOf<.*>$/)) {
            return new smt_exp_1.SMTValue(`(bsqkey_stringof_value ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::GUID$/)) {
            return new smt_exp_1.SMTValue(`(bsqkey_guid_value ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::LogicalTime$/)) {
            return new smt_exp_1.SMTValue(`(bsqkey_logicaltime_value ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::DataHash$/)) {
            return new smt_exp_1.SMTValue(`(bsqkey_datahash_value ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::CryptoHash$/)) {
            return new smt_exp_1.SMTValue(`(bsqkey_cryptohash_value ${exp.emit()})`);
        }
        else if (this.typecheckEntityAndProvidesName(into, this.enumtype)) {
            return new smt_exp_1.SMTValue(`(bsqkey_enum_value ${exp.emit()})`);
        }
        else if (this.typecheckEntityAndProvidesName(into, this.idkeytype)) {
            return new smt_exp_1.SMTValue(`(bsqkey_idkey_value ${exp.emit()})`);
        }
        else if (this.typecheckEntityAndProvidesName(into, this.guididkeytype)) {
            return new smt_exp_1.SMTValue(`(bsqkey_idkey_guid_value ${exp.emit()})`);
        }
        else if (this.typecheckEntityAndProvidesName(into, this.logicaltimeidkeytype)) {
            return new smt_exp_1.SMTValue(`(bsqkey_idkey_logicaltime_value ${exp.emit()})`);
        }
        else {
            return new smt_exp_1.SMTValue(`(bsqkey_idkey_cryptohash_value ${exp.emit()})`);
        }
    }
    coerceFromAtomicTerm(exp, from) {
        if (this.typecheckIsName(from, /^NSCore::Buffer<.*>$/)) {
            return new smt_exp_1.SMTValue(`(bsqterm_buffer ${exp.emit()})`);
        }
        else if (this.typecheckIsName(from, /^NSCore::ISOTime$/)) {
            return new smt_exp_1.SMTValue(`(bsqterm_isotime ${exp.emit()})`);
        }
        else if (this.typecheckIsName(from, /^NSCore::Regex$/)) {
            return new smt_exp_1.SMTValue(`(bsqterm_regex ${exp.emit()})`);
        }
        else if (this.typecheckTuple(from)) {
            return new smt_exp_1.SMTValue(`(bsqterm_tuple ${exp.emit()})`);
        }
        else if (this.typecheckRecord(from)) {
            return new smt_exp_1.SMTValue(`(bsqterm_record ${exp.emit()})`);
        }
        else {
            return new smt_exp_1.SMTValue(`(bsqterm_object "${this.mangleStringForSMT(from.trkey)}" (cons@bsq_object_from_${this.mangleStringForSMT(from.trkey)} ${exp.emit()}))`);
        }
    }
    coerceIntoAtomicKey(exp, into) {
        if (into.trkey === "NSCore::None") {
            return new smt_exp_1.SMTValue("bsqkey_none");
        }
        else {
            const cfrom = `(bsqterm_key_value ${exp.emit()})`;
            if (this.typecheckIsName(into, /^NSCore::Bool$/)) {
                return new smt_exp_1.SMTValue(`(bsqkey_bool_value ${cfrom})`);
            }
            else if (this.typecheckIsName(into, /^NSCore::Int$/)) {
                return new smt_exp_1.SMTValue(`(bsqkey_int_value ${cfrom})`);
            }
            else if (this.typecheckIsName(into, /^NSCore::String$/)) {
                return new smt_exp_1.SMTValue(`(bsqkey_string_value ${cfrom})`);
            }
            else if (this.typecheckIsName(into, /^NSCore::SafeString<.*>$/)) {
                return new smt_exp_1.SMTValue(`(bsq_safestring_value ${cfrom})`);
            }
            else if (this.typecheckIsName(into, /^NSCore::StringOf<.*>$/)) {
                return new smt_exp_1.SMTValue(`(bsq_stringof_value ${cfrom})`);
            }
            else if (this.typecheckIsName(into, /^NSCore::GUID$/)) {
                return new smt_exp_1.SMTValue(`(bsq_guid_value ${cfrom})`);
            }
            else if (this.typecheckIsName(into, /^NSCore::LogicalTime$/)) {
                return new smt_exp_1.SMTValue(`(bsq_logicaltime_value ${cfrom})`);
            }
            else if (this.typecheckIsName(into, /^NSCore::DataHash$/)) {
                return new smt_exp_1.SMTValue(`(bsq_datahash_value ${cfrom})`);
            }
            else if (this.typecheckIsName(into, /^NSCore::CryptoHash$/)) {
                return new smt_exp_1.SMTValue(`(bsq_cryptohash_value ${cfrom})`);
            }
            else if (this.typecheckEntityAndProvidesName(into, this.enumtype)) {
                return new smt_exp_1.SMTValue(`(bsq_enum_value ${cfrom})`);
            }
            else if (this.typecheckEntityAndProvidesName(into, this.idkeytype)) {
                return new smt_exp_1.SMTValue(`(bsq_idkey_value ${cfrom})`);
            }
            else if (this.typecheckEntityAndProvidesName(into, this.guididkeytype)) {
                return new smt_exp_1.SMTValue(`(bsq_idkey_guid_value ${cfrom})`);
            }
            else if (this.typecheckEntityAndProvidesName(into, this.logicaltimeidkeytype)) {
                return new smt_exp_1.SMTValue(`(bsq_idkey_logicaltime_value ${cfrom})`);
            }
            else {
                return new smt_exp_1.SMTValue(`(bsq_idkey_cryptohash_value ${cfrom})`);
            }
        }
    }
    coerceIntoAtomicTerm(exp, into) {
        if (this.typecheckIsName(into, /^NSCore::Buffer<.*>$/)) {
            return new smt_exp_1.SMTValue(`(bsqterm_buffer_value ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::ISOTime$/)) {
            return new smt_exp_1.SMTValue(`(bsqterm_isotime_value ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::Regex$/)) {
            return new smt_exp_1.SMTValue(`(bsqterm_regex_value ${exp.emit()})`);
        }
        else if (this.typecheckTuple(into)) {
            return new smt_exp_1.SMTValue(`(bsqterm_tuple_value ${exp.emit()})`);
        }
        else if (this.typecheckRecord(into)) {
            return new smt_exp_1.SMTValue(`(bsqterm_record_value ${exp.emit()})`);
        }
        else {
            return new smt_exp_1.SMTValue(`(bsqterm_object_${this.mangleStringForSMT(into.trkey)}_value (bsqterm_object_value ${exp.emit()}))`);
        }
    }
    coerce(exp, from, into) {
        if (this.getSMTTypeFor(from) === this.getSMTTypeFor(into)) {
            return exp;
        }
        if (from.trkey === "NSCore::None") {
            return this.coerceFromAtomicKey(exp, from, into);
        }
        else if (this.typecheckIsName(from, /^NSCore::Bool$/) || this.typecheckIsName(from, /^NSCore::Int$/) || this.typecheckIsName(from, /^NSCore::String$/)) {
            return this.coerceFromAtomicKey(exp, from, into);
        }
        else if (this.typecheckIsName(from, /^NSCore::SafeString<.*>$/) || this.typecheckIsName(from, /^NSCore::StringOf<.*>$/)
            || this.typecheckIsName(from, /^NSCore::GUID$/) || this.typecheckIsName(from, /^NSCore::LogicalTime$/)
            || this.typecheckIsName(from, /^NSCore::DataHash$/) || this.typecheckIsName(from, /^NSCore::CryptoHash$/)) {
            return this.coerceFromAtomicKey(exp, from, into);
        }
        else if (this.typecheckEntityAndProvidesName(from, this.enumtype) || this.typecheckEntityAndProvidesName(from, this.idkeytype) || this.typecheckEntityAndProvidesName(from, this.guididkeytype)
            || this.typecheckEntityAndProvidesName(from, this.logicaltimeidkeytype) || this.typecheckEntityAndProvidesName(from, this.contenthashidkeytype)) {
            return this.coerceFromAtomicKey(exp, from, into);
        }
        else if (this.typecheckAllKeys(from)) {
            const intotype = this.getSMTTypeFor(into);
            if (intotype === "BTerm") {
                return new smt_exp_1.SMTValue(`(bsqterm_key ${exp})`);
            }
            else {
                return this.coerceFromOptionsKey(exp, into);
            }
        }
        else if (this.typecheckIsName(from, /^NSCore::Buffer<.*>$/) || this.typecheckIsName(from, /^NSCore::ISOTime$/) || this.typecheckIsName(from, /^NSCore::Regex$/)) {
            return this.coerceFromAtomicTerm(exp, from);
        }
        else if (this.typecheckTuple(from) || this.typecheckRecord(from)) {
            return this.coerceFromAtomicTerm(exp, from);
        }
        else if (this.typecheckUEntity(from)) {
            return this.coerceFromAtomicTerm(exp, from);
        }
        else {
            //now from must be Bterm so we are projecting down
            assert(this.getSMTTypeFor(from) === "BTerm");
            if (into.trkey === "NSCore::None") {
                return this.coerceIntoAtomicKey(exp, into);
            }
            else if (this.typecheckIsName(into, /^NSCore::Bool$/) || this.typecheckIsName(into, /^NSCore::Int$/) || this.typecheckIsName(into, /^NSCore::String$/)) {
                return this.coerceIntoAtomicKey(exp, into);
            }
            else if (this.typecheckIsName(into, /^NSCore::SafeString<.*>$/) || this.typecheckIsName(into, /^NSCore::StringOf<.*>$/)
                || this.typecheckIsName(into, /^NSCore::GUID$/) || this.typecheckIsName(into, /^NSCore::LogicalTime$/)
                || this.typecheckIsName(into, /^NSCore::DataHash$/) || this.typecheckIsName(into, /^NSCore::CryptoHash$/)) {
                return this.coerceIntoAtomicKey(exp, into);
            }
            else if (this.typecheckEntityAndProvidesName(into, this.enumtype) || this.typecheckEntityAndProvidesName(into, this.idkeytype) || this.typecheckEntityAndProvidesName(into, this.guididkeytype)
                || this.typecheckEntityAndProvidesName(into, this.logicaltimeidkeytype) || this.typecheckEntityAndProvidesName(into, this.contenthashidkeytype)) {
                return this.coerceIntoAtomicKey(exp, into);
            }
            else if (this.typecheckAllKeys(into)) {
                return new smt_exp_1.SMTValue(`(bsqterm_key_value ${exp.emit()})`);
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
    generateEntityConstructor(ekey) {
        return `${this.mangleStringForSMT(ekey)}@cons`;
    }
    generateEntityAccessor(ekey, f) {
        return `${this.mangleStringForSMT(ekey)}@${this.mangleStringForSMT(f)}`;
    }
    generateConstructorTest(ekey) {
        return `is-${this.mangleStringForSMT(ekey)}@cons`;
    }
    generateSpecialTypeFieldName(stype, f) {
        return `${this.mangleStringForSMT(stype)}@@${f}`;
    }
    generateSpecialTypeFieldAccess(stype, f, arg) {
        return `(${this.generateSpecialTypeFieldName(stype, f)} ${arg})`;
    }
    generateSpecialTypeFieldAccessExp(stype, f, arg) {
        return new smt_exp_1.SMTValue(`(${this.generateSpecialTypeFieldName(stype, f)} ${arg})`);
    }
    generateEmptyHasArrayFor(ekey) {
        return this.mangleStringForSMT(`${ekey}_collection_has_array_empty`);
    }
    generateEmptyKeyArrayFor(ekey) {
        return this.mangleStringForSMT(`${ekey}_collection_key_array_empty`);
    }
    generateEmptyDataArrayFor(ekey) {
        return this.mangleStringForSMT(`${ekey}_collection_data_array_empty`);
    }
    generateListSMTEntity(entity) {
        const tt = this.getMIRType(entity.tkey);
        const ename = this.mangleStringForSMT(entity.tkey);
        const typet = entity.terms.get("T");
        const fargs = [
            `(${this.generateSpecialTypeFieldName(entity.tkey, "size")} Int)`,
            `(${this.generateSpecialTypeFieldName(entity.tkey, "entries")} (Array Int ${this.getSMTTypeFor(typet)}))`
        ];
        return {
            fwddecl: `(${ename} 0)`,
            fulldecl: `( (${this.generateEntityConstructor(entity.tkey)} ${fargs.join(" ")}) )`,
            ocons: `(cons@bsq_object_from_${ename} (bsqterm_object_${ename}_value ${this.getSMTTypeFor(tt)}))`,
            emptydecl: `(declare-const ${this.generateEmptyDataArrayFor(entity.tkey)} (Array Int ${this.getSMTTypeFor(typet)}))`
        };
    }
    getKeyListTypeForSet(entity) {
        const typet = entity.terms.get("T");
        const typekp = this.getKeyProjectedTypeFrom(typet);
        const itypekl = [...this.assembly.entityDecls].find((e) => e[1].ns === "NSCore" && e[1].name === "KeyList" && e[1].terms.get("K").trkey === typekp.trkey)[1];
        const rv = [...this.assembly.typeMap].find((entry) => entry[1].options.length == 2 && entry[1].options[0].trkey === itypekl.tkey && entry[1].options[1].trkey === "NSCore::None");
        return rv[1];
    }
    generateSetSMTEntity(entity) {
        const tt = this.getMIRType(entity.tkey);
        const ename = this.mangleStringForSMT(entity.tkey);
        const typet = entity.terms.get("T");
        const typekp = this.getKeyProjectedTypeFrom(typet);
        const typekl = this.getKeyListTypeForSet(entity);
        const fargs = [
            `(${this.generateSpecialTypeFieldName(entity.tkey, "size")} Int)`,
            `(${this.generateSpecialTypeFieldName(entity.tkey, "has")} (Array ${this.getSMTTypeFor(typekp)} Bool))`,
            `(${this.generateSpecialTypeFieldName(entity.tkey, "values")} (Array ${this.getSMTTypeFor(typekp)} ${this.getSMTTypeFor(typet)}))`,
            `(${this.generateSpecialTypeFieldName(entity.tkey, "keylist")} ${this.getSMTTypeFor(typekl)})`,
        ];
        return {
            fwddecl: `(${ename} 0)`,
            fulldecl: `( (${this.generateEntityConstructor(entity.tkey)} ${fargs.join(" ")}) )`,
            ocons: `(cons@bsq_object_from_${ename} (bsqterm_object_${ename}_value ${this.getSMTTypeFor(tt)}))`,
            emptydecl: [
                `(declare-const ${this.generateEmptyDataArrayFor(entity.tkey)} (Array ${this.getSMTTypeFor(typekp)} ${this.getSMTTypeFor(typet)}))`,
                `(declare-const ${this.generateEmptyHasArrayFor(entity.tkey)} (Array ${this.getSMTTypeFor(typekp)} Bool))`,
                `(assert (= ${this.generateEmptyHasArrayFor(entity.tkey)} ((as const (Array ${this.getSMTTypeFor(typekp)} Bool)) false)))`
            ].join("\n")
        };
    }
    getKeyListTypeForMap(entity) {
        const typet = entity.terms.get("K");
        const typekp = this.getKeyProjectedTypeFrom(typet);
        const itypekl = [...this.assembly.entityDecls].find((e) => e[1].ns === "NSCore" && e[1].name === "KeyList" && e[1].terms.get("K").trkey === typekp.trkey)[1];
        const rv = [...this.assembly.typeMap].find((entry) => entry[1].options.length == 2 && entry[1].options[0].trkey === itypekl.tkey && entry[1].options[1].trkey === "NSCore::None");
        return rv[1];
    }
    generateMapSMTEntity(entity) {
        const tt = this.getMIRType(entity.tkey);
        const ename = this.mangleStringForSMT(entity.tkey);
        const typet = entity.terms.get("K");
        const typeu = entity.terms.get("V");
        const typekp = this.getKeyProjectedTypeFrom(typet);
        const typekl = this.getKeyListTypeForMap(entity);
        const fargs = [
            `(${this.generateSpecialTypeFieldName(entity.tkey, "size")} Int)`,
            `(${this.generateSpecialTypeFieldName(entity.tkey, "has")} (Array ${this.getSMTTypeFor(typekp)} Bool))`,
            `(${this.generateSpecialTypeFieldName(entity.tkey, "keys")} (Array ${this.getSMTTypeFor(typekp)} ${this.getSMTTypeFor(typet)}))`,
            `(${this.generateSpecialTypeFieldName(entity.tkey, "values")} (Array ${this.getSMTTypeFor(typekp)} ${this.getSMTTypeFor(typeu)}))`,
            `(${this.generateSpecialTypeFieldName(entity.tkey, "keylist")} ${this.getSMTTypeFor(typekl)})`,
        ];
        return {
            fwddecl: `(${ename} 0)`,
            fulldecl: `( (${this.generateEntityConstructor(entity.tkey)} ${fargs.join(" ")}) )`,
            ocons: `(cons@bsq_object_from_${ename} (bsqterm_object_${ename}_value ${this.getSMTTypeFor(tt)}))`,
            emptydecl: [
                `(declare-const ${this.generateEmptyKeyArrayFor(entity.tkey)} (Array ${this.getSMTTypeFor(typekp)} ${this.getSMTTypeFor(typet)}))`,
                `(declare-const ${this.generateEmptyDataArrayFor(entity.tkey)} (Array ${this.getSMTTypeFor(typekp)} ${this.getSMTTypeFor(typeu)}))`,
                `(declare-const ${this.generateEmptyHasArrayFor(entity.tkey)} (Array ${this.getSMTTypeFor(typekp)} Bool))`,
                `(assert (= ${this.generateEmptyHasArrayFor(entity.tkey)} ((as const (Array ${this.getSMTTypeFor(typekp)} Bool)) false)))`
            ].join("\n")
        };
    }
    generateSMTEntity(entity) {
        const tt = this.getMIRType(entity.tkey);
        if (this.isSpecialReprEntity(tt)) {
            return undefined;
        }
        if (this.typecheckIsName(tt, /^NSCore::List<.*>$/)) {
            return this.generateListSMTEntity(entity);
        }
        else if (this.typecheckIsName(tt, /^NSCore::Set<.*>$/)) {
            return this.generateSetSMTEntity(entity);
        }
        else if (this.typecheckIsName(tt, /^NSCore::Map<.*>$/)) {
            return this.generateMapSMTEntity(entity);
        }
        else {
            const fargs = entity.fields.map((fd) => {
                return `(${this.generateEntityAccessor(entity.tkey, fd.fkey)} ${this.getSMTTypeFor(this.getMIRType(fd.declaredType))})`;
            });
            const ename = this.mangleStringForSMT(entity.tkey);
            return {
                fwddecl: `(${ename} 0)`,
                fulldecl: `( (${this.generateEntityConstructor(entity.tkey)} ${fargs.join(" ")}) )`,
                ocons: `(cons@bsq_object_from_${ename} (bsqterm_object_${ename}_value ${this.getSMTTypeFor(tt)}))`
            };
        }
    }
    generateSMTEphemeral(eph) {
        const ename = this.mangleStringForSMT(eph.trkey);
        const aargs = [];
        for (let i = 0; i < eph.entries.length; ++i) {
            aargs.push(`(${this.generateEntityAccessor(eph.trkey, `entry_${i}`)} ${this.getSMTTypeFor(eph.entries[i])})`);
        }
        return {
            fwddecl: `(${ename} 0)`,
            fulldecl: `( (${this.generateEntityConstructor(eph.trkey)} ${aargs.join(" ")}) )`
        };
    }
    generateCheckSubtype(ekey, oftype) {
        const lookups = oftype.ckeys.map((ckey) => {
            return `(select MIRConceptSubtypeArray__${this.mangleStringForSMT(ckey)} ${ekey})`;
        });
        if (lookups.length === 1) {
            return lookups[0];
        }
        else {
            return `(or ${lookups.join(" ")})`;
        }
    }
}
exports.SMTTypeEmitter = SMTTypeEmitter;
//# sourceMappingURL=smttype_emitter.js.map