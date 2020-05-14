"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const mir_assembly_1 = require("../../compiler/mir_assembly");
const type_repr_1 = require("./type_repr");
const assert = require("assert");
class CPPTypeEmitter {
    constructor(assembly) {
        this.mangledNameMap = new Map();
        this.conceptSubtypeRelation = new Map();
        this.ephemeralListConverts = new Map();
        this.assembly = assembly;
        this.anyType = assembly.typeMap.get("NSCore::Any");
        this.noneType = assembly.typeMap.get("NSCore::None");
        this.boolType = assembly.typeMap.get("NSCore::Bool");
        this.intType = assembly.typeMap.get("NSCore::Int");
        this.bigIntType = assembly.typeMap.get("NSCore::BigInt");
        this.float64Type = assembly.typeMap.get("NSCore::Float64");
        this.stringType = assembly.typeMap.get("NSCore::String");
        this.keyType = assembly.typeMap.get("NSCore::KeyType");
        this.validatorType = assembly.typeMap.get("NSCore::Validator");
        this.parsableType = assembly.typeMap.get("NSCore::Parsable");
        this.podType = assembly.typeMap.get("NSCore::PODType");
        this.apiType = assembly.typeMap.get("NSCore::APIType");
        this.tupleType = assembly.typeMap.get("NSCore::Tuple");
        this.recordType = assembly.typeMap.get("NSCore::Record");
        this.enumtype = assembly.typeMap.get("NSCore::Enum");
        this.idkeytype = assembly.typeMap.get("NSCore::IdKey");
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
    typecheckIsName_Option(tt, oftype) {
        return tt instanceof mir_assembly_1.MIREntityType && oftype.test(tt.trkey);
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
    typecheckEntityAndProvidesName_Option(tt, oftype) {
        return tt instanceof mir_assembly_1.MIREntityType && this.assembly.subtypeOf(mir_assembly_1.MIRType.createSingle(tt), oftype);
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
    typecheckIsStructuralEntity(tt) {
        if (tt.options.length !== 1 || !(tt.options[0] instanceof mir_assembly_1.MIREntityType)) {
            return false;
        }
        const edecl = this.assembly.entityDecls.get(tt.trkey);
        return edecl.attributes.includes("struct");
    }
    typecheckIsStructuralConcept(tt) {
        if (tt.options.length !== 1 || !(tt.options[0] instanceof mir_assembly_1.MIRConceptType) || tt.options[0].ckeys.length !== 1) {
            return false;
        }
        const cdecl = this.assembly.conceptDecls.get(tt.trkey);
        return cdecl.attributes.includes("struct");
    }
    typecheckIsParsable_Always(tt) {
        return this.assembly.subtypeOf(tt, this.parsableType);
    }
    typecheckIsParsable_Never(tt) {
        return tt.options.every((opt) => {
            if (opt instanceof mir_assembly_1.MIREntityType) {
                return !this.assembly.subtypeOf(this.getMIRType(opt.trkey), this.parsableType);
            }
            else if (opt instanceof mir_assembly_1.MIRConceptType) {
                return false; //TODO: this is very conservative -- we could do better by enumerating possible entities 
            }
            else if (opt instanceof mir_assembly_1.MIRTupleType) {
                return opt.entries.some((entry) => !entry.isOptional && this.typecheckIsParsable_Never(entry.type));
            }
            else if (opt instanceof mir_assembly_1.MIRRecordType) {
                return opt.entries.some((entry) => !entry.isOptional && this.typecheckIsParsable_Never(entry.type));
            }
            else {
                return false;
            }
        });
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
        if (!(this.typecheckIsParsable_Always(tt) || this.typecheckIsParsable_Never(tt))
            || !(this.typecheckIsPOD_Always(tt) || this.typecheckIsPOD_Never(tt))
            || !(this.typecheckIsAPI_Always(tt) || this.typecheckIsAPI_Never(tt))) {
            return "DATA_KIND_UNKNOWN_FLAG";
        }
        const ptt = this.typecheckIsParsable_Always(tt) ? "DATA_KIND_PARSABLE_FLAG" : "DATA_KIND_CLEAR_FLAG";
        const podtt = this.typecheckIsPOD_Always(tt) ? "DATA_KIND_POD_FLAG" : "DATA_KIND_CLEAR_FLAG";
        const apitt = this.typecheckIsAPI_Always(tt) ? "DATA_KIND_API_FLAG" : "DATA_KIND_CLEAR_FLAG";
        return `(${ptt} | ${podtt} | ${apitt})`;
    }
    getCPPReprFor_Option(tt) {
        if (this.typecheckIsName_Option(tt, /^NSCore::None$/)) {
            return new type_repr_1.NoneRepr();
        }
        else if (this.typecheckIsName_Option(tt, /^NSCore::Bool$/)) {
            return new type_repr_1.StructRepr(true, "bool", "*", "MIRNominalTypeEnum_Bool", "MIRNominalTypeEnum_Category_Empty");
        }
        else if (this.typecheckIsName_Option(tt, /^NSCore::Int$/)) {
            return new type_repr_1.StructRepr(true, "int64_t", "*", "MIRNominalTypeEnum_Int", "MIRNominalTypeEnum_Category_Empty");
        }
        else if (this.typecheckIsName_Option(tt, /^NSCore::BigInt$/)) {
            return new type_repr_1.RefRepr(true, "BigInt", "BigInt*", "MIRNominalTypeEnum_Category_BigInt");
        }
        else if (this.typecheckIsName_Option(tt, /^NSCore::String$/)) {
            return new type_repr_1.RefRepr(true, "BSQString", "BSQString*", "MIRNominalTypeEnum_Category_String");
        }
        else if (this.typecheckIsName_Option(tt, /^NSCore::SafeString<.*>$/)) {
            return new type_repr_1.RefRepr(true, "BSQSafeString", "BSQSafeString*", "MIRNominalTypeEnum_Category_SafeString");
        }
        else if (this.typecheckIsName_Option(tt, /^NSCore::StringOf<.*>$/)) {
            return new type_repr_1.RefRepr(true, "BSQStringOf", "BSQStringOf*", "MIRNominalTypeEnum_Category_StringOf");
        }
        else if (this.typecheckIsName_Option(tt, /^NSCore::UUID$/)) {
            return new type_repr_1.StructRepr(true, "BSQUUID", "Boxed_BSQUUID", "MIRNominalTypeEnum_UUID", "MIRNominalTypeEnum_Category_UUID");
        }
        else if (this.typecheckIsName_Option(tt, /^NSCore::LogicalTime$/)) {
            return new type_repr_1.StructRepr(true, "BSQLogicalTime", "Boxed_BSQLogicalTime", "MIRNominalTypeEnum_LogicalTime", "MIRNominalTypeEnum_Category_LogicalTime");
        }
        else if (this.typecheckIsName_Option(tt, /^NSCore::CryptoHash$/)) {
            return new type_repr_1.RefRepr(true, "BSQCryptoHash", "BSQCryptoHash*", "MIRNominalTypeEnum_Category_CryptoHash");
        }
        else if (this.typecheckEntityAndProvidesName_Option(tt, this.enumtype)) {
            return new type_repr_1.StructRepr(true, "BSQEnum", "Boxed_BSQEnum", `MIRNominalTypeEnum_${this.mangleStringForCpp(tt.trkey)}`, "MIRNominalTypeEnum_Category_Enum");
        }
        else if (this.typecheckEntityAndProvidesName_Option(tt, this.idkeytype)) {
            const iddecl = this.assembly.entityDecls.get(tt.trkey);
            if (iddecl.fields.length === 1) {
                return new type_repr_1.StructRepr(true, "BSQIdKeySimple", "Boxed_BSQIdKeySimple", `MIRNominalTypeEnum_${this.mangleStringForCpp(tt.trkey)}`, "MIRNominalTypeEnum_Category_IdKeySimple");
            }
            else {
                return new type_repr_1.RefRepr(true, "BSQIdKeyCompound", "BSQIdKeyCompound*", "MIRNominalTypeEnum_Category_IdKeyCompound");
            }
        }
        else {
            if (this.typecheckIsName_Option(tt, /^NSCore::Float64$/)) {
                return new type_repr_1.StructRepr(false, "double", "Boxed_double", "MIRNominalTypeEnum_Float64", "MIRNominalTypeEnum_Category_Float64");
            }
            else if (this.typecheckIsName_Option(tt, /^NSCore::ByteBuffer$/)) {
                return new type_repr_1.RefRepr(false, "BSQByteBuffer", "BSQByteBuffer*", "MIRNominalTypeEnum_Category_ByteBuffer");
            }
            else if (this.typecheckIsName_Option(tt, /^NSCore::Buffer<.*>$/)) {
                return new type_repr_1.RefRepr(false, "BSQBuffer", "BSQBuffer*", "MIRNominalTypeEnum_Category_Buffer");
            }
            else if (this.typecheckIsName_Option(tt, /^NSCore::BufferOf<.*>$/)) {
                return new type_repr_1.RefRepr(false, "BSQBufferOf", "BSQBufferOf*", "MIRNominalTypeEnum_Category_BufferOf");
            }
            else if (this.typecheckIsName_Option(tt, /^NSCore::ISOTime$/)) {
                return new type_repr_1.StructRepr(false, "BSQISOTime", "Boxed_BSQISOTime", "MIRNominalTypeEnum_ISOTime", "MIRNominalTypeEnum_Category_ISOTime");
            }
            else if (this.typecheckIsName_Option(tt, /^NSCore::Regex$/)) {
                return new type_repr_1.RefRepr(false, "BSQRegex", "BSQRegex*", "MIRNominalTypeEnum_Category_Regex");
            }
            else if (tt instanceof mir_assembly_1.MIRTupleType) {
                return new type_repr_1.StructRepr(false, "BSQTuple", "BSQTuple", "MIRNominalTypeEnum_Tuple", "MIRNominalTypeEnum_Category_Tuple");
            }
            else if (tt instanceof mir_assembly_1.MIRRecordType) {
                return new type_repr_1.StructRepr(false, "BSQRecord", "BSQRecord", "MIRNominalTypeEnum_Record", "MIRNominalTypeEnum_Category_Record");
            }
            else if (tt instanceof mir_assembly_1.MIREphemeralListType) {
                const eltypename = this.mangleStringForCpp(tt.trkey);
                return new type_repr_1.EphemeralListRepr(eltypename);
            }
            else if (tt instanceof mir_assembly_1.MIREntityType) {
                const iddecl = this.assembly.entityDecls.get(tt.trkey);
                const etname = this.mangleStringForCpp(tt.trkey);
                if (iddecl.attributes.includes("struct")) {
                    return new type_repr_1.StructRepr(false, etname, `Boxed_${etname}`, `MIRNominalTypeEnum::${this.mangleStringForCpp(tt.trkey)}`, "MIRNominalTypeEnum_Category_Object");
                }
                else {
                    let cat = "[INVALID]";
                    if (this.typecheckIsName_Option(tt, /^NSCore::List<.*>$/)) {
                        cat = "MIRNominalTypeEnum_Category_List";
                    }
                    else if (this.typecheckIsName_Option(tt, /^NSCore::Stack<.*>$/)) {
                        cat = "MIRNominalTypeEnum_Category_Stack";
                    }
                    else if (this.typecheckIsName_Option(tt, /^NSCore::Queue<.*>$/)) {
                        cat = "MIRNominalTypeEnum_Category_Queue";
                    }
                    else if (this.typecheckIsName_Option(tt, /^NSCore::Set<.*>$/)) {
                        cat = "MIRNominalTypeEnum_Category_Set";
                    }
                    else if (this.typecheckIsName_Option(tt, /^NSCore::DynamicSet<.*>$/)) {
                        cat = "MIRNominalTypeEnum_Category_DynamicSet";
                    }
                    else if (this.typecheckIsName_Option(tt, /^NSCore::Map<.*>$/)) {
                        cat = "MIRNominalTypeEnum_Category_Map";
                    }
                    else if (this.typecheckIsName_Option(tt, /^NSCore::DynamicMap<.*>$/)) {
                        cat = "MIRNominalTypeEnum_Category_DynamicMap";
                    }
                    else {
                        cat = "MIRNominalTypeEnum_Category_Object";
                    }
                    return new type_repr_1.RefRepr(false, etname, etname + "*", cat);
                }
            }
            else {
                const cdecl = this.assembly.conceptDecls.get(tt.trkey);
                if (cdecl.attributes.includes("struct")) {
                    if (this.assembly.subtypeOf(mir_assembly_1.MIRType.createSingle(tt), this.keyType)) {
                        return new type_repr_1.KeyValueRepr();
                    }
                    else {
                        return new type_repr_1.ValueRepr();
                    }
                }
                else {
                    if (this.assembly.subtypeOf(mir_assembly_1.MIRType.createSingle(tt), this.keyType)) {
                        return new type_repr_1.KeyValueRepr();
                    }
                    else {
                        return new type_repr_1.ValueRepr();
                    }
                }
            }
        }
    }
    getCPPReprFor(tt) {
        const ireprs = tt.options.map((opt) => this.getCPPReprFor_Option(opt));
        return ireprs.length === 1 ? ireprs[0] : type_repr_1.joinTypeReprs(...ireprs);
    }
    generateEphemeralListConvert(from, into) {
        const elconvsig = `${this.mangleStringForCpp(into.trkey)} convertFROM_${this.mangleStringForCpp(from.trkey)}_TO_${this.mangleStringForCpp(into.trkey)}(const ${this.mangleStringForCpp(from.trkey)}& elist)`;
        if (!this.ephemeralListConverts.has(elconvsig)) {
            const elfrom = from.options[0];
            const elinto = into.options[0];
            let argp = [];
            for (let i = 0; i < elfrom.entries.length; ++i) {
                argp.push(this.coerce(`elist.entry_${i}`, elfrom.entries[i], elinto.entries[i]));
            }
            const body = `{ return ${this.mangleStringForCpp(into.trkey)}(${argp.join(", ")}); }`;
            const elconv = `${elconvsig} ${body}`;
            this.ephemeralListConverts.set(elconvsig, elconv);
        }
        return `convertFROM_${this.mangleStringForCpp(from.trkey)}_TO_${this.mangleStringForCpp(into.trkey)}`;
    }
    coercePrimitive(exp, from, into) {
        const trfrom = this.getCPPReprFor(from);
        const trinto = this.getCPPReprFor(into);
        if (trfrom instanceof type_repr_1.NoneRepr) {
            assert(!(trinto instanceof type_repr_1.NoneRepr) && !(trinto instanceof type_repr_1.StructRepr) && !(trinto instanceof type_repr_1.RefRepr), "Should not be possible");
            if (trinto instanceof type_repr_1.KeyValueRepr) {
                return "((KeyValue)BSQ_VALUE_NONE)";
            }
            else {
                return "((Value)BSQ_VALUE_NONE)";
            }
        }
        else if (trfrom instanceof type_repr_1.StructRepr) {
            assert(!(trinto instanceof type_repr_1.NoneRepr) && !(trinto instanceof type_repr_1.StructRepr) && !(trinto instanceof type_repr_1.RefRepr), "Should not be possible");
            let cc = "[INVALID]";
            if (trfrom.base === "bool") {
                cc = `BSQ_ENCODE_VALUE_BOOL(${exp})`;
            }
            else if (trfrom.base === "int64_t") {
                cc = `BSQ_ENCODE_VALUE_TAGGED_INT(${exp})`;
            }
            else {
                const scope = this.mangleStringForCpp("$scope$");
                const ops = this.getFunctorsForType(from);
                cc = `BSQ_NEW_ADD_SCOPE(${scope}, ${trfrom.boxed}, ${ops.inc}{}(${exp}))`;
            }
            if (trinto instanceof type_repr_1.KeyValueRepr) {
                return `((KeyValue)${cc})`;
            }
            else {
                return `((Value)${cc})`;
            }
        }
        else if (trfrom instanceof type_repr_1.RefRepr) {
            assert(!(trinto instanceof type_repr_1.NoneRepr) && !(trinto instanceof type_repr_1.StructRepr) && !(trinto instanceof type_repr_1.RefRepr), "Should not be possible");
            if (trinto instanceof type_repr_1.KeyValueRepr) {
                return `((KeyValue)${exp})`;
            }
            else {
                return `((Value)${exp})`;
            }
        }
        else if (trfrom instanceof type_repr_1.KeyValueRepr) {
            if (trinto instanceof type_repr_1.NoneRepr) {
                return `BSQ_VALUE_NONE`;
            }
            else if (trinto instanceof type_repr_1.StructRepr) {
                if (trinto.base === "bool") {
                    return `BSQ_GET_VALUE_BOOL(${exp})`;
                }
                else if (trinto.base === "int64_t") {
                    return `BSQ_GET_VALUE_TAGGED_INT(${exp})`;
                }
                else {
                    if (trinto.base === "BSQTuple" || trinto.base === "BSQRecord") {
                        return `*${exp}`;
                    }
                    else {
                        return `BSQ_GET_VALUE_PTR(${exp}, ${trinto.boxed})->bval`;
                    }
                }
            }
            else if (trinto instanceof type_repr_1.RefRepr) {
                return `BSQ_GET_VALUE_PTR(${exp}, ${trinto.base})`;
            }
            else {
                return `((Value)${exp})`;
            }
        }
        else {
            if (trinto instanceof type_repr_1.NoneRepr) {
                return `BSQ_VALUE_NONE`;
            }
            else if (trinto instanceof type_repr_1.StructRepr) {
                if (trinto.base === "bool") {
                    return `BSQ_GET_VALUE_BOOL(${exp})`;
                }
                else if (trinto.base === "int64_t") {
                    return `BSQ_GET_VALUE_TAGGED_INT(${exp})`;
                }
                else {
                    if (trinto.base === "BSQTuple" || trinto.base === "BSQRecord") {
                        return `*${exp}`;
                    }
                    else {
                        return `BSQ_GET_VALUE_PTR(${exp}, ${trinto.boxed})->bval`;
                    }
                }
            }
            else if (trinto instanceof type_repr_1.RefRepr) {
                return `BSQ_GET_VALUE_PTR(${exp}, ${trinto.base})`;
            }
            else {
                return `((KeyValue)${exp})`;
            }
        }
    }
    coerce(exp, from, into) {
        const trfrom = this.getCPPReprFor(from);
        const trinto = this.getCPPReprFor(into);
        if (trfrom.base === trinto.base) {
            return exp;
        }
        if (this.typecheckEphemeral(from) && this.typecheckEphemeral(into)) {
            const cfunc = this.generateEphemeralListConvert(from, into);
            return `${cfunc}(${exp})`;
        }
        return this.coercePrimitive(exp, from, into);
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
    getEpehmeralType(tt) {
        return tt.options[0];
    }
    getRefCountableStatus(tt) {
        if (this.typecheckIsName(tt, /^NSCore::None$/) || this.typecheckIsName(tt, /^NSCore::None$/) || this.typecheckIsName(tt, /^NSCore::Bool$/) || this.typecheckIsName(tt, /^NSCore::Int$/)) {
            return "no";
        }
        else if (this.typecheckIsName(tt, /^NSCore::BigInt$/) || this.typecheckIsName(tt, /^NSCore::String$/) || this.typecheckIsName(tt, /^NSCore::SafeString<.*>$/) || this.typecheckIsName(tt, /^NSCore::StringOf<.*>$/)) {
            return "direct";
        }
        else if (this.typecheckIsName(tt, /^NSCore::UUID$/) || this.typecheckIsName(tt, /^NSCore::LogicalTime$/)) {
            return "no";
        }
        else if (this.typecheckIsName(tt, /^NSCore::UUID$/) || this.typecheckIsName(tt, /^NSCore::CryptoHash$/)) {
            return "direct";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.enumtype)) {
            return "no";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.idkeytype)) {
            return "ops";
        }
        else {
            const tr = this.getCPPReprFor(tt);
            if (tr instanceof type_repr_1.EphemeralListRepr) {
                return "ephemeral";
            }
            else if (tr instanceof type_repr_1.StructRepr) {
                return "ops";
            }
            else if (tr instanceof type_repr_1.RefRepr) {
                return "direct";
            }
            else {
                return "checked";
            }
        }
    }
    buildIncOpForType(tt, arg) {
        const rcinfo = this.getRefCountableStatus(tt);
        if (rcinfo === "no") {
            return arg;
        }
        else {
            const tr = this.getCPPReprFor(tt);
            assert(rcinfo !== "ephemeral");
            if (rcinfo === "direct") {
                return `INC_REF_DIRECT(${tr.base}, ${arg})`;
            }
            else if (rcinfo === "checked") {
                return `INC_REF_CHECK(${tr.base}, ${arg})`;
            }
            else {
                return `RCIncFunctor_${tr.base}{}(${arg})`;
            }
        }
    }
    buildReturnOpForType(tt, arg, scope) {
        const rcinfo = this.getRefCountableStatus(tt);
        if (rcinfo === "no") {
            return ";";
        }
        else {
            const tr = this.getCPPReprFor(tt);
            if (rcinfo === "ephemeral") {
                return `(${arg}).processForCallReturn(${scope});`;
            }
            else if (rcinfo === "direct") {
                return `${scope}.callReturnDirect(${arg});`;
            }
            else if (rcinfo === "checked") {
                return `${scope}.processReturnChecked(${arg});`;
            }
            else {
                return `RCReturnFunctor_${tr.base}{}(${arg}, ${scope});`;
            }
        }
    }
    buildDecOpForType(tt, arg) {
        const rcinfo = this.getRefCountableStatus(tt);
        if (rcinfo === "no") {
            return "";
        }
        else {
            const tr = this.getCPPReprFor(tt);
            assert(rcinfo !== "ephemeral");
            if (rcinfo === "direct") {
                return `BSQRef::decrementDirect(${arg})`;
            }
            else if (rcinfo === "checked") {
                return `BSQRef::decrementChecked(${arg})`;
            }
            else {
                return `RCDecFunctor_${tr.base}{}(${arg})`;
            }
        }
    }
    getFunctorsForType(tt) {
        const tr = this.getCPPReprFor(tt);
        assert(!(tr instanceof type_repr_1.EphemeralListRepr));
        if (tr instanceof type_repr_1.StructRepr) {
            return { inc: `RCIncFunctor_${tr.base}`, dec: `RCDecFunctor_${tr.base}`, ret: `RCReturnFunctor_${tr.base}`, eq: `EqualFunctor_${tr.base}`, less: `LessFunctor_${tr.base}`, display: `DisplayFunctor_${tr.base}` };
        }
        else if (tr instanceof type_repr_1.RefRepr) {
            if (this.isSpecialReprEntity(tt)) {
                return { inc: `RCIncFunctor_${tr.base}`, dec: `RCDecFunctor_${tr.base}`, ret: `RCReturnFunctor_${tr.base}`, eq: `EqualFunctor_${tr.base}`, less: `LessFunctor_${tr.base}`, display: `DisplayFunctor_${tr.base}` };
            }
            else {
                return { inc: "RCIncFunctor_BSQRef", dec: "RCDecFunctor_BSQRef", ret: "[INVALID_RET]", eq: "[INVALID_EQ]", less: "[INVALID_LESS]", display: "DisplayFunctor_BSQRef" };
            }
        }
        else {
            if (tr.iskey) {
                return { inc: "RCIncFunctor_KeyValue", dec: "RCDecFunctor_KeyValue", ret: "[INVALID_RET]", eq: "EqualFunctor_KeyValue", less: "LessFunctor_KeyValue", display: "DisplayFunctor_KeyValue" };
            }
            else {
                return { inc: "RCIncFunctor_Value", dec: "RCDecFunctor_Value", ret: "[INVALID_RET]", eq: "[INVALID_EQ]", less: "[INVALID_LESS]", display: "DisplayFunctor_Value" };
            }
        }
    }
    isSpecialReprEntity(tt) {
        if (this.typecheckIsName(tt, /^NSCore::None$/) || this.typecheckIsName(tt, /^NSCore::Bool$/) || this.typecheckIsName(tt, /^NSCore::Int$/) || this.typecheckIsName(tt, /^NSCore::BigInt$/) || this.typecheckIsName(tt, /^NSCore::String$/)) {
            return true;
        }
        else if (this.typecheckIsName(tt, /^NSCore::SafeString<.*>$/) || this.typecheckIsName(tt, /^NSCore::StringOf<.*>$/)) {
            return true;
        }
        else if (this.typecheckIsName(tt, /^NSCore::UUID$/) || this.typecheckIsName(tt, /^NSCore::LogicalTime$/) || this.typecheckIsName(tt, /^NSCore::CryptoHash$/)) {
            return true;
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.enumtype) || this.typecheckEntityAndProvidesName(tt, this.idkeytype)) {
            return true;
        }
        else {
            if (this.typecheckIsName(tt, /^NSCore::Float64$/)
                || this.typecheckIsName(tt, /^NSCore::ByteBuffer$/) || this.typecheckIsName(tt, /^NSCore::Buffer<.*>$/) || this.typecheckIsName(tt, /^NSCore::BufferOf<.*>$/)
                || this.typecheckIsName(tt, /^NSCore::ISOTime$/) || this.typecheckIsName(tt, /^NSCore::Regex$/)) {
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
            if (this.assembly.subtypeOf(this.tupleType, cctype)) {
                est.push(this.tupleType);
            }
            if (this.assembly.subtypeOf(this.recordType, cctype)) {
                est.push(this.recordType);
            }
            const keyarray = est.map((et) => et.trkey).sort();
            this.conceptSubtypeRelation.set(tt.tkey, keyarray);
        });
    }
    generateConstructorArgInc(argtype, arg) {
        const rcinfo = this.getRefCountableStatus(argtype);
        if (rcinfo === "no") {
            return arg;
        }
        return this.buildIncOpForType(argtype, arg);
    }
    generateListCPPEntity(entity) {
        const tt = this.getMIRType(entity.tkey);
        const typet = entity.terms.get("T");
        const declrepr = this.getCPPReprFor(tt);
        const crepr = this.getCPPReprFor(typet);
        const cops = this.getFunctorsForType(typet);
        const bc = `BSQList<${crepr.std}, ${cops.dec}, ${cops.display}>`;
        const decl = `class ${declrepr.base} : public ${bc}\n`
            + "{\n"
            + "public:\n"
            + `${declrepr.base}(MIRNominalTypeEnum ntype) : ${bc}(ntype) { ; }\n`
            + `${declrepr.base}(MIRNominalTypeEnum ntype, std::vector<${crepr.std}>&& vals) : ${bc}(ntype, std::move(vals)) { ; }\n`
            + `virtual ~${declrepr.base}() { ; }\n`
            + "};\n";
        return { isref: true, fwddecl: `class ${declrepr.base};`, fulldecl: decl };
    }
    generateStackCPPEntity(entity) {
        const tt = this.getMIRType(entity.tkey);
        const typet = entity.terms.get("T");
        const declrepr = this.getCPPReprFor(tt);
        const crepr = this.getCPPReprFor(typet);
        const cops = this.getFunctorsForType(typet);
        const bc = `BSQStack<${crepr.std}, ${cops.dec}, ${cops.display}>`;
        const decl = `class ${declrepr.base} : public ${bc}\n`
            + "{\n"
            + "public:\n"
            + `${declrepr.base}(MIRNominalTypeEnum ntype) : ${bc}(ntype) { ; }\n`
            + `${declrepr.base}(MIRNominalTypeEnum ntype, std::vector<${crepr.std}>&& vals) : ${bc}(ntype, std::move(vals)) { ; }\n`
            + `virtual ~${declrepr.base}() { ; }\n`
            + "};\n";
        return { isref: true, fwddecl: `class ${declrepr.base};`, fulldecl: decl };
    }
    generateQueueCPPEntity(entity) {
        const tt = this.getMIRType(entity.tkey);
        const typet = entity.terms.get("T");
        const declrepr = this.getCPPReprFor(tt);
        const crepr = this.getCPPReprFor(typet);
        const cops = this.getFunctorsForType(typet);
        const bc = `BSQQueue<${crepr.std}, ${cops.dec}, ${cops.display}>`;
        const decl = `class ${declrepr.base} : public ${bc}\n`
            + "{\n"
            + "public:\n"
            + `${declrepr.base}(MIRNominalTypeEnum ntype) : ${bc}(ntype) { ; }\n`
            + `${declrepr.base}(MIRNominalTypeEnum ntype, std::vector<${crepr.std}>&& vals) : ${bc}(ntype, std::move(vals)) { ; }\n`
            + `virtual ~${declrepr.base}() { ; }\n`
            + "};\n";
        return { isref: true, fwddecl: `class ${declrepr.base};`, fulldecl: decl };
    }
    generateSetCPPEntity(entity) {
        const tt = this.getMIRType(entity.tkey);
        const typet = entity.terms.get("T");
        const declrepr = this.getCPPReprFor(tt);
        const crepr = this.getCPPReprFor(typet);
        const cops = this.getFunctorsForType(typet);
        const bc = `BSQSet<${crepr.std}, ${cops.dec}, ${cops.display}, ${cops.eq}, ${cops.less}>`;
        const decl = `class ${declrepr.base} : public ${bc}\n`
            + "{\n"
            + "public:\n"
            + `${declrepr.base}(MIRNominalTypeEnum ntype) : ${bc}(ntype) { ; }\n`
            + `${declrepr.base}(MIRNominalTypeEnum ntype, std::vector<${crepr.std}>&& vals) : ${bc}(ntype, std::move(vals)) { ; }\n`
            + `virtual ~${declrepr.base}() { ; }\n`
            + "};\n";
        return { isref: true, fwddecl: `class ${declrepr.base};`, fulldecl: decl };
    }
    generateMapCPPEntity(entity) {
        const tt = this.getMIRType(entity.tkey);
        const typek = entity.terms.get("K");
        const typev = entity.terms.get("V");
        const declrepr = this.getCPPReprFor(tt);
        const krepr = this.getCPPReprFor(typek);
        const vrepr = this.getCPPReprFor(typev);
        const kops = this.getFunctorsForType(typek);
        const vops = this.getFunctorsForType(typev);
        const bc = `BSQMap<${krepr.std}, ${kops.dec}, ${kops.display}, ${kops.eq}, ${kops.less}, ${vrepr.std}, ${vops.dec}, ${vops.display}>`;
        const decl = `class ${declrepr.base} : public ${bc}\n`
            + "{\n"
            + "public:\n"
            + `${declrepr.base}(MIRNominalTypeEnum ntype) : ${bc}(ntype) { ; }\n`
            + `${declrepr.base}(MIRNominalTypeEnum ntype, std::vector<MEntry<${krepr.std}, ${vrepr.std}>>&& vals) : ${bc}(ntype, std::move(vals)) { ; }\n`
            + `virtual ~${declrepr.base}() { ; }\n`
            + "};\n";
        return { isref: true, fwddecl: `class ${declrepr.base};`, fulldecl: decl };
    }
    generateCPPEntity(entity) {
        const tt = this.getMIRType(entity.tkey);
        if (this.isSpecialReprEntity(tt)) {
            return undefined;
        }
        if (this.typecheckIsName(tt, /^NSCore::List<.*>$/)) {
            return this.generateListCPPEntity(entity);
        }
        else if (this.typecheckIsName(tt, /^NSCore::Stack<.*>$/)) {
            return this.generateStackCPPEntity(entity);
        }
        else if (this.typecheckIsName(tt, /^NSCore::Queue<.*>$/)) {
            return this.generateQueueCPPEntity(entity);
        }
        else if (this.typecheckIsName(tt, /^NSCore::Set<.*>$/) || this.typecheckIsName(tt, /^NSCore::DynamicSet<.*>$/)) {
            return this.generateSetCPPEntity(entity);
        }
        else if (this.typecheckIsName(tt, /^NSCore::Map<.*>$/) || this.typecheckIsName(tt, /^NSCore::DynamicMap<.*>$/)) {
            return this.generateMapCPPEntity(entity);
        }
        else {
            const constructor_args = entity.fields.map((fd) => {
                return `${this.getCPPReprFor(this.getMIRType(fd.declaredType)).std} ${fd.name}`;
            });
            const constructor_initializer = entity.fields.map((fd) => {
                return `${this.mangleStringForCpp(fd.fkey)}(${fd.name})`;
            });
            const fields = entity.fields.map((fd) => {
                return `${this.getCPPReprFor(this.getMIRType(fd.declaredType)).std} ${this.mangleStringForCpp(fd.fkey)};`;
            });
            const faccess = entity.fields.map((f) => this.coerce(`this->${this.mangleStringForCpp(f.fkey)}`, this.getMIRType(f.declaredType), this.anyType));
            const fjoins = faccess.length !== 0 ? faccess.map((fa) => `diagnostic_format(${fa})`).join(" + std::string(\", \") + ") : "\" \"";
            const display = "std::string display() const\n"
                + "    {\n"
                + `        BSQRefScope ${this.mangleStringForCpp("$scope$")};\n`
                + `        return std::string("${entity.tkey}{ ") + ${fjoins} + std::string(" }");\n`
                + "    }";
            if (!entity.attributes.includes("struct")) {
                const destructor_list = entity.fields.map((fd) => {
                    const rcinfo = this.getRefCountableStatus(this.getMIRType(fd.declaredType));
                    if (rcinfo === "no") {
                        return undefined;
                    }
                    const arg = `this->${this.mangleStringForCpp(fd.fkey)}`;
                    return `${this.buildDecOpForType(this.getMIRType(fd.declaredType), arg)};`;
                })
                    .filter((fd) => fd !== undefined);
                return {
                    isref: true,
                    fwddecl: `class ${this.mangleStringForCpp(entity.tkey)};`,
                    fulldecl: `class ${this.mangleStringForCpp(entity.tkey)} : public BSQObject\n`
                        + "{\n"
                        + "public:\n"
                        + `    ${fields.join("\n    ")}\n\n`
                        + `    ${this.mangleStringForCpp(entity.tkey)}(${constructor_args.join(", ")}) : BSQObject(MIRNominalTypeEnum::${this.mangleStringForCpp(entity.tkey)})${constructor_initializer.length !== 0 ? ", " : ""}${constructor_initializer.join(", ")} { ; }\n`
                        + `    virtual ~${this.mangleStringForCpp(entity.tkey)}() { ; }\n\n`
                        + `    virtual void destroy() { ${destructor_list.join(" ")} }\n\n`
                        + `    ${display}\n`
                        + "};"
                };
            }
            else {
                const copy_constructor_initializer = entity.fields.map((fd) => {
                    return `${this.mangleStringForCpp(fd.fkey)}(src.${this.mangleStringForCpp(fd.fkey)})`;
                });
                const copy_cons = `${this.mangleStringForCpp(entity.tkey)}(const ${this.mangleStringForCpp(entity.tkey)}& src) ${copy_constructor_initializer.length !== 0 ? ":" : ""} ${copy_constructor_initializer.join(", ")} { ; }`;
                const move_constructor_initializer = entity.fields.map((fd) => {
                    return `${this.mangleStringForCpp(fd.fkey)}(std::move(src.${this.mangleStringForCpp(fd.fkey)}))`;
                });
                const move_cons = `${this.mangleStringForCpp(entity.tkey)}(${this.mangleStringForCpp(entity.tkey)}&& src) ${move_constructor_initializer.length !== 0 ? ":" : ""} ${move_constructor_initializer.join(", ")} { ; }`;
                const copy_assign_ops = entity.fields.map((fd) => {
                    return `this->${this.mangleStringForCpp(fd.fkey)} = src.${this.mangleStringForCpp(fd.fkey)};`;
                });
                const copy_assign = `${this.mangleStringForCpp(entity.tkey)}& operator=(const ${this.mangleStringForCpp(entity.tkey)}& src)`
                    + `{\n`
                    + `  if (this == &src) return *this;\n\n  `
                    + copy_assign_ops.join("\n  ")
                    + `return *this;\n`
                    + `}\n`;
                const move_assign_ops = entity.fields.map((fd) => {
                    return `this->${this.mangleStringForCpp(fd.fkey)} = std::move(src.${this.mangleStringForCpp(fd.fkey)});`;
                });
                const move_assign = `${this.mangleStringForCpp(entity.tkey)}& operator=(${this.mangleStringForCpp(entity.tkey)}&& src)`
                    + `{\n`
                    + `  if (this == &src) return *this;\n\n  `
                    + move_assign_ops.join("\n  ")
                    + `return *this;\n`
                    + `}\n`;
                const incop_ops = entity.fields.map((fd) => {
                    return this.buildIncOpForType(this.getMIRType(fd.declaredType), `tt.${this.mangleStringForCpp(fd.fkey)}`) + ";";
                });
                const incop = `struct RCIncFunctor_${this.mangleStringForCpp(entity.tkey)}`
                    + `{\n`
                    + `  inline ${this.mangleStringForCpp(entity.tkey)} operator()(${this.mangleStringForCpp(entity.tkey)} tt) const\n`
                    + `  {\n`
                    + `    ${incop_ops.join("    \n")}\n`
                    + `    return tt;\n`
                    + `  }\n`
                    + `};\n`;
                const decop_ops = entity.fields.map((fd) => {
                    return this.buildDecOpForType(this.getMIRType(fd.declaredType), `tt.${this.mangleStringForCpp(fd.fkey)}`) + ";";
                });
                const decop = `struct RCDecFunctor_${this.mangleStringForCpp(entity.tkey)}`
                    + `{\n`
                    + `  inline void operator()(${this.mangleStringForCpp(entity.tkey)} tt) const\n`
                    + `  {\n`
                    + `    ${decop_ops.join("    \n")}\n`
                    + `  }\n`
                    + `};\n`;
                const returnop_ops = entity.fields.map((fd) => {
                    return this.buildReturnOpForType(this.getMIRType(fd.declaredType), `tt.${this.mangleStringForCpp(fd.fkey)}`, "scope") + ";";
                });
                const returnop = `struct RCReturnFunctor_${this.mangleStringForCpp(entity.tkey)}`
                    + `{\n`
                    + `  inline void operator()(${this.mangleStringForCpp(entity.tkey)}& tt, BSQRefScope& scope) const\n`
                    + `  {\n`
                    + `    ${returnop_ops.join("    \n")}\n`
                    + `  }\n`
                    + `};\n`;
                const displayop = `struct RCDisplayFunctor_${this.mangleStringForCpp(entity.tkey)}`
                    + `{\n`
                    + `  std::string operator()(${this.mangleStringForCpp(entity.tkey)}& tt) const\n`
                    + `  {\n`
                    + `    return tt.display();`
                    + `  }\n`
                    + `};\n`;
                return {
                    isref: false,
                    fwddecl: `class Boxed_${this.mangleStringForCpp(entity.tkey)};`,
                    fulldecl: `class ${this.mangleStringForCpp(entity.tkey)}\n`
                        + "{\n"
                        + "public:\n"
                        + `    ${fields.join("\n    ")}\n\n`
                        + `    ${this.mangleStringForCpp(entity.tkey)}() { ; }\n`
                        + `    ${this.mangleStringForCpp(entity.tkey)}(${constructor_args.join(", ")}) ${constructor_initializer.length !== 0 ? ": " : ""}${constructor_initializer.join(", ")} { ; }\n`
                        + `    ${copy_cons}\n`
                        + `    ${move_cons}\n\n`
                        + `    ${copy_assign}\n`
                        + `    ${move_assign}\n\n`
                        + `    ${display}\n\n`
                        + "};",
                    boxeddecl: `class Boxed_${this.mangleStringForCpp(entity.tkey)} : public BSQBoxedObject<${this.mangleStringForCpp(entity.tkey)}, RCDecFunctor_${this.mangleStringForCpp(entity.tkey)}>\n`
                        + "{\n"
                        + "public:\n"
                        + `    Boxed_${this.mangleStringForCpp(entity.tkey)}(const ${this.mangleStringForCpp(entity.tkey)}& bval) : BSQBoxedObject(MIRNominalTypeEnum::${this.mangleStringForCpp(entity.tkey)}, bval) { ; }\n`
                        + `    std::string display() const {return this->bval.display(); }\n\n`
                        + "};",
                    ops: [
                        incop,
                        decop,
                        returnop,
                        displayop
                    ]
                };
            }
        }
    }
    generateCPPEphemeral(tt) {
        let fields = [];
        let displayvals = [];
        let callretops = [];
        let constructor_args = [];
        let constructor_initializer = [];
        for (let i = 0; i < tt.entries.length; ++i) {
            const irepr = this.getCPPReprFor(tt.entries[i]);
            fields.push(`${irepr.std} entry_${i};`);
            const rctype = this.getRefCountableStatus(tt.entries[i]);
            if (rctype === "direct") {
                callretops.push(`scope.callReturnDirect(this->entry_${i});`);
            }
            else if (rctype === "checked") {
                callretops.push(`scope.processReturnChecked(this->entry_${i});`);
            }
            else if (rctype === "ops") {
                callretops.push(`RCReturnFunctor_${irepr.base}{}(this->entry_${i})`);
            }
            else {
                // nothing needs to be done
            }
            displayvals.push(this.coerce(`this->entry_${i}`, tt.entries[i], this.anyType));
            constructor_args.push(`${irepr.std} e${i}`);
            constructor_initializer.push(`entry_${i}(e${i})`);
        }
        const fjoins = displayvals.map((dv) => `diagnostic_format(${dv})`).join(" + std::string(\", \") + ");
        const display = "std::string display() const\n"
            + "    {\n"
            + `        BSQRefScope ${this.mangleStringForCpp("$scope$")};\n`
            + `        return std::string("(|) ") + ${fjoins} + std::string(" |)");\n`
            + "    }";
        const processForCallReturn = "void processForCallReturn(BSQRefScope& scope)\n"
            + "    {\n"
            + `        ${callretops.join("\n        ")}`
            + "    }";
        return `class ${this.mangleStringForCpp(tt.trkey)}\n`
            + "{\n"
            + "public:\n"
            + `    ${fields.join("\n    ")}\n\n`
            + `    ${this.mangleStringForCpp(tt.trkey)}() { ; }\n\n`
            + `    ${this.mangleStringForCpp(tt.trkey)}(${constructor_args.join(", ")}) : ${constructor_initializer.join(", ")} { ; }\n\n`
            + `    ${display}\n\n`
            + `    ${processForCallReturn}\n`
            + "};";
    }
}
exports.CPPTypeEmitter = CPPTypeEmitter;
//# sourceMappingURL=cpptype_emitter.js.map