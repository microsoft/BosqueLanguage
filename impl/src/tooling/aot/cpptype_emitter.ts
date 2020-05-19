//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIREntityTypeDecl, MIRTupleType, MIRRecordType, MIREntityType, MIRConceptType, MIREphemeralListType, MIRRecordTypeEntry, MIRConceptTypeDecl, MIRTypeOption } from "../../compiler/mir_assembly";
import { MIRResolvedTypeKey, MIRNominalTypeKey } from "../../compiler/mir_ops";
import { NoneRepr, StructRepr, RefRepr, EphemeralListRepr, ValueRepr, KeyValueRepr, TypeRepr, joinTypeReprs } from "./type_repr";

import * as assert from "assert";

class CPPTypeEmitter {
    readonly assembly: MIRAssembly;

    readonly anyType: MIRType;

    readonly noneType: MIRType;
    readonly boolType: MIRType;
    readonly intType: MIRType;
    readonly bigIntType: MIRType;
    readonly float64Type: MIRType;
    readonly stringType: MIRType;
    readonly regexType: MIRType;

    readonly keyType: MIRType;
    readonly validatorType: MIRType;
    readonly parsableType: MIRType;
    readonly podType: MIRType;
    readonly apiType: MIRType;
    readonly tupleType: MIRType;
    readonly recordType: MIRType;

    readonly enumtype: MIRType;
    readonly idkeytype: MIRType;

    private mangledNameMap: Map<string, string> = new Map<string, string>();

    conceptSubtypeRelation: Map<MIRNominalTypeKey, MIRNominalTypeKey[]> = new Map<MIRNominalTypeKey, MIRNominalTypeKey[]>();
    ephemeralListConverts: Map<string, string> = new Map<string, string>();

    constructor(assembly: MIRAssembly) {
        this.assembly = assembly;

        this.anyType = assembly.typeMap.get("NSCore::Any") as MIRType;

        this.noneType = assembly.typeMap.get("NSCore::None") as MIRType;
        this.boolType = assembly.typeMap.get("NSCore::Bool") as MIRType;
        this.intType = assembly.typeMap.get("NSCore::Int") as MIRType;
        this.bigIntType = assembly.typeMap.get("NSCore::BigInt") as MIRType;
        this.float64Type = assembly.typeMap.get("NSCore::Float64") as MIRType;
        this.stringType = assembly.typeMap.get("NSCore::String") as MIRType;
        this.regexType = assembly.typeMap.get("NSCore::Regex") as MIRType;

        this.keyType = assembly.typeMap.get("NSCore::KeyType") as MIRType;
        this.validatorType = assembly.typeMap.get("NSCore::Validator") as MIRType;
        this.parsableType = assembly.typeMap.get("NSCore::Parsable") as MIRType;
        this.podType = assembly.typeMap.get("NSCore::PODType") as MIRType;
        this.apiType = assembly.typeMap.get("NSCore::APIType") as MIRType;
        this.tupleType = assembly.typeMap.get("NSCore::Tuple") as MIRType;
        this.recordType = assembly.typeMap.get("NSCore::Record") as MIRType;

        this.enumtype = assembly.typeMap.get("NSCore::Enum") as MIRType;
        this.idkeytype = assembly.typeMap.get("NSCore::IdKey") as MIRType;
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

    typecheckIsName_Option(tt: MIRTypeOption, oftype: RegExp): boolean {
        return tt instanceof MIREntityType && oftype.test(tt.trkey);
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

    typecheckEntityAndProvidesName_Option(tt: MIRTypeOption, oftype: MIRType): boolean {
        return tt instanceof MIREntityType && this.assembly.subtypeOf(MIRType.createSingle(tt), oftype);
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

    typecheckIsStructuralEntity(tt: MIRType): boolean {
        if(tt.options.length !== 1 || !(tt.options[0] instanceof MIREntityType)) {
            return false;
        }

        const edecl = this.assembly.entityDecls.get(tt.trkey) as MIREntityTypeDecl;
        return edecl.attributes.includes("struct");
    }

    typecheckIsStructuralConcept(tt: MIRType): boolean {
        if(tt.options.length !== 1 || !(tt.options[0] instanceof MIRConceptType) || (tt.options[0] as MIRConceptType).ckeys.length !== 1) {
            return false;
        }

        const cdecl = this.assembly.conceptDecls.get(tt.trkey) as MIRConceptTypeDecl;
        return cdecl.attributes.includes("struct");
    }

    typecheckIsParsable_Always(tt: MIRType): boolean {
        return this.assembly.subtypeOf(tt, this.parsableType);
    }

    typecheckIsParsable_Never(tt: MIRType): boolean {
        return tt.options.every((opt) => {
            if(opt instanceof MIREntityType) {
                return !this.assembly.subtypeOf(this.getMIRType(opt.trkey), this.parsableType);
            }
            else if (opt instanceof MIRConceptType) {
                return false; //TODO: this is very conservative -- we could do better by enumerating possible entities 
            }
            else if (opt instanceof MIRTupleType) {
                return opt.entries.some((entry) => !entry.isOptional && this.typecheckIsParsable_Never(entry.type));
            }
            else if (opt instanceof MIRRecordType) {
                return opt.entries.some((entry) => !entry.isOptional && this.typecheckIsParsable_Never(entry.type));
            }
            else {
                return false;
            }
        });
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
        if(!(this.typecheckIsParsable_Always(tt) || this.typecheckIsParsable_Never(tt)) 
            || !(this.typecheckIsPOD_Always(tt) || this.typecheckIsPOD_Never(tt)) 
            || !(this.typecheckIsAPI_Always(tt) || this.typecheckIsAPI_Never(tt))) {
            return "DATA_KIND_UNKNOWN_FLAG";
        }

        const ptt = this.typecheckIsParsable_Always(tt) ? "DATA_KIND_PARSABLE_FLAG" : "DATA_KIND_CLEAR_FLAG";
        const podtt = this.typecheckIsPOD_Always(tt) ? "DATA_KIND_POD_FLAG" : "DATA_KIND_CLEAR_FLAG";
        const apitt = this.typecheckIsAPI_Always(tt) ? "DATA_KIND_API_FLAG" : "DATA_KIND_CLEAR_FLAG";

        return `(${ptt} | ${podtt} | ${apitt})`;
    }

    getCPPReprFor_Option(tt: MIRTypeOption): TypeRepr {
        if (this.typecheckIsName_Option(tt, /^NSCore::None$/)) {
            return new NoneRepr();
        }
        else if (this.typecheckIsName_Option(tt, /^NSCore::Bool$/)) {
            return new StructRepr(true, "bool", "*", "MIRNominalTypeEnum_Bool", "MIRNominalTypeEnum_Category_Empty");
        }
        else if (this.typecheckIsName_Option(tt, /^NSCore::Int$/)) {
            return new StructRepr(true, "int64_t", "*", "MIRNominalTypeEnum_Int", "MIRNominalTypeEnum_Category_Empty");
        }
        else if (this.typecheckIsName_Option(tt, /^NSCore::BigInt$/)) {
            return new RefRepr(true, "BigInt", "BigInt*", "MIRNominalTypeEnum_Category_BigInt");
        }
        else if (this.typecheckIsName_Option(tt, /^NSCore::String$/)) {
            return new RefRepr(true, "BSQString", "BSQString*", "MIRNominalTypeEnum_Category_String");
        }
        else if (this.typecheckIsName_Option(tt, /^NSCore::SafeString<.*>$/)) {
            return new RefRepr(true, "BSQSafeString", "BSQSafeString*", "MIRNominalTypeEnum_Category_SafeString");
        }
        else if (this.typecheckIsName_Option(tt, /^NSCore::StringOf<.*>$/)) {
            return new RefRepr(true, "BSQStringOf", "BSQStringOf*", "MIRNominalTypeEnum_Category_StringOf");
        }
        else if (this.typecheckIsName_Option(tt, /^NSCore::UUID$/)) {
            return new StructRepr(true, "BSQUUID", "Boxed_BSQUUID", "MIRNominalTypeEnum_UUID", "MIRNominalTypeEnum_Category_UUID");
        }
        else if (this.typecheckIsName_Option(tt, /^NSCore::LogicalTime$/)) {
            return new StructRepr(true, "BSQLogicalTime", "Boxed_BSQLogicalTime", "MIRNominalTypeEnum_LogicalTime", "MIRNominalTypeEnum_Category_LogicalTime");
        }
        else if (this.typecheckIsName_Option(tt, /^NSCore::CryptoHash$/)) {
            return new RefRepr(true, "BSQCryptoHash", "BSQCryptoHash*", "MIRNominalTypeEnum_Category_CryptoHash");
        }
        else if (this.typecheckEntityAndProvidesName_Option(tt, this.enumtype)) {
            return new StructRepr(true, "BSQEnum", "Boxed_BSQEnum", `MIRNominalTypeEnum_${this.mangleStringForCpp(tt.trkey)}`, "MIRNominalTypeEnum_Category_Enum");
        }
        else if (this.typecheckEntityAndProvidesName_Option(tt, this.idkeytype)) {
            const iddecl = this.assembly.entityDecls.get(tt.trkey) as MIREntityTypeDecl;
            if(iddecl.fields.length === 1) {
                return new StructRepr(true, "BSQIdKeySimple", "Boxed_BSQIdKeySimple", `MIRNominalTypeEnum_${this.mangleStringForCpp(tt.trkey)}`, "MIRNominalTypeEnum_Category_IdKeySimple");
            }
            else {
                return new RefRepr(true, "BSQIdKeyCompound", "BSQIdKeyCompound*", "MIRNominalTypeEnum_Category_IdKeyCompound");
            }
        }
        else {
            if (this.typecheckIsName_Option(tt, /^NSCore::Float64$/)) {
                return new StructRepr(false, "double", "Boxed_double", "MIRNominalTypeEnum_Float64", "MIRNominalTypeEnum_Category_Float64");
            }
            else if (this.typecheckIsName_Option(tt, /^NSCore::ByteBuffer$/)) {
                return new RefRepr(false, "BSQByteBuffer", "BSQByteBuffer*", "MIRNominalTypeEnum_Category_ByteBuffer");
            }
            else if (this.typecheckIsName_Option(tt, /^NSCore::Buffer<.*>$/)) {
                return new RefRepr(false, "BSQBuffer", "BSQBuffer*", "MIRNominalTypeEnum_Category_Buffer");
            }
            else if (this.typecheckIsName_Option(tt, /^NSCore::BufferOf<.*>$/)) {
                return new RefRepr(false, "BSQBufferOf", "BSQBufferOf*", "MIRNominalTypeEnum_Category_BufferOf");
            }
            else if (this.typecheckIsName_Option(tt, /^NSCore::ISOTime$/)) {
                return new StructRepr(false, "BSQISOTime", "Boxed_BSQISOTime", "MIRNominalTypeEnum_ISOTime", "MIRNominalTypeEnum_Category_ISOTime");
            }
            else if (this.typecheckIsName_Option(tt, /^NSCore::Regex$/)) {
                return new StructRepr(false, "BSQRegex", "Boxed_BSQRegex", "MIRNominalTypeEnum_Regex", "MIRNominalTypeEnum_Category_Regex", );
            }
            else if (tt instanceof MIRTupleType) {
                return new StructRepr(false, "BSQTuple", "BSQTuple", "MIRNominalTypeEnum_Tuple", "MIRNominalTypeEnum_Category_Tuple");
            }
            else if (tt instanceof MIRRecordType) {
                return new StructRepr(false, "BSQRecord", "BSQRecord", "MIRNominalTypeEnum_Record", "MIRNominalTypeEnum_Category_Record");
            }
            else if(tt instanceof MIREphemeralListType) {
                const eltypename = this.mangleStringForCpp(tt.trkey);
                return new EphemeralListRepr(eltypename);
            }
            else if (tt instanceof MIREntityType) {
                const iddecl = this.assembly.entityDecls.get(tt.trkey) as MIREntityTypeDecl;
                const etname = this.mangleStringForCpp(tt.trkey);

                if(iddecl.attributes.includes("struct")) {
                    return new StructRepr(false, etname, `Boxed_${etname}`, `MIRNominalTypeEnum::${this.mangleStringForCpp(tt.trkey)}`, "MIRNominalTypeEnum_Category_Object");
                }
                else {
                    let cat = "[INVALID]";
                    if(this.typecheckIsName_Option(tt, /^NSCore::List<.*>$/)) {
                        cat = "MIRNominalTypeEnum_Category_List";
                    }
                    else if(this.typecheckIsName_Option(tt, /^NSCore::Stack<.*>$/)) {
                        cat = "MIRNominalTypeEnum_Category_Stack";
                    }
                    else if(this.typecheckIsName_Option(tt, /^NSCore::Queue<.*>$/)) {
                        cat = "MIRNominalTypeEnum_Category_Queue";
                    }
                    else if(this.typecheckIsName_Option(tt, /^NSCore::Set<.*>$/)) {
                        cat = "MIRNominalTypeEnum_Category_Set";
                    }
                    else if(this.typecheckIsName_Option(tt, /^NSCore::DynamicSet<.*>$/)) {
                        cat = "MIRNominalTypeEnum_Category_DynamicSet";
                    }
                    else if(this.typecheckIsName_Option(tt, /^NSCore::Map<.*>$/)) {
                        cat = "MIRNominalTypeEnum_Category_Map";
                    }
                    else if(this.typecheckIsName_Option(tt, /^NSCore::DynamicMap<.*>$/)) {
                        cat = "MIRNominalTypeEnum_Category_DynamicMap";
                    }
                    else {
                        cat = "MIRNominalTypeEnum_Category_Object";
                    }

                    return new RefRepr(false, etname, etname + "*", cat);
                }
            }
            else {
                const cdecl = this.assembly.conceptDecls.get(tt.trkey) as MIRConceptTypeDecl;
                
                if(cdecl.attributes.includes("struct")) {
                    if(this.assembly.subtypeOf(MIRType.createSingle(tt), this.keyType)) {
                        return new KeyValueRepr();
                    }
                    else {
                        return new ValueRepr();
                    }
                }
                else {
                    if(this.assembly.subtypeOf(MIRType.createSingle(tt), this.keyType)) {
                        return new KeyValueRepr();
                    }
                    else {
                        return new ValueRepr();
                    }
                }
            }
        }
    }

    getCPPReprFor(tt: MIRType): TypeRepr {
        const ireprs = tt.options.map((opt) => this.getCPPReprFor_Option(opt));
        return ireprs.length === 1 ? ireprs[0] : joinTypeReprs(...ireprs);
    }

    generateEphemeralListConvert(from: MIRType, into: MIRType): string {
        const elconvsig = `${this.mangleStringForCpp(into.trkey)} convertFROM_${this.mangleStringForCpp(from.trkey)}_TO_${this.mangleStringForCpp(into.trkey)}(const ${this.mangleStringForCpp(from.trkey)}& elist)`;

        if (!this.ephemeralListConverts.has(elconvsig)) {
            const elfrom = from.options[0] as MIREphemeralListType;
            const elinto = into.options[0] as MIREphemeralListType;

            let argp: string[] = [];
            for(let i = 0; i < elfrom.entries.length; ++i) {
                argp.push(this.coerce(`elist.entry_${i}`, elfrom.entries[i], elinto.entries[i]));
            }
            const body = `{ return ${this.mangleStringForCpp(into.trkey)}(${argp.join(", ")}); }`;
            const elconv = `${elconvsig} ${body}`;

            this.ephemeralListConverts.set(elconvsig, elconv);
        }

        return `convertFROM_${this.mangleStringForCpp(from.trkey)}_TO_${this.mangleStringForCpp(into.trkey)}`;
    }

    coercePrimitive(exp: string, from: MIRType, into: MIRType): string {
        const trfrom = this.getCPPReprFor(from);
        const trinto = this.getCPPReprFor(into);

        if (trfrom instanceof NoneRepr) {
            assert(!(trinto instanceof NoneRepr) && !(trinto instanceof StructRepr) && !(trinto instanceof RefRepr), "Should not be possible");

            if (trinto instanceof KeyValueRepr) {
                return "((KeyValue)BSQ_VALUE_NONE)";
            }
            else {
                return "((Value)BSQ_VALUE_NONE)";
            }
        }
        else if (trfrom instanceof StructRepr) {
            assert(!(trinto instanceof NoneRepr) && !(trinto instanceof StructRepr) && !(trinto instanceof RefRepr), "Should not be possible");

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

            if (trinto instanceof KeyValueRepr) {
                return `((KeyValue)${cc})`;
            }
            else {
                return `((Value)${cc})`;
            }
        }
        else if (trfrom instanceof RefRepr) {
            assert(!(trinto instanceof NoneRepr) && !(trinto instanceof StructRepr) && !(trinto instanceof RefRepr), "Should not be possible");

            if (trinto instanceof KeyValueRepr) {
                return `((KeyValue)${exp})`;
            }
            else {
                return `((Value)${exp})`;
            }
        }
        else if (trfrom instanceof KeyValueRepr) {
            if (trinto instanceof NoneRepr) {
                return `BSQ_VALUE_NONE`;
            }
            else if (trinto instanceof StructRepr) {
                if (trinto.base === "bool") {
                    return `BSQ_GET_VALUE_BOOL(${exp})`;
                }
                else if (trinto.base === "int64_t") {
                    return `BSQ_GET_VALUE_TAGGED_INT(${exp})`;
                }
                else {
                    if(trinto.base === "BSQTuple" || trinto.base === "BSQRecord") {
                        return `*${exp}`
                    }
                    else {
                        return `BSQ_GET_VALUE_PTR(${exp}, ${trinto.boxed})->bval`;
                    }
                }
            }
            else if (trinto instanceof RefRepr) {
                return `BSQ_GET_VALUE_PTR(${exp}, ${trinto.base})`;
            }
            else {
                return `((Value)${exp})`;
            }
        }
        else {
            if (trinto instanceof NoneRepr) {
                return `BSQ_VALUE_NONE`;
            }
            else if (trinto instanceof StructRepr) {
                if (trinto.base === "bool") {
                    return `BSQ_GET_VALUE_BOOL(${exp})`;
                }
                else if (trinto.base === "int64_t") {
                    return `BSQ_GET_VALUE_TAGGED_INT(${exp})`;
                }
                else {
                    if(trinto.base === "BSQTuple" || trinto.base === "BSQRecord") {
                        return `*${exp}`
                    }
                    else {
                        return `BSQ_GET_VALUE_PTR(${exp}, ${trinto.boxed})->bval`;
                    }
                }
            }
            else if (trinto instanceof RefRepr) {
                return `BSQ_GET_VALUE_PTR(${exp}, ${trinto.base})`;
            }
            else {
                return `((KeyValue)${exp})`;
            } 
        }
    }

    coerce(exp: string, from: MIRType, into: MIRType): string {
        const trfrom = this.getCPPReprFor(from);
        const trinto = this.getCPPReprFor(into);

        if (trfrom.base === trinto.base) {
            return exp;
        }

        if(this.typecheckEphemeral(from) && this.typecheckEphemeral(into)) {
            const cfunc = this.generateEphemeralListConvert(from, into);
            return `${cfunc}(${exp})`;
        }

        return this.coercePrimitive(exp, from, into);
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

    getEpehmeralType(tt: MIRType): MIREphemeralListType {
        return (tt.options[0] as MIREphemeralListType);
    }
    
    getRefCountableStatus(tt: MIRType): "no" | "direct" | "checked" | "ephemeral" | "ops" {
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

            if (tr instanceof EphemeralListRepr) {
                return "ephemeral";
            }
            else if (tr instanceof StructRepr) {
                return "ops";
            }
            else if (tr instanceof RefRepr) {
                return "direct";
            }
            else {
                return "checked";
            }
        }
    }

    buildIncOpForType(tt: MIRType, arg: string): string {
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
                return `RCIncFunctor_${tr.base}{}(${arg})`
            }
        }
    }

    buildReturnOpForType(tt: MIRType, arg: string, scope: string): string {
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
                return `RCReturnFunctor_${tr.base}{}(${arg}, ${scope});`
            }
        }
    }

    buildDecOpForType(tt: MIRType, arg: string): string {
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
                return `RCDecFunctor_${tr.base}{}(${arg})`
            }
        }
    }

    getFunctorsForType(tt: MIRType): {inc: string, dec: string, ret: string, eq: string, less: string, display: string} {
        const tr = this.getCPPReprFor(tt);
        assert(!(tr instanceof EphemeralListRepr));

        if (tr instanceof StructRepr) {
            return { inc: `RCIncFunctor_${tr.base}`, dec: `RCDecFunctor_${tr.base}`, ret: `RCReturnFunctor_${tr.base}`, eq: `EqualFunctor_${tr.base}`, less: `LessFunctor_${tr.base}`, display: `DisplayFunctor_${tr.base}` };
        }
        else if (tr instanceof RefRepr) {
            if(this.isSpecialReprEntity(tt)) {
                return { inc: `RCIncFunctor_${tr.base}`, dec: `RCDecFunctor_${tr.base}`, ret: `RCReturnFunctor_${tr.base}`, eq: `EqualFunctor_${tr.base}`, less: `LessFunctor_${tr.base}`, display: `DisplayFunctor_${tr.base}` };
            }
            else {
                return { inc: "RCIncFunctor_BSQRef", dec: "RCDecFunctor_BSQRef", ret: "[INVALID_RET]", eq: "[INVALID_EQ]", less: "[INVALID_LESS]", display: "DisplayFunctor_BSQRef" };
            }
        }
        else {
            if(tr.iskey) {
                return { inc: "RCIncFunctor_KeyValue", dec: "RCDecFunctor_KeyValue", ret: "[INVALID_RET]", eq: "EqualFunctor_KeyValue", less: "LessFunctor_KeyValue", display: "DisplayFunctor_KeyValue" };
            }
            else {
                return { inc: "RCIncFunctor_Value", dec: "RCDecFunctor_Value", ret: "[INVALID_RET]", eq: "[INVALID_EQ]", less: "[INVALID_LESS]", display: "DisplayFunctor_Value" };
            }
        }
    }

    isSpecialReprEntity(tt: MIRType): boolean {
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

    initializeConceptSubtypeRelation(): void {
        this.assembly.conceptDecls.forEach((tt) => {
            const cctype = this.getMIRType(tt.tkey);
            const est = [...this.assembly.entityDecls].map((edecl) => this.getMIRType(edecl[0])).filter((et) => this.assembly.subtypeOf(et, cctype));

            if(this.assembly.subtypeOf(this.tupleType, cctype)) {
                est.push(this.tupleType);
            }
            if(this.assembly.subtypeOf(this.recordType, cctype)) {
                est.push(this.recordType);
            }

            const keyarray = est.map((et) => et.trkey).sort();

            this.conceptSubtypeRelation.set(tt.tkey, keyarray);
        });
    }

    generateConstructorArgInc(argtype: MIRType, arg: string): string {
        const rcinfo = this.getRefCountableStatus(argtype);
        if (rcinfo === "no") {
            return arg;
        }

        return this.buildIncOpForType(argtype, arg);
    }

    generateListCPPEntity(entity: MIREntityTypeDecl): { isref: boolean, fwddecl: string, fulldecl: string } {
        const tt = this.getMIRType(entity.tkey);
        const typet = entity.terms.get("T") as MIRType;

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
        + "};\n"

        return { isref: true, fwddecl: `class ${declrepr.base};`, fulldecl: decl };
    }

    generateStackCPPEntity(entity: MIREntityTypeDecl): { isref: boolean, fwddecl: string, fulldecl: string } {
        const tt = this.getMIRType(entity.tkey);
        const typet = entity.terms.get("T") as MIRType;

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
        + "};\n"

        return { isref: true, fwddecl: `class ${declrepr.base};`, fulldecl: decl };
    }

    generateQueueCPPEntity(entity: MIREntityTypeDecl): { isref: boolean, fwddecl: string, fulldecl: string } {
        const tt = this.getMIRType(entity.tkey);
        const typet = entity.terms.get("T") as MIRType;

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
        + "};\n"

        return { isref: true, fwddecl: `class ${declrepr.base};`, fulldecl: decl };
    }

    generateSetCPPEntity(entity: MIREntityTypeDecl): { isref: boolean, fwddecl: string, fulldecl: string } {
        const tt = this.getMIRType(entity.tkey);
        const typet = entity.terms.get("T") as MIRType;

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
        + "};\n"

        return { isref: true, fwddecl: `class ${declrepr.base};`, fulldecl: decl };
    }

    generateMapCPPEntity(entity: MIREntityTypeDecl): { isref: boolean, fwddecl: string, fulldecl: string } {
        const tt = this.getMIRType(entity.tkey);
        const typek = entity.terms.get("K") as MIRType;
        const typev = entity.terms.get("V") as MIRType;

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
        + "};\n"

        return { isref: true, fwddecl: `class ${declrepr.base};`, fulldecl: decl };
    }

    generateCPPEntity(entity: MIREntityTypeDecl): { isref: boolean, fwddecl: string, fulldecl: string } | { isref: boolean, fwddecl: string, fulldecl: string, boxeddecl: string, ops: string[] } | undefined {
        const tt = this.getMIRType(entity.tkey);

        if(this.isSpecialReprEntity(tt)) {
            return undefined;
        }

        if(this.typecheckIsName(tt, /^NSCore::List<.*>$/)) {
            return this.generateListCPPEntity(entity);
        }
        else if(this.typecheckIsName(tt, /^NSCore::Stack<.*>$/)) {
            return this.generateStackCPPEntity(entity);
        }
        else if(this.typecheckIsName(tt, /^NSCore::Queue<.*>$/)) {
            return this.generateQueueCPPEntity(entity,);
        }
        else if(this.typecheckIsName(tt, /^NSCore::Set<.*>$/) || this.typecheckIsName(tt, /^NSCore::DynamicSet<.*>$/)) {
            return this.generateSetCPPEntity(entity);
        }
        else if(this.typecheckIsName(tt, /^NSCore::Map<.*>$/) || this.typecheckIsName(tt, /^NSCore::DynamicMap<.*>$/)) {
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

            if(!entity.attributes.includes("struct")) {
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
                +  move_assign_ops.join("\n  ")
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

    generateCPPEphemeral(tt: MIREphemeralListType): string {        
        let fields: string[] = [];
        let displayvals: string[] = [];
        let callretops: string[] = [];
        let constructor_args: string[] = [];
        let constructor_initializer: string[] = [];

        for(let i = 0; i < tt.entries.length; ++i) {
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
            + "};"
    }
}

export {
    CPPTypeEmitter
};
