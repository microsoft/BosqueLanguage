"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
class ResolvedAtomType {
    constructor(rstr) {
        this.idStr = rstr;
    }
}
exports.ResolvedAtomType = ResolvedAtomType;
class ResolvedConceptAtomTypeEntry {
    constructor(idstr, concept, binds) {
        this.idStr = idstr;
        this.concept = concept;
        this.binds = binds;
    }
    static create(concept, binds) {
        let name = concept.ns + "::" + concept.name;
        if (concept.terms.length !== 0) {
            name += "<" + concept.terms.map((arg) => binds.get(arg.name).idStr).join(", ") + ">";
        }
        return new ResolvedConceptAtomTypeEntry(name, concept, binds);
    }
}
exports.ResolvedConceptAtomTypeEntry = ResolvedConceptAtomTypeEntry;
class ResolvedConceptAtomType extends ResolvedAtomType {
    constructor(rstr, concepts) {
        super(rstr);
        this.conceptTypes = concepts;
    }
    static create(concepts) {
        const sortedConcepts = concepts.sort((a, b) => a.idStr.localeCompare(b.idStr));
        const rstr = sortedConcepts.map((cpt) => cpt.idStr).join("&");
        return new ResolvedConceptAtomType(rstr, sortedConcepts);
    }
}
exports.ResolvedConceptAtomType = ResolvedConceptAtomType;
class ResolvedEntityAtomType extends ResolvedAtomType {
    constructor(rstr, object, binds) {
        super(rstr);
        this.object = object;
        this.binds = binds;
    }
    static create(object, binds) {
        let name = object.ns + "::" + object.name;
        if (object.terms.length !== 0) {
            name += "<" + object.terms.map((arg) => binds.get(arg.name).idStr).join(", ") + ">";
        }
        return new ResolvedEntityAtomType(name, object, binds);
    }
}
exports.ResolvedEntityAtomType = ResolvedEntityAtomType;
class ResolvedTupleAtomTypeEntry {
    constructor(type, isOpt) {
        this.isOptional = isOpt;
        this.type = type;
    }
}
exports.ResolvedTupleAtomTypeEntry = ResolvedTupleAtomTypeEntry;
class ResolvedTupleAtomType extends ResolvedAtomType {
    constructor(rstr, types) {
        super(rstr);
        this.types = types;
    }
    static create(entries) {
        let simplifiedEntries = [...entries];
        let cvalue = simplifiedEntries.map((entry) => (entry.isOptional ? "?:" : "") + entry.type.idStr).join(", ");
        return new ResolvedTupleAtomType("[" + cvalue + "]", simplifiedEntries);
    }
}
exports.ResolvedTupleAtomType = ResolvedTupleAtomType;
class ResolvedRecordAtomTypeEntry {
    constructor(name, type, isOpt) {
        this.name = name;
        this.type = type;
        this.isOptional = isOpt;
    }
}
exports.ResolvedRecordAtomTypeEntry = ResolvedRecordAtomTypeEntry;
class ResolvedRecordAtomType extends ResolvedAtomType {
    constructor(rstr, entries) {
        super(rstr);
        this.entries = entries;
    }
    static create(entries) {
        let simplifiedEntries = [...entries];
        simplifiedEntries.sort((a, b) => a.name.localeCompare(b.name));
        let cvalue = simplifiedEntries.map((entry) => entry.name + (entry.isOptional ? "?:" : ":") + entry.type.idStr).join(", ");
        return new ResolvedRecordAtomType("{" + cvalue + "}", simplifiedEntries);
    }
}
exports.ResolvedRecordAtomType = ResolvedRecordAtomType;
class ResolvedEphemeralListType extends ResolvedAtomType {
    constructor(rstr, types) {
        super(rstr);
        this.types = types;
    }
    static create(entries) {
        const simplifiedEntries = [...entries];
        const cvalue = simplifiedEntries.map((entry) => entry.idStr).join(", ");
        return new ResolvedEphemeralListType("(|" + cvalue + "|)", simplifiedEntries);
    }
}
exports.ResolvedEphemeralListType = ResolvedEphemeralListType;
class ResolvedType {
    constructor(rstr, options) {
        this.idStr = rstr;
        this.options = options;
    }
    static createEmpty() {
        return new ResolvedType("", []);
    }
    static createSingle(type) {
        return new ResolvedType(type.idStr, [type]);
    }
    static create(types) {
        if (types.length === 0) {
            return ResolvedType.createEmpty();
        }
        else if (types.length === 1) {
            return ResolvedType.createSingle(types[0]);
        }
        else {
            const atoms = types.sort((a, b) => a.idStr.localeCompare(b.idStr));
            const res = atoms.map((arg) => arg.idStr).join("|");
            return new ResolvedType(res, atoms);
        }
    }
    static tryGetOOTypeInfo(t) {
        if (t.options.length !== 1) {
            return undefined;
        }
        if (t.options[0] instanceof ResolvedEntityAtomType) {
            return t.options[0];
        }
        else if (t.options[0] instanceof ResolvedConceptAtomType) {
            return t.options[0];
        }
        else {
            return undefined;
        }
    }
    isEmptyType() {
        return this.options.length === 0;
    }
    isUniqueCallTargetType() {
        if (this.options.length !== 1) {
            return false;
        }
        return this.options[0] instanceof ResolvedEntityAtomType;
    }
    isNoneType() {
        return this.options.length === 1 && this.options[0].idStr === "NSCore::None";
    }
    isSomeType() {
        return this.options.length === 1 && this.options[0].idStr === "NSCore::Some";
    }
    isAnyType() {
        return this.options.length === 1 && this.options[0].idStr === "NSCore::Any";
    }
    isEphemeralListType() {
        return this.options.length === 1 && this.options[0] instanceof ResolvedEphemeralListType;
    }
}
exports.ResolvedType = ResolvedType;
class ResolvedFunctionTypeParam {
    constructor(name, type, isOpt, isRef) {
        this.name = name;
        this.type = type;
        this.isOptional = isOpt;
        this.isRef = isRef;
    }
}
exports.ResolvedFunctionTypeParam = ResolvedFunctionTypeParam;
class ResolvedFunctionType {
    constructor(rstr, recursive, params, optRestParamName, optRestParamType, resultType) {
        this.idStr = rstr;
        this.recursive = recursive;
        this.params = params;
        this.optRestParamName = optRestParamName;
        this.optRestParamType = optRestParamType;
        this.resultType = resultType;
        this.allParamNames = new Set();
    }
    static create(recursive, params, optRestParamName, optRestParamType, resultType) {
        const cvalues = params.map((param) => (param.isRef ? "ref " : "") + param.name + (param.isOptional ? "?: " : ": ") + param.type.idStr);
        let cvalue = cvalues.join(", ");
        let recstr = "";
        if (recursive === "yes") {
            recstr = "recursive ";
        }
        if (recursive === "cond") {
            recstr = "recursive? ";
        }
        if (optRestParamName !== undefined && optRestParamType !== undefined) {
            cvalue += ((cvalues.length !== 0 ? ", " : "") + ("..." + optRestParamName + ": " + optRestParamType.idStr));
        }
        return new ResolvedFunctionType(recstr + "(" + cvalue + ") -> " + resultType.idStr, recursive, params, optRestParamName, optRestParamType, resultType);
    }
}
exports.ResolvedFunctionType = ResolvedFunctionType;
//# sourceMappingURL=resolved_type.js.map