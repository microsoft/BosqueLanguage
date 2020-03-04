"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
class TypeSignature {
}
exports.TypeSignature = TypeSignature;
class ParseErrorTypeSignature extends TypeSignature {
}
exports.ParseErrorTypeSignature = ParseErrorTypeSignature;
class AutoTypeSignature extends TypeSignature {
}
exports.AutoTypeSignature = AutoTypeSignature;
class TemplateTypeSignature extends TypeSignature {
    constructor(name) {
        super();
        this.name = name;
    }
}
exports.TemplateTypeSignature = TemplateTypeSignature;
class NominalTypeSignature extends TypeSignature {
    constructor(ns, base, terms) {
        super();
        this.nameSpace = ns;
        this.baseName = base;
        this.terms = terms || [];
    }
}
exports.NominalTypeSignature = NominalTypeSignature;
class TupleTypeSignature extends TypeSignature {
    constructor(entries) {
        super();
        this.entries = entries;
    }
}
exports.TupleTypeSignature = TupleTypeSignature;
class RecordTypeSignature extends TypeSignature {
    constructor(entries) {
        super();
        this.entries = entries;
    }
}
exports.RecordTypeSignature = RecordTypeSignature;
class EphemeralListTypeSignature extends TypeSignature {
    constructor(entries) {
        super();
        this.entries = entries;
    }
}
exports.EphemeralListTypeSignature = EphemeralListTypeSignature;
class FunctionParameter {
    constructor(name, type, isOpt, isRef) {
        this.name = name;
        this.type = type;
        this.isOptional = isOpt;
        this.isRef = isRef;
    }
}
exports.FunctionParameter = FunctionParameter;
class FunctionTypeSignature extends TypeSignature {
    constructor(recursive, params, optRestParamName, optRestParamType, resultType) {
        super();
        this.recursive = recursive;
        this.params = params;
        this.optRestParamName = optRestParamName;
        this.optRestParamType = optRestParamType;
        this.resultType = resultType;
    }
}
exports.FunctionTypeSignature = FunctionTypeSignature;
class ProjectTypeSignature extends TypeSignature {
    constructor(fromtype, oftype) {
        super();
        this.fromtype = fromtype;
        this.oftype = oftype;
    }
}
exports.ProjectTypeSignature = ProjectTypeSignature;
class IntersectionTypeSignature extends TypeSignature {
    constructor(types) {
        super();
        this.types = types;
    }
}
exports.IntersectionTypeSignature = IntersectionTypeSignature;
class UnionTypeSignature extends TypeSignature {
    constructor(types) {
        super();
        this.types = types;
    }
}
exports.UnionTypeSignature = UnionTypeSignature;
//# sourceMappingURL=type_signature.js.map