//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import {  ConstantExpressionValue, LiteralExpressionValue } from "./body";

class TypeSignature {
}

class ParseErrorTypeSignature extends TypeSignature {
}

class AutoTypeSignature extends TypeSignature {
}

class TemplateTypeSignature extends TypeSignature {
    readonly name: string;

    constructor(name: string) {
        super();
        this.name = name;
    }
}

class NominalTypeSignature extends TypeSignature {
    readonly nameSpace: string;
    readonly tnames: string[];
    readonly terms: TypeSignature[];

    constructor(ns: string, tnames: string[], terms?: TypeSignature[]) {
        super();
        this.nameSpace = ns;
        this.tnames = tnames;
        this.terms = terms || [];
    }

    computeResolvedName(): string {
        return this.tnames.join("::");
    }
}

class LiteralTypeSignature extends TypeSignature {
    readonly typevalue: LiteralExpressionValue;

    constructor(typevalue: LiteralExpressionValue) {
        super();
        this.typevalue = typevalue;
    }
}

class TupleTypeSignature extends TypeSignature {
    readonly isvalue: boolean;
    readonly entries: [TypeSignature, boolean][];

    constructor(isvalue: boolean, entries: [TypeSignature, boolean][]) {
        super();
        this.isvalue = isvalue;
        this.entries = entries;
    }
}

class RecordTypeSignature extends TypeSignature {
    readonly isvalue: boolean;
    readonly entries: [string, TypeSignature, boolean][];

    constructor(isvalue: boolean, entries: [string, TypeSignature, boolean][]) {
        super();
        this.isvalue = isvalue;
        this.entries = entries;
    }
}

class EphemeralListTypeSignature extends TypeSignature {
    readonly entries: TypeSignature[];

    constructor(entries: TypeSignature[]) {
        super();
        this.entries = entries;
    }
}

class FunctionParameter {
    readonly name: string;
    readonly type: TypeSignature;
    readonly refKind: "ref" | "out" | "out?" | undefined;
    readonly isOptional: boolean;
    readonly defaultexp: ConstantExpressionValue | undefined;
    readonly litexp: LiteralExpressionValue | undefined;

    constructor(name: string, type: TypeSignature, isOpt: boolean, refKind: "ref" | "out" | "out?" | undefined, defaultexp: ConstantExpressionValue | undefined, litexp: LiteralExpressionValue | undefined) {
        this.name = name;
        this.type = type;
        this.isOptional = isOpt;
        this.refKind = refKind;
        this.defaultexp = defaultexp;
        this.litexp = litexp;
    }
}

class FunctionTypeSignature extends TypeSignature {
    readonly recursive: "yes" | "no" | "cond";
    readonly params: FunctionParameter[];
    readonly optRestParamName: string | undefined;
    readonly optRestParamType: TypeSignature | undefined;
    readonly resultType: TypeSignature;

    constructor(recursive: "yes" | "no" | "cond", params: FunctionParameter[], optRestParamName: string | undefined, optRestParamType: TypeSignature | undefined, resultType: TypeSignature) {
        super();
        this.recursive = recursive;
        this.params = params;
        this.optRestParamName = optRestParamName;
        this.optRestParamType = optRestParamType;
        this.resultType = resultType;
    }
}

class ProjectTypeSignature extends TypeSignature {
    readonly fromtype: TypeSignature;
    readonly oftype: TypeSignature;

    constructor(fromtype: TypeSignature, oftype: TypeSignature) {
        super();
        this.fromtype = fromtype;
        this.oftype = oftype;
    }
}

class PlusTypeSignature extends TypeSignature {
    readonly types: TypeSignature[];

    constructor(types: TypeSignature[]) {
        super();
        this.types = types;
    }
}

class AndTypeSignature extends TypeSignature {
    readonly types: TypeSignature[];

    constructor(types: TypeSignature[]) {
        super();
        this.types = types;
    }
}

class UnionTypeSignature extends TypeSignature {
    readonly types: TypeSignature[];

    constructor(types: TypeSignature[]) {
        super();
        this.types = types;
    }
}

export { 
    TypeSignature, ParseErrorTypeSignature, AutoTypeSignature, 
    TemplateTypeSignature, LiteralTypeSignature, NominalTypeSignature, 
    TupleTypeSignature, RecordTypeSignature, EphemeralListTypeSignature,
    FunctionParameter, FunctionTypeSignature, ProjectTypeSignature, PlusTypeSignature, AndTypeSignature, UnionTypeSignature
};
