//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ConceptTypeDecl, EntityTypeDecl } from "./assembly";

import * as assert from "assert";

abstract class ResolvedAtomType {
    readonly typeID: string;

    constructor(typeID: string) {
        this.typeID = typeID;
    }

    abstract hasTemplateType(): boolean;
}

class ResolvedTemplateUnifyType extends ResolvedAtomType {
    constructor(typeID: string) {
        super(typeID);
    }

    static create(name: string): ResolvedTemplateUnifyType {
        return new ResolvedTemplateUnifyType(name);
    }

    hasTemplateType(): boolean {
        return true;
    }
}

class ResolvedEntityAtomType extends ResolvedAtomType {
    readonly object: EntityTypeDecl;
    readonly binds: Map<string, ResolvedType>;

    constructor(typeID: string, object: EntityTypeDecl, binds: Map<string, ResolvedType>) {
        super(typeID);
        this.object = object;
        this.binds = binds;
    }

    static create(object: EntityTypeDecl, binds: Map<string, ResolvedType>): ResolvedEntityAtomType {
        let name = (object.ns !== "Core" ? (object.ns + "::") : "") + object.name;
        if (object.terms.length !== 0) {
            name += "<" + object.terms.map((arg) => (binds.get(arg.name) as ResolvedType).typeID).join(", ") + ">";
        }

        return new ResolvedEntityAtomType(name, object, binds);
    }

    hasTemplateType(): boolean {
        return false;
    }
}

class ResolvedConceptAtomTypeEntry {
    readonly typeID: string;
    readonly concept: ConceptTypeDecl;
    readonly binds: Map<string, ResolvedType>;

    constructor(typeID: string, concept: ConceptTypeDecl, binds: Map<string, ResolvedType>) {
        this.typeID = typeID;
        this.concept = concept;
        this.binds = binds;
    }

    static create(concept: ConceptTypeDecl, binds: Map<string, ResolvedType>): ResolvedConceptAtomTypeEntry {
        let name = (concept.ns !== "Core" ? (concept.ns + "::") : "") + concept.name;
        if (concept.terms.length !== 0) {
            name += "<" + concept.terms.map((arg) => (binds.get(arg.name) as ResolvedType).typeID).join(", ") + ">";
        }

        return new ResolvedConceptAtomTypeEntry(name, concept, binds);
    }
}

class ResolvedConceptAtomType extends ResolvedAtomType {
    readonly conceptTypes: ResolvedConceptAtomTypeEntry[];

    constructor(typeID: string, concepts: ResolvedConceptAtomTypeEntry[]) {
        super(typeID);
        this.conceptTypes = concepts;
    }

    static create(concepts: ResolvedConceptAtomTypeEntry[]): ResolvedConceptAtomType {
        const sortedConcepts = concepts.sort((a, b) => a.typeID.localeCompare(b.typeID));
        const name = sortedConcepts.map((cpt) => cpt.typeID).join("&");

        return new ResolvedConceptAtomType(name, sortedConcepts);
    }

    hasTemplateType(): boolean {
        return false;
    }
}

class ResolvedTupleAtomType extends ResolvedAtomType {
    readonly types: ResolvedType[];

    constructor(typeID: string, types: ResolvedType[]) {
        super(typeID);
        this.types = types;
    }

    static create(types: ResolvedType[]): ResolvedTupleAtomType {
        const name = types.map((entry) => entry.typeID).join(", ");

        return new ResolvedTupleAtomType("[" + name + "]", types);
    }

    hasTemplateType(): boolean {
        return this.types.some((entry) => entry.hasTemplateType());
    }
}

class ResolvedRecordAtomType extends ResolvedAtomType {
    readonly entries: {pname: string, ptype: ResolvedType}[];

    constructor(typeID: string, entries: {pname: string, ptype: ResolvedType}[]) {
        super(typeID);
        this.entries = entries;
    }

    static create(entries: {pname: string, ptype: ResolvedType}[]): ResolvedRecordAtomType {
        let simplifiedEntries = [...entries].sort((a, b) => a.pname.localeCompare(b.pname));
        const name = simplifiedEntries.map((entry) => entry.pname + ": " + entry.ptype.typeID).join(", ");

        return new ResolvedRecordAtomType("{" + name + "}", simplifiedEntries);
    }

    hasTemplateType(): boolean {
        return this.entries.some((entry) => entry.ptype.hasTemplateType());
    }
}

class ResolvedEphemeralListType extends ResolvedAtomType {
    readonly types: ResolvedType[];

    constructor(typeID: string, types: ResolvedType[]) {
        super(typeID);
        this.types = types;
    }

    static create(entries: ResolvedType[]): ResolvedEphemeralListType {
        const name = entries.map((entry) => entry.typeID).join(", ");

        return new ResolvedEphemeralListType("(|" + name + "|)", entries);
    }

    hasTemplateType(): boolean {
        return this.types.some((type) => type.hasTemplateType());
    }
}

class ResolvedType {
    readonly typeID: string;
    readonly options: ResolvedAtomType[];

    constructor(typeID: string, options: ResolvedAtomType[]) {
        this.typeID = typeID;
        this.options = options;
    }

    static createEmpty(): ResolvedType {
        return new ResolvedType("", []);
    }

    static createSingle(type: ResolvedAtomType): ResolvedType {
        return new ResolvedType(type.typeID, [type]);
    }

    static create(types: ResolvedAtomType[]): ResolvedType {
        if (types.length === 0) {
            return ResolvedType.createEmpty();
        }
        else if (types.length === 1) {
            return ResolvedType.createSingle(types[0]);
        }
        else {
            const atoms = types.sort((a, b) => a.typeID.localeCompare(b.typeID));
            const name = atoms.map((arg) => arg.typeID).join(" | ");

            return new ResolvedType(name, atoms);
        }
    }

    static tryGetOOTypeInfo(t: ResolvedType): ResolvedEntityAtomType | ResolvedConceptAtomType | undefined {
        if (t.options.length !== 1) {
            return undefined;
        }

        if (t.options[0] instanceof ResolvedEntityAtomType) {
            return (t.options[0] as ResolvedEntityAtomType);
        }
        else if (t.options[0] instanceof ResolvedConceptAtomType) {
            return t.options[0] as ResolvedConceptAtomType;
        }
        else {
            return undefined;
        }
    }

    isEmptyType(): boolean {
        return this.options.length === 0;
    }

    hasTemplateType(): boolean {
        return this.options.some((opt) => opt.hasTemplateType());
    }

    isTupleTargetType(): boolean {
        return this.options.every((opt) => opt instanceof ResolvedTupleAtomType);
    }

    getTupleTargetTypeIndexRange(): { req: number, opt: number } {
        assert(this.isTupleTargetType());

        const req = Math.min(...this.options.map((tup) => (tup as ResolvedTupleAtomType).types.length));
        const opt = Math.max(...this.options.map((tup) => (tup as ResolvedTupleAtomType).types.length));

        return { req: req, opt: opt };
    }

    isUniqueTupleTargetType(): boolean {
        return this.isTupleTargetType() && this.options.length === 1;
    }

    getUniqueTupleTargetType(): ResolvedTupleAtomType {
        return (this.options[0] as ResolvedTupleAtomType);
    }

    tryGetInferrableTupleConstructorType(): ResolvedTupleAtomType | undefined {
        const tcopts = this.options.filter((opt) => opt instanceof ResolvedTupleAtomType);

        if (tcopts.length !== 1) {
            return undefined;
        }

        return tcopts[0] as ResolvedTupleAtomType;
    }

    isRecordTargetType(): boolean {
        return this.options.every((opt) => opt instanceof ResolvedRecordAtomType);
    }

    getRecordTargetTypePropertySets(): {req: Set<string>, opt: Set<string>} {
        let allopts = new Set<string>();
        this.options.forEach((opt) => {
            (opt as ResolvedRecordAtomType).entries.forEach((entry) => allopts.add(entry.pname));
        });

        let req = new Set<string>();
        allopts.forEach((oname) => {
            if(this.options.every((opt) => (opt as ResolvedRecordAtomType).entries.findIndex((entry) => entry.pname === oname) !== -1)) {
                req.add(oname);
            }
        });

        return { req: req, opt: allopts };
    }

    isUniqueRecordTargetType(): boolean {
        return this.isRecordTargetType() && this.options.length === 1;
    }

    getUniqueRecordTargetType(): ResolvedRecordAtomType {
        return (this.options[0] as ResolvedRecordAtomType);
    }

    tryGetInferrableRecordConstructorType(): ResolvedRecordAtomType | undefined {
        const rcopts = this.options.filter((opt) => opt instanceof ResolvedRecordAtomType);

        if (rcopts.length !== 1) {
            return undefined;
        }

        return rcopts[0] as ResolvedRecordAtomType;
    }

    isUniqueCallTargetType(): boolean {
        if (this.options.length !== 1) {
            return false;
        }

        return this.options[0] instanceof ResolvedEntityAtomType;
    }

    getUniqueCallTargetType(): ResolvedEntityAtomType {
        return this.options[0] as ResolvedEntityAtomType;
    }

    getCollectionContentsType(): ResolvedType {
        const oodecl = this.getUniqueCallTargetType().object;
        const oobinds = this.getUniqueCallTargetType().binds;
        
        const etype = oodecl.attributes.includes("__map_type") 
                ? ResolvedType.createSingle(ResolvedTupleAtomType.create([oobinds.get("K") as ResolvedType, oobinds.get("V") as ResolvedType]))
                : oobinds.get("T") as ResolvedType;

        return etype;
    }

    isGroundedType(): boolean {
        return this.options.every((opt) => {
            if(opt instanceof ResolvedConceptAtomType) {
                return opt.conceptTypes.every((cpt) => !cpt.concept.attributes.includes("__universal"));
            }
            else if (opt instanceof ResolvedTupleAtomType) {
                return opt.types.every((tt) => tt.isGroundedType());
            }
            else if (opt instanceof ResolvedRecordAtomType) {
                return opt.entries.every((entry) => entry.ptype.isGroundedType());
            }
            else {
                return true;
            }
        });
    }

    tryGetInferrableValueListConstructorType(): ResolvedEphemeralListType | undefined {
        const vlopts = this.options.filter((opt) => opt instanceof ResolvedEphemeralListType);

        if (vlopts.length !== 1) {
            return undefined;
        }

        return (vlopts[0] as ResolvedEphemeralListType);
    }

    
    isSameType(otype: ResolvedType): boolean {
        return this.typeID === otype.typeID;
    }

    isNoneType(): boolean {
        return this.typeID === "None";
    }

    isSomeType(): boolean {
        return this.typeID === "Some";
    }

    isAnyType(): boolean {
        return this.typeID === "Any";
    }

    isNothingType(): boolean {
        return this.typeID === "Nothing";
    }

    isSomethingType(): boolean {
        if(!this.isUniqueCallTargetType()) {
            return false;
        }

        const oodecl = this.getUniqueCallTargetType().object;
        return oodecl.attributes.includes("__something_type");
    }

    isOptionType(): boolean {
        if(this.options.length !== 1 || !(this.options[0] instanceof ResolvedConceptAtomType)) {
            return false;
        }

        const ccpt = this.options[0] as ResolvedConceptAtomType;
        return ccpt.conceptTypes.length === 1 && ccpt.conceptTypes[0].concept.attributes.includes("__option_type");
    }

    isOkType(): boolean {
        if(!this.isUniqueCallTargetType()) {
            return false;
        }

        const oodecl = this.getUniqueCallTargetType().object;
        return oodecl.attributes.includes("__ok_type");
    }

    isErrType(): boolean {
        if(!this.isUniqueCallTargetType()) {
            return false;
        }

        const oodecl = this.getUniqueCallTargetType().object;
        return oodecl.attributes.includes("__err_type");
    }

    isResultType(): boolean {
        if(this.options.length !== 1 || !(this.options[0] instanceof ResolvedConceptAtomType)) {
            return false;
        }

        const ccpt = this.options[0] as ResolvedConceptAtomType;
        return ccpt.conceptTypes.length === 1 && ccpt.conceptTypes[0].concept.attributes.includes("__option_type");
    }

    isUniqueType(): boolean {
        if(this.options.length !== 1) {
            return false;
        }

        return !(this.options[0] instanceof ResolvedConceptAtomType);
    }
}

class ResolvedFunctionTypeParam {
    readonly name: string;
    readonly type: ResolvedType | ResolvedFunctionType;
    readonly refKind: "ref" | "out" | "out?" | undefined;
    readonly isOptional: boolean;
    readonly litexp: string | undefined;

    constructor(name: string, type: ResolvedType | ResolvedFunctionType, isOpt: boolean, refKind: "ref" | "out" | "out?" | undefined, litexp: string | undefined) {
        this.name = name;
        this.type = type;
        this.isOptional = isOpt;
        this.refKind = refKind;
        this.litexp = litexp;
    }
}

class ResolvedFunctionType {
    readonly typeID: string;
    readonly recursive: "yes" | "no" | "cond";
    readonly params: ResolvedFunctionTypeParam[];
    readonly optRestParamName: string | undefined;
    readonly optRestParamType: ResolvedType | undefined;
    readonly resultType: ResolvedType;
    readonly isPred: boolean;

    readonly allParamNames: Set<string>;

    constructor(typeID: string, recursive: "yes" | "no" | "cond", params: ResolvedFunctionTypeParam[], optRestParamName: string | undefined, optRestParamType: ResolvedType | undefined, resultType: ResolvedType, isPred: boolean) {
        this.typeID = typeID;
        this.recursive = recursive;
        this.params = params;
        this.optRestParamName = optRestParamName;
        this.optRestParamType = optRestParamType;
        this.resultType = resultType;
        this.isPred = isPred;

        this.allParamNames = new Set<string>();
    }

    static create(recursive: "yes" | "no" | "cond", params: ResolvedFunctionTypeParam[], optRestParamName: string | undefined, optRestParamType: ResolvedType | undefined, resultType: ResolvedType, isPred: boolean): ResolvedFunctionType {
        const cvalues = params.map((param) => (param.refKind !== undefined ? param.refKind : "") + param.name + (param.isOptional ? "?: " : ": ") + param.type.typeID + (param.litexp !== undefined ? ("==" + param.litexp) : ""));
        let cvalue = cvalues.join(", ");

        if (optRestParamName !== undefined && optRestParamType !== undefined) {
            cvalue += ((cvalues.length !== 0 ? ", " : "") + ("..." + optRestParamName + ": " + optRestParamType.typeID));
        }

        const lstr = isPred ? "pred" : "fn";
        const name = lstr + "(" + cvalue + ") -> " + resultType.typeID;
        return new ResolvedFunctionType(name, recursive, params, optRestParamName, optRestParamType, resultType, isPred);
    }
}

export {
    ResolvedAtomType,
    ResolvedTemplateUnifyType,
    ResolvedConceptAtomTypeEntry, ResolvedConceptAtomType, ResolvedEntityAtomType,
    ResolvedTupleAtomType, ResolvedRecordAtomType, 
    ResolvedEphemeralListType,
    ResolvedType, 
    ResolvedFunctionTypeParam, ResolvedFunctionType
};
