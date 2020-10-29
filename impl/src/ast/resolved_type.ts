//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ConceptTypeDecl, EntityTypeDecl, SpecialTypeCategory } from "./assembly";
import { Expression } from "./body";

abstract class ResolvedAtomType {
    readonly idStr: string;

    constructor(rstr: string) {
        this.idStr = rstr;
    }

    abstract hasTemplateType(): boolean;
}

class ResolvedTemplateUnifyType extends ResolvedAtomType {
    constructor(rstr: string) {
        super(rstr);
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

    constructor(rstr: string, object: EntityTypeDecl, binds: Map<string, ResolvedType>) {
        super(rstr);
        this.object = object;
        this.binds = binds;
    }

    static create(object: EntityTypeDecl, binds: Map<string, ResolvedType>): ResolvedEntityAtomType {
        let name = object.ns + "::" + object.name;
        if (object.terms.length !== 0) {
            name += "<" + object.terms.map((arg) => (binds.get(arg.name) as ResolvedType).idStr).join(", ") + ">";
        }

        return new ResolvedEntityAtomType(name, object, binds);
    }

    hasTemplateType(): boolean {
        return false;
    }
}

class ResolvedLiteralAtomType extends ResolvedAtomType {
    readonly oftype: ResolvedType;
    readonly vexp: Expression; //Literal bool, number, typed number, or enum

    constructor(rstr: string, oftype: ResolvedType, vexp: Expression) {
        super(rstr);
        this.oftype = oftype;
        this.vexp = vexp;
    }

    static create(oftype: ResolvedType, vexp: Expression, ofvalue: boolean | string): ResolvedLiteralAtomType {
        return new ResolvedLiteralAtomType(`${oftype.idStr}::${ofvalue}`, oftype, vexp);
    }

    hasTemplateType(): boolean {
        return false;
    }
}

class ResolvedConceptAtomTypeEntry {
    readonly idStr: string;
    readonly concept: ConceptTypeDecl;
    readonly binds: Map<string, ResolvedType>;

    constructor(idstr: string, concept: ConceptTypeDecl, binds: Map<string, ResolvedType>) {
        this.idStr = idstr;
        this.concept = concept;
        this.binds = binds;
    }

    static create(concept: ConceptTypeDecl, binds: Map<string, ResolvedType>): ResolvedConceptAtomTypeEntry {
        let name = concept.ns + "::" + concept.name;
        if (concept.terms.length !== 0) {
            name += "<" + concept.terms.map((arg) => (binds.get(arg.name) as ResolvedType).idStr).join(", ") + ">";
        }

        return new ResolvedConceptAtomTypeEntry(name, concept, binds);
    }
}

class ResolvedConceptAtomType extends ResolvedAtomType {
    readonly conceptTypes: ResolvedConceptAtomTypeEntry[];

    constructor(rstr: string, concepts: ResolvedConceptAtomTypeEntry[]) {
        super(rstr);
        this.conceptTypes = concepts;
    }

    static create(concepts: ResolvedConceptAtomTypeEntry[]): ResolvedConceptAtomType {
        const sortedConcepts = concepts.sort((a, b) => a.idStr.localeCompare(b.idStr));
        const rstr = sortedConcepts.map((cpt) => cpt.idStr).join("&");

        return new ResolvedConceptAtomType(rstr, sortedConcepts);
    }

    hasTemplateType(): boolean {
        return false;
    }
}

class ResolvedTupleAtomTypeEntry {
    readonly type: ResolvedType;
    readonly isOptional: boolean;

    constructor(type: ResolvedType, isOpt: boolean) {
        this.isOptional = isOpt;
        this.type = type;
    }
}

class ResolvedTupleAtomType extends ResolvedAtomType {
    readonly isvalue: boolean;
    readonly grounded: boolean;
    readonly types: ResolvedTupleAtomTypeEntry[];

    constructor(rstr: string, isvalue: boolean, grounded: boolean, types: ResolvedTupleAtomTypeEntry[]) {
        super(rstr);
        this.isvalue = isvalue;
        this.grounded = grounded;
        this.types = types;
    }

    static create(isvalue: boolean, entries: ResolvedTupleAtomTypeEntry[]): ResolvedTupleAtomType {
        const cvalue = entries.map((entry) => (entry.isOptional ? "?:" : "") + entry.type.idStr).join(", ");
        const grounded = entries.every((entry) => entry.type.isGroundedType());

        return new ResolvedTupleAtomType((isvalue ? "#[" : "@[") + cvalue + "]", isvalue, grounded, entries);
    }

    hasTemplateType(): boolean {
        return this.types.some((entry) => entry.type.hasTemplateType());
    }
}

class ResolvedRecordAtomTypeEntry {
    readonly name: string;
    readonly type: ResolvedType;
    readonly isOptional: boolean;

    constructor(name: string, type: ResolvedType, isOpt: boolean) {
        this.name = name;
        this.type = type;
        this.isOptional = isOpt;
    }
}

class ResolvedRecordAtomType extends ResolvedAtomType {
    readonly isvalue: boolean;
    readonly grounded: boolean;
    readonly entries: ResolvedRecordAtomTypeEntry[];

    constructor(rstr: string, isvalue: boolean, grounded: boolean, entries: ResolvedRecordAtomTypeEntry[]) {
        super(rstr);
        this.isvalue = isvalue;
        this.grounded = grounded;
        this.entries = entries;
    }

    static create(isvalue: boolean, entries: ResolvedRecordAtomTypeEntry[]): ResolvedRecordAtomType {
        let simplifiedEntries: ResolvedRecordAtomTypeEntry[] = [...entries];
        simplifiedEntries.sort((a, b) => a.name.localeCompare(b.name));
        const cvalue = simplifiedEntries.map((entry) => entry.name + (entry.isOptional ? "?:" : ":") + entry.type.idStr).join(", ");
        const grounded = entries.every((entry) => entry.type.isGroundedType());

        return new ResolvedRecordAtomType((isvalue ? "#{" : "@{") + cvalue + "}", isvalue, grounded, simplifiedEntries);
    }

    hasTemplateType(): boolean {
        return this.entries.some((entry) => entry.type.hasTemplateType());
    }
}

class ResolvedEphemeralListType extends ResolvedAtomType {
    readonly types: ResolvedType[];

    constructor(rstr: string, types: ResolvedType[]) {
        super(rstr);
        this.types = types;
    }

    static create(entries: ResolvedType[]): ResolvedEphemeralListType {
        const simplifiedEntries = [...entries];
        const cvalue = simplifiedEntries.map((entry) => entry.idStr).join(", ");
        return new ResolvedEphemeralListType("(|" + cvalue + "|)", simplifiedEntries);
    }

    hasTemplateType(): boolean {
        return this.types.some((type) => type.hasTemplateType());
    }
}

class ResolvedType {
    readonly idStr: string;
    readonly options: ResolvedAtomType[];

    constructor(rstr: string, options: ResolvedAtomType[]) {
        this.idStr = rstr;
        this.options = options;
    }

    static createEmpty(): ResolvedType {
        return new ResolvedType("", []);
    }

    static createSingle(type: ResolvedAtomType): ResolvedType {
        return new ResolvedType(type.idStr, [type]);
    }

    static create(types: ResolvedAtomType[]): ResolvedType {
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
        if(this.options.length === 0) {
            return { req: 0, opt: 0 }; 
        }

        let req: number[] = [];
        let opt = -1;

        for (let i = 0; i < this.options.length; ++i) {
            const rta = (this.options[i] as ResolvedTupleAtomType);

            const opti = rta.types.findIndex((tt) => tt.isOptional);
            req.push(opti !== -1 ? opti : rta.types.length)

            opt = Math.max(opt, rta.types.length);
        }

        return { req: Math.min(...req), opt: opt };
    }

    isUniqueTupleTargetType(): boolean {
        if (this.options.length !== 1) {
            return false;
        }

        return (this.options[0] instanceof ResolvedTupleAtomType) && !(this.options[0] as ResolvedTupleAtomType).types.some((value) => value.isOptional);
    }

    getUniqueTupleTargetType(): ResolvedTupleAtomType {
        return (this.options[0] as ResolvedTupleAtomType);
    }

    tryGetInferrableTupleConstructorType(isvalue: boolean): ResolvedTupleAtomType | undefined {
        const tcopts = this.options.filter((opt) => opt instanceof ResolvedTupleAtomType && opt.isvalue === isvalue);

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
            (opt as ResolvedRecordAtomType).entries.forEach((entry) => allopts.add(entry.name));
        });

        let req = new Set<string>();
        allopts.forEach((oname) => {
            if(this.options.every((opt) => (opt as ResolvedRecordAtomType).entries.findIndex((entry) => entry.name === oname) !== -1)) {
                req.add(oname);
            }
        });

        return { req: req, opt: allopts };
    }

    isUniqueRecordTargetType(): boolean {
        if (this.options.length !== 1) {
            return false;
        }

        return (this.options[0] instanceof ResolvedRecordAtomType) && !(this.options[0] as ResolvedRecordAtomType).entries.some((value) => value.isOptional);
    }

    getUniqueRecordTargetType(): ResolvedRecordAtomType {
        return (this.options[0] as ResolvedRecordAtomType);
    }

    tryGetInferrableRecordConstructorType(isvalue: boolean): ResolvedRecordAtomType | undefined {
        const rcopts = this.options.filter((opt) => opt instanceof ResolvedRecordAtomType && opt.isvalue === isvalue);

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
        
        const etype = oodecl.specialDecls.has(SpecialTypeCategory.MapTypeDecl) 
                ? ResolvedType.createSingle(ResolvedTupleAtomType.create(true, [new ResolvedTupleAtomTypeEntry(oobinds.get("K") as ResolvedType, false), new ResolvedTupleAtomTypeEntry(oobinds.get("V") as ResolvedType, false)]))
                : oobinds.get("T") as ResolvedType;

        return etype;
    }

    tryGetInferrableValueListConstructorType(): ResolvedEphemeralListType | undefined {
        const vlopts = this.options.filter((opt) => opt instanceof ResolvedEphemeralListType);

        if (vlopts.length !== 1) {
            return undefined;
        }

        return (vlopts[0] as ResolvedEphemeralListType);
    }

    isNoneType(): boolean {
        return this.options.length === 1 && this.options[0].idStr === "NSCore::None";
    }

    isSomeType(): boolean {
        return this.options.length === 1 && this.options[0].idStr === "NSCore::Some";
    }

    isAnyType(): boolean {
        return this.options.length === 1 && this.options[0].idStr === "NSCore::Any";
    }

    isSameType(otype: ResolvedType): boolean {
        return this.idStr === otype.idStr;
    }

    isResultConceptType(): boolean {
        if(this.options.length !== 1 || !(this.options[0] instanceof ResolvedConceptAtomType)) {
            return false;
        }

        const ccpt = this.options[0] as ResolvedConceptAtomType;
        return ccpt.conceptTypes.length === 1 && ccpt.conceptTypes[0].concept.specialDecls.has(SpecialTypeCategory.ResultDecl);
    }

    isResultEntityType(): boolean {
        if(this.options.length !== 1 || !(this.options[0] instanceof ResolvedConceptAtomType)) {
            return false;
        }

        const ccpt = this.options[0] as ResolvedConceptAtomType;
        return ccpt.conceptTypes.every((cpt) => cpt.concept.specialDecls.has(SpecialTypeCategory.ResultOkDecl) || cpt.concept.specialDecls.has(SpecialTypeCategory.ResultErrDecl));
    }

    isResultGeneralType(): boolean {
        return this.isResultConceptType() || this.isResultEntityType();
    }

    isNotResultGeneralType(): boolean {
        return this.options.every((opt) => {
            if(opt instanceof ResolvedConceptAtomType) {
                return opt.conceptTypes.every((cpt) => !cpt.concept.specialDecls.has(SpecialTypeCategory.ResultDecl));
            }
            else if(opt instanceof ResolvedEntityAtomType) {
                return !opt.object.specialDecls.has(SpecialTypeCategory.ResultOkDecl) && !opt.object.specialDecls.has(SpecialTypeCategory.ResultErrDecl);
            }
            else {
                return true;
            }
        });
    }

    isGroundedType(): boolean {
        return this.options.every((opt) => {
            if(opt instanceof ResolvedConceptAtomType) {
                return false;
            }
            else if(opt instanceof ResolvedEntityAtomType) {
                if(opt.object.specialDecls.has(SpecialTypeCategory.GroundedTypeDecl)) {
                    return true;
                }
                else if(opt.object.specialDecls.has(SpecialTypeCategory.ListTypeDecl)) {
                    return (opt.binds.get("T") as ResolvedType).isGroundedType();
                }
                else if(opt.object.specialDecls.has(SpecialTypeCategory.VectorTypeDecl)) {
                    return (opt.binds.get("T") as ResolvedType).isGroundedType();
                }
                else if(opt.object.specialDecls.has(SpecialTypeCategory.StackTypeDecl)) {
                    return (opt.binds.get("T") as ResolvedType).isGroundedType();
                }
                else if(opt.object.specialDecls.has(SpecialTypeCategory.QueueTypeDecl)) {
                    return (opt.binds.get("T") as ResolvedType).isGroundedType();
                }
                else if(opt.object.specialDecls.has(SpecialTypeCategory.SetTypeDecl)) {
                    return (opt.binds.get("T") as ResolvedType).isGroundedType();
                }
                else if(opt.object.specialDecls.has(SpecialTypeCategory.MapTypeDecl)) {
                    return (opt.binds.get("K") as ResolvedType).isGroundedType() && (opt.binds.get("V") as ResolvedType).isGroundedType();
                }
                else {
                    return false;
                }
            }
            else if(opt instanceof ResolvedLiteralAtomType) {
                return true;
            }
            else if(opt instanceof ResolvedTupleAtomType) {
                return opt.grounded;
            }
            else if(opt instanceof ResolvedRecordAtomType) {
                return opt.grounded;
            }
            else {
                //ephemeral list should never be in a grounded position
                return false;
            }
        });
    }

    isUniqueType(): boolean {
        if(this.options.length !== 1) {
            return false;
        }

        const opt = this.options[0];
        if (opt instanceof ResolvedConceptAtomType) {
            return false;
        }
        else if (opt instanceof ResolvedEntityAtomType) {
            return true;
        }
        else if (opt instanceof ResolvedLiteralAtomType) {
            return true;
        }
        else if (opt instanceof ResolvedTupleAtomType) {
            return opt.grounded && !opt.types[0].isOptional;
        }
        else if (opt instanceof ResolvedRecordAtomType) {
            return opt.grounded && !opt.entries[0].isOptional;
        }
        else {
            //ephemeral list should never be in a unique position
            return false;
        }
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
    readonly idStr: string;
    readonly recursive: "yes" | "no" | "cond";
    readonly params: ResolvedFunctionTypeParam[];
    readonly optRestParamName: string | undefined;
    readonly optRestParamType: ResolvedType | undefined;
    readonly resultType: ResolvedType;

    readonly allParamNames: Set<string>;

    constructor(rstr: string, recursive: "yes" | "no" | "cond", params: ResolvedFunctionTypeParam[], optRestParamName: string | undefined, optRestParamType: ResolvedType | undefined, resultType: ResolvedType) {
        this.idStr = rstr;
        this.recursive = recursive;
        this.params = params;
        this.optRestParamName = optRestParamName;
        this.optRestParamType = optRestParamType;
        this.resultType = resultType;

        this.allParamNames = new Set<string>();
    }

    static create(recursive: "yes" | "no" | "cond", params: ResolvedFunctionTypeParam[], optRestParamName: string | undefined, optRestParamType: ResolvedType | undefined, resultType: ResolvedType): ResolvedFunctionType {
        const cvalues = params.map((param) => (param.refKind !== undefined ? param.refKind : "") + param.name + (param.isOptional ? "?: " : ": ") + param.type.idStr + (param.litexp !== undefined ? ("==" + param.litexp) : ""));
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

export {
    ResolvedAtomType,
    ResolvedTemplateUnifyType,
    ResolvedConceptAtomTypeEntry, ResolvedConceptAtomType, ResolvedEntityAtomType, 
    ResolvedLiteralAtomType,
    ResolvedTupleAtomTypeEntry, ResolvedTupleAtomType, 
    ResolvedRecordAtomTypeEntry, ResolvedRecordAtomType, 
    ResolvedEphemeralListType,
    ResolvedType, 
    ResolvedFunctionTypeParam, ResolvedFunctionType
};
