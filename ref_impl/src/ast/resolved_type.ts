//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ConceptTypeDecl, EntityTypeDecl } from "./assembly";

class ResolvedAtomType {
    readonly idStr: string;

    constructor(rstr: string) {
        this.idStr = rstr;
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
            name += "[" + concept.terms.map((arg) => (binds.get(arg.name) as ResolvedType).idStr).join(", ") + "]";
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
            name += "[" + object.terms.map((arg) => (binds.get(arg.name) as ResolvedType).idStr).join(", ") + "]";
        }

        return new ResolvedEntityAtomType(name, object, binds);
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
    readonly types: ResolvedTupleAtomTypeEntry[];
    readonly isOpen: boolean;

    constructor(rstr: string, types: ResolvedTupleAtomTypeEntry[], isOpen: boolean) {
        super(rstr);
        this.types = types;
        this.isOpen = isOpen;
    }

    static create(isOpen: boolean, entries: ResolvedTupleAtomTypeEntry[]): ResolvedTupleAtomType {
        let simplifiedEntries = [...entries];

        //if Open then drop all tailing [, ?: Any ] entries since they are already covered more compactly with the open specifier
        if (isOpen) {
            let pos: number = simplifiedEntries.length - 1;
            while (pos >= 0 && simplifiedEntries[pos].isOptional && simplifiedEntries[pos].type.isAnyType()) {
                --pos;
            }
            pos++;

            simplifiedEntries = simplifiedEntries.slice(0, pos);
        }

        let cvalue = simplifiedEntries.map((entry) => (entry.isOptional ? "?:" : "") + entry.type.idStr).join(", ");
        if (isOpen) {
            cvalue += (simplifiedEntries.length !== 0 ? ", " : "") + "...";
        }

        return new ResolvedTupleAtomType("[" + cvalue + "]", simplifiedEntries, isOpen);
    }

    static createGenericOpen(): ResolvedTupleAtomType {
        return new ResolvedTupleAtomType("[...]", [], true);
    }

    isAllOpenType(): boolean {
        return this.isOpen && this.types.length === 0;
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
    readonly entries: ResolvedRecordAtomTypeEntry[];
    readonly isOpen: boolean;

    constructor(rstr: string, entries: ResolvedRecordAtomTypeEntry[], isOpen: boolean) {
        super(rstr);
        this.entries = entries;
        this.isOpen = isOpen;
    }

    static create(isOpen: boolean, entries: ResolvedRecordAtomTypeEntry[]): ResolvedRecordAtomType {
        let simplifiedEntries: ResolvedRecordAtomTypeEntry[] = [];
        if (!isOpen) {
            simplifiedEntries = entries;
        }
        else {
            simplifiedEntries = entries.filter((entry) => !entry.isOptional || !entry.type.isAnyType());
        }
        simplifiedEntries.sort((a, b) => a.name.localeCompare(b.name));

        let cvalue = simplifiedEntries.map((entry) => entry.name + (entry.isOptional ? "?:" : ":") + entry.type.idStr).join(", ");
        if (isOpen) {
            cvalue += (simplifiedEntries.length !== 0 ? ", " : "") + "...";
        }

        return new ResolvedRecordAtomType("{" + cvalue + "}", simplifiedEntries, isOpen);
    }

    static createGenericOpen(): ResolvedRecordAtomType {
        return new ResolvedRecordAtomType("{...}", [], true);
    }

    isAllOpenType(): boolean {
        return this.isOpen && this.entries.length === 0;
    }
}

class ResolvedFunctionAtomTypeParam {
    readonly name: string;
    readonly isOptional: boolean;
    readonly type: ResolvedType;

    constructor(name: string, isOptional: boolean, type: ResolvedType) {
        this.name = name;
        this.isOptional = isOptional;
        this.type = type;
    }
}

class ResolvedFunctionAtomType extends ResolvedAtomType {
    readonly params: ResolvedFunctionAtomTypeParam[];
    readonly optRestParamName: string | undefined;
    readonly optRestParamType: ResolvedType | undefined;
    readonly resultType: ResolvedType;

    readonly allParamNames: Set<string>;

    constructor(rstr: string, params: ResolvedFunctionAtomTypeParam[], optRestParamName: string | undefined, optRestParamType: ResolvedType | undefined, resultType: ResolvedType, allParamNames: Set<string>) {
        super(rstr);
        this.params = params;
        this.optRestParamName = optRestParamName;
        this.optRestParamType = optRestParamType;
        this.resultType = resultType;

        this.allParamNames = new Set<string>();
    }

    static create(params: ResolvedFunctionAtomTypeParam[], optRestParamName: string | undefined, optRestParamType: ResolvedType | undefined, resultType: ResolvedType): ResolvedFunctionAtomType {
        let cvalues: string[] = [];
        let allNames = new Set<string>();
        params.forEach((param) => {
            if (param.name !== "_") {
                allNames.add(param.name);
            }
            cvalues.push(param.name + (param.isOptional ? "?: " : ": ") + param.type.idStr);
        });
        let cvalue = cvalues.join(", ");

        if (optRestParamName !== undefined && optRestParamType !== undefined) {
            cvalue += ((cvalues.length !== 0 ? ", " : "") + ("..." + optRestParamName + ": " + optRestParamType.idStr));
        }

        return new ResolvedFunctionAtomType("(" + cvalue + ") -> " + resultType.idStr, params, optRestParamName, optRestParamType, resultType, allNames);
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

    static tryGetUniqueFunctionTypeAtom(t: ResolvedType): ResolvedFunctionAtomType | undefined {
        if (t.options.length === 1 && t.options[0] instanceof ResolvedFunctionAtomType) {
            return t.options[0] as ResolvedFunctionAtomType;
        }
        else {
            return undefined;
        }
    }

    isEmptyType(): boolean {
        return this.options.length === 0;
    }

    isUniqueTemplateInstantiationType(): boolean {
        if (this.options.length !== 1) {
            return false;
        }

        if (this.options[0] instanceof ResolvedEntityAtomType) {
            return true;
        }
        else if (this.options[0] instanceof ResolvedConceptAtomType) {
            return (this.options[0] as ResolvedConceptAtomType).conceptTypes.length === 1;
        }
        else {
            return false;
        }
    }

    isUniqueCallTargetType(): boolean {
        if (this.options.length !== 1) {
            return false;
        }

        return this.options[0] instanceof ResolvedEntityAtomType;
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
}

export { ResolvedAtomType, ResolvedConceptAtomTypeEntry, ResolvedConceptAtomType, ResolvedEntityAtomType, ResolvedTupleAtomTypeEntry, ResolvedTupleAtomType, ResolvedRecordAtomTypeEntry, ResolvedRecordAtomType, ResolvedFunctionAtomTypeParam, ResolvedFunctionAtomType, ResolvedType };
