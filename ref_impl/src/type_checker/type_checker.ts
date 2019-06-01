//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ResolvedType, ResolvedTupleAtomType, ResolvedEntityAtomType, ResolvedTupleAtomTypeEntry, ResolvedRecordAtomType, ResolvedRecordAtomTypeEntry, ResolvedAtomType, ResolvedConceptAtomType, ResolvedFunctionAtomType, ResolvedConceptAtomTypeEntry } from "../ast/resolved_type";
import { Assembly, NamespaceConstDecl, OOPTypeDecl, StaticMemberDecl, EntityTypeDecl, StaticFunctionDecl, InvokeDecl, MemberFieldDecl, NamespaceFunctionDecl, TemplateTermDecl, OOMemberLookupInfo, MemberMethodDecl, ConceptTypeDecl } from "../ast/assembly";
import { TypeEnvironment, ExpressionReturnResult, VarInfo, FlowTypeTruthValue } from "./type_environment";
import { TypeSignature, TemplateTypeSignature, NominalTypeSignature, AutoTypeSignature } from "../ast/type_signature";
import { Expression, ExpressionTag, LiteralTypedStringExpression, LiteralTypedStringConstructorExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, NamedArgument, ConstructorPrimaryExpression, ConstructorPrimaryWithFactoryExpression, ConstructorTupleExpression, ConstructorRecordExpression, Arguments, PositionalArgument, ConstructorLambdaExpression, CallNamespaceFunctionExpression, CallStaticFunctionExpression, PostfixOp, PostfixOpTag, PostfixAccessFromIndex, PostfixProjectFromIndecies, PostfixAccessFromName, PostfixProjectFromNames, PostfixInvoke, PostfixProjectFromType, PostfixModifyWithIndecies, PostfixModifyWithNames, PostfixStructuredExtend, PostfixCallLambda, PrefixOp, BinOpExpression, BinEqExpression, BinCmpExpression, LiteralNoneExpression, BinLogicExpression, NonecheckExpression, CoalesceExpression, SelectExpression, VariableDeclarationStatement, VariableAssignmentStatement, IfElseStatement, Statement, StatementTag, BlockStatement, ReturnStatement, LiteralBoolExpression, LiteralIntegerExpression, LiteralStringExpression, BodyImplementation, AssertStatement, CheckStatement, DebugStatement, StructuredVariableAssignmentStatement, StructuredAssignment, RecordStructuredAssignment, IgnoreTermStructuredAssignment, ConstValueStructuredAssignment, VariableDeclarationStructuredAssignment, VariableAssignmentStructuredAssignment, TupleStructuredAssignment, MatchStatement, MatchGuard, WildcardMatchGuard, TypeMatchGuard, StructureMatchGuard, AbortStatement, YieldStatement, IfExpression, MatchExpression, BlockStatementExpression } from "../ast/body";
import { MIREmitter, MIRKeyGenerator } from "../compiler/mir_emitter";
import { MIRTempRegister, MIRArgument, MIRConstantNone, MIRBody, MIRTypeKey, MIRFunctionKey, MIRLambdaKey, MIRStaticKey, MIRMethodKey, MIRVirtualMethodKey, MIRGlobalKey, MIRConstKey, MIRRegisterArgument, MIRVarLocal, MIRVarParameter, MIRVarCaptured } from "../compiler/mir_ops";
import { SourceInfo } from "../ast/parser";
import { MIREntityTypeDecl, MIRConceptTypeDecl, MIRFieldDecl, MIRFunctionDecl, MIRInvokeDecl, MIRFunctionParameter, MIRType, MIREntityType, MIRStaticDecl, MIRGlobalDecl, MIRConstDecl, MIRMethodDecl, MIROOTypeDecl } from "../compiler/mir_assembly";

class TypeError extends Error {
    readonly file: string;
    readonly line: number;

    constructor(file: string, line: number, message?: string) {
        super(`Type error on ${line} -- ${message}`);
        Object.setPrototypeOf(this, new.target.prototype);

        this.file = file;
        this.line = line;
    }
}

type ExpandedArgument = {
    name: string | undefined,
    argtype: ResolvedType,
    expando: boolean,
    treg: MIRTempRegister
};

class TypeChecker {
    private readonly m_assembly: Assembly;

    private m_file: string;
    private m_errors: [string, number, string][];

    private m_emitEnabled: boolean;
    private readonly m_emitter: MIREmitter;

    private readonly AnyMethods = ["is", "as", "tryAs", "defaultAs", "isNone", "isSome"];
    private readonly AnySplitMethods = ["is", "isSome", "isNone"];

    constructor(assembly: Assembly, emitEnabled: boolean, emitter: MIREmitter) {
        this.m_assembly = assembly;

        this.m_file = "[No File]";
        this.m_errors = [];

        this.m_emitEnabled = emitEnabled;
        this.m_emitter = emitter;
    }

    private raiseError(sinfo: SourceInfo, msg?: string) {
        this.m_emitEnabled = false;

        this.m_errors.push([this.m_file, sinfo.line, msg || "Type error"]);
        throw new TypeError(this.m_file, sinfo.line, msg || "Type error");
    }

    private raiseErrorIf(sinfo: SourceInfo, cond: boolean, msg?: string) {
        if (cond) {
            this.raiseError(sinfo, msg);
        }
    }

    getErrorList(): [string, number, string][] {
        return this.m_errors;
    }

    private resolveAndEnsureType(sinfo: SourceInfo, ttype: TypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const rtype = this.m_assembly.normalizeType(ttype, binds);
        this.raiseErrorIf(sinfo, rtype.isEmptyType(), "Bad type signature");

        //
        //TODO: if this is a record then we should make sure the property names don't shadow a method on Any -- also for field names in OO decls
        //

        return rtype;
    }

    private checkBadRecordNames(sinfo: SourceInfo, rentries: ResolvedRecordAtomTypeEntry[]) {
        const isBad = rentries.some((entry) => this.AnyMethods.indexOf(entry.name) !== -1);
        this.raiseErrorIf(sinfo, isBad, "Cannot mask methods in NSCore::Any with record property names");
    }

    private checkTemplateTypes(sinfo: SourceInfo, terms: TemplateTermDecl[], binds: Map<string, ResolvedType>, optTypeRestrict?: [string, ResolvedType][]) {
        const boundsok = terms.every((t) => this.m_assembly.subtypeOf(binds.get(t.name) as ResolvedType, this.resolveAndEnsureType(sinfo, t.ttype, new Map<string, ResolvedType>())));
        const uniqok = terms.every((t) => !t.isUnique || (binds.get(t.name) as ResolvedType).isUniqueTemplateInstantiationType());
        this.raiseErrorIf(sinfo, !boundsok || !uniqok, "Template instantiation does not satisfy specified bounds");

        if (optTypeRestrict !== undefined) {
            const restrictok = optTypeRestrict.every((r) => this.m_assembly.subtypeOf(binds.get(r[0]) as ResolvedType, r[1]));
            this.raiseErrorIf(sinfo, !restrictok, "Violates type restriction in instantiation");
        }
    }

    private checkInvokeDecl(sinfo: SourceInfo, invoke: InvokeDecl, invokeBinds: Map<string, ResolvedType>) {
        this.raiseErrorIf(sinfo, invoke.optRestType !== undefined && invoke.params.some((param) => param.isOptional), "Cannot have optional and rest parameters in an invocation signature");

        const allNames = new Set<string>();
        if (invoke.optRestName !== undefined && invoke.optRestName !== "_") {
            allNames.add(invoke.optRestName);
        }
        for (let i = 0; i < invoke.params.length; ++i) {
            if (invoke.params[i].name !== "_") {
                this.raiseErrorIf(sinfo, allNames.has(invoke.params[i].name), `Duplicate name in invocation signature paramaters "${invoke.params[i].name}"`);
                allNames.add(invoke.params[i].name);
            }
            this.resolveAndEnsureType(sinfo, invoke.params[i].type, invokeBinds);
        }

        const firstOptIndex = invoke.params.findIndex((param) => param.isOptional);
        if (firstOptIndex === -1) {
            return;
        }

        for (let i = firstOptIndex; i < invoke.params.length; ++i) {
            this.raiseErrorIf(sinfo, !invoke.params[i].isOptional, "Cannot have required paramaters following optional parameters");
        }

        if (invoke.optRestType !== undefined) {
            this.resolveAndEnsureType(sinfo, invoke.optRestType, invokeBinds);
        }
        this.resolveAndEnsureType(sinfo, invoke.resultType, invokeBinds);
    }

    private checkValueEq(lhs: ResolvedType, rhs: ResolvedType): boolean {
        return lhs.options.some((lhsopt) => {
            const lhst = ResolvedType.createSingle(lhsopt);
            return rhs.options.some((rhsopt) => {
                const rhst = ResolvedType.createSingle(rhsopt);
                return this.checkValueEq_Single(lhst, rhst);
            });
        });
    }

    private checkValueEq_Single(lhs: ResolvedType, rhs: ResolvedType): boolean {
        if (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialNoneType()) || this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialNoneType())) {
            return true;
        }

        const bothBool = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialBoolType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialBoolType()));
        const bothInt = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialIntType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialIntType()));
        const bothString = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialStringType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialStringType()));
        const bothGUID = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialGUIDType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialGUIDType()));

        if (bothBool || bothInt || bothString || bothGUID) {
            return true;
        }

        const bothEnum = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialEnumType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialEnumType()));
        const bothCustomKey = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialCustomKeyType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialCustomKeyType()));

        if (bothEnum || bothCustomKey) {
            return this.m_assembly.subtypeOf(lhs, rhs) && this.m_assembly.subtypeOf(rhs, lhs); //types are equal
        }

        const bothTuple = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialTupleConceptType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialTupleConceptType()));
        if (bothTuple) {
            const tup1 = this.m_assembly.normalizeToTupleRepresentation(lhs.options[0]);
            const tup2 = this.m_assembly.normalizeToTupleRepresentation(rhs.options[0]);

            for (let i = 0; i < Math.max(tup1.types.length, tup2.types.length); ++i) {
                const t1 = (i < tup1.types.length) ? tup1.types[i] : undefined;
                const t2 = (i < tup2.types.length) ? tup2.types[i] : undefined;

                if (t1 !== undefined && !t1.isOptional && t2 !== undefined && !t2.isOptional) {
                    if (!this.checkValueEq(t1.type, t2.type)) {
                        return false;
                    }
                }
                else {
                    if (t1 !== undefined && t2 === undefined) {
                        if (!t1.isOptional && !tup2.isOpen) {
                            return false;
                        }
                    }

                    if (t1 === undefined && t2 !== undefined) {
                        if (!tup1.isOpen && !t2.isOptional) {
                            return false;
                        }
                    }
                }
            }

            return true;
        }

        const bothRecord = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialRecordConceptType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialRecordConceptType()));
        if (bothRecord) {
            const rec1 = this.m_assembly.normalizeToRecordRepresentation(lhs.options[0]);
            const rec2 = this.m_assembly.normalizeToRecordRepresentation(rhs.options[0]);

            let allprops = new Set<string>();
            rec1.entries.forEach((e) => allprops.add(e.name));
            rec2.entries.forEach((e) => allprops.add(e.name));

            let pl: string[] = [];
            allprops.forEach((se) => pl.push(se));

            for (let i = 0; i < pl.length; ++i) {
                const t1 = rec1.entries.find((v) => v.name === pl[i]);
                const t2 = rec2.entries.find((v) => v.name === pl[i]);

                if (t1 !== undefined && !t1.isOptional && t2 !== undefined && !t2.isOptional) {
                    if (!this.checkValueEq(t1.type, t2.type)) {
                        return false;
                    }
                }
                else {
                    if (t1 !== undefined && t2 === undefined) {
                        if (!t1.isOptional && !rec2.isOpen) {
                            return false;
                        }
                    }

                    if (t1 === undefined && t2 !== undefined) {
                        if (!rec1.isOpen && !t2.isOptional) {
                            return false;
                        }
                    }
                }
            }

            return true;
        }

        return false;
    }

    private checkValueLess(lhs: ResolvedType, rhs: ResolvedType): boolean {
        const bothInt = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialIntType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialIntType()));
        const bothString = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialStringType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialStringType()));

        return (bothInt || bothString);
    }

    private getInfoForLoadFromIndex(rtype: ResolvedType, idx: number): ResolvedType {
        const options = rtype.options.map((atom) => {
            const tatom = this.m_assembly.normalizeToTupleRepresentation(atom);
            if (idx < tatom.types.length) {
                if (!tatom.types[idx].isOptional) {
                    return tatom.types[idx].type;
                }
                else {
                    return this.m_assembly.typeUnion([tatom.types[idx].type, this.m_assembly.getSpecialNoneType()]);
                }
            }
            else if (tatom.isOpen) {
                return this.m_assembly.getSpecialAnyType();
            }
            else {
                return this.m_assembly.getSpecialNoneType();
            }
        });

        return this.m_assembly.typeUnion(options);
    }

    private getInfoForLoadFromPropertyName(rtype: ResolvedType, pname: string): ResolvedType {
        const options = rtype.options.map((atom) => {
            const ratom = this.m_assembly.normalizeToRecordRepresentation(atom);
            const tidx = ratom.entries.findIndex((re) => re.name === pname);
            if (tidx !== -1) {
                if (!ratom.entries[tidx].isOptional) {
                    return ratom.entries[tidx].type;
                }
                else {
                    return this.m_assembly.typeUnion([ratom.entries[tidx].type, this.m_assembly.getSpecialNoneType()]);
                }
            }
            else if (ratom.isOpen) {
                return this.m_assembly.getSpecialAnyType();
            }
            else {
                return this.m_assembly.getSpecialNoneType();
            }
        });

        return this.m_assembly.typeUnion(options);
    }

    private projectTupleAtom(sinfo: SourceInfo, opt: ResolvedAtomType, ptype: ResolvedTupleAtomType): ResolvedType {
        const tuple = this.m_assembly.normalizeToTupleRepresentation(opt);

        let tentries: ResolvedTupleAtomTypeEntry[] = [];
        for (let i = 0; i < ptype.types.length; ++i) {
            if (!ptype.types[i].isOptional) {
                this.raiseErrorIf(sinfo, i >= tuple.types.length || tuple.types[i].isOptional, "Type mismatch in projection");
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(tuple.types[i].type, ptype.types[i].type), "Type mismatch in projection");

                tentries.push(new ResolvedTupleAtomTypeEntry(tuple.types[i].type, false));
            }
            else {
                if (i < tuple.types.length) {
                    this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(tuple.types[i].type, ptype.types[i].type), "Type mismatch in projection");
                    tentries.push(new ResolvedTupleAtomTypeEntry(tuple.types[i].type, tuple.types[i].isOptional));
                }
                else {
                    if (tuple.isOpen) {
                        tentries.push(new ResolvedTupleAtomTypeEntry(this.m_assembly.getSpecialAnyType(), true));
                    }
                }
            }
        }

        if (ptype.isOpen) {
            for (let i = ptype.types.length; i < tuple.types.length; ++i) {
                tentries.push(tuple.types[i]);
            }
        }

        return ResolvedType.createSingle(ResolvedTupleAtomType.create(ptype.isOpen && tuple.isOpen, tentries));
    }

    private projectRecordAtom(sinfo: SourceInfo, opt: ResolvedAtomType, ptype: ResolvedRecordAtomType): ResolvedType {
        const record = this.m_assembly.normalizeToRecordRepresentation(opt);

        let rentries: ResolvedRecordAtomTypeEntry[] = [];
        for (let i = 0; i < ptype.entries.length; ++i) {
            const riter = record.entries.find((v) => v.name === ptype.entries[i].name);
            if (!ptype.entries[i].isOptional) {
                this.raiseErrorIf(sinfo, riter === undefined || riter.isOptional, "Type mismatch in projection");
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf((riter as ResolvedRecordAtomTypeEntry).type, ptype.entries[i].type), "Type mismatch in projection");

                rentries.push(new ResolvedRecordAtomTypeEntry(ptype.entries[i].name, (riter as ResolvedRecordAtomTypeEntry).type, false));
            }
            else {
                if (riter !== undefined) {
                    this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(riter.type, ptype.entries[i].type), "Type mismatch in projection");
                    rentries.push(new ResolvedRecordAtomTypeEntry(ptype.entries[i].name, riter.type, riter.isOptional));
                }
                else {
                    if (record.isOpen) {
                        rentries.push(new ResolvedRecordAtomTypeEntry(ptype.entries[i].name, this.m_assembly.getSpecialAnyType(), true));
                    }
                }
            }
        }

        if (ptype.isOpen) {
            for (let i = 0; i < record.entries.length; ++i) {
                const idx = ptype.entries.findIndex((e) => e.name === record.entries[i].name);
                if (idx === -1) {
                    rentries.push(record.entries[i]);
                }
            }
        }

        this.checkBadRecordNames(sinfo, rentries);
        return ResolvedType.createSingle(ResolvedRecordAtomType.create(ptype.isOpen && record.isOpen, rentries));
    }

    private projectOOTypeAtom(sinfo: SourceInfo, opt: ResolvedType, ptype: ResolvedConceptAtomType): ResolvedType[] {
        let fields = new Set<string>();
        ptype.conceptTypes.forEach((concept) => {
            const fmap = this.m_assembly.getAllOOFields(concept.concept, concept.binds);
            fmap.forEach((v, k) => fields.add(k));
        });

        let farray: string[] = [];
        fields.forEach((f) => farray.push(f));
        farray.sort();

        farray.forEach((f) => {
            const finfo = this.m_assembly.tryGetOOMemberDeclOptions(opt, "field", f);
            this.raiseErrorIf(sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");
        });

        const rentries = opt.options.map((atom) => {
            const oentries = farray.map((f) => {
                const finfo = this.m_assembly.tryGetOOMemberDeclUnique(ResolvedType.createSingle(atom), "field", f) as OOMemberLookupInfo;
                const ftype = this.resolveAndEnsureType(sinfo, (finfo.decl as MemberFieldDecl).declaredType, finfo.binds);
                return new ResolvedRecordAtomTypeEntry(f, ftype, false);
            });

            this.checkBadRecordNames(sinfo, oentries);
            return ResolvedType.createSingle(ResolvedRecordAtomType.create(false, oentries));
        });

        return rentries;
    }

    private updateTupleIndeciesAtom(sinfo: SourceInfo, t: ResolvedAtomType, updates: [number, ResolvedType][]): ResolvedType {
        const tuple = this.m_assembly.normalizeToTupleRepresentation(t);

        let tentries: ResolvedTupleAtomTypeEntry[] = [];
        for (let i = 0; i < updates.length; ++i) {
            const update = updates[i];
            this.raiseErrorIf(sinfo, update[0] < 0, "Update index is out of tuple bounds");

            if (update[0] > tentries.length) {
                const extendCount = (update[0] - tentries.length) + 1;
                for (let j = 0; j < extendCount; ++j) {
                    if (tentries.length + j < tuple.types.length) {
                        if (!tuple.types[i].isOptional) {
                            tentries.push(new ResolvedTupleAtomTypeEntry(tuple.types[j].type, false));
                        }
                        else {
                            tentries.push(new ResolvedTupleAtomTypeEntry(this.m_assembly.typeUnion([tuple.types[j].type, this.m_assembly.getSpecialNoneType()]), false));
                        }
                    }
                    else {
                        tentries.push(new ResolvedTupleAtomTypeEntry(tuple.isOpen ? this.m_assembly.getSpecialAnyType() : this.m_assembly.getSpecialNoneType(), false));
                    }
                }
            }
            tentries[update[0]] = new ResolvedTupleAtomTypeEntry(update[1], false);
        }

        return ResolvedType.createSingle(ResolvedTupleAtomType.create(tuple.isOpen, tentries));
    }

    private updateNamedPropertiesAtom(sinfo: SourceInfo, t: ResolvedAtomType, updates: [string, ResolvedType][]): ResolvedType {
        const record = this.m_assembly.normalizeToRecordRepresentation(t);

        let rentries: ResolvedRecordAtomTypeEntry[] = [...record.entries];
        for (let i = 0; i < updates.length; ++i) {
            const update = updates[i];
            const idx = rentries.findIndex((e) => e.name === update[0]);
            rentries[idx !== -1 ? idx : rentries.length] = new ResolvedRecordAtomTypeEntry(update[0], update[1], false);
        }

        this.checkBadRecordNames(sinfo, rentries);
        return ResolvedType.createSingle(ResolvedRecordAtomType.create(record.isOpen, rentries));
    }

    private updateNamedFieldsAtom(sinfo: SourceInfo, t: ResolvedType, updates: [string, ResolvedType][]) {
        updates.forEach((update) => {
            const finfo = this.m_assembly.tryGetOOMemberDeclOptions(t, "field", update[0]);
            this.raiseErrorIf(sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");
        });
    }

    private appendIntoTupleAtom(t: ResolvedTupleAtomType, merge: ResolvedAtomType): ResolvedType {
        const tuple = this.m_assembly.normalizeToTupleRepresentation(merge);

        let tentries: ResolvedTupleAtomTypeEntry[] = [];
        let isOpen = false;
        if (t.isOpen || tuple.isOpen) {
            //TODO: This is not the most precise transformer but for now we go with it
            isOpen = true;
        }
        else if (t.types.length === 0 || tuple.types.length === 0) {
            tentries = t.types.length !== 0 ? [...t.types] : [...tuple.types];
        }
        else if (t.types.some((entry) => entry.isOptional)) {
            tentries = t.types.slice(0, t.types.findIndex((entry) => entry.isOptional));
            isOpen = true;
        }
        else {
            //not open and no optional entries so just copy everything along
            tentries = [...t.types, ...tuple.types];
            isOpen = tuple.isOpen;
        }

        return ResolvedType.createSingle(ResolvedTupleAtomType.create(isOpen, tentries));
    }

    private mergeIntoRecordAtom(sinfo: SourceInfo, t: ResolvedRecordAtomType, merge: ResolvedAtomType): ResolvedType {
        const record = this.m_assembly.normalizeToRecordRepresentation(merge);

        let rentries: ResolvedRecordAtomTypeEntry[] = [];
        let isOpen = false;
        if (t.isOpen || record.isOpen) {
            isOpen = true;
        }
        else {
            rentries = [...t.entries];

            for (let i = 0; i < record.entries.length; ++i) {
                const update = record.entries[i];
                const fidx = rentries.findIndex((e) => e.name === update.name);
                const idx = fidx !== -1 ? fidx : rentries.length;

                if (!update.isOptional) {
                    rentries[idx] = new ResolvedRecordAtomTypeEntry(update.name, update.type, false);
                }
                else {
                    if (idx === rentries.length) {
                        rentries[idx] = update;
                    }
                    else {
                        rentries[idx] = new ResolvedRecordAtomTypeEntry(update.name, this.m_assembly.typeUnion([update.type, rentries[idx].type]), true);
                    }
                }
            }
        }

        this.checkBadRecordNames(sinfo, rentries);
        return ResolvedType.createSingle(ResolvedRecordAtomType.create(isOpen, rentries));
    }

    private mergeIntoEntityConceptAtom(sinfo: SourceInfo, t: ResolvedType, merge: ResolvedAtomType) {
        const record = this.m_assembly.normalizeToRecordRepresentation(merge);
        this.raiseErrorIf(sinfo, record.isOpen, "Cannot update a Concept/Entity with a open record of values");

        record.entries.forEach((entry) => {
            const finfo = this.m_assembly.tryGetOOMemberDeclOptions(t, "field", entry.name);
            this.raiseErrorIf(sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");
        });
    }

    private checkTypeOkForTupleExpando(rtype: ResolvedType): [boolean, number, number] {
        const tslist = rtype.options.map((opt) => this.m_assembly.ensureTupleStructuralRepresentation(opt));
        const reqlen = tslist.reduce((acc, v) => Math.min(acc, v.types.filter((te) => !te.isOptional).length), Number.MAX_SAFE_INTEGER);
        const tlen = tslist.reduce((acc, v) => Math.max(acc, v.types.length), 0);

        const ok = tslist.every((topt) => !topt.isOpen);

        return [ok, reqlen, tlen];
    }

    private checkTypeOkForRecordExpando(rtype: ResolvedType): [boolean, Set<string>, Set<string>] {
        const rslist = rtype.options.map((opt) => this.m_assembly.ensureRecordStructuralRepresentation(opt));

        let allNames = new Set<string>();
        rslist.forEach((opt) => {
            opt.entries.forEach((re) => {
                allNames.add(re.name);
            });
        });

        let reqNames = new Set<string>(allNames);
        rslist.forEach((opt) => {
            opt.entries.forEach((re) => {
                if (re.isOptional) {
                    allNames.delete(re.name);
                }
            });
        });

        const ok = rslist.every((opt) => !opt.isOpen);

        return [ok, reqNames, allNames];
    }

    private checkArgumentsEvaluationWSig(env: TypeEnvironment, sig: ResolvedFunctionAtomType, args: Arguments, optSelfValue: [ResolvedType, MIRTempRegister] | undefined, skipEmit?: boolean): ExpandedArgument[] {
        let eargs: ExpandedArgument[] = [];

        const emitRestore = this.m_emitEnabled;
        if (skipEmit) {
            this.m_emitEnabled = false;
        }

        if (optSelfValue !== undefined) {
            eargs.push({ name: "this", argtype: optSelfValue[0], expando: false, treg: optSelfValue[1] });
        }

        const skipthisidx = optSelfValue !== undefined ? 1 : 0;
        const noExpando = args.argList.every((arg) => !(arg instanceof PositionalArgument) || !arg.isSpread);
        const firstNameIdx = sig.params.findIndex((p) => args.argList.some((arg) => arg instanceof NamedArgument && arg.name !== "_" && arg.name === p.name));

        for (let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i];
            const oftype = (noExpando && (firstNameIdx === -1 || i < firstNameIdx) && i < sig.params.length && !sig.params[i].isOptional) ? sig.params[i + skipthisidx].type : this.m_assembly.getSpecialAnyType();
            const treg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const earg = this.checkExpression(env, arg.value, treg, oftype).getExpressionResult().etype;

            if (arg instanceof NamedArgument) {
                eargs.push({ name: arg.name, argtype: earg, expando: false, treg: treg });
            }
            else {
                eargs.push({ name: undefined, argtype: earg, expando: (arg as PositionalArgument).isSpread, treg: treg });
            }
        }

        if (skipEmit) {
            this.m_emitEnabled = emitRestore && true;
        }

        return eargs;
    }

    private checkArgumentsEvaluationNoSig(env: TypeEnvironment, args: Arguments): ExpandedArgument[] {
        let eargs: ExpandedArgument[] = [];

        for (let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i];
            const treg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const earg = this.checkExpression(env, arg.value, treg).getExpressionResult().etype;

            if (arg instanceof NamedArgument) {
                eargs.push({ name: arg.name, argtype: earg, expando: false, treg: treg });
            }
            else {
                eargs.push({ name: undefined, argtype: earg, expando: (arg as PositionalArgument).isSpread, treg: treg });
            }
        }

        return eargs;
    }

    private checkArgumentsTupleConstructor(sinfo: SourceInfo, env: TypeEnvironment, args: ExpandedArgument[], trgt: MIRTempRegister): ResolvedType {
        let targs: ResolvedType[] = [];

        for (let i = 0; i < args.length; ++i) {
            this.raiseErrorIf(sinfo, args[i].expando, "Expando parameters are not allowed in Tuple constructor");
            this.raiseErrorIf(sinfo, args[i].name !== undefined, "Named parameters are not allowed in Tuple constructor");

            targs.push(args[i].argtype);
        }

        if (this.m_emitEnabled) {
            const regs = args.map((e) => e.treg);
            this.m_emitter.bodyEmitter.emitConstructorTuple(sinfo, regs, trgt);
        }

        const tupleatom = ResolvedTupleAtomType.create(false, targs.map((targ) => new ResolvedTupleAtomTypeEntry(targ, false)));
        return ResolvedType.createSingle(tupleatom);
    }

    private checkArgumentsRecordConstructor(sinfo: SourceInfo, env: TypeEnvironment, args: ExpandedArgument[], trgt: MIRTempRegister): ResolvedType {
        let rargs: [string, ResolvedType][] = [];

        const seenNames = new Set<string>();
        for (let i = 0; i < args.length; ++i) {
            this.raiseErrorIf(sinfo, args[i].expando, "Expando parameters are not allowed in Record constructor");
            this.raiseErrorIf(sinfo, args[i].name === undefined, "Positional parameters are not allowed in Record constructor");

            this.raiseErrorIf(sinfo, seenNames.has(args[i].name as string), "Duplicate argument name in Record constructor");

            rargs.push([args[i].name as string, args[i].argtype]);
        }

        if (this.m_emitEnabled) {
            const regs = args.map<[string, MIRTempRegister]>((e) => [e.name as string, e.treg]).sort((a, b) => a[0].localeCompare(b[0]));
            this.m_emitter.bodyEmitter.emitConstructorRecord(sinfo, regs, trgt);
        }

        const rentries = rargs.map((targ) => new ResolvedRecordAtomTypeEntry(targ[0], targ[1], false));
        this.checkBadRecordNames(sinfo, rentries);
        const recordatom = ResolvedRecordAtomType.create(false, rentries);
        return ResolvedType.createSingle(recordatom);
    }

    private checkArgumentsCollectionConstructor(sinfo: SourceInfo, env: TypeEnvironment, oftype: ResolvedEntityAtomType, ctype: ResolvedType, args: ExpandedArgument[], trgt: MIRTempRegister): ResolvedType {
        for (let i = 0; i < args.length; ++i) {
            this.raiseErrorIf(sinfo, args[i].name !== undefined, "Named parameters are not allowed in Collection constructors");

            const arg = args[i];
            if (!arg.expando) {
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(arg.argtype, ctype));
            }
            else {
                arg.argtype.options.forEach((opt) => {
                    this.raiseErrorIf(sinfo, !(opt instanceof ResolvedEntityAtomType) || !((opt as ResolvedEntityAtomType).object.isTypeACollectionEntity() || (opt as ResolvedEntityAtomType).object.isTypeAMapEntity()), "Can only expand other container types in container constructor");
                    const oatom = opt as ResolvedEntityAtomType;

                    if (oatom.object.isTypeACollectionEntity()) {
                        const ttype = oatom.binds.get("T") as ResolvedType;
                        this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(ttype, ctype), "Container contents not of suitable subtype");
                    }
                    else {
                        const ktype = oatom.binds.get("K") as ResolvedType;
                        const vtype = oatom.binds.get("V") as ResolvedType;
                        const tupleType = ResolvedType.createSingle(ResolvedTupleAtomType.create(false, [new ResolvedTupleAtomTypeEntry(ktype, false), new ResolvedTupleAtomTypeEntry(vtype, false)]));
                        this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(tupleType, ctype), "Container contents not of suitable subtype");
                    }
                });
            }
        }

        if (this.m_emitEnabled) {
            this.m_emitter.registerTypeInstantiation(oftype.object, oftype.binds);
            const tkey = MIRKeyGenerator.generateTypeKey(oftype.object, oftype.binds);

            if (args.length === 0) {
                this.m_emitter.bodyEmitter.emitConstructorPrimaryCollectionEmpty(sinfo, tkey, trgt);
            }
            else {
                if (args.every((v) => !v.expando)) {
                    this.m_emitter.bodyEmitter.emitConstructorPrimaryCollectionSingletons(sinfo, tkey, args.map((arg) => arg.treg), trgt);
                }
                else if (args.every((v) => v.expando)) {
                    this.m_emitter.bodyEmitter.emitConstructorPrimaryCollectionCopies(sinfo, tkey, args.map((arg) => arg.treg), trgt);
                }
                else {
                    this.m_emitter.bodyEmitter.emitConstructorPrimaryCollectionMixed(sinfo, tkey, args.map<[boolean, MIRArgument]>((arg) => [arg.expando, arg.treg]), trgt);
                }
            }
        }

        return ResolvedType.createSingle(oftype);
    }

    private checkArgumentsConstructor(sinfo: SourceInfo, env: TypeEnvironment, oftype: ResolvedEntityAtomType, args: ExpandedArgument[], trgt: MIRTempRegister): ResolvedType {
        const fieldInfo = this.m_assembly.getAllOOFields(oftype.object, oftype.binds);
        let fields: string[] = [];
        fieldInfo.forEach((v, k) => {
            fields.push(k);
        });
        fields = fields.sort();

        let filledLocations: { vtype: ResolvedType, mustDef: boolean, trgt: MIRArgument }[] = [];

        //figure out named parameter mapping first
        for (let i = 0; i < args.length; ++i) {
            const arg = args[i];
            if (arg.name !== undefined) {
                const fidx = fields.indexOf(arg.name);
                this.raiseErrorIf(sinfo, fidx === -1, `Entity ${oftype.idStr} does not have field named "${arg.name}"`);
                this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${arg.name}"`);

                filledLocations[fidx] = { vtype: arg.argtype, mustDef: true, trgt: arg.treg };
            }
            else if (arg.expando && this.m_assembly.subtypeOf(arg.argtype, this.m_assembly.getSpecialRecordConceptType())) {
                const expandInfo = this.checkTypeOkForRecordExpando(arg.argtype);
                this.raiseErrorIf(sinfo, !expandInfo[0], `Type cannot be expanded as part of Entity constructor ${arg.argtype.idStr}`);

                expandInfo[2].forEach((pname) => {
                    const fidx = fields.indexOf(pname);
                    this.raiseErrorIf(sinfo, fidx === -1, `Entity ${oftype.idStr} does not have field named "${pname}"`);
                    this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${pname}"`);

                    this.raiseErrorIf(sinfo, (fieldInfo.get(pname) as [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>])[1].value !== undefined && !expandInfo[1].has(pname), `Constructor requires "${pname}" but it is provided as an optional argument`);

                    const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                    if (this.m_emitEnabled) {
                        this.m_emitter.bodyEmitter.emitLoadProperty(sinfo, arg.treg, pname, etreg);
                    }

                    filledLocations[fidx] = { vtype: this.getInfoForLoadFromPropertyName(arg.argtype, pname), mustDef: expandInfo[1].has(pname), trgt: etreg };
                });
            }
            else {
                //nop
            }
        }

        //go through names and fill out info for any that should use the default value -- raise error if any are missing
        for (let i = 0; i < fields.length; ++i) {
            const field = (fieldInfo.get(fields[i]) as [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]);
            const fieldtype = this.resolveAndEnsureType(sinfo, field[1].declaredType, field[2]);

            if (filledLocations[i] === undefined) {
                this.raiseErrorIf(sinfo, field[1].value === undefined, `Field "${fields[i]}" is required and must be assigned a value in constructor`);

                const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                if (this.m_emitEnabled) {
                    this.m_emitter.bodyEmitter.emitLoadMemberFieldDefaultValue(sinfo, MIRKeyGenerator.generateFieldKey(field[0], field[2], field[1].name), etreg);
                }

                filledLocations[i] = { vtype: fieldtype, mustDef: true, trgt: etreg };
            }

            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(filledLocations[i].vtype, fieldtype), `Field "${fields[i]}" expected argument of type ${fieldtype.idStr} but got ${filledLocations[i].vtype.idStr}`);
        }

        if (this.m_emitEnabled) {
            this.m_emitter.registerTypeInstantiation(oftype.object, oftype.binds);
            const tkey = MIRKeyGenerator.generateTypeKey(oftype.object, oftype.binds);

            this.m_emitter.bodyEmitter.emitConstructorPrimary(sinfo, tkey, filledLocations.map((fl) => fl.trgt), trgt);
        }

        return ResolvedType.createSingle(oftype);
    }

    private checkArgumentsSignature(sinfo: SourceInfo, env: TypeEnvironment, sig: ResolvedFunctionAtomType, args: ExpandedArgument[], skipEmit?: boolean): MIRArgument[] {
        let filledLocations: { vtype: ResolvedType, mustDef: boolean, trgt: MIRArgument }[] = [];

        const emitRestore = this.m_emitEnabled;
        if (skipEmit) {
            this.m_emitEnabled = false;
        }

        //figure out named parameter mapping first
        for (let j = 0; j < args.length; ++j) {
            const arg = args[j];
            if (arg.name !== undefined) {
                const fidx = sig.params.findIndex((param) => param.name === arg.name);
                this.raiseErrorIf(sinfo, fidx === -1, `Call does not have parameter named "${arg.name}"`);
                this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name ${arg.name}`);

                filledLocations[fidx] = { vtype: arg.argtype, mustDef: true, trgt: arg.treg };
            }
            else if (arg.expando && this.m_assembly.subtypeOf(arg.argtype, this.m_assembly.getSpecialRecordConceptType())) {
                const expandInfo = this.checkTypeOkForRecordExpando(arg.argtype);
                this.raiseErrorIf(sinfo, !expandInfo[0], "Type cannot be expanded as part of call");

                expandInfo[2].forEach((pname) => {
                    const fidx = sig.params.findIndex((param) => param.name === arg.name);
                    this.raiseErrorIf(sinfo, fidx === -1, `Call does not have parameter named "${arg.name}"`);
                    this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${arg.name}"`);

                    this.raiseErrorIf(sinfo, !sig.params[fidx].isOptional && !expandInfo[1].has(pname), `Call requires "${pname}" but it is provided as an optional argument`);

                    const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                    if (this.m_emitEnabled) {
                        this.m_emitter.bodyEmitter.emitLoadProperty(sinfo, arg.treg, pname, etreg);
                    }

                    filledLocations[fidx] = { vtype: this.getInfoForLoadFromPropertyName(arg.argtype, pname), mustDef: expandInfo[1].has(pname), trgt: etreg };
                });
            }
            else {
                //nop
            }
        }

        //now fill in positional parameters
        let apos = args.findIndex((ae) => ae.name === undefined && !(ae.expando && this.m_assembly.subtypeOf(ae.argtype, this.m_assembly.getSpecialRecordConceptType())));
        if (apos === -1) {
            apos = args.length;
        }

        let ii = 0;
        while (ii < sig.params.length && apos < args.length) {
            if (filledLocations[ii] !== undefined) {
                this.raiseErrorIf(sinfo, !filledLocations[ii].mustDef, `We have an potentially ambigious binding of an optional parameter "${sig.params[ii].name}"`);
                ++ii;
                continue;
            }

            const arg = args[apos];
            if (!arg.expando) {
                filledLocations[ii] = { vtype: arg.argtype, mustDef: true, trgt: arg.treg };
                ++ii;
            }
            else {
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(arg.argtype, this.m_assembly.getSpecialTupleConceptType()), "Only Tuple types can be expanded as positional arguments");

                const expandInfo = this.checkTypeOkForTupleExpando(arg.argtype);
                this.raiseErrorIf(sinfo, !expandInfo[0], "Type cannot be expanded as part of call");

                for (let ectr = 0; ectr < expandInfo[2]; ++ectr) {
                    this.raiseErrorIf(sinfo, ii >= sig.params.length, "Too many arguments as part of tuple expando and/or cannot split tuple expando (between arguments and rest)");
                    this.raiseErrorIf(sinfo, !sig.params[ii].isOptional && ectr >= expandInfo[1], `Call requires "${sig.params[ii].name}" but it is provided as an optional argument as part of tuple expando`);

                    const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                    if (this.m_emitEnabled) {
                        this.m_emitter.bodyEmitter.emitLoadTupleIndex(sinfo, arg.treg, ectr, etreg);
                    }

                    filledLocations[ii] = { vtype: this.getInfoForLoadFromIndex(arg.argtype, ectr), mustDef: ectr < expandInfo[1], trgt: etreg };

                    while (filledLocations[ii] !== undefined) {
                        this.raiseErrorIf(sinfo, !filledLocations[ii].mustDef, `We have an potentially ambigious binding of an optional parameter "${sig.params[ii].name}"`);
                        ii++;
                    }
                }
            }

            apos++;
            while (apos < args.length && (args[apos].name !== undefined || (args[apos].expando && this.m_assembly.subtypeOf(args[apos].argtype, this.m_assembly.getSpecialRecordConceptType())))) {
                apos++;
            }
        }

        while (filledLocations[ii] !== undefined) {
            this.raiseErrorIf(sinfo, !filledLocations[ii].mustDef, `We have an potentially ambigious binding of an optional parameter "${sig.params[ii].name}"`);
            ii++;
        }

        while (apos < args.length && (args[apos].name !== undefined || (args[apos].expando && this.m_assembly.subtypeOf(args[apos].argtype, this.m_assembly.getSpecialRecordConceptType())))) {
            apos++;
        }

        if (ii < sig.params.length) {
            this.raiseErrorIf(sinfo, !sig.params[ii].isOptional, `Insufficient number of parameters -- missing value for ${sig.params[ii].name}`);
        }
        else {
            this.raiseErrorIf(sinfo, apos !== args.length && sig.optRestParamType === undefined, "Too many arguments for call");
        }

        //go through names and fill out info for any that should use the default value -- raise error if any are missing
        for (let j = 0; j < sig.params.length; ++j) {
            const paramtype = sig.params[j].type;
            if (filledLocations[j] === undefined) {
                this.raiseErrorIf(sinfo, !sig.params[j].isOptional, `Parameter ${sig.params[j].name} is required and must be assigned a value in constructor`);

                filledLocations[j] = { vtype: paramtype, mustDef: true, trgt: new MIRConstantNone() };
            }

            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(filledLocations[j].vtype, paramtype), `Parameter ${sig.params[j].name} expected argument of type ${paramtype.idStr} but got ${filledLocations[j].vtype.idStr}`);
        }

        let margs = filledLocations.map((fl) => fl.trgt);

        //if this has a rest parameter check it
        if (sig.optRestParamType !== undefined) {
            const objtype = ResolvedType.tryGetOOTypeInfo(sig.optRestParamType);
            this.raiseErrorIf(sinfo, objtype === undefined || !(objtype instanceof ResolvedEntityAtomType), "Invalid rest type");

            const oodecl = (objtype as ResolvedEntityAtomType).object;
            const oobinds = (objtype as ResolvedEntityAtomType).binds;
            const oftype = ResolvedEntityAtomType.create(oodecl, oobinds);

            const rargs = args.slice(apos).filter((arg) => arg.name === undefined);

            const rtreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            if (oodecl.isTypeACollectionEntity()) {
                this.checkArgumentsCollectionConstructor(sinfo, env, oftype, oobinds.get("T") as ResolvedType, rargs, rtreg);
            }
            else {
                const contentstype = ResolvedType.createSingle(ResolvedTupleAtomType.create(false, [new ResolvedTupleAtomTypeEntry(oobinds.get("K") as ResolvedType, false), new ResolvedTupleAtomTypeEntry(oobinds.get("V") as ResolvedType, false)]));
                this.checkArgumentsCollectionConstructor(sinfo, env, oftype, contentstype, rargs, rtreg);
            }

            margs.push(rtreg);
        }

        if (skipEmit) {
            this.m_emitEnabled = emitRestore && true;
        }

        return margs;
    }

    private checkLiteralNoneExpression(env: TypeEnvironment, exp: LiteralNoneExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitLoadConstNone(exp.sinfo, trgt);
        }

        return [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), FlowTypeTruthValue.False)];
    }

    private checkLiteralBoolExpression(env: TypeEnvironment, exp: LiteralBoolExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitLoadConstBool(exp.sinfo, exp.value, trgt);
        }

        return [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), exp.value ? FlowTypeTruthValue.True : FlowTypeTruthValue.False)];
    }

    private checkLiteralIntegerExpression(env: TypeEnvironment, exp: LiteralIntegerExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitLoadConstInt(exp.sinfo, exp.value, trgt);
        }

        return [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialIntType())];
    }

    private checkLiteralStringExpression(env: TypeEnvironment, exp: LiteralStringExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitLoadConstString(exp.sinfo, exp.value, trgt);
        }

        return [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialStringType())];
    }

    private checkTypedStringCommon(sinfo: SourceInfo, env: TypeEnvironment, ttype: TypeSignature): { oftype: [OOPTypeDecl, Map<string, ResolvedType>], ofresolved: ResolvedType, stringtype: ResolvedType } {
        const oftype = this.resolveAndEnsureType(sinfo, ttype, env.terms);

        const aoftype = ResolvedType.tryGetOOTypeInfo(oftype);
        this.raiseErrorIf(sinfo, aoftype === undefined, "Can only make string type using concept or object types");
        this.raiseErrorIf(sinfo, aoftype instanceof ResolvedConceptAtomType && aoftype.conceptTypes.length !== 1, "Must have unique entity/concept type for string");

        const oodecl = (aoftype instanceof ResolvedEntityAtomType) ? (aoftype as ResolvedEntityAtomType).object : (aoftype as ResolvedConceptAtomType).conceptTypes[0].concept;
        const oobinds = (aoftype instanceof ResolvedEntityAtomType) ? (aoftype as ResolvedEntityAtomType).binds : (aoftype as ResolvedConceptAtomType).conceptTypes[0].binds;

        //ensure full string[T] type is registered
        const terms = [new TemplateTypeSignature("T")];
        const binds = new Map<string, ResolvedType>().set("T", oftype);
        const stype = this.resolveAndEnsureType(sinfo, new NominalTypeSignature("NSCore", "String", terms), binds);

        //do dynamic check to see if string is valid of format
        this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(oftype, this.m_assembly.getSpecialParsableConcept()), "Type must provide 'Parsable' concept");

        return { oftype: [oodecl, oobinds], ofresolved: oftype, stringtype: stype };
    }

    private checkCreateTypedString(env: TypeEnvironment, exp: LiteralTypedStringExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const aoftype = this.checkTypedStringCommon(exp.sinfo, env, exp.stype);

        if (this.m_emitEnabled) {
            this.m_emitter.registerTypeInstantiation(...aoftype.oftype);
            const stype = this.m_emitter.registerResolvedTypeReference(aoftype.stringtype);

            this.m_emitter.bodyEmitter.emitLoadConstTypedString(exp.sinfo, exp.value, MIRKeyGenerator.generateTypeKey(...aoftype.oftype), stype.trkey, trgt);
        }

        return [env.setExpressionResult(this.m_assembly, aoftype.stringtype)];
    }

    private checkTypedStringConstructor(env: TypeEnvironment, exp: LiteralTypedStringConstructorExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const aoftype = this.checkTypedStringCommon(exp.sinfo, env, exp.stype);

        const sdecl = aoftype.oftype[0].staticFunctions.get("tryParse");
        this.raiseErrorIf(exp.sinfo, sdecl === undefined, "Missing static function 'tryParse'");

        if (this.m_emitEnabled) {
            this.m_emitter.registerTypeInstantiation(...aoftype.oftype);
            const stype = this.m_emitter.registerResolvedTypeReference(aoftype.stringtype);

            this.m_emitter.registerStaticCall(aoftype.oftype[0], sdecl as StaticFunctionDecl, "tryParse", aoftype.oftype[1]);

            const tmpr = this.m_emitter.bodyEmitter.generateTmpRegister();
            this.m_emitter.bodyEmitter.emitLoadConstTypedString(exp.sinfo, exp.value, MIRKeyGenerator.generateTypeKey(...aoftype.oftype), stype.trkey, tmpr);
            this.m_emitter.bodyEmitter.emitCallStaticFunction(exp.sinfo, MIRKeyGenerator.generateStaticKey(aoftype.oftype[0], "tryParse", aoftype.oftype[1]), [tmpr], trgt);
        }

        return [env.setExpressionResult(this.m_assembly, aoftype.ofresolved)];
    }

    private checkAccessNamespaceConstant(env: TypeEnvironment, exp: AccessNamespaceConstantExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        this.raiseErrorIf(exp.sinfo, !this.m_assembly.hasNamespace(exp.ns), `Namespace '${exp.ns}' is not defined`);
        const nsdecl = this.m_assembly.getNamespace(exp.ns);

        this.raiseErrorIf(exp.sinfo, !nsdecl.consts.has(exp.name), `Constant named '${exp.name}' is not defined`);
        const cdecl = nsdecl.consts.get(exp.name) as NamespaceConstDecl;

        const rtype = this.resolveAndEnsureType(exp.sinfo, cdecl.declaredType, new Map<string, ResolvedType>());

        if (this.m_emitEnabled) {
            this.m_emitter.registerPendingGlobalProcessing(cdecl);
            this.m_emitter.bodyEmitter.emitAccessNamespaceConstant(exp.sinfo, MIRKeyGenerator.generateGlobalKey(exp.ns, exp.name), trgt);
        }

        return [env.setExpressionResult(this.m_assembly, rtype)];
    }

    private checkAccessStaticField(env: TypeEnvironment, exp: AccessStaticFieldExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const baseType = this.resolveAndEnsureType(exp.sinfo, exp.stype, env.terms);

        const cdecltry = this.m_assembly.tryGetOOMemberDeclUnique(baseType, "const", exp.name);
        this.raiseErrorIf(exp.sinfo, cdecltry === undefined, `Constant value not defined for type '${baseType.idStr}'`);

        const cdecl = cdecltry as OOMemberLookupInfo;
        const rtype = this.resolveAndEnsureType(exp.sinfo, (cdecl.decl as StaticMemberDecl).declaredType, cdecl.binds);

        if (this.m_emitEnabled) {
            this.m_emitter.registerTypeInstantiation(cdecl.contiainingType, cdecl.binds);
            this.m_emitter.registerPendingConstProcessing(cdecl.contiainingType, cdecl.decl as StaticMemberDecl, cdecl.binds);
            this.m_emitter.bodyEmitter.emitAccessConstField(exp.sinfo, MIRKeyGenerator.generateConstKey(cdecl.contiainingType, cdecl.binds, exp.name), trgt);
        }

        return [env.setExpressionResult(this.m_assembly, rtype)];
    }

    private checkAccessVariable(env: TypeEnvironment, exp: AccessVariableExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        this.raiseErrorIf(exp.sinfo, !env.isVarNameDefined(exp.name), `Variable name '${exp.name}' is not defined`);

        if (this.m_emitEnabled) {
            switch (env.lookupVarScope(exp.name)) {
                case "captured":
                    this.m_emitter.bodyEmitter.emitAccessCapturedVariable(exp.sinfo, exp.name, trgt);
                    break;
                case "arg":
                    this.m_emitter.bodyEmitter.emitAccessArgVariable(exp.sinfo, exp.name, trgt);
                    break;
                case "local":
                    this.m_emitter.bodyEmitter.emitAccessLocalVariable(exp.sinfo, exp.name, trgt);
                    break;
            }
        }

        const vinfo = env.lookupVar(exp.name) as VarInfo;
        this.raiseErrorIf(exp.sinfo, !vinfo.mustDefined, "Var may not be defined at use");

        return [env.setExpressionResult(this.m_assembly, vinfo.flowType)];
    }

    private checkConstructorPrimary(env: TypeEnvironment, exp: ConstructorPrimaryExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const ctype = this.resolveAndEnsureType(exp.sinfo, exp.ctype, env.terms);
        const objtype = ResolvedType.tryGetOOTypeInfo(ctype);
        this.raiseErrorIf(exp.sinfo, objtype === undefined || !(objtype instanceof ResolvedEntityAtomType), "Invalid constructor type");

        const oodecl = (objtype as ResolvedEntityAtomType).object;
        const oobinds = (objtype as ResolvedEntityAtomType).binds;
        this.checkTemplateTypes(exp.sinfo, oodecl.terms, oobinds);

        const eargs = this.checkArgumentsEvaluationNoSig(env, exp.args);

        const oftype = ResolvedEntityAtomType.create(oodecl, oobinds);
        if (oodecl.isTypeACollectionEntity()) {
            return [env.setExpressionResult(this.m_assembly, this.checkArgumentsCollectionConstructor(exp.sinfo, env, oftype, oobinds.get("T") as ResolvedType, eargs, trgt))];
        }
        else if (oodecl.isTypeAMapEntity()) {
            const contentstype = ResolvedType.createSingle(ResolvedTupleAtomType.create(false, [new ResolvedTupleAtomTypeEntry(oobinds.get("K") as ResolvedType, false), new ResolvedTupleAtomTypeEntry(oobinds.get("V") as ResolvedType, false)]));
            return [env.setExpressionResult(this.m_assembly, this.checkArgumentsCollectionConstructor(exp.sinfo, env, oftype, contentstype, eargs, trgt))];
        }
        else {
            return [env.setExpressionResult(this.m_assembly, this.checkArgumentsConstructor(exp.sinfo, env, oftype, eargs, trgt))];
        }
    }

    private checkConstructorPrimaryWithFactory(env: TypeEnvironment, exp: ConstructorPrimaryWithFactoryExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const baseType = this.resolveAndEnsureType(exp.sinfo, exp.ctype, env.terms);
        const objtype = ResolvedType.tryGetOOTypeInfo(baseType);
        this.raiseErrorIf(exp.sinfo, objtype === undefined || !(objtype instanceof ResolvedEntityAtomType), "Invalid constructor type");

        const oodecl = (objtype as ResolvedEntityAtomType).object;
        const oobinds = (objtype as ResolvedEntityAtomType).binds;
        this.raiseErrorIf(exp.sinfo, !(oodecl instanceof EntityTypeDecl), "Can only construct concrete entities");
        this.checkTemplateTypes(exp.sinfo, oodecl.terms, oobinds);

        const fdecl = oodecl.staticFunctions.get(exp.factoryName);
        this.raiseErrorIf(exp.sinfo, fdecl === undefined || !OOPTypeDecl.attributeSetContains("factory", fdecl.attributes), `Function is not a factory function for type '${baseType.idStr}'`);

        const binds = this.m_assembly.resolveBindsForCall((fdecl as StaticFunctionDecl).invoke.terms, exp.terms.targs, oobinds, env.terms);
        this.raiseErrorIf(exp.sinfo, binds === undefined, "Call bindings could not be resolved");

        this.checkTemplateTypes(exp.sinfo, (fdecl as StaticFunctionDecl).invoke.terms, binds as Map<string, ResolvedType>);

        if (this.m_emitEnabled) {
            this.m_emitter.registerTypeInstantiation(oodecl, oobinds);
            this.m_emitter.registerStaticCall(oodecl, fdecl as StaticFunctionDecl, exp.factoryName, binds as Map<string, ResolvedType>);
        }

        const fsig = this.resolveAndEnsureType(exp.sinfo, (fdecl as StaticFunctionDecl).invoke.generateSig(), binds as Map<string, ResolvedType>);
        const eargs = this.checkArgumentsEvaluationWSig(env, ResolvedType.tryGetUniqueFunctionTypeAtom(fsig) as ResolvedFunctionAtomType, exp.args, undefined);
        const rargs = this.checkArgumentsSignature(exp.sinfo, env, ResolvedType.tryGetUniqueFunctionTypeAtom(fsig) as ResolvedFunctionAtomType, eargs);

        const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitCallStaticFunction(exp.sinfo, MIRKeyGenerator.generateStaticKey(oodecl, exp.factoryName, binds as Map<string, ResolvedType>), rargs, etreg);
        }

        const oftype = ResolvedEntityAtomType.create(oodecl, oobinds);
        const returntype = (ResolvedType.tryGetUniqueFunctionTypeAtom(fsig) as ResolvedFunctionAtomType).resultType;
        return [env.setExpressionResult(this.m_assembly, this.checkArgumentsConstructor(exp.sinfo, env, oftype, [{ name: undefined, argtype: returntype, expando: true, treg: etreg }], trgt))];
    }

    private checkTupleConstructor(env: TypeEnvironment, exp: ConstructorTupleExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const eargs = this.checkArgumentsEvaluationNoSig(env, exp.args);
        return [env.setExpressionResult(this.m_assembly, this.checkArgumentsTupleConstructor(exp.sinfo, env, eargs, trgt))];
    }

    private checkRecordConstructor(env: TypeEnvironment, exp: ConstructorRecordExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const eargs = this.checkArgumentsEvaluationNoSig(env, exp.args);
        return [env.setExpressionResult(this.m_assembly, this.checkArgumentsRecordConstructor(exp.sinfo, env, eargs, trgt))];
    }

    private checkLambdaConstructor(env: TypeEnvironment, exp: ConstructorLambdaExpression, trgt: MIRTempRegister, expectedType?: ResolvedType): TypeEnvironment[] {
        this.raiseErrorIf(exp.sinfo, exp.isAuto && expectedType === undefined, "Could not infer auto lambda function type");

        const ltypetry = exp.isAuto ? expectedType : this.resolveAndEnsureType(exp.sinfo, exp.invoke.generateSig(), env.terms);
        this.raiseErrorIf(exp.sinfo, ltypetry === undefined || ResolvedType.tryGetUniqueFunctionTypeAtom(ltypetry) === undefined, "Invalid lambda type");

        if (this.m_emitEnabled) {
            let captured = new Map<string, MIRRegisterArgument>();
            let capturedMap: Map<string, ResolvedType> = new Map<string, ResolvedType>();

            let captures: string[] = [];
            exp.invoke.captureSet.forEach((v) => captures.push(v));
            captures.sort();

            captures.forEach((v) => {
                const vinfo = env.lookupVar(v) as VarInfo;
                const scope = env.lookupVarScope(v);
                if (scope === "local") {
                    captured.set(v, new MIRVarLocal(v));
                }
                else if (scope === "arg") {
                    captured.set(v, new MIRVarParameter(v));
                }
                else {
                    captured.set(v, new MIRVarCaptured(v));
                }
                capturedMap.set(v, vinfo.flowType);
            });

            const lkey = MIRKeyGenerator.generateLambdaKey(this.m_file, exp.sinfo.line, exp.sinfo.column, exp.sinfo.pos, new Map<string, ResolvedType>(env.terms));
            this.m_emitter.registerResolvedTypeReference(ltypetry as ResolvedType);
            this.m_emitter.registerLambda(lkey, capturedMap, exp.invoke, env.terms, ResolvedType.tryGetUniqueFunctionTypeAtom(ltypetry as ResolvedType) as ResolvedFunctionAtomType);

            const ltype = this.m_emitter.registerResolvedTypeReference(ltypetry as ResolvedType);
            this.m_emitter.bodyEmitter.emitConstructorLambda(exp.sinfo, lkey, ltype.trkey, captured, trgt);
        }

        return [env.setExpressionResult(this.m_assembly, ltypetry as ResolvedType)];
    }

    private checkCallNamespaceFunctionExpression(env: TypeEnvironment, exp: CallNamespaceFunctionExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        this.raiseErrorIf(exp.sinfo, !this.m_assembly.hasNamespace(exp.ns), `Namespace '${exp.ns}' is not defined`);
        const nsdecl = this.m_assembly.getNamespace(exp.ns);

        this.raiseErrorIf(exp.sinfo, !nsdecl.functions.has(exp.name), `Function named '${exp.name}' is not defined`);
        const fdecl = nsdecl.functions.get(exp.name) as NamespaceFunctionDecl;

        const binds = this.m_assembly.resolveBindsForCall(fdecl.invoke.terms, exp.terms.targs, new Map<string, ResolvedType>(), env.terms);
        this.raiseErrorIf(exp.sinfo, binds === undefined, "Call bindings could not be resolved");

        this.checkTemplateTypes(exp.sinfo, fdecl.invoke.terms, binds as Map<string, ResolvedType>);

        const fsig = this.resolveAndEnsureType(exp.sinfo, fdecl.invoke.generateSig(), binds as Map<string, ResolvedType>);
        const eargs = this.checkArgumentsEvaluationWSig(env, ResolvedType.tryGetUniqueFunctionTypeAtom(fsig) as ResolvedFunctionAtomType, exp.args, undefined);

        const margs = this.checkArgumentsSignature(exp.sinfo, env, ResolvedType.tryGetUniqueFunctionTypeAtom(fsig) as ResolvedFunctionAtomType, eargs);
        if (this.m_emitEnabled) {
            this.m_emitter.registerFunctionCall(exp.ns, exp.name, fdecl, binds as Map<string, ResolvedType>);
            this.m_emitter.bodyEmitter.emitCallNamespaceFunction(exp.sinfo, MIRKeyGenerator.generateFunctionKey(exp.ns, exp.name, binds as Map<string, ResolvedType>), margs, trgt);
        }

        return [env.setExpressionResult(this.m_assembly, this.resolveAndEnsureType(exp.sinfo, fdecl.invoke.resultType, binds as Map<string, ResolvedType>))];
    }

    private checkCallStaticFunctionExpression(env: TypeEnvironment, exp: CallStaticFunctionExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const baseType = this.resolveAndEnsureType(exp.sinfo, exp.ttype, env.terms);

        const fdecltry = this.m_assembly.tryGetOOMemberDeclUnique(baseType, "static", exp.name);
        this.raiseErrorIf(exp.sinfo, fdecltry === undefined, `Constant value not defined for type '${baseType.idStr}'`);

        const fdecl = fdecltry as OOMemberLookupInfo;
        const binds = this.m_assembly.resolveBindsForCall((fdecl.decl as StaticFunctionDecl).invoke.terms, exp.terms.targs, fdecl.binds, env.terms);
        this.raiseErrorIf(exp.sinfo, binds === undefined, "Call bindings could not be resolved");

        this.checkTemplateTypes(exp.sinfo, (fdecl.decl as StaticFunctionDecl).invoke.terms, binds as Map<string, ResolvedType>);

        const fsig = this.resolveAndEnsureType(exp.sinfo, (fdecl.decl as StaticFunctionDecl).invoke.generateSig(), binds as Map<string, ResolvedType>);
        const eargs = this.checkArgumentsEvaluationWSig(env, ResolvedType.tryGetUniqueFunctionTypeAtom(fsig) as ResolvedFunctionAtomType, exp.args, undefined);

        const margs = this.checkArgumentsSignature(exp.sinfo, env, ResolvedType.tryGetUniqueFunctionTypeAtom(fsig) as ResolvedFunctionAtomType, eargs);
        if (this.m_emitEnabled) {
            this.m_emitter.registerTypeInstantiation(fdecl.contiainingType, fdecl.binds);
            this.m_emitter.registerStaticCall(fdecl.contiainingType, fdecl.decl as StaticFunctionDecl, (fdecl.decl as StaticFunctionDecl).name, binds as Map<string, ResolvedType>);

            this.m_emitter.bodyEmitter.emitCallStaticFunction(exp.sinfo, MIRKeyGenerator.generateStaticKey(fdecl.contiainingType, (fdecl.decl as StaticFunctionDecl).name, binds as Map<string, ResolvedType>), margs, trgt);
        }

        return [env.setExpressionResult(this.m_assembly, this.resolveAndEnsureType(exp.sinfo, (fdecl.decl as StaticFunctionDecl).invoke.resultType, binds as Map<string, ResolvedType>))];
    }

    private checkAccessFromIndex(env: TypeEnvironment, op: PostfixAccessFromIndex, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialTupleConceptType()), "Base of index expression must be of Tuple type");
        this.raiseErrorIf(op.sinfo, op.index < 0, "Index cannot be negative");

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitLoadTupleIndex(op.sinfo, arg, op.index, trgt);
        }

        return [env.setExpressionResult(this.m_assembly, this.getInfoForLoadFromIndex(texp, op.index))];
    }

    private checkProjectFromIndecies(env: TypeEnvironment, op: PostfixProjectFromIndecies, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialTupleConceptType()), "Base of index expression must be of Tuple type");
        this.raiseErrorIf(op.sinfo, op.indecies.some((idx) => idx < 0), "Index cannot be negative");

        const resultOptions = texp.options.map((opt) => {
            let ttypes = op.indecies.map((idx) => new ResolvedTupleAtomTypeEntry(this.getInfoForLoadFromIndex(ResolvedType.createSingle(opt), idx), false));
            return ResolvedType.createSingle(ResolvedTupleAtomType.create(false, ttypes));
        });

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitProjectTupleIndecies(op.sinfo, arg, op.indecies, trgt);
        }

        return [env.setExpressionResult(this.m_assembly, this.m_assembly.typeUnion(resultOptions))];
    }

    private checkAccessFromName(env: TypeEnvironment, op: PostfixAccessFromName, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType())) {
            const rtype = this.getInfoForLoadFromPropertyName(texp, op.name);

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitLoadProperty(op.sinfo, arg, op.name, trgt);
            }

            return [env.setExpressionResult(this.m_assembly, rtype)];
        }
        else {
            const finfo = this.m_assembly.tryGetOOMemberDeclOptions(texp, "field", op.name);
            this.raiseErrorIf(op.sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");

            const topts = (finfo.decls as OOMemberLookupInfo[]).map((info) => this.resolveAndEnsureType(op.sinfo, (info.decl as MemberFieldDecl).declaredType, info.binds));
            const rtype = this.m_assembly.typeUnion(topts);

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitLoadField(op.sinfo, arg, op.name, trgt);
            }

            return [env.setExpressionResult(this.m_assembly, rtype)];
        }
    }

    private checkProjectFromNames(env: TypeEnvironment, op: PostfixProjectFromNames, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType())) {
            const resultOptions = texp.options.map((opt) => {
                let ttypes = op.names.map((name) => new ResolvedRecordAtomTypeEntry(name, this.getInfoForLoadFromPropertyName(ResolvedType.createSingle(opt), name), false));

                this.checkBadRecordNames(op.sinfo, ttypes);
                return ResolvedType.createSingle(ResolvedRecordAtomType.create(false, ttypes));
            });

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitProjectProperties(op.sinfo, arg, op.names, trgt);
            }

            return [env.setExpressionResult(this.m_assembly, this.m_assembly.typeUnion(resultOptions))];
        }
        else {
            op.names.forEach((f) => {
                const finfo = this.m_assembly.tryGetOOMemberDeclOptions(texp, "field", f);
                this.raiseErrorIf(op.sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");
            });

            const resultOptions = texp.options.map((atom) => {
                const oentries = op.names.map((f) => {
                    const finfo = this.m_assembly.tryGetOOMemberDeclUnique(ResolvedType.createSingle(atom), "field", f) as OOMemberLookupInfo;
                    const ftype = this.resolveAndEnsureType(op.sinfo, (finfo.decl as MemberFieldDecl).declaredType, finfo.binds);
                    return new ResolvedRecordAtomTypeEntry(f, ftype, false);
                });

                this.checkBadRecordNames(op.sinfo, oentries);
                return ResolvedType.createSingle(ResolvedRecordAtomType.create(false, oentries));
            });

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitProjectFields(op.sinfo, arg, op.names, trgt);
            }

            return [env.setExpressionResult(this.m_assembly, this.m_assembly.typeUnion(resultOptions))];
        }
    }

    private checkProjectFromType(env: TypeEnvironment, op: PostfixProjectFromType, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        let resultOptions: ResolvedType[] = [];
        const opType = this.resolveAndEnsureType(op.sinfo, op.ptype, env.terms);
        this.raiseErrorIf(op.sinfo, opType.options.length !== 1, "Invalid type");

        const ptype = opType.options[0];
        if (ptype instanceof ResolvedTupleAtomType) {
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialTupleConceptType()));

            resultOptions = texp.options.map((opt) => this.projectTupleAtom(op.sinfo, opt, ptype));

            if (this.m_emitEnabled) {
                const ttype = this.m_emitter.registerResolvedTypeReference(opType);
                this.m_emitter.bodyEmitter.emitProjectFromTypeTuple(op.sinfo, arg, ttype.trkey, trgt);
            }
        }
        else if (ptype instanceof ResolvedRecordAtomType) {
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType()));

            resultOptions = texp.options.map((opt) => this.projectRecordAtom(op.sinfo, opt, ptype));

            if (this.m_emitEnabled) {
                const ttype = this.m_emitter.registerResolvedTypeReference(opType);
                this.m_emitter.bodyEmitter.emitProjectFromTypeRecord(op.sinfo, arg, ttype.trkey, trgt);
            }
        }
        else {
            this.raiseErrorIf(op.sinfo, !(ptype instanceof ResolvedConceptAtomType), "Can only project on Tuple, Record, Object, or Concept types");
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, opType), "Must be subtype for project operation to be valid");

            resultOptions = this.projectOOTypeAtom(op.sinfo, texp, ptype as ResolvedConceptAtomType);

            if (this.m_emitEnabled) {
                this.m_emitter.registerResolvedTypeReference(opType);
                (ptype as ResolvedConceptAtomType).conceptTypes.map((ctype) => this.m_emitter.registerTypeInstantiation(ctype.concept, ctype.binds));

                const ckeys = (ptype as ResolvedConceptAtomType).conceptTypes.map((ctype) => MIRKeyGenerator.generateTypeKey(ctype.concept, ctype.binds));
                this.m_emitter.bodyEmitter.emitProjectFromTypeConcept(op.sinfo, arg, ckeys, trgt);
            }
        }

        return [env.setExpressionResult(this.m_assembly, this.m_assembly.typeUnion(resultOptions))];
    }

    private checkModifyWithIndecies(env: TypeEnvironment, op: PostfixModifyWithIndecies, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialTupleConceptType()));

        const updates = op.updates.map<[number, ResolvedType, MIRTempRegister]>((update) => {
            const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            return [update[0], this.checkExpression(env, update[1], etreg).getExpressionResult().etype, etreg];
        });

        const resultOptions = texp.options.map((opt) => this.updateTupleIndeciesAtom(op.sinfo, opt, updates.map<[number, ResolvedType]>((update) => [update[0], update[1]])));

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitModifyWithIndecies(op.sinfo, arg, updates.map<[number, MIRArgument]>((update) => [update[0], update[2]]), trgt);
        }

        return [env.setExpressionResult(this.m_assembly, this.m_assembly.typeUnion(resultOptions))];
    }

    private checkModifyWithNames(env: TypeEnvironment, op: PostfixModifyWithNames, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        const updates = op.updates.map<[string, ResolvedType, MIRTempRegister]>((update) => {
            const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            return [update[0], this.checkExpression(env, update[1], etreg).getExpressionResult().etype, etreg];
        });

        if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType())) {
            const resultOptions = texp.options.map((opt) => this.updateNamedPropertiesAtom(op.sinfo, opt, updates.map<[string, ResolvedType]>((update) => [update[0], update[1]])));

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitModifyWithProperties(op.sinfo, arg, updates.map<[string, MIRArgument]>((update) => [update[0], update[2]]), trgt);
            }

            return [env.setExpressionResult(this.m_assembly, this.m_assembly.typeUnion(resultOptions))];
        }
        else {
            this.updateNamedFieldsAtom(op.sinfo, texp, updates.map<[string, ResolvedType]>((update) => [update[0], update[1]]));

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitModifyWithFields(op.sinfo, arg, updates.map<[string, MIRArgument]>((update) => [update[0], update[2]]), trgt);
            }

            return [env.setExpressionResult(this.m_assembly, texp)];
        }
    }

    private checkStructuredExtend(env: TypeEnvironment, op: PostfixStructuredExtend, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        let mergeValue = this.checkExpression(env, op.extension, etreg).getExpressionResult().etype;

        let resultOptions: ResolvedType[] = [];
        if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialTupleConceptType())) {
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(mergeValue, this.m_assembly.getSpecialTupleConceptType()), "Must be two Tuples to merge");

            resultOptions = resultOptions.concat(...texp.options.map((topt) => {
                return mergeValue.options.map((tmerge) => this.appendIntoTupleAtom(topt as ResolvedTupleAtomType, tmerge));
            }));

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitStructuredExtendTuple(op.sinfo, arg, etreg, trgt);
            }

            return [env.setExpressionResult(this.m_assembly, this.m_assembly.typeUnion(resultOptions))];
        }
        else if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType())) {
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(mergeValue, this.m_assembly.getSpecialRecordConceptType()), "Must be two Records to merge");

            resultOptions = resultOptions.concat(...texp.options.map((topt) => {
                return mergeValue.options.map((tmerge) => this.mergeIntoRecordAtom(op.sinfo, topt as ResolvedRecordAtomType, tmerge));
            }));

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitStructuredExtendRecord(op.sinfo, arg, etreg, trgt);
            }

            return [env.setExpressionResult(this.m_assembly, this.m_assembly.typeUnion(resultOptions))];
        }
        else {
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialObjectConceptType()), "Can only merge onto Tuples/Records/Objects");
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(mergeValue, this.m_assembly.getSpecialRecordConceptType()), "Must be Record to merge into Object");

            mergeValue.options.map((tmerge) => this.mergeIntoEntityConceptAtom(op.sinfo, texp, tmerge));

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitStructuredExtendObject(op.sinfo, arg, etreg, trgt);
            }

            return [env.setExpressionResult(this.m_assembly, texp)];
        }
    }

    private checkInvoke(env: TypeEnvironment, op: PostfixInvoke, arg: MIRTempRegister, trgt: MIRTempRegister, optArgVar?: string): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        if (op.specificResolve !== undefined || (texp.isUniqueCallTargetType() && this.m_assembly.tryGetOOMemberDeclUnique(texp, "method", op.name))) {
            const resolveType = op.specificResolve !== undefined ? this.resolveAndEnsureType(op.sinfo, op.specificResolve, env.terms) : texp;

            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, resolveType), "This is not a subtype of specified resolve type");

            const mdecltry = this.m_assembly.tryGetOOMemberDeclUnique(resolveType, "method", op.name);
            this.raiseErrorIf(op.sinfo, mdecltry === undefined, `Method not defined for type '${resolveType.idStr}'`);

            const mdecl = mdecltry as OOMemberLookupInfo;

            const binds = this.m_assembly.resolveBindsForCall((mdecl.decl as MemberMethodDecl).invoke.terms, op.terms.targs, mdecl.binds, env.terms);
            this.raiseErrorIf(op.sinfo, binds === undefined, "Call bindings could not be resolved");

            const fsig = this.resolveAndEnsureType(op.sinfo, (mdecl.decl as MemberMethodDecl).invoke.generateSig(), binds as Map<string, ResolvedType>);
            const eargs = this.checkArgumentsEvaluationWSig(env, ResolvedType.tryGetUniqueFunctionTypeAtom(fsig) as ResolvedFunctionAtomType, op.args, [resolveType, arg]);
            const margs = this.checkArgumentsSignature(op.sinfo, env, ResolvedType.tryGetUniqueFunctionTypeAtom(fsig) as ResolvedFunctionAtomType, eargs);
            if (this.m_emitEnabled) {
                this.m_emitter.registerTypeInstantiation(mdecl.contiainingType, mdecl.binds);
                this.m_emitter.registerMethodCall(mdecl.contiainingType, mdecl.decl as MemberMethodDecl, mdecl.binds, (mdecl.decl as MemberMethodDecl).name, binds as Map<string, ResolvedType>);

                this.m_emitter.bodyEmitter.emitInvokeKnownTarget(op.sinfo, MIRKeyGenerator.generateMethodKey(mdecl.contiainingType, (mdecl.decl as MemberMethodDecl).name, binds as Map<string, ResolvedType>), margs, trgt);
            }

            return [env.setExpressionResult(this.m_assembly, (ResolvedType.tryGetUniqueFunctionTypeAtom(fsig) as ResolvedFunctionAtomType).resultType)];
        }
        else {
            const vinfo = this.m_assembly.tryGetOOMemberDeclOptions(texp, "method", op.name);

            //if we can find a method def for every option with consistent roots try it -- otherwise try field below which will fail if there is a mix
            if (vinfo.root !== undefined) {
                const vopts = (vinfo.decls as OOMemberLookupInfo[]).map((opt) => {
                    const mdecl = (opt.decl as MemberMethodDecl);
                    const binds = this.m_assembly.resolveBindsForCall(mdecl.invoke.terms, op.terms.targs, opt.binds, env.terms) as Map<string, ResolvedType>;
                    return ResolvedType.tryGetUniqueFunctionTypeAtom(this.resolveAndEnsureType(op.sinfo, mdecl.invoke.generateSig(), binds)) as ResolvedFunctionAtomType;
                });

                const rootdecl = (vinfo.root as OOMemberLookupInfo).contiainingType.memberMethods.get(op.name) as MemberMethodDecl;
                const rootbinds = this.m_assembly.resolveBindsForCall(rootdecl.invoke.terms, op.terms.targs, (vinfo.root as OOMemberLookupInfo).binds, env.terms) as Map<string, ResolvedType>;
                const rootsig = ResolvedType.tryGetUniqueFunctionTypeAtom(this.resolveAndEnsureType(op.sinfo, rootdecl.invoke.generateSig(), rootbinds)) as ResolvedFunctionAtomType;

                vopts.forEach((fopt) => {
                    this.raiseErrorIf(op.sinfo, !(fopt instanceof ResolvedFunctionAtomType), "Non-function type at lambda invocation site");
                    const optsig = fopt as ResolvedFunctionAtomType;
                    const optargs = this.checkArgumentsEvaluationWSig(env, optsig, op.args, [texp, arg], true);
                    this.checkArgumentsSignature(op.sinfo, env, optsig, optargs, true);
                });

                const lsigtry = this.m_assembly.computeUnifiedFunctionType(vopts, rootsig);
                this.raiseErrorIf(op.sinfo, lsigtry === undefined, "Ambigious signature for invoke");

                const lsig = lsigtry as ResolvedFunctionAtomType;

                const eargs = this.checkArgumentsEvaluationWSig(env, lsig, op.args, [texp, arg]);
                const margs = this.checkArgumentsSignature(op.sinfo, env, lsig, eargs);

                if (this.m_emitEnabled) {
                    let cbindsonly = this.m_assembly.resolveBindsForCall(rootdecl.invoke.terms, op.terms.targs, new Map<string, ResolvedType>(), env.terms) as Map<string, ResolvedType>;

                    if (op.name === "isNone") {
                        this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()).trkey, margs[0]);
                    }
                    else if (op.name === "isSome") {
                        this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialSomeType()).trkey, margs[0]);
                    }
                    else if (op.name === "is" || op.name === "as" || op.name === "tryAs" || op.name === "defaultAs") {
                        const ttype = rootbinds.get("T") as ResolvedType;
                        const mt = this.m_emitter.registerResolvedTypeReference(ttype);

                        if (op.name === "is") {
                            this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, trgt, mt.trkey, margs[0]);
                        }
                        else if (op.name === "as") {
                            const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Las_done");
                            const failblck = this.m_emitter.bodyEmitter.createNewBlock("Las_fail");
                            const creg = this.m_emitter.bodyEmitter.generateTmpRegister();
                            this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, creg, mt.trkey, margs[0]);
                            this.m_emitter.bodyEmitter.emitBoolJump(op.sinfo, creg, doneblck, failblck);

                            this.m_emitter.bodyEmitter.setActiveBlock(failblck);
                            this.m_emitter.bodyEmitter.emitAbort(op.sinfo, true, "as<T> fail");
                            this.m_emitter.bodyEmitter.emitDirectJump(op.sinfo, "exit");

                            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
                            this.m_emitter.bodyEmitter.emitRegAssign(op.sinfo, margs[0], trgt);
                        }
                        else if (op.name === "tryAs") {
                            this.m_emitter.bodyEmitter.emitRegAssign(op.sinfo, margs[0], trgt);

                            const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Ltryas_done");
                            const noneblck = this.m_emitter.bodyEmitter.createNewBlock("Ltryas_none");
                            const creg = this.m_emitter.bodyEmitter.generateTmpRegister();
                            this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, creg, mt.trkey, margs[0]);
                            this.m_emitter.bodyEmitter.emitBoolJump(op.sinfo, creg, doneblck, noneblck);

                            this.m_emitter.bodyEmitter.setActiveBlock(noneblck);
                            this.m_emitter.bodyEmitter.emitLoadConstNone(op.sinfo, trgt);
                            this.m_emitter.bodyEmitter.emitDirectJump(op.sinfo, doneblck);

                            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
                        }
                        else {
                            this.m_emitter.bodyEmitter.emitRegAssign(op.sinfo, margs[0], trgt);

                            const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Ldefaultas_done");
                            const noneblck = this.m_emitter.bodyEmitter.createNewBlock("Ldefaultas_none");
                            const creg = this.m_emitter.bodyEmitter.generateTmpRegister();
                            this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, creg, mt.trkey, margs[0]);
                            this.m_emitter.bodyEmitter.emitBoolJump(op.sinfo, creg, doneblck, noneblck);

                            this.m_emitter.bodyEmitter.setActiveBlock(noneblck);
                            this.m_emitter.bodyEmitter.emitLoadConstNone(op.sinfo, trgt);
                            this.m_emitter.bodyEmitter.emitRegAssign(op.sinfo, margs[1], trgt);

                            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
                        }
                    }
                    else {
                        this.m_emitter.registerVirtualMethodCall((vinfo.root as OOMemberLookupInfo).contiainingType, (vinfo.root as OOMemberLookupInfo).binds, op.name, cbindsonly);
                        this.m_emitter.bodyEmitter.emitInvokeVirtualTarget(op.sinfo, MIRKeyGenerator.generateVirtualMethodKey(op.name, rootbinds), margs, trgt);
                    }
                }

                if (optArgVar === undefined || !this.AnySplitMethods.some((m) => m === op.name)) {
                    const returnOpts = vopts.map((ropt) => ropt.resultType);
                    return [env.setExpressionResult(this.m_assembly, this.m_assembly.typeUnion(returnOpts))];
                }
                else {
                    //
                    //TODO: we may want to do some as/tryAs action here as well
                    //
                    let opname = op.name;
                    if (op.name === "is") {
                        const ttype = rootbinds.get("T") as ResolvedType;
                        if (ttype.isNoneType()) {
                            opname = "isNone";
                        }
                        if (ttype.isSomeType()) {
                            opname = "isSome";
                        }
                    }

                    if (opname === "isNone" || opname === "isSome") {
                        const [enone, esome] = TypeEnvironment.convertToNoneSomeFlowsOnExpressionResult(this.m_assembly, [env]);
                        this.raiseErrorIf(op.sinfo, enone.length === 0, "Value is never equal to none");
                        this.raiseErrorIf(op.sinfo, esome.length === 0, "Value is always equal to none");

                        if (optArgVar === undefined) {
                            const eqnone = enone.map((opt) => opt.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), opname === "isNone" ? FlowTypeTruthValue.True : FlowTypeTruthValue.False));
                            const neqnone = esome.map((opt) => opt.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), opname === "isNone" ? FlowTypeTruthValue.False : FlowTypeTruthValue.True));

                            return [...eqnone, ...neqnone];
                        }
                        else {
                            const eqnone = enone.map((opt) => opt
                                .assumeVar(optArgVar, (opt.expressionResult as ExpressionReturnResult).etype)
                                .setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), opname === "isNone" ? FlowTypeTruthValue.True : FlowTypeTruthValue.False));

                            const neqnone = esome.map((opt) => opt
                                .assumeVar(optArgVar, (opt.expressionResult as ExpressionReturnResult).etype)
                                .setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), opname === "isNone" ? FlowTypeTruthValue.False : FlowTypeTruthValue.True));

                            return [...eqnone, ...neqnone];
                        }
                    }
                    else {
                        const ttype = rootbinds.get("T") as ResolvedType;

                        const tvals = [env]
                            .filter((opt) => !this.m_assembly.restrictT(opt.getExpressionResult().etype, ttype).isEmptyType())
                            .map((opt) => opt
                                .assumeVar(optArgVar, this.m_assembly.restrictT(opt.getExpressionResult().etype, ttype))
                                .setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True));

                        const ntvals = [env]
                            .filter((opt) => !this.m_assembly.restrictNotT(opt.getExpressionResult().etype, ttype).isEmptyType())
                            .map((opt) => opt
                                .assumeVar(optArgVar, this.m_assembly.restrictNotT(opt.getExpressionResult().etype, ttype))
                                .setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False));

                        this.raiseErrorIf(op.sinfo, tvals.length === 0, "Value is never of type");
                        this.raiseErrorIf(op.sinfo, ntvals.length === 0, "Value is always of type");

                        return [...tvals, ...ntvals];
                    }
                }
            }
            else {
                let lambda: ResolvedType | undefined = undefined;
                const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();

                if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType())) {
                    lambda = this.getInfoForLoadFromPropertyName(texp, op.name);

                    if (this.m_emitEnabled) {
                        this.m_emitter.bodyEmitter.emitLoadProperty(op.sinfo, arg, op.name, etreg);
                    }
                }
                else {
                    const finfo = this.m_assembly.tryGetOOMemberDeclOptions(texp, "field", op.name);
                    this.raiseErrorIf(op.sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");
                    lambda = this.m_assembly.typeUnion((finfo.decls as OOMemberLookupInfo[]).map((decl) => this.resolveAndEnsureType(op.sinfo, (decl.decl as MemberFieldDecl).declaredType, decl.binds)));

                    if (this.m_emitEnabled) {
                        this.m_emitter.bodyEmitter.emitLoadField(op.sinfo, arg, op.name, etreg);
                    }
                }
                this.raiseErrorIf(op.sinfo, lambda === undefined || !this.m_assembly.subtypeOf(lambda, this.m_assembly.getSpecialFunctionConceptType()), "Ambigious signature for invoke");
                this.raiseErrorIf(op.sinfo, op.terms.targs.length !== 0, "Cannot have template args on lambda invoke");

                lambda.options.forEach((fopt) => {
                    this.raiseErrorIf(op.sinfo, !(fopt instanceof ResolvedFunctionAtomType), "Non-function type at lambda invocation site");
                    const optsig = fopt as ResolvedFunctionAtomType;
                    const optargs = this.checkArgumentsEvaluationWSig(env, optsig, op.args, [texp, arg], true);
                    this.checkArgumentsSignature(op.sinfo, env, optsig, optargs, true);
                });

                const lsigtry = this.m_assembly.computeUnifiedFunctionType(lambda.options);
                this.raiseErrorIf(op.sinfo, lsigtry === undefined, "Ambigious signature for invoke");

                const lsig = lsigtry as ResolvedFunctionAtomType;

                const eargs = this.checkArgumentsEvaluationWSig(env, lsig, op.args, [texp, arg]);
                const margs = this.checkArgumentsSignature(op.sinfo, env, lsig, eargs);

                if (this.m_emitEnabled) {
                    this.m_emitter.bodyEmitter.emitCallLambda(op.sinfo, etreg, margs, trgt);
                }

                const returnOpts = lambda.options.map((sopt) => (sopt as ResolvedFunctionAtomType).resultType);
                return [env.setExpressionResult(this.m_assembly, this.m_assembly.typeUnion(returnOpts))];
            }
        }
    }

    private checkCallLambda(env: TypeEnvironment, op: PostfixCallLambda, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialFunctionConceptType()), "Ambigious signature for invoke");

        texp.options.forEach((fopt) => {
            this.raiseErrorIf(op.sinfo, !(fopt instanceof ResolvedFunctionAtomType), "Non-function type at lambda invocation site");
            const optsig = fopt as ResolvedFunctionAtomType;
            const optargs = this.checkArgumentsEvaluationWSig(env, optsig, op.args, undefined, true);
            this.checkArgumentsSignature(op.sinfo, env, optsig, optargs, true);
        });

        const lsigtry = this.m_assembly.computeUnifiedFunctionType(texp.options);
        this.raiseErrorIf(op.sinfo, lsigtry === undefined, "Ambigious signature for call");

        const lsig = lsigtry as ResolvedFunctionAtomType;

        const eargs = this.checkArgumentsEvaluationWSig(env, lsig, op.args, undefined);
        const margs = this.checkArgumentsSignature(op.sinfo, env, lsig, eargs);

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitCallLambda(op.sinfo, arg, margs, trgt);
        }

        const returnOpts = texp.options.map((sopt) => (sopt as ResolvedFunctionAtomType).resultType);
        return [env.setExpressionResult(this.m_assembly, this.m_assembly.typeUnion(returnOpts))];
    }

    private checkElvisAction(sinfo: SourceInfo, env: TypeEnvironment[], elvisEnabled: boolean, etrgt: MIRTempRegister, noneblck: string): [TypeEnvironment[], TypeEnvironment[]] {
        const [enone, esome] = TypeEnvironment.convertToNoneSomeFlowsOnExpressionResult(this.m_assembly, env);
        this.raiseErrorIf(sinfo, enone.length === 0 && elvisEnabled, "None value is not possible -- will never return none and elvis access is redundant");
        this.raiseErrorIf(sinfo, esome.length === 0 && elvisEnabled, "Some value is not possible -- will always return none and following expression is redundant");

        if (this.m_emitEnabled && elvisEnabled) {
            const nextblk = this.m_emitter.bodyEmitter.createNewBlock("Lelvis");
            this.m_emitter.bodyEmitter.emitNoneJump(sinfo, etrgt, noneblck, nextblk);
            this.m_emitter.bodyEmitter.setActiveBlock(nextblk);
        }

        return elvisEnabled ? [esome, enone] : [[...esome, ...enone], []];
    }

    private checkPostfixExpression(env: TypeEnvironment, exp: PostfixOp, trgt: MIRTempRegister): TypeEnvironment[] {
        const hasNoneCheck = exp.ops.some((op) => op.isElvis);
        const noneblck = hasNoneCheck && this.m_emitEnabled ? this.m_emitter.bodyEmitter.createNewBlock("Lelvis_none") : "[DISABLED]";
        const doneblck = hasNoneCheck && this.m_emitEnabled ? this.m_emitter.bodyEmitter.createNewBlock("Lelvis_done") : "[DISABLED]";

        let etgrt = this.m_emitter.bodyEmitter.generateTmpRegister();
        let eenv = this.checkExpressionMultiFlow(env, exp.rootExp, etgrt);

        if (exp.rootExp instanceof AccessVariableExpression && exp.ops.length === 1 && exp.ops[0] instanceof PostfixInvoke) {
            const [fflow, scflow] = this.checkElvisAction(exp.sinfo, eenv, exp.ops[0].isElvis, etgrt, noneblck);

            const res = this.checkInvoke(TypeEnvironment.join(this.m_assembly, ...fflow), exp.ops[0] as PostfixInvoke, etgrt, trgt, exp.rootExp.name);

            if (hasNoneCheck && this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);

                this.m_emitter.bodyEmitter.setActiveBlock(noneblck);
                this.m_emitter.bodyEmitter.emitLoadConstNone(exp.sinfo, trgt);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);

                this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
            }

            return [...res, ...scflow];
        }
        else {
            let scflows: TypeEnvironment[] = [];
            let cenv = eenv;
            for (let i = 0; i < exp.ops.length; ++i) {
                const [fflow, scflow] = this.checkElvisAction(exp.sinfo, cenv, exp.ops[i].isElvis, etgrt, noneblck);
                scflows = [...scflows, ...scflow];

                const nflow = TypeEnvironment.join(this.m_assembly, ...fflow);
                const ntgrt = this.m_emitter.bodyEmitter.generateTmpRegister();
                switch (exp.ops[i].op) {
                    case PostfixOpTag.PostfixAccessFromIndex:
                        cenv = this.checkAccessFromIndex(nflow, exp.ops[i] as PostfixAccessFromIndex, etgrt, ntgrt);
                        break;
                    case PostfixOpTag.PostfixProjectFromIndecies:
                        cenv = this.checkProjectFromIndecies(nflow, exp.ops[i] as PostfixProjectFromIndecies, etgrt, ntgrt);
                        break;
                    case PostfixOpTag.PostfixAccessFromName:
                        cenv = this.checkAccessFromName(nflow, exp.ops[i] as PostfixAccessFromName, etgrt, ntgrt);
                        break;
                    case PostfixOpTag.PostfixProjectFromNames:
                        cenv = this.checkProjectFromNames(nflow, exp.ops[i] as PostfixProjectFromNames, etgrt, ntgrt);
                        break;
                    case PostfixOpTag.PostfixProjectFromType:
                        cenv = this.checkProjectFromType(nflow, exp.ops[i] as PostfixProjectFromType, etgrt, ntgrt);
                        break;
                    case PostfixOpTag.PostfixModifyWithIndecies:
                        cenv = this.checkModifyWithIndecies(nflow, exp.ops[i] as PostfixModifyWithIndecies, etgrt, ntgrt);
                        break;
                    case PostfixOpTag.PostfixModifyWithNames:
                        cenv = this.checkModifyWithNames(nflow, exp.ops[i] as PostfixModifyWithNames, etgrt, ntgrt);
                        break;
                    case PostfixOpTag.PostfixStructuredExtend:
                        cenv = this.checkStructuredExtend(nflow, exp.ops[i] as PostfixStructuredExtend, etgrt, ntgrt);
                        break;
                    case PostfixOpTag.PostfixInvoke:
                        cenv = this.checkInvoke(nflow, exp.ops[i] as PostfixInvoke, etgrt, ntgrt);
                        break;
                    default:
                        this.raiseErrorIf(exp.sinfo, exp.ops[i].op !== PostfixOpTag.PostfixCallLambda, "Unknown postfix op");
                        cenv = this.checkCallLambda(nflow, exp.ops[i] as PostfixCallLambda, etgrt, ntgrt);
                        break;
                }

                etgrt = ntgrt;
            }

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitRegAssign(exp.sinfo, etgrt, trgt);

                if (hasNoneCheck) {
                    this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);

                    this.m_emitter.bodyEmitter.setActiveBlock(noneblck);
                    this.m_emitter.bodyEmitter.emitLoadConstNone(exp.sinfo, trgt);
                    this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);

                    this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
                }
            }

            return [...cenv, ...scflows];
        }
    }

    private checkPrefixOp(env: TypeEnvironment, exp: PrefixOp, trgt: MIRTempRegister): TypeEnvironment[] {
        if (exp.op === "+" || exp.op === "-") {
            const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const eres = this.checkExpression(env, exp.exp, etreg);
            this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(eres.getExpressionResult().etype, this.m_assembly.getSpecialIntType()), "Operators + and - only applicable to numeric values");

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitPrefixOp(exp.sinfo, exp.op, etreg, trgt);
            }

            return [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialIntType())];
        }
        else {
            const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const estates = this.checkExpressionMultiFlow(env, exp.exp, etreg);
            const okType = this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);

            this.raiseErrorIf(exp.sinfo, estates.some((state) => !this.m_assembly.subtypeOf(state.getExpressionResult().etype, okType)), "Operator ! only applicable to None/Bool values");

            const [tstates, fstates] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, estates);
            const ntstates = tstates.map((state) => state.setExpressionResult(this.m_assembly, state.getExpressionResult().etype, FlowTypeTruthValue.False));
            const nfstates = fstates.map((state) => state.setExpressionResult(this.m_assembly, state.getExpressionResult().etype, FlowTypeTruthValue.True));

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitPrefixOp(exp.sinfo, "!", etreg, trgt);
            }

            return [...ntstates, ...nfstates];
        }
    }

    private checkBinOp(env: TypeEnvironment, exp: BinOpExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const lhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const lhs = this.checkExpression(env, exp.lhs, lhsreg);

        const rhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const rhs = this.checkExpression(env, exp.rhs, rhsreg);

        this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(lhs.getExpressionResult().etype, this.m_assembly.getSpecialIntType()) || !this.m_assembly.subtypeOf(rhs.getExpressionResult().etype, this.m_assembly.getSpecialIntType()));

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitBinOp(exp.sinfo, lhsreg, exp.op, rhsreg, trgt);
        }

        return [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialIntType())];
    }

    private checkBinEq(env: TypeEnvironment, exp: BinEqExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const lhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const lhs = this.checkExpression(env, exp.lhs, lhsreg);

        const rhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const rhs = this.checkExpression(env, exp.rhs, rhsreg);

        const pairwiseok = this.checkValueEq(lhs.getExpressionResult().etype, rhs.getExpressionResult().etype);
        this.raiseErrorIf(exp.sinfo, !pairwiseok, "Types are incompatible for equality compare");

        if (this.m_emitEnabled) {
            if (exp.lhs instanceof LiteralNoneExpression && exp.rhs instanceof LiteralNoneExpression) {
                this.m_emitter.bodyEmitter.emitLoadConstBool(exp.sinfo, exp.op === "==" ? true : false, trgt);
            }
            else if (exp.lhs instanceof LiteralNoneExpression) {
                const chktype = this.m_emitter.registerResolvedTypeReference(exp.op === "==" ? this.m_assembly.getSpecialNoneType() : this.m_assembly.getSpecialSomeType());
                this.m_emitter.bodyEmitter.emitTypeOf(exp.sinfo, trgt, chktype.trkey, rhsreg);
            }
            else if (exp.rhs instanceof LiteralNoneExpression) {
                const chktype = this.m_emitter.registerResolvedTypeReference(exp.op === "==" ? this.m_assembly.getSpecialNoneType() : this.m_assembly.getSpecialSomeType());
                this.m_emitter.bodyEmitter.emitTypeOf(exp.sinfo, trgt, chktype.trkey, lhsreg);
            }
            else {
                this.m_emitter.bodyEmitter.emitBinEq(exp.sinfo, lhsreg, exp.op, rhsreg, trgt);
            }
        }

        if ((exp.lhs instanceof LiteralNoneExpression && exp.rhs instanceof AccessVariableExpression) ||
            (exp.lhs instanceof AccessVariableExpression && exp.rhs instanceof LiteralNoneExpression)) {

            const [enone, esome] = TypeEnvironment.convertToNoneSomeFlowsOnExpressionResult(this.m_assembly, exp.rhs instanceof AccessVariableExpression ? [rhs] : [lhs]);
            this.raiseErrorIf(exp.sinfo, enone.length === 0, "Value is never equal to none");
            this.raiseErrorIf(exp.sinfo, esome.length === 0, "Value is always equal to none");

            const vname = exp.rhs instanceof AccessVariableExpression ? exp.rhs.name : (exp.lhs as AccessVariableExpression).name;

            const eqnone = enone.map((opt) => opt
                .assumeVar(vname, (opt.expressionResult as ExpressionReturnResult).etype)
                .setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), exp.op === "==" ? FlowTypeTruthValue.True : FlowTypeTruthValue.False));

            const neqnone = esome.map((opt) => opt
                .assumeVar(vname, (opt.expressionResult as ExpressionReturnResult).etype)
                .setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), exp.op === "==" ? FlowTypeTruthValue.False : FlowTypeTruthValue.True));

            return [...eqnone, ...neqnone];
        }
        else {
            //
            //TODO: maybe later (since this is tricky) infer that variable is strengthened by type on other side in case of -- exp.rhs instanceof AccessVariableExpression || exp.lhs instanceof AccessVariableExpression
            //
            return [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType())];
        }
    }

    private checkBinCmp(env: TypeEnvironment, exp: BinCmpExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const lhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const lhs = this.checkExpression(env, exp.lhs, lhsreg);

        const rhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const rhs = this.checkExpression(env, exp.rhs, rhsreg);

        this.raiseErrorIf(exp.sinfo, !this.checkValueLess(lhs.getExpressionResult().etype, rhs.getExpressionResult().etype), "Types are incompatible for order compare");

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitBinCmp(exp.sinfo, lhsreg, exp.op, rhsreg, trgt);
        }

        return [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType())];
    }

    private checkBinLogic(env: TypeEnvironment, exp: BinLogicExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const okType = this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);

        const lhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const lhs = this.checkExpressionMultiFlow(env, exp.lhs, lhsreg);

        this.raiseErrorIf(exp.sinfo, lhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Llogic_done");
        const scblck = this.m_emitter.bodyEmitter.createNewBlock("Llogic_shortcircuit");
        const restblck = this.m_emitter.bodyEmitter.createNewBlock("Llogic_rest");
        if (this.m_emitEnabled) {
            if (exp.op === "||") {
                this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, lhsreg, scblck, restblck);

                this.m_emitter.bodyEmitter.setActiveBlock(scblck);
                this.m_emitter.bodyEmitter.emitLoadConstBool(exp.sinfo, true, trgt);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            }
            else if (exp.op === "&&") {
                this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, lhsreg, restblck, scblck);

                this.m_emitter.bodyEmitter.setActiveBlock(scblck);
                this.m_emitter.bodyEmitter.emitLoadConstBool(exp.sinfo, false, trgt);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            }
            else {
                this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, lhsreg, restblck, scblck);

                this.m_emitter.bodyEmitter.setActiveBlock(scblck);
                this.m_emitter.bodyEmitter.emitLoadConstBool(exp.sinfo, true, trgt);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            }

            this.m_emitter.bodyEmitter.setActiveBlock(restblck);
        }

        const [trueflow, falseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, lhs);
        this.raiseErrorIf(exp.sinfo, trueflow.length === 0 || falseflow.length === 0, "Expression is always true/false rest of expression is infeasible");

        if (exp.op === "||") {
            const rhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const rhs = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...falseflow), exp.rhs, rhsreg);
            this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitTruthyConversion(exp.sinfo, rhsreg, trgt);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
                this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
            }

            const [rtflow, rfflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, rhs);
            this.raiseErrorIf(exp.sinfo, rtflow.length === 0 || rfflow.length === 0, "Expression is never true/false and not needed");
            return [...trueflow, ...rtflow, ...rfflow];
        }
        else if (exp.op === "&&") {
            const rhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const rhs = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...trueflow), exp.rhs, rhsreg);
            this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitTruthyConversion(exp.sinfo, rhsreg, trgt);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
                this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
            }

            const [rtflow, rfflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, rhs);
            this.raiseErrorIf(exp.sinfo, rtflow.length === 0 || rfflow.length === 0, "Expression is never true/false and not needed");
            return [...falseflow, ...rtflow, ...rfflow];
        }
        else {
            const rhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const rhs = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...trueflow), exp.rhs, rhsreg);
            this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitTruthyConversion(exp.sinfo, rhsreg, trgt);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
                this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
            }

            const [rtflow, rfflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, rhs);
            this.raiseErrorIf(exp.sinfo, rtflow.length === 0 || rfflow.length === 0, "Expression is never true/false and not needed");
            return [...falseflow.map((opt) => opt.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)), ...rtflow, ...rfflow];
        }
    }

    private checkNonecheck(env: TypeEnvironment, exp: NonecheckExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const lhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const lhs = this.checkExpressionMultiFlow(env, exp.lhs, lhsreg);

        let [enone, esome] = TypeEnvironment.convertToNoneSomeFlowsOnExpressionResult(this.m_assembly, lhs);
        this.raiseErrorIf(exp.sinfo, enone.length === 0, "Value is never equal to none");
        this.raiseErrorIf(exp.sinfo, esome.length === 0, "Value is always equal to none");

        if (exp.lhs instanceof AccessVariableExpression) {
            const vname = (exp.lhs as AccessVariableExpression).name;
            enone = enone.map((opt) => opt.assumeVar(vname, (opt.expressionResult as ExpressionReturnResult).etype));
            esome = esome.map((opt) => opt.assumeVar(vname, (opt.expressionResult as ExpressionReturnResult).etype));
        }

        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lnonecheck_done");
        const scblck = this.m_emitter.bodyEmitter.createNewBlock("Lnonecheck_shortcircuit");
        const restblck = this.m_emitter.bodyEmitter.createNewBlock("Lnonecheck_rest");
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitNoneJump(exp.sinfo, lhsreg, scblck, restblck);

            this.m_emitter.bodyEmitter.setActiveBlock(scblck);
            this.m_emitter.bodyEmitter.emitLoadConstNone(exp.sinfo, trgt);
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);

            this.m_emitter.bodyEmitter.setActiveBlock(restblck);
        }

        const rhs = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...esome), exp.rhs, trgt);

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }

        return [...enone, ...rhs];
    }

    private checkCoalesce(env: TypeEnvironment, exp: CoalesceExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const lhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const lhs = this.checkExpressionMultiFlow(env, exp.lhs, lhsreg);

        let [enone, esome] = TypeEnvironment.convertToNoneSomeFlowsOnExpressionResult(this.m_assembly, lhs);
        this.raiseErrorIf(exp.sinfo, enone.length === 0, "Value is never equal to none");
        this.raiseErrorIf(exp.sinfo, esome.length === 0, "Value is always equal to none");

        if (exp.lhs instanceof AccessVariableExpression) {
            const vname = (exp.lhs as AccessVariableExpression).name;
            enone = enone.map((opt) => opt.assumeVar(vname, (opt.expressionResult as ExpressionReturnResult).etype));
            esome = esome.map((opt) => opt.assumeVar(vname, (opt.expressionResult as ExpressionReturnResult).etype));
        }

        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lcoalesce_done");
        const scblck = this.m_emitter.bodyEmitter.createNewBlock("Lcoalesce_shortcircuit");
        const restblck = this.m_emitter.bodyEmitter.createNewBlock("Lcoalesce_rest");
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitNoneJump(exp.sinfo, lhsreg, restblck, scblck);

            this.m_emitter.bodyEmitter.setActiveBlock(scblck);
            this.m_emitter.bodyEmitter.emitRegAssign(exp.sinfo, lhsreg, trgt);
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);

            this.m_emitter.bodyEmitter.setActiveBlock(restblck);
        }

        const rhs = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...enone), exp.rhs, trgt);

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }

        return [...esome, ...rhs];
    }

    private checkSelect(env: TypeEnvironment, exp: SelectExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const okType = this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);

        const testreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const test = this.checkExpressionMultiFlow(env, exp.test, testreg);

        this.raiseErrorIf(exp.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

        const [trueflow, falseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test);
        this.raiseErrorIf(exp.sinfo, trueflow.length === 0 || falseflow.length === 0, "Expression is always true/false expression test is redundant");

        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lselect_done");
        const trueblck = this.m_emitter.bodyEmitter.createNewBlock("Lselect_true");
        const falseblck = this.m_emitter.bodyEmitter.createNewBlock("Lselect_false");
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, testreg, trueblck, falseblck);
        }

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.setActiveBlock(trueblck);
        }

        const truestate = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...trueflow), exp.option1, trgt);
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
        }

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.setActiveBlock(falseblck);
        }

        const falsestate = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...falseflow), exp.option2, trgt);
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }

        const rtype = this.m_assembly.typeUnion([truestate.getExpressionResult().etype, falsestate.getExpressionResult().etype]);
        return [env.setExpressionResult(this.m_assembly, rtype)];
    }

    private checkBlockExpression(env: TypeEnvironment, exp: BlockStatementExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        let cenv = env.pushLocalScope().pushYieldTarget(trgt);

        for (let i = 0; i < exp.ops.length; ++i) {
            if (!cenv.hasNormalFlow()) {
                break;
            }

            cenv = this.checkStatement(cenv, exp.ops[i]);
        }

        if (this.m_emitEnabled && cenv.hasNormalFlow()) {
            const deadvars = cenv.getCurrentFrameNames();
            for (let i = 0; i < deadvars.length; ++i) {
                this.m_emitter.bodyEmitter.localLifetimeEnd(exp.sinfo, deadvars[i]);
            }
        }

        this.raiseErrorIf(exp.sinfo, cenv.hasNormalFlow(), "Not all flow paths yield a value!");
        this.raiseErrorIf(exp.sinfo, cenv.yieldResult === undefined, "No valid flow through expresssion block");

        const ytype = cenv.yieldResult as ResolvedType;
        return [env.setExpressionResult(this.m_assembly, ytype)];
    }

    private checkIfExpression(env: TypeEnvironment, exp: IfExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const okType = this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);

        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lifexp_done");

        let cenv = env;
        let results: TypeEnvironment[] = [];
        for (let i = 0; i < exp.flow.conds.length; ++i) {
            const testreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const test = this.checkExpressionMultiFlow(cenv, exp.flow.conds[i].cond, testreg);

            this.raiseErrorIf(exp.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

            const [trueflow, falseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test);
            this.raiseErrorIf(exp.sinfo, trueflow.length === 0 || falseflow.length === 0, "Expression is always true/false expression test is redundant");

            const trueblck = this.m_emitter.bodyEmitter.createNewBlock(`Lifexp_${i}true`);
            const falseblck = this.m_emitter.bodyEmitter.createNewBlock(`Lifexp_${i}false`);
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, testreg, trueblck, falseblck);
            }

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.setActiveBlock(trueblck);
            }

            const truestate = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...trueflow), exp.flow.conds[i].action, trgt);
            if (this.m_emitEnabled) {
                if (truestate.hasNormalFlow()) {
                    this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
                }

                this.m_emitter.bodyEmitter.setActiveBlock(falseblck);
            }

            results.push(truestate);
            cenv = TypeEnvironment.join(this.m_assembly, ...falseflow);
        }

        const aenv = this.checkExpression(cenv, exp.flow.elseAction as Expression, trgt);
        results.push(aenv);

        if (this.m_emitEnabled && aenv.hasNormalFlow()) {
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
        }

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }

        return results;
    }

    private checkMatchExpression(env: TypeEnvironment, exp: MatchExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const vreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const venv = this.checkExpression(env, exp.sval, vreg);

        const svname = exp.sval instanceof AccessVariableExpression ? exp.sval.name : undefined;

        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lswitchexp_done");

        let cenv = venv;
        let vtype = venv.getExpressionResult().etype;
        let results: TypeEnvironment[] = [];
        for (let i = 0; i < exp.flow.length; ++i) {
            const nextlabel = this.m_emitter.bodyEmitter.createNewBlock(`Lswitchexp_${i}next`);
            const actionlabel = this.m_emitter.bodyEmitter.createNewBlock(`Lswitchexp_${i}action`);

            const test = this.checkMatchGuard(exp.sinfo, i, vreg, vtype, cenv, exp.flow[i].check, nextlabel, actionlabel, svname, i === exp.flow.length - 1);

            vtype = test.nexttype;
            const [trueflow, falseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test.envinfo);
            this.raiseErrorIf(exp.sinfo, trueflow.length === 0 || (falseflow.length === 0 && i !== exp.flow.length - 1) , "Expression is always true/false expression test is redundant");

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.setActiveBlock(actionlabel);
            }

            const truestate = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...trueflow), exp.flow[i].action, trgt);
            if (this.m_emitEnabled) {
                if (truestate.hasNormalFlow()) {
                    this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
                }

                this.m_emitter.bodyEmitter.setActiveBlock(nextlabel);
            }

            results.push(truestate);
            cenv = falseflow.length !== 0 ? TypeEnvironment.join(this.m_assembly, ...falseflow) : cenv;
        }

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitAbort(exp.sinfo, true, "exhaustive");
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, "exit");
        }

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }

        return results;
    }

    private checkExpression(env: TypeEnvironment, exp: Expression, trgt: MIRTempRegister, inferType?: ResolvedType): TypeEnvironment {
        const res = this.checkExpressionMultiFlow(env, exp, trgt, inferType);
        this.raiseErrorIf(exp.sinfo, res.length === 0, "No feasible flow for expression");

        return TypeEnvironment.join(this.m_assembly, ...res);
    }

    private checkExpressionMultiFlow(env: TypeEnvironment, exp: Expression, trgt: MIRTempRegister, inferType?: ResolvedType): TypeEnvironment[] {
        switch (exp.tag) {
            case ExpressionTag.LiteralNoneExpression:
                return this.checkLiteralNoneExpression(env, exp as LiteralNoneExpression, trgt);
            case ExpressionTag.LiteralBoolExpression:
                return this.checkLiteralBoolExpression(env, exp as LiteralBoolExpression, trgt);
            case ExpressionTag.LiteralIntegerExpression:
                return this.checkLiteralIntegerExpression(env, exp as LiteralIntegerExpression, trgt);
            case ExpressionTag.LiteralStringExpression:
                return this.checkLiteralStringExpression(env, exp as LiteralStringExpression, trgt);
            case ExpressionTag.LiteralTypedStringExpression:
                return this.checkCreateTypedString(env, exp as LiteralTypedStringExpression, trgt);
            case ExpressionTag.LiteralTypedStringConstructorExpression:
                return this.checkTypedStringConstructor(env, exp as LiteralTypedStringConstructorExpression, trgt);
            case ExpressionTag.AccessNamespaceConstantExpression:
                return this.checkAccessNamespaceConstant(env, exp as AccessNamespaceConstantExpression, trgt);
            case ExpressionTag.AccessStaticFieldExpression:
                return this.checkAccessStaticField(env, exp as AccessStaticFieldExpression, trgt);
            case ExpressionTag.AccessVariableExpression:
                return this.checkAccessVariable(env, exp as AccessVariableExpression, trgt);
            case ExpressionTag.ConstructorPrimaryExpression:
                return this.checkConstructorPrimary(env, exp as ConstructorPrimaryExpression, trgt);
            case ExpressionTag.ConstructorPrimaryWithFactoryExpression:
                return this.checkConstructorPrimaryWithFactory(env, exp as ConstructorPrimaryWithFactoryExpression, trgt);
            case ExpressionTag.ConstructorTupleExpression:
                return this.checkTupleConstructor(env, exp as ConstructorTupleExpression, trgt);
            case ExpressionTag.ConstructorRecordExpression:
                return this.checkRecordConstructor(env, exp as ConstructorRecordExpression, trgt);
            case ExpressionTag.ConstructorLambdaExpression:
                return this.checkLambdaConstructor(env, exp as ConstructorLambdaExpression, trgt, inferType);
            case ExpressionTag.CallNamespaceFunctionExpression:
                return this.checkCallNamespaceFunctionExpression(env, exp as CallNamespaceFunctionExpression, trgt);
            case ExpressionTag.CallStaticFunctionExpression:
                return this.checkCallStaticFunctionExpression(env, exp as CallStaticFunctionExpression, trgt);
            case ExpressionTag.PostfixOpExpression:
                return this.checkPostfixExpression(env, exp as PostfixOp, trgt);
            case ExpressionTag.PrefixOpExpression:
                return this.checkPrefixOp(env, exp as PrefixOp, trgt);
            case ExpressionTag.BinOpExpression:
                return this.checkBinOp(env, exp as BinOpExpression, trgt);
            case ExpressionTag.BinEqExpression:
                return this.checkBinEq(env, exp as BinEqExpression, trgt);
            case ExpressionTag.BinCmpExpression:
                return this.checkBinCmp(env, exp as BinCmpExpression, trgt);
            case ExpressionTag.BinLogicExpression:
                return this.checkBinLogic(env, exp as BinLogicExpression, trgt);
            case ExpressionTag.NonecheckExpression:
                return this.checkNonecheck(env, exp as NonecheckExpression, trgt);
            case ExpressionTag.CoalesceExpression:
                return this.checkCoalesce(env, exp as CoalesceExpression, trgt);
            case ExpressionTag.SelectExpression:
                return this.checkSelect(env, exp as SelectExpression, trgt);
            case ExpressionTag.BlockStatementExpression:
                return this.checkBlockExpression(env, exp as BlockStatementExpression, trgt);
            case ExpressionTag.IfExpression:
                return this.checkIfExpression(env, exp as IfExpression, trgt);
            default:
                this.raiseErrorIf(exp.sinfo, exp.tag !== ExpressionTag.MatchExpression, "Unknown expression");
                return this.checkMatchExpression(env, exp as MatchExpression, trgt);
        }
    }

    private checkVariableDeclarationStatement(env: TypeEnvironment, stmt: VariableDeclarationStatement): TypeEnvironment {
        this.raiseErrorIf(stmt.sinfo, env.isVarNameDefined(stmt.name), "Cannot shadow previous definition");

        const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const venv = stmt.exp !== undefined ? this.checkExpression(env, stmt.exp, etreg) : undefined;
        this.raiseErrorIf(stmt.sinfo, venv === undefined && stmt.isConst, "Must define const var at declaration site");
        this.raiseErrorIf(stmt.sinfo, venv === undefined && stmt.vtype instanceof AutoTypeSignature, "Must define auto typed var at declaration site");

        const vtype = (stmt.vtype instanceof AutoTypeSignature) ? (venv as TypeEnvironment).getExpressionResult().etype : this.resolveAndEnsureType(stmt.sinfo, stmt.vtype, env.terms);
        this.raiseErrorIf(stmt.sinfo, venv !== undefined && !this.m_assembly.subtypeOf(venv.getExpressionResult().etype, vtype), "Expression is not of declared type");

        if (this.m_emitEnabled) {
            const mirvtype = this.m_emitter.registerResolvedTypeReference(vtype);
            this.m_emitter.bodyEmitter.localLifetimeStart(stmt.sinfo, stmt.name, mirvtype.trkey);

            if (venv !== undefined) {
                this.m_emitter.bodyEmitter.emitVarStore(stmt.sinfo, etreg, stmt.name);
            }
        }

        return env.addVar(stmt.name, stmt.isConst, vtype, venv !== undefined, venv !== undefined ? venv.getExpressionResult().etype : vtype);
    }

    private checkVariableAssignmentStatement(env: TypeEnvironment, stmt: VariableAssignmentStatement): TypeEnvironment {
        const vinfo = env.lookupVar(stmt.name);
        this.raiseErrorIf(stmt.sinfo, vinfo === undefined, "Variable was not previously defined");
        this.raiseErrorIf(stmt.sinfo, (vinfo as VarInfo).isConst, "Variable defined as const");

        const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const venv = this.checkExpression(env, stmt.exp, etreg);
        this.raiseErrorIf(stmt.sinfo, !this.m_assembly.subtypeOf(venv.getExpressionResult().etype, (vinfo as VarInfo).declaredType), "Assign value is not subtype of declared variable type");

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitVarStore(stmt.sinfo, etreg, stmt.name);
        }

        return env.setVar(stmt.name, venv.getExpressionResult().etype);
    }

    private checkStructuredAssign(sinfo: SourceInfo, env: TypeEnvironment, isopt: boolean, cpath: (string|number)[], assign: StructuredAssignment, expt: ResolvedType, allDeclared: [boolean, string, ResolvedType, (string|number)[], ResolvedType][], allAssigned: [string, (string|number)[], ResolvedType][]) {
        if (assign instanceof IgnoreTermStructuredAssignment) {
            this.raiseErrorIf(sinfo, isopt && !assign.isOptional, "Missing value for required entry");

            const itype = this.resolveAndEnsureType(sinfo, assign.termType, env.terms);
            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(expt, itype), "Ignore type is not a subtype of declared type");
        }
        else if (assign instanceof ConstValueStructuredAssignment) {
            this.raiseErrorIf(sinfo, isopt, "Missing value for required entry");
            this.raiseError(sinfo, "Cannot use constants in structured assignment");
        }
        else if (assign instanceof VariableDeclarationStructuredAssignment) {
            this.raiseErrorIf(sinfo, allDeclared.find((decl) => decl[1] === assign.vname) !== undefined || allAssigned.find((asgn) => asgn[0] === assign.vname) !== undefined, "Duplicate variables used in structured assign");
            this.raiseErrorIf(sinfo, isopt && !assign.isOptional, "Missing value for required entry");

            const vtype = (assign.vtype instanceof AutoTypeSignature)
                ? expt
                : (assign.isOptional
                    ? this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.resolveAndEnsureType(sinfo, assign.vtype, env.terms)])
                    : this.resolveAndEnsureType(sinfo, assign.vtype, env.terms));

            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(expt, vtype), "Expression is not of declared type");

            allDeclared.push([assign.isConst, assign.vname, vtype, [...cpath], expt]);
        }
        else if (assign instanceof VariableAssignmentStructuredAssignment) {
            this.raiseErrorIf(sinfo, allDeclared.find((decl) => decl[1] === assign.vname) !== undefined || allAssigned.find((asgn) => asgn[0] === assign.vname) !== undefined, "Duplicate variables used in structured assign");
            this.raiseErrorIf(sinfo, isopt && !assign.isOptional, "Missing value for required entry");

            const vinfo = env.lookupVar(assign.vname);
            this.raiseErrorIf(sinfo, vinfo === undefined, "Variable was not previously defined");
            this.raiseErrorIf(sinfo, (vinfo as VarInfo).isConst, "Variable defined as const");

            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(expt, (vinfo as VarInfo).declaredType), "Assign value is not subtype of declared variable type");

            allAssigned.push([assign.vname, [...cpath], expt]);
        }
        else if (assign instanceof TupleStructuredAssignment) {
            this.raiseErrorIf(sinfo, isopt, "Missing value for required entry");
            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(expt, this.m_assembly.getSpecialTupleConceptType()), "Assign value is not subtype of declared variable type");
            const tuptype = ResolvedType.create(expt.options.map((opt) => this.m_assembly.ensureTupleStructuralRepresentation(opt)));

            for (let i = 0; i < assign.assigns.length; ++i) {
                const aopt = tuptype.options.some((atom) => (atom as ResolvedTupleAtomType).types.length < i || (atom as ResolvedTupleAtomType).types[i].isOptional);
                const ttype = this.getInfoForLoadFromIndex(tuptype, i);
                this.checkStructuredAssign(sinfo, env, aopt, [...cpath, i], assign.assigns[i], ttype, allDeclared, allAssigned);
            }

            if (!assign.isOpen) {
                this.raiseErrorIf(sinfo, tuptype.options.some((atom) => (atom as ResolvedTupleAtomType).types.length > assign.assigns.length), "More values in tuple that assignment");
                this.raiseErrorIf(sinfo, tuptype.options.some((atom) => (atom as ResolvedTupleAtomType).isOpen), "Tuple is open and assignemnt is not");
            }
        }
        else {
            this.raiseErrorIf(sinfo, !(assign instanceof RecordStructuredAssignment), "Unknown structured assignment type");

            this.raiseErrorIf(sinfo, isopt, "Missing value for required entry");
            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(expt, this.m_assembly.getSpecialRecordConceptType()), "Assign value is not subtype of declared variable type");
            const rectype = ResolvedType.create(expt.options.map((opt) => this.m_assembly.ensureRecordStructuralRepresentation(opt)));

            const rassign = assign as RecordStructuredAssignment;
            for (let i = 0; i < rassign.assigns.length; ++i) {
                const pname = rassign.assigns[i][0];
                const aopt = rectype.options.some((atom) => {
                    const entry = (atom as ResolvedRecordAtomType).entries.find((re) => re.name === pname);
                    return (entry === undefined || entry.isOptional);
                });
                const ttype = this.getInfoForLoadFromPropertyName(rectype, pname);
                this.checkStructuredAssign(sinfo, env, aopt, [...cpath, pname], rassign.assigns[i][1], ttype, allDeclared, allAssigned);
            }

            if (!rassign.isOpen) {
                this.raiseErrorIf(sinfo, rectype.options.some((atom) => {
                    return (atom as ResolvedRecordAtomType).entries.some((re) => {
                        const entry = rassign.assigns.find((e) => e[0] === re.name);
                        return entry === undefined;
                    });
                }), "More values in record that assignment");
                this.raiseErrorIf(sinfo, rectype.options.some((atom) => (atom as ResolvedRecordAtomType).isOpen), "Record is open and assignemnt is not");
            }
        }
    }

    private generateAssignOps(sinfo: SourceInfo, ereg: MIRTempRegister, assign: (string|number)[]): MIRTempRegister {
        let creg = ereg;
        for (let i = 0; i < assign.length; ++i) {
            const nreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            if (typeof (assign[i]) === "number") {
                this.m_emitter.bodyEmitter.emitLoadTupleIndex(sinfo, creg, assign[i] as number, nreg);
            }
            else {
                this.m_emitter.bodyEmitter.emitLoadProperty(sinfo, creg, assign[i] as string, nreg);
            }
            creg = nreg;
        }
        return creg;
    }

    private generateEqualityOps(env: TypeEnvironment, sinfo: SourceInfo, ereg: MIRTempRegister, assign: (string|number)[], value: Expression): MIRTempRegister {
        let creg = ereg;
        for (let i = 0; i < assign.length; ++i) {
            const nreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            if (typeof (assign[i]) === "number") {
                this.m_emitter.bodyEmitter.emitLoadTupleIndex(sinfo, creg, assign[i] as number, nreg);
            }
            else {
                this.m_emitter.bodyEmitter.emitLoadProperty(sinfo, creg, assign[i] as string, nreg);
            }
            creg = nreg;
        }

        const vreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        this.checkExpression(env, value, vreg);

        const rreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        this.m_emitter.bodyEmitter.emitBinEq(sinfo, creg, "==", vreg, rreg);

        return rreg;
    }

    private checkStructuredVariableAssignmentStatement(env: TypeEnvironment, stmt: StructuredVariableAssignmentStatement): TypeEnvironment {
        const expreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const eenv = this.checkExpression(env, stmt.exp, expreg);

        let allDeclared: [boolean, string, ResolvedType, (string|number)[], ResolvedType][] = [];
        let allAssigned: [string, (string|number)[], ResolvedType][] = [];
        this.checkStructuredAssign(stmt.sinfo, env, false, [], stmt.assign, eenv.getExpressionResult().etype, allDeclared, allAssigned);

        if (this.m_emitEnabled) {
            for (let i = 0; i < allDeclared.length; ++i) {
                const declv = allDeclared[i];

                const mirvtype = this.m_emitter.registerResolvedTypeReference(declv[2]);
                this.m_emitter.bodyEmitter.localLifetimeStart(stmt.sinfo, declv[1], mirvtype.trkey);

                const treg = this.generateAssignOps(stmt.sinfo, expreg, declv[3]);
                this.m_emitter.bodyEmitter.emitVarStore(stmt.sinfo, treg, declv[1]);
            }

            for (let i = 0; i < allAssigned.length; ++i) {
                const assignv = allAssigned[i];

                const treg = this.generateAssignOps(stmt.sinfo, expreg, assignv[1]);
                this.m_emitter.bodyEmitter.emitVarStore(stmt.sinfo, treg, assignv[0]);
            }
        }

        return eenv.multiVarUpdate(allDeclared, allAssigned);
    }

    private checkIfElseStatement(env: TypeEnvironment, stmt: IfElseStatement): TypeEnvironment {
        const okType = this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);

        this.raiseErrorIf(stmt.sinfo, stmt.flow.conds.length > 1 && stmt.flow.elseAction === undefined, "Must terminate elseifs with an else clause");

        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lifstmt_done");

        let cenv = env;
        let results: TypeEnvironment[] = [];
        for (let i = 0; i < stmt.flow.conds.length; ++i) {
            const testreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const test = this.checkExpressionMultiFlow(cenv, stmt.flow.conds[i].cond, testreg);

            this.raiseErrorIf(stmt.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

            const [trueflow, falseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test);
            this.raiseErrorIf(stmt.sinfo, trueflow.length === 0 || falseflow.length === 0, "Expression is always true/false expression test is redundant");

            const trueblck = this.m_emitter.bodyEmitter.createNewBlock(`Lifstmt_${i}true`);
            const falseblck = (i < stmt.flow.conds.length - 1 || stmt.flow.elseAction !== undefined) ? this.m_emitter.bodyEmitter.createNewBlock(`Lifstmt_${i}false`) : doneblck;
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitBoolJump(stmt.sinfo, testreg, trueblck, falseblck);
            }

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.setActiveBlock(trueblck);
            }

            const truestate = this.checkBlock(TypeEnvironment.join(this.m_assembly, ...trueflow), stmt.flow.conds[i].action);
            if (this.m_emitEnabled) {
                if (truestate.hasNormalFlow()) {
                    this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, doneblck);
                }

                this.m_emitter.bodyEmitter.setActiveBlock(falseblck);
            }

            results.push(truestate);
            cenv = TypeEnvironment.join(this.m_assembly, ...falseflow);
        }

        if (stmt.flow.elseAction === undefined) {
            results.push(cenv);
        }
        else {
            const aenv = this.checkStatement(cenv, stmt.flow.elseAction);
            results.push(aenv);

            if (this.m_emitEnabled && aenv.hasNormalFlow()) {
                this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, doneblck);
            }
        }

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }

        return TypeEnvironment.join(this.m_assembly, ...results);
    }

    private checkStructuredMatch(sinfo: SourceInfo, env: TypeEnvironment, cpath: (string|number)[], assign: StructuredAssignment, expt: ResolvedType, allDeclared: [boolean, string, ResolvedType, (string|number)[], ResolvedType][], allAssigned: [string, (string|number)[], ResolvedType][], allEqChecks: [(string|number)[], Expression][]): [ResolvedType, boolean] {
        if (assign instanceof IgnoreTermStructuredAssignment) {
            return [this.resolveAndEnsureType(sinfo, assign.termType, env.terms), assign.isOptional];
        }
        else if (assign instanceof ConstValueStructuredAssignment) {
            allEqChecks.push([[...cpath], assign.constValue]);

            const emitRestore = this.m_emitEnabled;
            this.m_emitEnabled = false;

            let ctype = this.checkExpression(env, assign.constValue, this.m_emitter.bodyEmitter.generateTmpRegister()).getExpressionResult().etype;

            this.m_emitEnabled = emitRestore && true;

            return [ctype, false];
        }
        else if (assign instanceof VariableDeclarationStructuredAssignment) {
            this.raiseErrorIf(sinfo, allDeclared.find((decl) => decl[1] === assign.vname) !== undefined || allAssigned.find((asgn) => asgn[0] === assign.vname) !== undefined, "Duplicate variables used in structured assign");

            const vtype = (assign.isOptional
                    ? this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.resolveAndEnsureType(sinfo, assign.vtype, env.terms)])
                    : this.resolveAndEnsureType(sinfo, assign.vtype, env.terms));

            allDeclared.push([assign.isConst, assign.vname, vtype, [...cpath], vtype]);
            return [this.resolveAndEnsureType(sinfo, assign.vtype, env.terms), assign.isOptional];
        }
        else if (assign instanceof VariableAssignmentStructuredAssignment) {
            this.raiseErrorIf(sinfo, allDeclared.find((decl) => decl[1] === assign.vname) !== undefined || allAssigned.find((asgn) => asgn[0] === assign.vname) !== undefined, "Duplicate variables used in structured assign");

            const vinfo = env.lookupVar(assign.vname);
            this.raiseErrorIf(sinfo, vinfo === undefined, "Variable was not previously defined");
            this.raiseErrorIf(sinfo, (vinfo as VarInfo).isConst, "Variable defined as const");

            allAssigned.push([assign.vname, [...cpath], (vinfo as VarInfo).declaredType]);
            return [(vinfo as VarInfo).declaredType, assign.isOptional];
        }
        else if (assign instanceof TupleStructuredAssignment) {
            const tupopts = expt.options.filter((opt) => opt instanceof ResolvedTupleAtomType || this.m_assembly.atomSubtypeOf(ResolvedTupleAtomType.createGenericOpen(), opt)).map((opt) => this.m_assembly.ensureTupleStructuralRepresentation(opt));
            this.raiseErrorIf(sinfo, tupopts.length === 0, "Check will always fail");

            const tuptype = ResolvedType.create(tupopts);
            const tupcheck: ResolvedTupleAtomTypeEntry[] = [];
            for (let i = 0; i < assign.assigns.length; ++i) {
                const ttype = this.getInfoForLoadFromIndex(tuptype, i);
                const einfo = this.checkStructuredMatch(sinfo, env, [...cpath, i], assign.assigns[i], ttype, allDeclared, allAssigned, allEqChecks);
                tupcheck.push(new ResolvedTupleAtomTypeEntry(...einfo));
            }

            return [ResolvedType.createSingle(ResolvedTupleAtomType.create(assign.isOpen, tupcheck)), false];
        }
        else {
            this.raiseErrorIf(sinfo, !(assign instanceof RecordStructuredAssignment), "Unknown structured assignment type");

            const recopts = expt.options.filter((opt) => opt instanceof ResolvedRecordAtomType || this.m_assembly.atomSubtypeOf(ResolvedRecordAtomType.createGenericOpen(), opt)).map((opt) => this.m_assembly.ensureRecordStructuralRepresentation(opt));
            this.raiseErrorIf(sinfo, recopts.length === 0, "Check will always fail");

            const rassign = assign as RecordStructuredAssignment;
            const rectype = ResolvedType.create(recopts);
            const reccheck: ResolvedRecordAtomTypeEntry[] = [];
            for (let i = 0; i < rassign.assigns.length; ++i) {
                const pname = rassign.assigns[i][0];
                const ttype = this.getInfoForLoadFromPropertyName(rectype, pname);
                const einfo = this.checkStructuredMatch(sinfo, env, [...cpath, pname], rassign.assigns[i][1], ttype, allDeclared, allAssigned, allEqChecks);
                reccheck.push(new ResolvedRecordAtomTypeEntry(pname, ...einfo));
            }

            return [ResolvedType.createSingle(ResolvedRecordAtomType.create(rassign.isOpen, reccheck)), false];
        }
    }

    private checkMatchGuard(sinfo: SourceInfo, midx: number, vreg: MIRTempRegister, sexp: ResolvedType, env: TypeEnvironment, guard: MatchGuard, nextlabel: string, actionlabel: string, svname: string | undefined, lastoption: boolean): { envinfo: TypeEnvironment[], nexttype: ResolvedType } {
        let opts: TypeEnvironment[] = [];
        let nexttype = sexp;
        let mreg = this.m_emitter.bodyEmitter.generateTmpRegister();

        if (guard instanceof WildcardMatchGuard) {
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitLoadConstBool(sinfo, true, mreg);
            }

            opts = [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)];
        }
        else if (guard instanceof TypeMatchGuard) {
            const tmatch = this.resolveAndEnsureType(sinfo, guard.oftype, env.terms);

            if (this.m_emitEnabled) {
                const mt = this.m_emitter.registerResolvedTypeReference(tmatch);
                this.m_emitter.bodyEmitter.emitTypeOf(sinfo, mreg, mt.trkey, vreg);
            }

            if (svname === undefined) {
                opts = [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType())];
            }
            else {
                this.raiseErrorIf(sinfo, this.m_assembly.restrictT(sexp, tmatch).isEmptyType(), "Value is never of type");
                this.raiseErrorIf(sinfo, !lastoption && this.m_assembly.restrictNotT(sexp, tmatch).isEmptyType(), "Value is always of type");

                const tval = env
                    .assumeVar(svname, this.m_assembly.restrictT(sexp, tmatch))
                    .setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True);

                const ntval = env
                    .assumeVar(svname, this.m_assembly.restrictNotT(sexp, tmatch))
                    .setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False);

                opts = [tval, ntval];
            }

            nexttype = this.m_assembly.restrictNotT(sexp, tmatch);
        }
        else {
            const sguard = guard as StructureMatchGuard;

            let allDeclared: [boolean, string, ResolvedType, (string | number)[], ResolvedType][] = [];
            let allAssigned: [string, (string | number)[], ResolvedType][] = [];
            let allEqChecks: [(string | number)[], Expression][] = [];
            const oftype = this.checkStructuredMatch(sinfo, env, [], sguard.match, sexp, allDeclared, allAssigned, allEqChecks)[0];

            if (this.m_emitEnabled) {
                const oft = this.m_emitter.registerResolvedTypeReference(oftype);
                const tcreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                this.m_emitter.bodyEmitter.emitTypeOf(sinfo, tcreg, oft.trkey, vreg);

                const filllabel = this.m_emitter.bodyEmitter.createNewBlock(`match${midx}_scfill`);
                if (allEqChecks.length === 0) {
                    this.m_emitter.bodyEmitter.emitRegAssign(sinfo, tcreg, mreg);
                    this.m_emitter.bodyEmitter.emitDirectJump(sinfo, filllabel);
                }
                else {
                    const eqlabel = this.m_emitter.bodyEmitter.createNewBlock(`match${midx}_sceq`);
                    this.m_emitter.bodyEmitter.emitBoolJump(sinfo, tcreg, eqlabel, nextlabel);

                    this.m_emitter.bodyEmitter.setActiveBlock(eqlabel);
                    this.m_emitter.bodyEmitter.emitLoadConstBool(sinfo, true, mreg);

                    for (let i = 0; i < allEqChecks.length; ++i) {
                        const eqreg = this.generateEqualityOps(env, sinfo, vreg, allEqChecks[i][0], allEqChecks[i][1]);
                        this.m_emitter.bodyEmitter.emitLogicStore(sinfo, mreg, mreg, "&", eqreg);
                    }

                    this.m_emitter.bodyEmitter.emitDirectJump(sinfo, filllabel);
                }

                this.m_emitter.bodyEmitter.setActiveBlock(filllabel);
                for (let i = 0; i < allDeclared.length; ++i) {
                    const declv = allDeclared[i];

                    const mirvtype = this.m_emitter.registerResolvedTypeReference(declv[2]);
                    this.m_emitter.bodyEmitter.localLifetimeStart(sinfo, declv[1], mirvtype.trkey);

                    const treg = this.generateAssignOps(sinfo, vreg, declv[3]);
                    this.m_emitter.bodyEmitter.emitVarStore(sinfo, treg, declv[1]);
                }

                for (let i = 0; i < allAssigned.length; ++i) {
                    const assignv = allAssigned[i];

                    const treg = this.generateAssignOps(sinfo, vreg, assignv[1]);
                    this.m_emitter.bodyEmitter.emitVarStore(sinfo, treg, assignv[0]);
                }
            }

            if (svname === undefined) {
                opts = [
                    env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False),
                    env.multiVarUpdate(allDeclared, allAssigned).setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)
                ];
            }
            else {
                this.raiseErrorIf(sinfo, this.m_assembly.restrictT(sexp, oftype).isEmptyType(), "Value is never of type");

                const tval = env
                        .assumeVar(svname, this.m_assembly.restrictT(sexp, oftype))
                        .multiVarUpdate(allDeclared, allAssigned)
                        .setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True);

                const ntval = env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False);

                opts = [tval, ntval];
            }

            nexttype = this.m_assembly.restrictNotT(sexp, oftype);
        }

        if (guard.optionalWhen === undefined) {
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitBoolJump(sinfo, mreg, actionlabel, nextlabel);
            }

            return { envinfo: opts, nexttype: nexttype };
        }
        else {
            const [gtrueflow, gfalseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, opts);

            if (this.m_emitEnabled) {
                const whenblck = this.m_emitter.bodyEmitter.createNewBlock(`match${midx}_when`);
                this.m_emitter.bodyEmitter.emitBoolJump(sinfo, mreg, whenblck, nextlabel);

                this.m_emitter.bodyEmitter.setActiveBlock(whenblck);
            }

            let wreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const wopts = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...gtrueflow), guard.optionalWhen, wreg);

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitBoolJump(sinfo, wreg, actionlabel, nextlabel);
            }

            const [wtrueflow, wfalseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, wopts);

            return { envinfo: [...wtrueflow, ...gfalseflow, ...wfalseflow], nexttype: nexttype };
        }
    }

    private checkMatchStatement(env: TypeEnvironment, stmt: MatchStatement): TypeEnvironment {
        const vreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const venv = this.checkExpression(env, stmt.sval, vreg);

        const svname = stmt.sval instanceof AccessVariableExpression ? stmt.sval.name : undefined;

        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lswitchstmt_done");

        let cenv = venv;
        let vtype = venv.getExpressionResult().etype;
        let results: TypeEnvironment[] = [];
        for (let i = 0; i < stmt.flow.length; ++i) {
            const nextlabel = this.m_emitter.bodyEmitter.createNewBlock(`Lswitchstmt_${i}next`);
            const actionlabel = this.m_emitter.bodyEmitter.createNewBlock(`Lswitchstmt_${i}action`);

            const test = this.checkMatchGuard(stmt.sinfo, i, vreg, vtype, cenv, stmt.flow[i].check, nextlabel, actionlabel, svname, i === stmt.flow.length - 1);

            vtype = test.nexttype;
            const [trueflow, falseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test.envinfo);
            this.raiseErrorIf(stmt.sinfo, trueflow.length === 0 || (falseflow.length === 0 && i !== stmt.flow.length - 1) , "Expression is always true/false expression test is redundant");

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.setActiveBlock(actionlabel);
            }

            const truestate = this.checkBlock(TypeEnvironment.join(this.m_assembly, ...trueflow), stmt.flow[i].action);
            if (this.m_emitEnabled) {
                if (truestate.hasNormalFlow()) {
                    this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, doneblck);
                }

                this.m_emitter.bodyEmitter.setActiveBlock(nextlabel);
            }

            results.push(truestate);
            cenv = falseflow.length !== 0 ? TypeEnvironment.join(this.m_assembly, ...falseflow) : cenv;
        }

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitAbort(stmt.sinfo, true, "exhaustive");
            this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, "exit");
        }

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }

        return TypeEnvironment.join(this.m_assembly, ...results);
    }

    private checkReturnStatement(env: TypeEnvironment, stmt: ReturnStatement): TypeEnvironment {
        const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const venv = this.checkExpression(env, stmt.value, etreg);

        this.raiseErrorIf(stmt.sinfo, env.isInYieldBlock(), "Cannot use return statment inside an expression block");

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitReturnAssign(stmt.sinfo, etreg);
            this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, "exit");
        }

        return env.setReturn(this.m_assembly, venv.getExpressionResult().etype);
    }

    private checkYieldStatement(env: TypeEnvironment, stmt: YieldStatement): TypeEnvironment {
        const yinfo = env.getYieldTargetInfo();
        const venv = this.checkExpression(env, stmt.value, yinfo);

        this.raiseErrorIf(stmt.sinfo, !env.isInYieldBlock(), "Cannot use yield statment outside expression blocks");

        return env.setYield(this.m_assembly, venv.getExpressionResult().etype);
    }

    private checkAbortStatement(env: TypeEnvironment, stmt: AbortStatement): TypeEnvironment {
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitAbort(stmt.sinfo, true, "abort");
            this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, "exit");
        }

        return env.setAbort();
    }

    private checkAssertStatement(env: TypeEnvironment, stmt: AssertStatement): TypeEnvironment {
        const okType = this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);
        const testreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const test = this.checkExpressionMultiFlow(env, stmt.cond, testreg);

        this.raiseErrorIf(stmt.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

        const [trueflow, falseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test);
        this.raiseErrorIf(stmt.sinfo, trueflow.length === 0 || falseflow.length === 0, "Expression is always true/false assert is redundant");

        if (this.m_emitEnabled) {
            const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lassert_done");
            const failblck = this.m_emitter.bodyEmitter.createNewBlock("Lassert_fail");
            this.m_emitter.bodyEmitter.emitBoolJump(stmt.sinfo, testreg, doneblck, failblck);

            this.m_emitter.bodyEmitter.setActiveBlock(failblck);
            this.m_emitter.bodyEmitter.emitAbort(stmt.sinfo, false, "assert fail");
            this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, "exit");

            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }

        return TypeEnvironment.join(this.m_assembly, ...trueflow);
    }

    private checkCheckStatement(env: TypeEnvironment, stmt: CheckStatement): TypeEnvironment {
        const okType = this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);
        const testreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const test = this.checkExpressionMultiFlow(env, stmt.cond, testreg);

        this.raiseErrorIf(stmt.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

        const [trueflow, falseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test);
        this.raiseErrorIf(stmt.sinfo, trueflow.length === 0 || falseflow.length === 0, "Expression is always true/false check is redundant");

        if (this.m_emitEnabled) {
            const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lcheck_done");
            const failblck = this.m_emitter.bodyEmitter.createNewBlock("Lcheck_fail");
            this.m_emitter.bodyEmitter.emitBoolJump(stmt.sinfo, testreg, doneblck, failblck);

            this.m_emitter.bodyEmitter.setActiveBlock(failblck);
            this.m_emitter.bodyEmitter.emitAbort(stmt.sinfo, true, "check fail");
            this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, "exit");

            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }

        return TypeEnvironment.join(this.m_assembly, ...trueflow);
    }

    private checkDebugStatement(env: TypeEnvironment, stmt: DebugStatement): TypeEnvironment {
        if (stmt.value === undefined) {
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitDebugBreak(stmt.sinfo);
            }
        }
        else {
            const vreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            this.checkExpression(env, stmt.value, vreg);

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitDebugPrint(stmt.sinfo, vreg);
            }
        }

        return env;
    }

    private checkStatement(env: TypeEnvironment, stmt: Statement): TypeEnvironment {
        this.raiseErrorIf(stmt.sinfo, !env.hasNormalFlow(), "Unreachable statements");

        switch (stmt.tag) {
            case StatementTag.EmptyStatement:
                return env;
            case StatementTag.VariableDeclarationStatement:
                return this.checkVariableDeclarationStatement(env, stmt as VariableDeclarationStatement);
            case StatementTag.VariableAssignmentStatement:
                return this.checkVariableAssignmentStatement(env, stmt as VariableAssignmentStatement);
            case StatementTag.StructuredVariableAssignmentStatement:
                return this.checkStructuredVariableAssignmentStatement(env, stmt as StructuredVariableAssignmentStatement);
            case StatementTag.IfElseStatement:
                return this.checkIfElseStatement(env, stmt as IfElseStatement);
            case StatementTag.MatchStatement:
                return this.checkMatchStatement(env, stmt as MatchStatement);
            case StatementTag.ReturnStatement:
                return this.checkReturnStatement(env, stmt as ReturnStatement);
            case StatementTag.YieldStatement:
                return this.checkYieldStatement(env, stmt as YieldStatement);
            case StatementTag.AbortStatement:
                return this.checkAbortStatement(env, stmt as AbortStatement);
            case StatementTag.AssertStatement:
                return this.checkAssertStatement(env, stmt as AssertStatement);
            case StatementTag.CheckStatement:
                return this.checkCheckStatement(env, stmt as CheckStatement);
            case StatementTag.DebugStatement:
                return this.checkDebugStatement(env, stmt as DebugStatement);
            default:
                this.raiseErrorIf(stmt.sinfo, stmt.tag !== StatementTag.BlockStatement, "Unknown statement");
                return this.checkBlock(env, stmt as BlockStatement);
        }
    }

    private checkBlock(env: TypeEnvironment, stmt: BlockStatement): TypeEnvironment {
        let cenv = env.pushLocalScope();

        for (let i = 0; i < stmt.statements.length; ++i) {
            if (!cenv.hasNormalFlow()) {
                break;
            }

            cenv = this.checkStatement(cenv, stmt.statements[i]);
        }

        if (this.m_emitEnabled && cenv.hasNormalFlow()) {
            const deadvars = cenv.getCurrentFrameNames();
            for (let i = 0; i < deadvars.length; ++i) {
                this.m_emitter.bodyEmitter.localLifetimeEnd(stmt.sinfo, deadvars[i]);
            }
        }

        return cenv.popLocalScope();
    }

    private checkBody(env: TypeEnvironment, body: BodyImplementation, args: string[], captured: string[], resultType: ResolvedType): MIRBody | undefined {
        if (typeof (body.body) === "string") {
            return new MIRBody(body.file, new SourceInfo(0, 0, 0, 0), body.body);
        }
        else if (body.body instanceof Expression) {
            if (this.m_emitEnabled) {
                this.m_emitter.initializeBodyEmitter();
            }

            const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const evalue = this.checkExpression(env, body.body, etreg);

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitReturnAssign(body.body.sinfo, etreg);
                this.m_emitter.bodyEmitter.emitDirectJump(body.body.sinfo, "exit");
            }

            this.raiseErrorIf(body.body.sinfo, !this.m_assembly.subtypeOf(evalue.getExpressionResult().etype, resultType), "Did not produce the expected return type");

            return this.m_emitEnabled ? this.m_emitter.bodyEmitter.getBody(this.m_file, body.body.sinfo, args, captured) : undefined;
        }
        else if (body.body instanceof BlockStatement) {
            if (this.m_emitEnabled) {
                this.m_emitter.initializeBodyEmitter();
            }

            const renv = this.checkBlock(env, body.body);
            this.raiseErrorIf(body.body.sinfo, renv.hasNormalFlow(), "Not all flow paths return a value!");
            this.raiseErrorIf(body.body.sinfo, !this.m_assembly.subtypeOf(renv.returnResult as ResolvedType, resultType), "Did not produce the expected return type");

            return this.m_emitEnabled ? this.m_emitter.bodyEmitter.getBody(this.m_file, body.body.sinfo, args, captured) : undefined;
        }
        else {
            return undefined;
        }
    }

    private checkExpressionAsBody(env: TypeEnvironment, exp: Expression, ofType: ResolvedType): MIRBody {
        if (this.m_emitEnabled) {
            this.m_emitter.initializeBodyEmitter();
        }

        const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const evalue = this.checkExpression(env, exp, etreg);

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitReturnAssign(exp.sinfo, etreg);
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, "exit");
        }

        this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(evalue.getExpressionResult().etype, ofType), "Did not produce the expected type");

        let argNames: string[] = [];
        (env.args as Map<string, VarInfo>).forEach((arg, name) => argNames.push(name));

        return this.m_emitter.bodyEmitter.getBody(this.m_file, exp.sinfo, argNames, []);
    }

    private abortIfTooManyErrors() {
        if (this.m_errors.length > 20) {
            throw new Error("More than 20 errors ... halting type checker");
        }
    }

    processOOType(tkey: MIRTypeKey, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>) {
        try {
            this.m_file = tdecl.srcFile;

            let terms = new Map<string, MIRType>();
            tdecl.terms.forEach((term) => terms.set(term.name, this.m_emitter.registerResolvedTypeReference(binds.get(term.name) as ResolvedType)));

            const provides = tdecl.provides.map((provide) => {
                const ptype = this.resolveAndEnsureType(new SourceInfo(0, 0, 0, 0), provide, binds);
                const cpt = ((ptype.options[0]) as ResolvedConceptAtomType).conceptTypes[0];

                this.m_emitter.registerTypeInstantiation(cpt.concept, cpt.binds);
                return MIRKeyGenerator.generateTypeKey(cpt.concept, cpt.binds);
            });

            const invariants = tdecl.invariants.map((inv) => {
                const thistype = ResolvedType.createSingle(tdecl instanceof EntityTypeDecl ? ResolvedEntityAtomType.create(tdecl, binds) : ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(tdecl as ConceptTypeDecl, binds)]));
                const invenv = TypeEnvironment.createInitialEnvForCall(binds, new Map<string, VarInfo>().set("this", new VarInfo(thistype, true, true, thistype)));
                return this.checkExpressionAsBody(invenv, inv, this.m_assembly.getSpecialBoolType());
            });

            //
            //TODO: we need to check inheritance and provies rules here -- diamonds, virtual/abstract/override use, etc.
            //

            const fields: MIRFieldDecl[] = [];
            tdecl.memberFields.forEach((f) => {
                const fkey = MIRKeyGenerator.generateFieldKey(tdecl, binds, f.name);
                const ckey = MIRKeyGenerator.generateTypeKey(tdecl, binds);
                const dtypeResolved = this.resolveAndEnsureType(f.sourceLocation, f.declaredType, binds);
                const dtype = this.m_emitter.registerResolvedTypeReference(dtypeResolved);
                let value = undefined;
                if (f.value !== undefined) {
                    value = this.checkExpressionAsBody(TypeEnvironment.createInitialEnvForCall(binds, new Map<string, VarInfo>()), f.value, dtypeResolved);
                }

                const mfield = new MIRFieldDecl(f.sourceLocation, f.srcFile, fkey, f.attributes, f.name, ckey, dtype, value);
                fields.push(mfield);
                this.m_emitter.masm.memberFields.set(fkey, mfield);
            });

            if (tdecl instanceof EntityTypeDecl) {
                const mirentity = new MIREntityTypeDecl(tkey, tdecl.srcFile, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, tdecl.isTypeACollectionEntity(), tdecl.isTypeAMapEntity(), invariants, fields, (tdecl as EntityTypeDecl).isEnum, (tdecl as EntityTypeDecl).isKey);
                this.m_emitter.masm.entityMap.set(tkey, mirentity);
            }
            else {
                const mirconcept = new MIRConceptTypeDecl(tkey, tdecl.srcFile, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, tdecl.isTypeACollectionEntity(), tdecl.isTypeAMapEntity(), invariants, fields);
                this.m_emitter.masm.conceptMap.set(tkey, mirconcept);
            }
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    processGlobal(gkey: MIRGlobalKey, gdecl: NamespaceConstDecl) {
        try {
            const emptybinds = new Map<string, ResolvedType>();

            this.m_file = gdecl.srcFile;
            const ddecltype = this.resolveAndEnsureType(gdecl.sourceLocation, gdecl.declaredType, emptybinds);
            const dtype = this.m_emitter.registerResolvedTypeReference(ddecltype);
            const vbody = this.checkExpressionAsBody(TypeEnvironment.createInitialEnvForCall(emptybinds, new Map<string, VarInfo>()), gdecl.value, ddecltype);

            const mirglobal = new MIRGlobalDecl(gdecl.sourceLocation, gdecl.srcFile, gkey, gdecl.attributes, gdecl.ns, gdecl.name, dtype, vbody);
            this.m_emitter.masm.globalDecls.set(gkey, mirglobal);
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    processConst(ckey: MIRConstKey, containingDecl: OOPTypeDecl, cdecl: StaticMemberDecl, binds: Map<string, ResolvedType>) {
        try {
            this.m_file = cdecl.srcFile;
            const enclosingType = MIRKeyGenerator.generateTypeKey(containingDecl, binds);
            const ddecltype = this.resolveAndEnsureType(cdecl.sourceLocation, cdecl.declaredType, binds);
            const dtype = this.m_emitter.registerResolvedTypeReference(ddecltype);
            let vbody: MIRBody | undefined = undefined;
            if (cdecl.value !== undefined) {
                vbody = this.checkExpressionAsBody(TypeEnvironment.createInitialEnvForCall(binds, new Map<string, VarInfo>()), cdecl.value, ddecltype);
            }

            const mirconst = new MIRConstDecl(cdecl.sourceLocation, cdecl.srcFile, ckey, cdecl.attributes, cdecl.name, enclosingType, dtype, vbody);
            this.m_emitter.masm.constDecls.set(ckey, mirconst);
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    private processInvokeInfo(sinfo: SourceInfo, invoke: InvokeDecl, binds: Map<string, ResolvedType>): { terms: Map<string, MIRType>, params: MIRFunctionParameter[], orname: string | undefined, ortype: MIREntityType | undefined, rtype: MIRType, preconds: MIRBody[], postconds: MIRBody[], mbody: MIRBody | undefined } {
        this.checkInvokeDecl(sinfo, invoke, binds);

        let terms = new Map<string, MIRType>();
        invoke.terms.forEach((term) => terms.set(term.name, this.m_emitter.registerResolvedTypeReference(binds.get(term.name) as ResolvedType)));

        let cargs = new Map<string, VarInfo>();
        let argsNames: string[] = [];
        let params: MIRFunctionParameter[] = [];
        invoke.params.forEach((p) => {
            const pdecltype = this.resolveAndEnsureType(sinfo, p.type, binds);
            const ptype = p.isOptional ? this.m_assembly.typeUnion([pdecltype, this.m_assembly.getSpecialNoneType()]) : pdecltype;
            cargs.set(p.name, new VarInfo(ptype, true, true, ptype));
            argsNames.push(p.name);

            const mtype = this.m_emitter.registerResolvedTypeReference(pdecltype);
            params.push(new MIRFunctionParameter(p.name, mtype, p.isOptional));
        });

        let optRestName: string | undefined = undefined;
        let optRestType: MIREntityType | undefined = undefined;
        if (invoke.optRestType !== undefined) {
            const rtype = this.resolveAndEnsureType(sinfo, invoke.optRestType, binds);
            cargs.set(invoke.optRestName as string, new VarInfo(rtype, true, true, rtype));
            argsNames.push(invoke.optRestName as string);

            optRestName = invoke.optRestName as string;
            optRestType = this.m_emitter.registerResolvedTypeReference(rtype).options[0] as MIREntityType;
        }

        const resolvedResult = this.resolveAndEnsureType(sinfo, invoke.resultType, binds);
        const resultType = this.m_emitter.registerResolvedTypeReference(resolvedResult);

        const preargs = new Map<string, VarInfo>(cargs);
        const preconds = invoke.preconditions.map((pre) => {
            const preenv = TypeEnvironment.createInitialEnvForCall(binds, preargs);
            return this.checkExpressionAsBody(preenv, pre, this.m_assembly.getSpecialBoolType());
        });

        const postargs = new Map<string, VarInfo>(cargs).set("_return_", new VarInfo(resolvedResult, true, true, resolvedResult));
        const postconds = invoke.postconditions.map((post) => {
            const postenv = TypeEnvironment.createInitialEnvForCall(binds, postargs);
            return this.checkExpressionAsBody(postenv, post, this.m_assembly.getSpecialBoolType());
        });

        const env = TypeEnvironment.createInitialEnvForCall(binds, cargs);
        const mbody = this.checkBody(env, invoke.body as BodyImplementation, argsNames, [], this.resolveAndEnsureType(sinfo, invoke.resultType, binds));

        return { terms: terms, params: params, orname: optRestName, ortype: optRestType, rtype: resultType, preconds: preconds, postconds: postconds, mbody: mbody };
    }

    processNamespaceFunction(fkey: MIRFunctionKey, f: NamespaceFunctionDecl, binds: Map<string, ResolvedType>) {
        try {
            this.m_file = f.srcFile;
            const invinfo = this.processInvokeInfo(f.sourceLocation, f.invoke, binds);

            const invoke = MIRInvokeDecl.createStaticInvokeDecl(f.sourceLocation, f.srcFile, invinfo.terms, invinfo.params, invinfo.orname, invinfo.ortype, invinfo.rtype, invinfo.preconds, invinfo.postconds, invinfo.mbody);

            const mirfunc = new MIRFunctionDecl(f.sourceLocation, f.srcFile, fkey, f.attributes, f.ns, f.name, invoke);
            this.m_emitter.masm.functionDecls.set(fkey, mirfunc);
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    processLambdaFunction(lkey: MIRLambdaKey, invoke: InvokeDecl, captured: Map<string, ResolvedType>, binds: Map<string, ResolvedType>, rsig: ResolvedFunctionAtomType) {
        try {
            this.m_file = invoke.srcFile;
            let captureEnv = new Map<string, VarInfo>();
            let captureNames: string[] = [];
            let captureInfo = new Map<string, MIRType>();
            captured.forEach((v, k) => {
                captureEnv.set(k, new VarInfo(v, true, true, v));
                captureNames.push(k);

                const ci = this.m_emitter.registerResolvedTypeReference(v);
                captureInfo.set(k, ci);
            });

            this.raiseErrorIf(invoke.sourceLocation, invoke.optRestType !== undefined && invoke.params.some((param) => param.isOptional), "Cannot have optional and rest parameters in an invocation signature");
            const allNames = new Set<string>();
            if (invoke.optRestName !== undefined && invoke.optRestName !== "_") {
                allNames.add(invoke.optRestName);
            }
            for (let i = 0; i < invoke.params.length; ++i) {
                if (invoke.params[i].name !== "_") {
                    this.raiseErrorIf(invoke.sourceLocation, allNames.has(invoke.params[i].name), `Duplicate name in invocation signature paramaters "${invoke.params[i].name}"`);
                    allNames.add(invoke.params[i].name);
                }
            }

            const firstOptIndex = invoke.params.findIndex((param) => param.isOptional);
            if (firstOptIndex !== -1) {
                for (let i = firstOptIndex; i < invoke.params.length; ++i) {
                    this.raiseErrorIf(invoke.sourceLocation, !invoke.params[i].isOptional, "Cannot have required paramaters following optional parameters");
                }
            }

            let cargs = new Map<string, VarInfo>();
            let argsNames: string[] = [];
            let params: MIRFunctionParameter[] = [];
            for (let i = 0; i < invoke.params.length; ++i) {
                const pdecltype = rsig.params[i].type;
                const ptype = invoke.params[i].isOptional ? this.m_assembly.typeUnion([pdecltype, this.m_assembly.getSpecialNoneType()]) : pdecltype;
                cargs.set(invoke.params[i].name, new VarInfo(ptype, true, true, ptype));
                argsNames.push(invoke.params[i].name);

                const mtype = this.m_emitter.registerResolvedTypeReference(pdecltype);
                params.push(new MIRFunctionParameter(invoke.params[i].name, mtype, invoke.params[i].isOptional));
            }

            let optRestName: string | undefined = undefined;
            let optRestType: MIREntityType | undefined = undefined;
            if (invoke.optRestType !== undefined) {
                const rtype = rsig.optRestParamType as ResolvedType;
                cargs.set(invoke.optRestName as string, new VarInfo(rtype, true, true, rtype));
                argsNames.push(invoke.optRestName as string);

                optRestName = invoke.optRestName as string;
                optRestType = this.m_emitter.registerResolvedTypeReference(rtype).options[0] as MIREntityType;
            }

            const resolvedResult = rsig.resultType as ResolvedType;
            const resultType = this.m_emitter.registerResolvedTypeReference(resolvedResult);

            const env = TypeEnvironment.createInitialEnvForCall(binds, cargs, captureEnv);
            const mbody = this.checkBody(env, invoke.body as BodyImplementation, argsNames, captureNames, resolvedResult);

            const mirlambda = MIRInvokeDecl.createLambdaInvokeDecl(invoke.sourceLocation, invoke.srcFile, params, optRestName, optRestType, resultType, captureInfo, mbody as MIRBody);
            this.m_emitter.masm.lambdaDecls.set(lkey, mirlambda);
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    processStaticFunction(skey: MIRStaticKey, ctype: OOPTypeDecl, sfdecl: StaticFunctionDecl, binds: Map<string, ResolvedType>) {
        try {
            this.m_file = sfdecl.srcFile;
            const invinfo = this.processInvokeInfo(sfdecl.sourceLocation, sfdecl.invoke, binds);
            const invoke = MIRInvokeDecl.createStaticInvokeDecl(sfdecl.sourceLocation, sfdecl.srcFile, invinfo.terms, invinfo.params, invinfo.orname, invinfo.ortype, invinfo.rtype, invinfo.preconds, invinfo.postconds, invinfo.mbody);

            const enckey = MIRKeyGenerator.generateTypeKey(ctype, binds);
            const mirfunc = new MIRStaticDecl(sfdecl.sourceLocation, sfdecl.srcFile, skey, sfdecl.attributes, sfdecl.name, enckey, invoke);
            this.m_emitter.masm.staticDecls.set(skey, mirfunc);
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    processMethodFunction(vkey: MIRVirtualMethodKey, mkey: MIRMethodKey, ctype: OOPTypeDecl, cbinds: Map<string, ResolvedType>, mdecl: MemberMethodDecl, binds: Map<string, ResolvedType>) {
        try {
            if (this.m_emitter.masm.methodDecls.has(mkey)) {
                return;
            }

            this.m_file = mdecl.srcFile;
            const invinfo = this.processInvokeInfo(mdecl.sourceLocation, mdecl.invoke, binds);
            const invoke = MIRInvokeDecl.createMemberInvokeDecl(mdecl.sourceLocation, mdecl.srcFile, invinfo.terms, invinfo.params, invinfo.orname, invinfo.ortype, invinfo.rtype, invinfo.preconds, invinfo.postconds, invinfo.mbody);

            const enckey = MIRKeyGenerator.generateTypeKey(ctype, cbinds);
            const mirfunc = new MIRMethodDecl(mdecl.sourceLocation, mdecl.srcFile, vkey, mkey, mdecl.attributes, mdecl.name, enckey, invoke);
            this.m_emitter.masm.methodDecls.set(mkey, mirfunc);

            const tdecl = (this.m_emitter.masm.entityMap.get(enckey) || this.m_emitter.masm.conceptMap.get(enckey)) as MIROOTypeDecl;
            tdecl.memberMethods.push(mirfunc);
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }
}

export { TypeError, TypeChecker };
