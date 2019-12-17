//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ResolvedType, ResolvedTupleAtomType, ResolvedEntityAtomType, ResolvedTupleAtomTypeEntry, ResolvedRecordAtomType, ResolvedRecordAtomTypeEntry, ResolvedAtomType, ResolvedConceptAtomType, ResolvedFunctionType, ResolvedConceptAtomTypeEntry, ResolvedFunctionTypeParam } from "../ast/resolved_type";
import { Assembly, NamespaceConstDecl, OOPTypeDecl, StaticMemberDecl, EntityTypeDecl, StaticFunctionDecl, InvokeDecl, MemberFieldDecl, NamespaceFunctionDecl, TemplateTermDecl, OOMemberLookupInfo, MemberMethodDecl, ConceptTypeDecl } from "../ast/assembly";
import { TypeEnvironment, ExpressionReturnResult, VarInfo, FlowTypeTruthValue } from "./type_environment";
import { TypeSignature, TemplateTypeSignature, NominalTypeSignature, AutoTypeSignature } from "../ast/type_signature";
import { Expression, ExpressionTag, LiteralTypedStringExpression, LiteralTypedStringConstructorExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, NamedArgument, ConstructorPrimaryExpression, ConstructorPrimaryWithFactoryExpression, ConstructorTupleExpression, ConstructorRecordExpression, Arguments, PositionalArgument, CallNamespaceFunctionExpression, CallStaticFunctionExpression, PostfixOp, PostfixOpTag, PostfixAccessFromIndex, PostfixProjectFromIndecies, PostfixAccessFromName, PostfixProjectFromNames, PostfixInvoke, PostfixProjectFromType, PostfixModifyWithIndecies, PostfixModifyWithNames, PostfixStructuredExtend, PrefixOp, BinOpExpression, BinEqExpression, BinCmpExpression, LiteralNoneExpression, BinLogicExpression, NonecheckExpression, CoalesceExpression, SelectExpression, VariableDeclarationStatement, VariableAssignmentStatement, IfElseStatement, Statement, StatementTag, BlockStatement, ReturnStatement, LiteralBoolExpression, LiteralIntegerExpression, LiteralStringExpression, BodyImplementation, AssertStatement, CheckStatement, DebugStatement, StructuredVariableAssignmentStatement, StructuredAssignment, RecordStructuredAssignment, IgnoreTermStructuredAssignment, ConstValueStructuredAssignment, VariableDeclarationStructuredAssignment, VariableAssignmentStructuredAssignment, TupleStructuredAssignment, MatchStatement, MatchGuard, WildcardMatchGuard, TypeMatchGuard, StructureMatchGuard, AbortStatement, YieldStatement, IfExpression, MatchExpression, BlockStatementExpression, ConstructorPCodeExpression, PCodeInvokeExpression, ExpOrExpression } from "../ast/body";
import { PCode, MIREmitter, MIRKeyGenerator } from "../compiler/mir_emitter";
import { MIRTempRegister, MIRArgument, MIRConstantNone, MIRBody, MIRVirtualMethodKey, MIRRegisterArgument, MIRVariable, MIRNominalTypeKey, MIRConstantKey, MIRInvokeKey, MIRResolvedTypeKey, MIRBodyKey, MIRFieldKey } from "../compiler/mir_ops";
import { SourceInfo } from "../ast/parser";
import { MIREntityTypeDecl, MIRConceptTypeDecl, MIRFieldDecl, MIRInvokeDecl, MIRFunctionParameter, MIRType, MIROOTypeDecl, MIRConstantDecl, MIRPCode, MIRInvokePrimitiveDecl, MIRInvokeBodyDecl, MIRTupleType, MIRTupleTypeEntry } from "../compiler/mir_assembly";

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
    argtype: ResolvedType | ResolvedFunctionType,
    expando: boolean,
    ref: string | undefined,
    pcode: PCode | undefined,
    treg: MIRTempRegister
};

type FilledLocation = {
    vtype: ResolvedType | ResolvedFunctionType,
    mustDef: boolean,
    ref: string | undefined,
    pcode: PCode | undefined,
    trgt: MIRArgument
};

class TypeChecker {
    private readonly m_assembly: Assembly;

    private readonly m_doInvariantCheck: boolean;
    private readonly m_doPrePostCheck: boolean;
    private readonly m_doAssertCheck: boolean;

    private m_file: string;
    private m_errors: [string, number, string][];

    private m_emitEnabled: boolean;
    private readonly m_emitter: MIREmitter;

    private readonly AnySplitMethods = ["is", "isSome", "isNone"];

    constructor(assembly: Assembly, emitEnabled: boolean, emitter: MIREmitter, doInvariantCheck: boolean, doPrePostCheck: boolean, doAssertCheck: boolean) {
        this.m_assembly = assembly;

        this.m_doInvariantCheck = doInvariantCheck;
        this.m_doPrePostCheck = doPrePostCheck;
        this.m_doAssertCheck = doAssertCheck;

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

    private resolveAndEnsureTypeOnly(sinfo: SourceInfo, ttype: TypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const rtype = this.m_assembly.normalizeTypeOnly(ttype, binds);
        this.raiseErrorIf(sinfo, rtype.isEmptyType(), "Bad type signature");

        return rtype;
    }

    private checkTemplateTypes(sinfo: SourceInfo, terms: TemplateTermDecl[], binds: Map<string, ResolvedType>, optTypeRestrict?: [string, ResolvedType][]) {
        const boundsok = terms.every((t) => this.m_assembly.subtypeOf(binds.get(t.name) as ResolvedType, this.resolveAndEnsureTypeOnly(sinfo, t.ttype, new Map<string, ResolvedType>())));
        this.raiseErrorIf(sinfo, !boundsok, "Template instantiation does not satisfy specified bounds");

        if (optTypeRestrict !== undefined) {
            const restrictok = optTypeRestrict.every((r) => this.m_assembly.subtypeOf(binds.get(r[0]) as ResolvedType, r[1]));
            this.raiseErrorIf(sinfo, !restrictok, "Violates type restriction in instantiation");
        }
    }

    private checkInvokeDecl(sinfo: SourceInfo, invoke: InvokeDecl, invokeBinds: Map<string, ResolvedType>, pcodes: PCode[]) {
        this.raiseErrorIf(sinfo, invoke.optRestType !== undefined && invoke.params.some((param) => param.isOptional), "Cannot have optional and rest parameters in an invocation signature");

        this.raiseErrorIf(sinfo, invoke.recursive === "no" && pcodes.some((pc) => pc.code.recursive === "yes"), "Recursive decl does not match use");

        const allNames = new Set<string>();
        if (invoke.optRestName !== undefined && invoke.optRestName !== "_") {
            allNames.add(invoke.optRestName);
        }
        for (let i = 0; i < invoke.params.length; ++i) {
            if (invoke.params[i].name !== "_") {
                this.raiseErrorIf(sinfo, allNames.has(invoke.params[i].name), `Duplicate name in invocation signature paramaters "${invoke.params[i].name}"`);
                allNames.add(invoke.params[i].name);
            }
            const rtype = this.m_assembly.normalizeTypeGeneral(invoke.params[i].type, invokeBinds);
            this.raiseErrorIf(sinfo, rtype instanceof ResolvedType && rtype.isEmptyType(), "Bad type signature");
        }

        const firstOptIndex = invoke.params.findIndex((param) => param.isOptional);
        if (firstOptIndex === -1) {
            return;
        }

        for (let i = firstOptIndex; i < invoke.params.length; ++i) {
            this.raiseErrorIf(sinfo, !invoke.params[i].isOptional, "Cannot have required paramaters following optional parameters");
        }

        if (invoke.optRestType !== undefined) {
            this.resolveAndEnsureTypeOnly(sinfo, invoke.optRestType, invokeBinds);
        }
        this.resolveAndEnsureTypeOnly(sinfo, invoke.resultType, invokeBinds);
    }

    private checkPCodeDecl(sinfo: SourceInfo, fsig: ResolvedFunctionType, rec: "yes" | "no" | "cond") {
        this.raiseErrorIf(sinfo, fsig.optRestParamType !== undefined && fsig.params.some((param) => param.isOptional), "Cannot have optional and rest parameters in an invocation signature");
        this.raiseErrorIf(sinfo, rec === "no" && fsig.recursive === "yes", "Recursive decl does not match use");

        const allNames = new Set<string>();
        if (fsig.optRestParamName !== undefined && fsig.optRestParamName !== "_") {
            allNames.add(fsig.optRestParamName);
        }
        for (let i = 0; i < fsig.params.length; ++i) {
            if (fsig.params[i].name !== "_") {
                this.raiseErrorIf(sinfo, allNames.has(fsig.params[i].name), `Duplicate name in invocation signature paramaters "${fsig.params[i].name}"`);
                allNames.add(fsig.params[i].name);
            }
        }

        const firstOptIndex = fsig.params.findIndex((param) => param.isOptional);
        if (firstOptIndex === -1) {
            return;
        }

        for (let i = firstOptIndex; i < fsig.params.length; ++i) {
            this.raiseErrorIf(sinfo, !fsig.params[i].isOptional, "Cannot have required paramaters following optional parameters");
        }
    }

    private checkRecursion(sinfo: SourceInfo, fsig: ResolvedFunctionType, pcodes: PCode[], crec: "yes" | "no" | "cond") {
        if ((fsig.recursive === "no" && crec === "no") || (fsig.recursive === "yes" && crec === "yes")) {
            return;
        }

        let sigr = fsig.recursive;
        if (sigr === "cond") {
            sigr = pcodes.some((pc) => pc.code.recursive === "yes") ? "yes" : "no";
        }

        let callr = crec;
        if (callr === "cond") {
            callr = pcodes.some((pc) => pc.code.recursive === "yes") ? "yes" : "no";
        }

        this.raiseErrorIf(sinfo, (sigr === "yes" && callr === "no") || (sigr === "no" && callr === "yes"), "Mismatched recursive annotations on call");
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

        const bothStringOf = (lhs.idStr.startsWith("NSCore::StringOf<") && rhs.idStr.startsWith("NSCore::StringOf<"));
        if (bothStringOf) {
            return this.m_assembly.subtypeOf(lhs, rhs) || this.m_assembly.subtypeOf(rhs, lhs); //types are compatible
        }

        const bothEnum = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialEnumType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialEnumType()));
        const bothCustomKey = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialCustomKeyType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialCustomKeyType()));

        if (bothEnum || bothCustomKey) {
            return this.m_assembly.subtypeOf(lhs, rhs) && this.m_assembly.subtypeOf(rhs, lhs); //types are equal
        }

        const lhskeytype = lhs.idStr === "NSCore::KeyType" && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialKeyTypeConcept());
        const rhskeytype = this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialKeyTypeConcept()) && rhs.idStr === "NSCore::KeyType";
        if (lhskeytype || rhskeytype) {
            return true;
        }

        return false;
    }

    private checkValueLess(lhs: ResolvedType, rhs: ResolvedType): boolean {
        const bothInt = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialIntType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialIntType()));
        if (bothInt) {
            return true;
        }

        return false;
    }

    private getInfoForLoadFromIndex(rtype: ResolvedType, idx: number): ResolvedType {
        const options = rtype.options.map((atom) => {
            if (atom instanceof ResolvedEntityAtomType) {
                return this.m_assembly.getSpecialAnyType();
            }

            const tatom = atom as ResolvedTupleAtomType;
            if (idx < tatom.types.length) {
                if (!tatom.types[idx].isOptional) {
                    return tatom.types[idx].type;
                }
                else {
                    return this.m_assembly.typeUnion([tatom.types[idx].type, this.m_assembly.getSpecialNoneType()]);
                }
            }
            else {
                return this.m_assembly.getSpecialNoneType();
            }
        });

        return this.m_assembly.typeUnion(options);
    }

    private getInfoForLoadFromPropertyName(rtype: ResolvedType, pname: string): ResolvedType {
        const options = rtype.options.map((atom) => {
            if (atom instanceof ResolvedEntityAtomType) {
                return this.m_assembly.getSpecialAnyType();
            }

            const ratom = atom as ResolvedRecordAtomType;
            const tidx = ratom.entries.findIndex((re) => re.name === pname);
            if (tidx !== -1) {
                if (!ratom.entries[tidx].isOptional) {
                    return ratom.entries[tidx].type;
                }
                else {
                    return this.m_assembly.typeUnion([ratom.entries[tidx].type, this.m_assembly.getSpecialNoneType()]);
                }
            }
            else {
                return this.m_assembly.getSpecialNoneType();
            }
        });

        return this.m_assembly.typeUnion(options);
    }

    private projectTupleAtom(sinfo: SourceInfo, opt: ResolvedAtomType, ptype: ResolvedTupleAtomType): ResolvedType {
        this.raiseErrorIf(sinfo, !(opt instanceof ResolvedTupleAtomType), "Cannot project over 'Tuple' type");
        const tuple = opt as ResolvedTupleAtomType;

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
            }
        }

        return ResolvedType.createSingle(ResolvedTupleAtomType.create(tentries));
    }

    private projectRecordAtom(sinfo: SourceInfo, opt: ResolvedAtomType, ptype: ResolvedRecordAtomType): ResolvedType {
        this.raiseErrorIf(sinfo, !(opt instanceof ResolvedRecordAtomType), "Cannot project over 'Record' type");
        const record = opt as ResolvedRecordAtomType;

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
            }
        }

        return ResolvedType.createSingle(ResolvedRecordAtomType.create(rentries));
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
                const ftype = this.resolveAndEnsureTypeOnly(sinfo, (finfo.decl as MemberFieldDecl).declaredType, finfo.binds);
                return new ResolvedRecordAtomTypeEntry(f, ftype, false);
            });

            return ResolvedType.createSingle(ResolvedRecordAtomType.create(oentries));
        });

        return rentries;
    }

    private updateTupleIndeciesAtom(sinfo: SourceInfo, t: ResolvedAtomType, updates: [number, ResolvedType][]): ResolvedType {
        this.raiseErrorIf(sinfo, !(t instanceof ResolvedTupleAtomType), "Cannot update on 'Tuple' type");
        const tuple = t as ResolvedTupleAtomType;

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
                        tentries.push(new ResolvedTupleAtomTypeEntry(this.m_assembly.getSpecialNoneType(), false));
                    }
                }
            }
            tentries[update[0]] = new ResolvedTupleAtomTypeEntry(update[1], false);
        }

        return ResolvedType.createSingle(ResolvedTupleAtomType.create(tentries));
    }

    private updateNamedPropertiesAtom(sinfo: SourceInfo, t: ResolvedAtomType, updates: [string, ResolvedType][]): ResolvedType {
        this.raiseErrorIf(sinfo, !(t instanceof ResolvedRecordAtomType), "Cannot update on 'Record' type");
        const record = t as ResolvedRecordAtomType;

        let rentries: ResolvedRecordAtomTypeEntry[] = [...record.entries];
        for (let i = 0; i < updates.length; ++i) {
            const update = updates[i];
            const idx = rentries.findIndex((e) => e.name === update[0]);
            rentries[idx !== -1 ? idx : rentries.length] = new ResolvedRecordAtomTypeEntry(update[0], update[1], false);
        }

        return ResolvedType.createSingle(ResolvedRecordAtomType.create(rentries));
    }

    private appendIntoTupleAtom(sinfo: SourceInfo, t: ResolvedTupleAtomType, merge: ResolvedAtomType): ResolvedType {
        this.raiseErrorIf(sinfo, !(t instanceof ResolvedTupleAtomType), "Cannot append on 'Tuple' type");
        const tuple = merge as ResolvedTupleAtomType;

        let tentries: ResolvedTupleAtomTypeEntry[] = [];
        if (t.types.some((entry) => entry.isOptional)) {
            this.raiseError(sinfo, "Appending to tuple with optional entries creates ambigious result tuple");
        }
        else {
            //just copy everything along
            tentries = [...t.types, ...tuple.types];
        }

        return ResolvedType.createSingle(ResolvedTupleAtomType.create(tentries));
    }

    private mergeIntoRecordAtom(sinfo: SourceInfo, t: ResolvedRecordAtomType, merge: ResolvedAtomType): ResolvedType {
        this.raiseErrorIf(sinfo, !(t instanceof ResolvedRecordAtomType), "Cannot merge with 'Record' type");
        const record = merge as ResolvedRecordAtomType;

        let rentries: ResolvedRecordAtomTypeEntry[] = [...t.entries];
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

        return ResolvedType.createSingle(ResolvedRecordAtomType.create(rentries));
    }

    private checkTypeOkForTupleExpando(sinfo: SourceInfo, rtype: ResolvedType): [number, number] {
        const tslist = rtype.options.map((opt) => {
            this.raiseErrorIf(sinfo, !(opt instanceof ResolvedTupleAtomType), "Cannot expando on 'Tuple' type argument");
            return opt as ResolvedTupleAtomType;
        });
        const reqlen = tslist.reduce((acc, v) => Math.min(acc, v.types.filter((te) => !te.isOptional).length), Number.MAX_SAFE_INTEGER);
        const tlen = tslist.reduce((acc, v) => Math.max(acc, v.types.length), 0);

        return [reqlen, tlen];
    }

    private checkTypeOkForRecordExpando(sinfo: SourceInfo, rtype: ResolvedType): [Set<string>, Set<string>] {
        const rslist = rtype.options.map((opt) => {
            this.raiseErrorIf(sinfo, !(opt instanceof ResolvedRecordAtomType), "Cannot expando on 'Record' type argument");
            return opt as ResolvedRecordAtomType;
        });

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

        return [reqNames, allNames];
    }

    private checkPCodeExpression(env: TypeEnvironment, exp: ConstructorPCodeExpression, expectedFunction?: ResolvedFunctionType): PCode {
        this.raiseErrorIf(exp.sinfo, exp.isAuto && expectedFunction === undefined, "Could not infer auto function type");

        const ltypetry = exp.isAuto ? expectedFunction : this.m_assembly.normalizeTypeFunction(exp.invoke.generateSig(), env.terms);
        this.raiseErrorIf(exp.sinfo, ltypetry === undefined, "Invalid lambda type");

        let captured = new Map<string, MIRRegisterArgument>();
        let capturedMap: Map<string, ResolvedType> = new Map<string, ResolvedType>();

        let captures: string[] = [];
        exp.invoke.captureSet.forEach((v) => captures.push(v));
        captures.sort();

        captures.forEach((v) => {
            const vinfo = env.lookupVar(v) as VarInfo;

            this.raiseErrorIf(exp.sinfo, vinfo.declaredType instanceof ResolvedFunctionType, "Cannot capture function typed argument");

            captured.set(v, new MIRVariable(v));
            capturedMap.set(v, vinfo.flowType);
        });

        this.m_emitter.registerPCode(exp.invoke, ltypetry as ResolvedFunctionType, env.terms, [...capturedMap].sort((a, b) => a[0].localeCompare(b[0])));

        return {code: exp.invoke, scope: env.scope, captured: capturedMap, ftype: ltypetry as ResolvedFunctionType};
    }

    private checkArgumentsEvaluationWSig(env: TypeEnvironment, sig: ResolvedFunctionType, args: Arguments, optSelfValue: [ResolvedType, MIRTempRegister] | undefined, refallowed: boolean): ExpandedArgument[] {
        let eargs: ExpandedArgument[] = [];

        if (optSelfValue !== undefined) {
            eargs.push({ name: "this", argtype: optSelfValue[0], ref: undefined, expando: false, pcode: undefined, treg: optSelfValue[1] });
        }

        const skipthisidx = optSelfValue !== undefined ? 1 : 0;
        const noExpando = args.argList.every((arg) => !(arg instanceof PositionalArgument) || !arg.isSpread);
        const firstNameIdx = sig.params.findIndex((p) => args.argList.some((arg) => arg instanceof NamedArgument && arg.name !== "_" && arg.name === p.name));

        for (let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i];
            const treg = this.m_emitter.bodyEmitter.generateTmpRegister();

            this.raiseErrorIf(arg.value.sinfo, arg.isRef && !refallowed, "Cannot use ref params in this call position");
            this.raiseErrorIf(arg.value.sinfo, arg.isRef && arg instanceof PositionalArgument && arg.isSpread, "Cannot use ref on spread argument");

            if (arg.value instanceof ConstructorPCodeExpression) {
                const oftype = (noExpando && (firstNameIdx === -1 || i < firstNameIdx) && i < sig.params.length && !sig.params[i].isOptional) ? sig.params[i + skipthisidx].type : this.m_assembly.getSpecialAnyType();
                this.raiseErrorIf(arg.value.sinfo, !(oftype instanceof ResolvedFunctionType), "Must have function type for function arg");
                this.raiseErrorIf(arg.value.sinfo, arg.isRef, "Cannot use ref params on function argument");

                const pcode = this.checkPCodeExpression(env, arg.value, oftype as ResolvedFunctionType);

                if (arg instanceof NamedArgument) {
                    eargs.push({ name: arg.name, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                }
                else {
                    this.raiseErrorIf(arg.value.sinfo, (arg as PositionalArgument).isSpread, "Cannot have spread on pcode argument");

                    eargs.push({ name: undefined, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                }
            }
            else if (arg.value instanceof AccessVariableExpression && env.pcodes.has(arg.value.name)) {
                const oftype = (noExpando && (firstNameIdx === -1 || i < firstNameIdx) && i < sig.params.length && !sig.params[i].isOptional) ? sig.params[i + skipthisidx].type : this.m_assembly.getSpecialAnyType();
                this.raiseErrorIf(arg.value.sinfo, !(oftype instanceof ResolvedFunctionType), "Must have function type for function arg");
                this.raiseErrorIf(arg.value.sinfo, arg.isRef, "Cannot use ref params on function argument");

                const pcode =  (env.pcodes.get(arg.value.name) as { pcode: PCode, captured: string[] }).pcode;

                if (arg instanceof NamedArgument) {
                    eargs.push({ name: arg.name, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                }
                else {
                    this.raiseErrorIf(arg.value.sinfo, (arg as PositionalArgument).isSpread, "Cannot have spread on pcode argument");

                    eargs.push({ name: undefined, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                }
            }
            else {
                if (arg.isRef) {
                    this.raiseErrorIf(arg.value.sinfo, !(arg.value instanceof AccessVariableExpression), "Can only ref on variable names");

                    const rvname = (arg.value as AccessVariableExpression).name;
                    this.raiseErrorIf(arg.value.sinfo, env.lookupVar(rvname) === null, "Variable name is not defined");

                    this.checkExpression(env, arg.value, treg);
                    const earg = (env.lookupVar(rvname) as VarInfo).declaredType;

                    if (arg instanceof NamedArgument) {
                        eargs.push({ name: arg.name, argtype: earg, ref: rvname, expando: false, pcode: undefined, treg: treg });
                    }
                    else {
                        eargs.push({ name: undefined, argtype: earg, ref: rvname, expando: false, pcode: undefined, treg: treg });
                    }
                }
                else {
                    const earg = this.checkExpression(env, arg.value, treg).getExpressionResult().etype;

                    if (arg instanceof NamedArgument) {
                        eargs.push({ name: arg.name, argtype: earg, ref: undefined, expando: false, pcode: undefined, treg: treg });
                    }
                    else {
                        eargs.push({ name: undefined, argtype: earg, ref: undefined, expando: (arg as PositionalArgument).isSpread, pcode: undefined, treg: treg });
                    }
                }
            }
        }

        return eargs;
    }

    private checkArgumentsEvaluationNoSig(env: TypeEnvironment, args: Arguments): ExpandedArgument[] {
        let eargs: ExpandedArgument[] = [];

        for (let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i];
            this.raiseErrorIf(arg.value.sinfo, arg.isRef, "Cannot use ref params in this call position");
            this.raiseErrorIf(arg.value.sinfo, arg.value instanceof ConstructorPCodeExpression, "Cannot use function in this call position");

            const treg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const earg = this.checkExpression(env, arg.value, treg).getExpressionResult().etype;

            if (arg instanceof NamedArgument) {
                eargs.push({ name: arg.name, argtype: earg, ref: undefined, expando: false, treg: treg, pcode: undefined });
            }
            else {
                eargs.push({ name: undefined, argtype: earg, ref: undefined, expando: (arg as PositionalArgument).isSpread, treg: treg, pcode: undefined });
            }
        }

        return eargs;
    }

    private checkArgumentsTupleConstructor(sinfo: SourceInfo, env: TypeEnvironment, args: ExpandedArgument[], trgt: MIRTempRegister): ResolvedType {
        let targs: ResolvedType[] = [];

        for (let i = 0; i < args.length; ++i) {
            this.raiseErrorIf(sinfo, args[i].expando, "Expando parameters are not allowed in Tuple constructor");
            this.raiseErrorIf(sinfo, args[i].name !== undefined, "Named parameters are not allowed in Tuple constructor");
            this.raiseErrorIf(sinfo, args[i].ref !== undefined, "Cannot use ref params in this call position");

            targs.push(args[i].argtype as ResolvedType);
        }

        const tupleatom = ResolvedTupleAtomType.create(targs.map((targ) => new ResolvedTupleAtomTypeEntry(targ, false)));
        const rtuple = ResolvedType.createSingle(tupleatom);

        if (this.m_emitEnabled) {
            const regs = args.map((e) => e.treg);
            const tupkey = this.m_emitter.registerResolvedTypeReference(rtuple);
            this.m_emitter.bodyEmitter.emitConstructorTuple(sinfo, tupkey.trkey, regs, trgt);
        }

        return rtuple;
    }

    private checkArgumentsRecordConstructor(sinfo: SourceInfo, env: TypeEnvironment, args: ExpandedArgument[], trgt: MIRTempRegister): ResolvedType {
        let rargs: [string, ResolvedType][] = [];

        const seenNames = new Set<string>();
        for (let i = 0; i < args.length; ++i) {
            this.raiseErrorIf(sinfo, args[i].expando, "Expando parameters are not allowed in Record constructor");
            this.raiseErrorIf(sinfo, args[i].name === undefined, "Positional parameters are not allowed in Record constructor");
            this.raiseErrorIf(sinfo, args[i].ref !== undefined, "Cannot use ref params in this call position");

            this.raiseErrorIf(sinfo, seenNames.has(args[i].name as string), "Duplicate argument name in Record constructor");

            rargs.push([args[i].name as string, args[i].argtype as ResolvedType]);
        }

        const rentries = rargs.map((targ) => new ResolvedRecordAtomTypeEntry(targ[0], targ[1], false));
        const recordatom = ResolvedRecordAtomType.create(rentries);
        const rrecord = ResolvedType.createSingle(recordatom);

        if (this.m_emitEnabled) {
            const regs = args.map<[string, MIRTempRegister]>((e) => [e.name as string, e.treg]).sort((a, b) => a[0].localeCompare(b[0]));
            const regkey = this.m_emitter.registerResolvedTypeReference(rrecord);
            this.m_emitter.bodyEmitter.emitConstructorRecord(sinfo, regkey.trkey, regs, trgt);
        }

       return rrecord;
    }

    private checkArgumentsCollectionConstructor(sinfo: SourceInfo, oftype: ResolvedEntityAtomType, ctype: ResolvedType, args: ExpandedArgument[], trgt: MIRTempRegister): ResolvedType {
        for (let i = 0; i < args.length; ++i) {
            this.raiseErrorIf(sinfo, args[i].name !== undefined, "Named parameters are not allowed in Collection constructors");
            this.raiseErrorIf(sinfo, args[i].ref !== undefined, "Cannot use ref params in this call position");

            const arg = args[i];
            if (!arg.expando) {
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(arg.argtype as ResolvedType, ctype));
            }
            else {
                (arg.argtype as ResolvedType).options.forEach((opt) => {
                    this.raiseErrorIf(sinfo, !(opt instanceof ResolvedEntityAtomType) || !((opt as ResolvedEntityAtomType).object.isTypeACollectionEntity() || (opt as ResolvedEntityAtomType).object.isTypeAMapEntity()), "Can only expand other container types in container constructor");
                    const oatom = opt as ResolvedEntityAtomType;

                    if (oatom.object.isTypeACollectionEntity()) {
                        const ttype = oatom.binds.get("T") as ResolvedType;
                        this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(ttype, ctype), "Container contents not of suitable subtype");
                    }
                    else {
                        const ktype = oatom.binds.get("K") as ResolvedType;
                        const vtype = oatom.binds.get("V") as ResolvedType;
                        const tupleType = ResolvedType.createSingle(ResolvedTupleAtomType.create([new ResolvedTupleAtomTypeEntry(ktype, false), new ResolvedTupleAtomTypeEntry(vtype, false)]));
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
                if(oftype.object.name === "Set") {
                    const sdecl = oftype.object.staticFunctions.get("_cons_insert") as StaticFunctionDecl;
                    this.m_emitter.registerStaticCall(oftype.object, oftype.binds, sdecl, "_cons_insert", oftype.binds, [], []);
                }
                
                if(oftype.object.name === "Map") {
                    const sdecl = oftype.object.staticFunctions.get("_cons_insert") as StaticFunctionDecl;
                    this.m_emitter.registerStaticCall(oftype.object, oftype.binds, sdecl, "_cons_insert", oftype.binds, [], []);
                }

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

    private checkArgumentsConstructor(sinfo: SourceInfo, oftype: ResolvedEntityAtomType, args: ExpandedArgument[], trgt: MIRTempRegister): ResolvedType {
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
            this.raiseErrorIf(sinfo, args[i].ref !== undefined, "Cannot use ref params in this call position");

            if (arg.name !== undefined) {
                const fidx = fields.indexOf(arg.name);
                this.raiseErrorIf(sinfo, fidx === -1, `Entity ${oftype.idStr} does not have field named "${arg.name}"`);
                this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${arg.name}"`);

                filledLocations[fidx] = { vtype: arg.argtype as ResolvedType, mustDef: true, trgt: arg.treg };
            }
            else if (arg.expando && this.m_assembly.subtypeOf(arg.argtype as ResolvedType, this.m_assembly.getSpecialRecordConceptType())) {
                const expandInfo = this.checkTypeOkForRecordExpando(sinfo, arg.argtype as ResolvedType);
                this.raiseErrorIf(sinfo, !expandInfo[0], `Type cannot be expanded as part of Entity constructor ${arg.argtype.idStr}`);

                expandInfo[1].forEach((pname) => {
                    const fidx = fields.indexOf(pname);
                    this.raiseErrorIf(sinfo, fidx === -1, `Entity ${oftype.idStr} does not have field named "${pname}"`);
                    this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${pname}"`);

                    this.raiseErrorIf(sinfo, (fieldInfo.get(pname) as [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>])[1].value !== undefined && !expandInfo[1].has(pname), `Constructor requires "${pname}" but it is provided as an optional argument`);

                    const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                    const lvtype =  this.getInfoForLoadFromPropertyName(arg.argtype as ResolvedType, pname);
                    if (this.m_emitEnabled) {
                        const ptype = this.m_emitter.registerResolvedTypeReference(lvtype);
                        this.m_emitter.bodyEmitter.emitLoadProperty(sinfo, ptype.trkey, arg.treg, pname, etreg);
                    }

                    filledLocations[fidx] = { vtype: lvtype, mustDef: expandInfo[1].has(pname), trgt: etreg };
                });
            }
            else {
                //nop
            }
        }

        //go through names and fill out info for any that should use the default value -- raise error if any are missing
        for (let i = 0; i < fields.length; ++i) {
            const field = (fieldInfo.get(fields[i]) as [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]);
            const fieldtype = this.resolveAndEnsureTypeOnly(sinfo, field[1].declaredType, field[2]);

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

    private checkArgumentsSignature(sinfo: SourceInfo, env: TypeEnvironment, sig: ResolvedFunctionType, args: ExpandedArgument[]): { args: MIRArgument[], types: ResolvedType[], refs: string[], pcodes: PCode[], cinfo: [string, ResolvedType][] } {
        let filledLocations: FilledLocation[] = [];

        //figure out named parameter mapping first
        for (let j = 0; j < args.length; ++j) {
            const arg = args[j];
            if (arg.name !== undefined) {
                const fidx = sig.params.findIndex((param) => param.name === arg.name);
                this.raiseErrorIf(sinfo, fidx === -1, `Call does not have parameter named "${arg.name}"`);
                this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name ${arg.name}`);

                filledLocations[fidx] = { vtype: arg.argtype, mustDef: true, ref: arg.ref, pcode: arg.pcode, trgt: arg.treg };
            }
            else if (arg.expando && this.m_assembly.subtypeOf(arg.argtype as ResolvedType, this.m_assembly.getSpecialRecordConceptType())) {
                const expandInfo = this.checkTypeOkForRecordExpando(sinfo, arg.argtype as ResolvedType);
                this.raiseErrorIf(sinfo, !expandInfo[0], "Type cannot be expanded as part of call");

                expandInfo[1].forEach((pname) => {
                    const fidx = sig.params.findIndex((param) => param.name === pname);
                    this.raiseErrorIf(sinfo, fidx === -1, `Call does not have parameter named "${pname}"`);
                    this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${pname}"`);

                    this.raiseErrorIf(sinfo, !sig.params[fidx].isOptional && !expandInfo[1].has(pname), `Call requires "${pname}" but it is provided as an optional argument`);

                    const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                    const lvtype = this.getInfoForLoadFromPropertyName(arg.argtype as ResolvedType, pname);
                    if (this.m_emitEnabled) {
                        const ptype = this.m_emitter.registerResolvedTypeReference(lvtype);
                        this.m_emitter.bodyEmitter.emitLoadProperty(sinfo, ptype.trkey, arg.treg, pname, etreg);
                    }

                    filledLocations[fidx] = { vtype: lvtype, mustDef: expandInfo[1].has(pname), ref: undefined, pcode: undefined, trgt: etreg };
                });
            }
            else {
                //nop
            }
        }

        //now fill in positional parameters
        let apos = args.findIndex((ae) => ae.name === undefined && !(ae.expando && this.m_assembly.subtypeOf(ae.argtype as ResolvedType, this.m_assembly.getSpecialRecordConceptType())));
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
                filledLocations[ii] = { vtype: arg.argtype, mustDef: true, ref: arg.ref, pcode: arg.pcode, trgt: arg.treg };
                ++ii;
            }
            else {
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(arg.argtype as ResolvedType, this.m_assembly.getSpecialTupleConceptType()), "Only Tuple types can be expanded as positional arguments");
                const expandInfo = this.checkTypeOkForTupleExpando(sinfo, arg.argtype as ResolvedType);

                for (let ectr = 0; ectr < expandInfo[1]; ++ectr) {
                    this.raiseErrorIf(sinfo, ii >= sig.params.length, "Too many arguments as part of tuple expando and/or cannot split tuple expando (between arguments and rest)");
                    this.raiseErrorIf(sinfo, !sig.params[ii].isOptional && ectr >= expandInfo[1], `Call requires "${sig.params[ii].name}" but it is provided as an optional argument as part of tuple expando`);

                    const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                    const lvtype = this.getInfoForLoadFromIndex(arg.argtype as ResolvedType, ectr);
                    if (this.m_emitEnabled) {
                        const itype = this.m_emitter.registerResolvedTypeReference(lvtype);
                        this.m_emitter.bodyEmitter.emitLoadTupleIndex(sinfo, itype.trkey, arg.treg, ectr, etreg);
                    }

                    filledLocations[ii] = { vtype: lvtype, mustDef: ectr < expandInfo[1], ref: undefined, pcode: undefined, trgt: etreg };

                    while (filledLocations[ii] !== undefined) {
                        this.raiseErrorIf(sinfo, !filledLocations[ii].mustDef, `We have an potentially ambigious binding of an optional parameter "${sig.params[ii].name}"`);
                        ii++;
                    }
                }
            }

            apos++;
            while (apos < args.length && (args[apos].name !== undefined || (args[apos].expando && this.m_assembly.subtypeOf(args[apos].argtype as ResolvedType, this.m_assembly.getSpecialRecordConceptType())))) {
                apos++;
            }
        }

        while (filledLocations[ii] !== undefined) {
            this.raiseErrorIf(sinfo, !filledLocations[ii].mustDef, `We have an potentially ambigious binding of an optional parameter "${sig.params[ii].name}"`);
            ii++;
        }

        while (apos < args.length && (args[apos].name !== undefined || (args[apos].expando && this.m_assembly.subtypeOf(args[apos].argtype as ResolvedType, this.m_assembly.getSpecialRecordConceptType())))) {
            apos++;
        }

        if (ii < sig.params.length) {
            this.raiseErrorIf(sinfo, !sig.params[ii].isOptional, `Insufficient number of parameters -- missing value for ${sig.params[ii].name}`);
        }
        else {
            this.raiseErrorIf(sinfo, apos !== args.length && sig.optRestParamType === undefined, "Too many arguments for call");
        }

        //go through names and fill out info for any that should use the default value -- raise error if any are missing
        //check ref, pcode, and regular arg types -- plus build up emit data
        let margs: MIRArgument[] = [];
        let mtypes: ResolvedType[] = [];
        let pcodes: PCode[] = [];
        let refs: string[] = [];
        for (let j = 0; j < sig.params.length; ++j) {
            const paramtype = sig.params[j].type;
            if (filledLocations[j] === undefined) {
                this.raiseErrorIf(sinfo, !sig.params[j].isOptional, `Parameter ${sig.params[j].name} is required and must be assigned a value in constructor`);

                filledLocations[j] = { vtype: paramtype, mustDef: true, ref: undefined, pcode: undefined, trgt: new MIRConstantNone() };
            }

            if (sig.params[j].type instanceof ResolvedFunctionType) {
                this.raiseErrorIf(sinfo, filledLocations[j].pcode === undefined, `Parameter ${sig.params[j].name} expected a function`);
                this.raiseErrorIf(sinfo, !this.m_assembly.functionSubtypeOf(filledLocations[j].vtype as ResolvedFunctionType, paramtype as ResolvedFunctionType), `Parameter ${sig.params[j].name} expected function of type ${paramtype.idStr} but got ${filledLocations[j].vtype.idStr}`);

                pcodes.push(filledLocations[j].pcode as PCode);
            }
            else {
                this.raiseErrorIf(sinfo, filledLocations[j].pcode !== undefined, `Parameter ${sig.params[j].name} cannot take a function`);

                if (sig.params[j].isRef) {
                    this.raiseErrorIf(sinfo, filledLocations[j].ref === undefined, `Parameter ${sig.params[j].name} expected reference parameter`);
                    this.raiseErrorIf(sinfo, (filledLocations[j].vtype as ResolvedType).idStr !== (paramtype as ResolvedType).idStr, `Parameter ${sig.params[j].name} expected argument of type ${paramtype.idStr} but got ${filledLocations[j].vtype.idStr}`);

                    refs.push(filledLocations[j].ref as string);
                    margs.push(filledLocations[j].trgt);
                    mtypes.push(filledLocations[j].vtype as ResolvedType);
                }
                else {
                    this.raiseErrorIf(sinfo, filledLocations[j].ref !== undefined, `Parameter ${sig.params[j].name} reference parameter is not alloed in this position`);
                    this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(filledLocations[j].vtype as ResolvedType, paramtype as ResolvedType), `Parameter ${sig.params[j].name} expected argument of type ${paramtype.idStr} but got ${filledLocations[j].vtype.idStr}`);

                    margs.push(filledLocations[j].trgt);
                    mtypes.push(filledLocations[j].vtype as ResolvedType);
                }
            }
        }

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
                this.checkArgumentsCollectionConstructor(sinfo, oftype, oobinds.get("T") as ResolvedType, rargs, rtreg);
            }
            else {
                const contentstype = ResolvedType.createSingle(ResolvedTupleAtomType.create([new ResolvedTupleAtomTypeEntry(oobinds.get("K") as ResolvedType, false), new ResolvedTupleAtomTypeEntry(oobinds.get("V") as ResolvedType, false)]));
                this.checkArgumentsCollectionConstructor(sinfo, oftype, contentstype, rargs, rtreg);
            }

            margs.push(rtreg);
            mtypes.push(ResolvedType.createSingle(oftype));
        }

        //take all the pcodes and pass the "captured" variables in as arguments in alpha order
        let cinfo: [string, ResolvedType][] = [];
        if (pcodes.length !== 0) {
            let allcaptured = new Set<string>();
            pcodes.forEach((pc) => pc.captured.forEach((v, k) => allcaptured.add(k)));

            const cnames = [...allcaptured].sort();
                for (let i = 0; i < cnames.length; ++i) {
                    const vinfo = (env.lookupVar(cnames[i]) as VarInfo);
                    margs.push(new MIRVariable(vinfo.isCaptured ? this.m_emitter.bodyEmitter.generateCapturedVarName(cnames[i]) : cnames[i]));
                    mtypes.push(vinfo.flowType);

                    cinfo.push([cnames[i], vinfo.flowType]);
            }
        }

        return { args: margs, types: mtypes, refs: refs, pcodes: pcodes, cinfo: cinfo };
    }

    private generateRefInfoForCallEmit(fsig: ResolvedFunctionType, refs: string[]): [MIRType, [string, MIRType][]] {
        const rtype = this.m_emitter.registerResolvedTypeReference(fsig.resultType);
        const refinfo = refs.map((rn) => {
            const rp = fsig.params.find((p) => p.name === rn);
            const ptk = this.m_emitter.registerResolvedTypeReference((rp as ResolvedFunctionTypeParam).type as ResolvedType);
            return [rn, ptk] as [string, MIRType];
        });

        return [rtype, refinfo];
    }

    private generateRefInfoForReturnEmit(rtype: ResolvedType, env: TypeEnvironment): MIRResolvedTypeKey | undefined {
        if (env.refparams.length === 0) {
            return undefined;
        }
        else {
            const entries = [
                new ResolvedTupleAtomTypeEntry(rtype, false),
                ...env.refparams.map((rn) => new ResolvedTupleAtomTypeEntry((env.lookupVar(rn) as VarInfo).declaredType, false))
            ];

            return this.m_emitter.registerResolvedTypeReference(ResolvedType.createSingle(ResolvedTupleAtomType.create(entries))).trkey;
        }
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
        const oftype = this.resolveAndEnsureTypeOnly(sinfo, ttype, env.terms);

        //do dynamic check to see if string is valid of format
        this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(oftype, this.m_assembly.getSpecialParsableConcept()), "Type must provide 'Parsable' concept");

        const fdecltry = this.m_assembly.tryGetOOMemberDeclUnique(oftype, "static", "tryParse");
        this.raiseErrorIf(sinfo, fdecltry === undefined, `Constant value not defined for type '${oftype.idStr}'`);

        const aoftype = ResolvedType.tryGetOOTypeInfo(oftype);
        this.raiseErrorIf(sinfo, aoftype === undefined, "Can only make string type using concept or object types");

        const oodecl = (aoftype instanceof ResolvedEntityAtomType) ? (aoftype as ResolvedEntityAtomType).object : (aoftype as ResolvedConceptAtomType).conceptTypes[0].concept;
        const oobinds = (aoftype instanceof ResolvedEntityAtomType) ? (aoftype as ResolvedEntityAtomType).binds : (aoftype as ResolvedConceptAtomType).conceptTypes[0].binds;

        //ensure full string[T] type is registered
        const terms = [new TemplateTypeSignature("T")];
        const binds = new Map<string, ResolvedType>().set("T", oftype);
        const stype = this.resolveAndEnsureTypeOnly(sinfo, new NominalTypeSignature("NSCore", "StringOf", terms), binds);

        return { oftype: [oodecl, oobinds], ofresolved: oftype, stringtype: stype };
    }

    private checkCreateTypedString(env: TypeEnvironment, exp: LiteralTypedStringExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const aoftype = this.checkTypedStringCommon(exp.sinfo, env, exp.stype);

        if (this.m_emitEnabled) {
            this.m_emitter.registerTypeInstantiation(...aoftype.oftype);
            const stype = this.m_emitter.registerResolvedTypeReference(aoftype.stringtype);

            const sdecl = aoftype.oftype[0].staticFunctions.get("tryParse");
            this.raiseErrorIf(exp.sinfo, sdecl === undefined, "Missing static function 'tryParse'");
            const pfunckey = this.m_emitter.registerStaticCall(aoftype.oftype[0], aoftype.oftype[1], sdecl as StaticFunctionDecl, "tryParse", aoftype.oftype[1], [], []);

            //
            //TODO -- should emit parse checking code here
            //

            this.m_emitter.bodyEmitter.emitLoadConstTypedString(exp.sinfo, exp.value, MIRKeyGenerator.generateTypeKey(...aoftype.oftype), stype.trkey, pfunckey, trgt);
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

            const skey = this.m_emitter.registerStaticCall(aoftype.oftype[0], aoftype.oftype[1], sdecl as StaticFunctionDecl, "tryParse", aoftype.oftype[1], [], []);

            const tmpr = this.m_emitter.bodyEmitter.generateTmpRegister();
            this.m_emitter.bodyEmitter.emitLoadConstString(exp.sinfo, exp.value, tmpr);
            this.m_emitter.bodyEmitter.emitInvokeFixedFunction(this.m_emitter.masm, exp.sinfo, stype, skey, [tmpr], [], trgt);

            //
            //TODO -- should emit parse checking code here
            //
        }

        return [env.setExpressionResult(this.m_assembly, aoftype.ofresolved)];
    }

    private checkAccessNamespaceConstant(env: TypeEnvironment, exp: AccessNamespaceConstantExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        this.raiseErrorIf(exp.sinfo, !this.m_assembly.hasNamespace(exp.ns), `Namespace '${exp.ns}' is not defined`);
        const nsdecl = this.m_assembly.getNamespace(exp.ns);

        this.raiseErrorIf(exp.sinfo, !nsdecl.consts.has(exp.name), `Constant named '${exp.name}' is not defined`);
        const cdecl = nsdecl.consts.get(exp.name) as NamespaceConstDecl;

        const rtype = this.resolveAndEnsureTypeOnly(exp.sinfo, cdecl.declaredType, new Map<string, ResolvedType>());

        if (this.m_emitEnabled) {
            const gkey = this.m_emitter.registerPendingGlobalProcessing(cdecl);
            this.m_emitter.bodyEmitter.emitAccessConstant(exp.sinfo, gkey, trgt);
        }

        return [env.setExpressionResult(this.m_assembly, rtype)];
    }

    private checkAccessStaticField(env: TypeEnvironment, exp: AccessStaticFieldExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const baseType = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.stype, env.terms);

        const cdecltry = this.m_assembly.tryGetOOMemberDeclUnique(baseType, "const", exp.name);
        this.raiseErrorIf(exp.sinfo, cdecltry === undefined, `Constant value not defined for type '${baseType.idStr}'`);

        const cdecl = cdecltry as OOMemberLookupInfo;
        const rtype = this.resolveAndEnsureTypeOnly(exp.sinfo, (cdecl.decl as StaticMemberDecl).declaredType, cdecl.binds);

        if (this.m_emitEnabled) {
            this.m_emitter.registerTypeInstantiation(cdecl.contiainingType, cdecl.binds);
            const skey = this.m_emitter.registerPendingConstProcessing(cdecl.contiainingType, cdecl.decl as StaticMemberDecl, cdecl.binds);
            this.m_emitter.bodyEmitter.emitAccessConstant(exp.sinfo, skey, trgt);
        }

        return [env.setExpressionResult(this.m_assembly, rtype)];
    }

    private checkAccessVariable(env: TypeEnvironment, exp: AccessVariableExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        this.raiseErrorIf(exp.sinfo, !env.isVarNameDefined(exp.name), `Variable name '${exp.name}' is not defined`);

        if (this.m_emitEnabled) {
            if (env.getLocalVarInfo(exp.name) !== undefined) {
                this.m_emitter.bodyEmitter.emitAccessLocalVariable(exp.sinfo, exp.name, trgt);
            }
            else {
                if ((env.lookupVar(exp.name) as VarInfo).isCaptured) {
                    this.m_emitter.bodyEmitter.emitAccessArgVariable(exp.sinfo, this.m_emitter.bodyEmitter.generateCapturedVarName(exp.name), trgt);
                }
                else {
                    this.m_emitter.bodyEmitter.emitAccessArgVariable(exp.sinfo, exp.name, trgt);
                }
            }
        }

        const vinfo = env.lookupVar(exp.name) as VarInfo;
        this.raiseErrorIf(exp.sinfo, !vinfo.mustDefined, "Var may not be defined at use");

        return [env.setExpressionResult(this.m_assembly, vinfo.flowType)];
    }

    private checkConstructorPrimary(env: TypeEnvironment, exp: ConstructorPrimaryExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const ctype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.ctype, env.terms);
        const objtype = ResolvedType.tryGetOOTypeInfo(ctype);
        this.raiseErrorIf(exp.sinfo, objtype === undefined || !(objtype instanceof ResolvedEntityAtomType), "Invalid constructor type");

        const oodecl = (objtype as ResolvedEntityAtomType).object;
        const oobinds = (objtype as ResolvedEntityAtomType).binds;
        this.checkTemplateTypes(exp.sinfo, oodecl.terms, oobinds);

        const eargs = this.checkArgumentsEvaluationNoSig(env, exp.args);

        const oftype = ResolvedEntityAtomType.create(oodecl, oobinds);
        if (oodecl.isTypeACollectionEntity()) {
            return [env.setExpressionResult(this.m_assembly, this.checkArgumentsCollectionConstructor(exp.sinfo, oftype, oobinds.get("T") as ResolvedType, eargs, trgt))];
        }
        else if (oodecl.isTypeAMapEntity()) {
            const contentstype = ResolvedType.createSingle(ResolvedTupleAtomType.create([new ResolvedTupleAtomTypeEntry(oobinds.get("K") as ResolvedType, false), new ResolvedTupleAtomTypeEntry(oobinds.get("V") as ResolvedType, false)]));
            return [env.setExpressionResult(this.m_assembly, this.checkArgumentsCollectionConstructor(exp.sinfo, oftype, contentstype, eargs, trgt))];
        }
        else {
            return [env.setExpressionResult(this.m_assembly, this.checkArgumentsConstructor(exp.sinfo, oftype, eargs, trgt))];
        }
    }

    private checkConstructorPrimaryWithFactory(env: TypeEnvironment, exp: ConstructorPrimaryWithFactoryExpression, trgt: MIRTempRegister, refok: boolean): TypeEnvironment[] {
        const baseType = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.ctype, env.terms);
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

        const fsig = this.m_assembly.normalizeTypeFunction((fdecl as StaticFunctionDecl).invoke.generateSig(), binds as Map<string, ResolvedType>);
        this.raiseErrorIf(exp.sinfo, fsig === undefined, "Invalid function signature");

        const eargs = this.checkArgumentsEvaluationWSig(env, fsig as ResolvedFunctionType, exp.args, undefined, refok);
        const rargs = this.checkArgumentsSignature(exp.sinfo, env, fsig as ResolvedFunctionType, eargs);

        this.checkRecursion(exp.sinfo, fsig as ResolvedFunctionType, rargs.pcodes, exp.pragmas.recursive);

        const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        if (this.m_emitEnabled) {
            this.m_emitter.registerTypeInstantiation(oodecl, oobinds);
            const skey = this.m_emitter.registerStaticCall(oodecl, oobinds, fdecl as StaticFunctionDecl, exp.factoryName, binds as Map<string, ResolvedType>, rargs.pcodes, rargs.cinfo);

            const [frtype, refinfo] = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
            this.m_emitter.bodyEmitter.emitInvokeFixedFunction(this.m_emitter.masm, exp.sinfo, frtype, skey, rargs.args, refinfo, etreg);
        }

        const oftype = ResolvedEntityAtomType.create(oodecl, oobinds);
        const returntype = (fsig as ResolvedFunctionType).resultType;
        return [env.setExpressionResult(this.m_assembly, this.checkArgumentsConstructor(exp.sinfo, oftype, [{ name: undefined, argtype: returntype, expando: true, ref: undefined, pcode: undefined, treg: etreg }], trgt))];
    }

    private checkTupleConstructor(env: TypeEnvironment, exp: ConstructorTupleExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const eargs = this.checkArgumentsEvaluationNoSig(env, exp.args);
        return [env.setExpressionResult(this.m_assembly, this.checkArgumentsTupleConstructor(exp.sinfo, env, eargs, trgt))];
    }

    private checkRecordConstructor(env: TypeEnvironment, exp: ConstructorRecordExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const eargs = this.checkArgumentsEvaluationNoSig(env, exp.args);
        return [env.setExpressionResult(this.m_assembly, this.checkArgumentsRecordConstructor(exp.sinfo, env, eargs, trgt))];
    }

    private checkCallNamespaceFunctionExpression(env: TypeEnvironment, exp: CallNamespaceFunctionExpression, trgt: MIRTempRegister, refok: boolean): TypeEnvironment[] {
        this.raiseErrorIf(exp.sinfo, !this.m_assembly.hasNamespace(exp.ns), `Namespace '${exp.ns}' is not defined`);
        const nsdecl = this.m_assembly.getNamespace(exp.ns);

        this.raiseErrorIf(exp.sinfo, !nsdecl.functions.has(exp.name), `Function named '${exp.name}' is not defined`);
        const fdecl = nsdecl.functions.get(exp.name) as NamespaceFunctionDecl;

        const binds = this.m_assembly.resolveBindsForCall(fdecl.invoke.terms, exp.terms.targs, new Map<string, ResolvedType>(), env.terms);
        this.raiseErrorIf(exp.sinfo, binds === undefined, "Call bindings could not be resolved");

        this.checkTemplateTypes(exp.sinfo, fdecl.invoke.terms, binds as Map<string, ResolvedType>);

        const fsig = this.m_assembly.normalizeTypeFunction(fdecl.invoke.generateSig(), binds as Map<string, ResolvedType>);
        this.raiseErrorIf(exp.sinfo, fsig === undefined, "Invalid function signature");

        const eargs = this.checkArgumentsEvaluationWSig(env, fsig as ResolvedFunctionType, exp.args, undefined, refok);
        const margs = this.checkArgumentsSignature(exp.sinfo, env, fsig as ResolvedFunctionType, eargs);

        this.checkRecursion(exp.sinfo, fsig as ResolvedFunctionType, margs.pcodes, exp.pragmas.recursive);

        if (this.m_emitEnabled) {
            const ckey = this.m_emitter.registerFunctionCall(exp.ns, exp.name, fdecl, binds as Map<string, ResolvedType>, margs.pcodes, margs.cinfo);

            const [frtype, refinfo] = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, margs.refs);
            this.m_emitter.bodyEmitter.emitInvokeFixedFunction(this.m_emitter.masm, exp.sinfo, frtype, ckey, margs.args, refinfo, trgt);
        }

        return [env.setExpressionResult(this.m_assembly, this.resolveAndEnsureTypeOnly(exp.sinfo, fdecl.invoke.resultType, binds as Map<string, ResolvedType>))];
    }

    private checkCallStaticFunctionExpression(env: TypeEnvironment, exp: CallStaticFunctionExpression, trgt: MIRTempRegister, refok: boolean): TypeEnvironment[] {
        const baseType = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.ttype, env.terms);

        const fdecltry = this.m_assembly.tryGetOOMemberDeclUnique(baseType, "static", exp.name);
        this.raiseErrorIf(exp.sinfo, fdecltry === undefined, `Constant value not defined for type '${baseType.idStr}'`);

        const fdecl = fdecltry as OOMemberLookupInfo;
        const binds = this.m_assembly.resolveBindsForCall((fdecl.decl as StaticFunctionDecl).invoke.terms, exp.terms.targs, fdecl.binds, env.terms);
        this.raiseErrorIf(exp.sinfo, binds === undefined, "Call bindings could not be resolved");

        this.checkTemplateTypes(exp.sinfo, (fdecl.decl as StaticFunctionDecl).invoke.terms, binds as Map<string, ResolvedType>);

        const fsig = this.m_assembly.normalizeTypeFunction((fdecl.decl as StaticFunctionDecl).invoke.generateSig(), binds as Map<string, ResolvedType>);
        this.raiseErrorIf(exp.sinfo, fsig === undefined, "Invalid function signature");

        const eargs = this.checkArgumentsEvaluationWSig(env, fsig as ResolvedFunctionType, exp.args, undefined, refok);
        const margs = this.checkArgumentsSignature(exp.sinfo, env, fsig as ResolvedFunctionType, eargs);

        this.checkRecursion(exp.sinfo, fsig as ResolvedFunctionType, margs.pcodes, exp.pragmas.recursive);

        if (this.m_emitEnabled) {
            const isindexableop = fdecl.contiainingType.ns === "NSCore" && fdecl.contiainingType.name === "Indexable";
            const keytype = this.m_assembly.getSpecialKeyTypeConcept();
            const mirkeytype = this.m_emitter.registerResolvedTypeReference(keytype);

            if (isindexableop && exp.name === "getKey") {
                const mirargtypeinfer = this.m_emitter.registerResolvedTypeReference(margs.types[0]);

                if(this.m_assembly.subtypeOf(margs.types[0], keytype)) {
                    this.m_emitter.bodyEmitter.emitRegAssign(exp.sinfo, margs.args[0], trgt);
                }
                else {
                    //
                    // TODO: we should infer the keytype from the Indexable info to do a better emit and type inference
                    //
                    this.m_emitter.bodyEmitter.emitGetKey(exp.sinfo, mirargtypeinfer.trkey, margs.args[0], mirkeytype.trkey, trgt);
                }
            }
            else if (isindexableop && exp.name === "equal") {
                let mirargtypeinferlhs = this.m_emitter.registerResolvedTypeReference(margs.types[0]);
                let mirargtypeinferrhs = this.m_emitter.registerResolvedTypeReference(margs.types[1]);

                let lhs = margs.args[0];
                if (!this.m_assembly.subtypeOf(margs.types[0], keytype)) {
                    lhs = this.m_emitter.bodyEmitter.generateTmpRegister();
                    this.m_emitter.bodyEmitter.emitGetKey(exp.sinfo, mirargtypeinferlhs.trkey, margs.args[0], mirkeytype.trkey, lhs as MIRTempRegister);
                    mirargtypeinferlhs = mirkeytype;
                }

                let rhs = margs.args[0];
                if (!this.m_assembly.subtypeOf(margs.types[1], keytype)) {
                    rhs = this.m_emitter.bodyEmitter.generateTmpRegister();
                    this.m_emitter.bodyEmitter.emitGetKey(exp.sinfo, mirargtypeinferrhs.trkey, margs.args[1], mirkeytype.trkey, rhs as MIRTempRegister);
                    mirargtypeinferrhs = mirkeytype;
                }

                //
                // TODO: we should infer the keytype from the Indexable info to do a better emit and type inference
                //
                this.m_emitter.bodyEmitter.emitBinEq(exp.sinfo, mirargtypeinferlhs.trkey, lhs, mirargtypeinferrhs.trkey, "==", rhs, trgt);
            }
            else if (isindexableop && exp.name === "less") {
                let mirargtypeinferlhs = this.m_emitter.registerResolvedTypeReference(margs.types[0]);
                let mirargtypeinferrhs = this.m_emitter.registerResolvedTypeReference(margs.types[1]);

                let lhs = margs.args[0];
                if (!this.m_assembly.subtypeOf(margs.types[0], keytype)) {
                    lhs = this.m_emitter.bodyEmitter.generateTmpRegister();
                    this.m_emitter.bodyEmitter.emitGetKey(exp.sinfo, mirargtypeinferlhs.trkey, margs.args[0], mirkeytype.trkey, lhs as MIRTempRegister);
                    mirargtypeinferlhs = mirkeytype;
                }

                let rhs = margs.args[0];
                if (!this.m_assembly.subtypeOf(margs.types[1], keytype)) {
                    rhs = this.m_emitter.bodyEmitter.generateTmpRegister();
                    this.m_emitter.bodyEmitter.emitGetKey(exp.sinfo, mirargtypeinferrhs.trkey, margs.args[1], mirkeytype.trkey, rhs as MIRTempRegister);
                    mirargtypeinferrhs = mirkeytype;
                }

                //
                // TODO: we should infer the keytype from the Indexable info to do a better emit and type inference
                //
                this.m_emitter.bodyEmitter.emitBinCmp(exp.sinfo, mirargtypeinferlhs.trkey, lhs, mirargtypeinferrhs.trkey, "<", rhs, trgt);
            }
            else {
                this.m_emitter.registerTypeInstantiation(fdecl.contiainingType, fdecl.binds);
                const skey = this.m_emitter.registerStaticCall(fdecl.contiainingType, fdecl.binds, fdecl.decl as StaticFunctionDecl, (fdecl.decl as StaticFunctionDecl).name, binds as Map<string, ResolvedType>, margs.pcodes, margs.cinfo);

                const [frtype, refinfo] = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, margs.refs);
                this.m_emitter.bodyEmitter.emitInvokeFixedFunction(this.m_emitter.masm, exp.sinfo, frtype, skey, margs.args, refinfo, trgt);
            }
        }

        return [env.setExpressionResult(this.m_assembly, this.resolveAndEnsureTypeOnly(exp.sinfo, (fdecl.decl as StaticFunctionDecl).invoke.resultType, binds as Map<string, ResolvedType>))];
    }

    private checkPCodeInvokeExpression(env: TypeEnvironment, exp: PCodeInvokeExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const pco = env.lookupPCode(exp.pcode);
        this.raiseErrorIf(exp.sinfo, pco === undefined, "Code name not defined");
        const pcode = (pco as { pcode: PCode, captured: string[] }).pcode;
        const captured = (pco as { pcode: PCode, captured: string[] }).captured;

        const cargs = [...exp.args.argList, ...captured.map((cv) => new PositionalArgument(false, false, new AccessVariableExpression(exp.sinfo, cv)))];
        const eargs = this.checkArgumentsEvaluationWSig(env, pcode.ftype, new Arguments(cargs), undefined, false);
        const margs = this.checkArgumentsSignature(exp.sinfo, env, pcode.ftype, eargs);

        this.checkRecursion(exp.sinfo, pcode.ftype, margs.pcodes, exp.pragmas.recursive);

        if (this.m_emitEnabled) {
            const ftype = this.m_emitter.registerResolvedTypeReference((pcode as PCode).ftype.resultType);
            this.m_emitter.bodyEmitter.emitInvokeFixedFunction(this.m_emitter.masm, exp.sinfo, ftype, MIRKeyGenerator.generatePCodeKey((pcode as PCode).code), margs.args, [], trgt);
        }

        return [env.setExpressionResult(this.m_assembly, (pcode as PCode).ftype.resultType)];
    }

    private checkAccessFromIndex(env: TypeEnvironment, op: PostfixAccessFromIndex, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialTupleConceptType()), "Base of index expression must be of Tuple type");
        this.raiseErrorIf(op.sinfo, op.index < 0, "Index cannot be negative");

        const idxtype = this.getInfoForLoadFromIndex(texp, op.index);
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitLoadTupleIndex(op.sinfo, this.m_emitter.registerResolvedTypeReference(idxtype).trkey, arg, op.index, trgt);
        }

        return [env.setExpressionResult(this.m_assembly, idxtype)];
    }

    private checkProjectFromIndecies(env: TypeEnvironment, op: PostfixProjectFromIndecies, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialTupleConceptType()), "Base of index expression must be of Tuple type");
        this.raiseErrorIf(op.sinfo, op.indecies.some((idx) => idx < 0), "Index cannot be negative");

        const resultOptions = texp.options.map((opt) => {
            let ttypes = op.indecies.map((idx) => new ResolvedTupleAtomTypeEntry(this.getInfoForLoadFromIndex(ResolvedType.createSingle(opt), idx), false));
            return ResolvedType.createSingle(ResolvedTupleAtomType.create(ttypes));
        });
        const restype = this.m_assembly.typeUnion(resultOptions);

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitProjectTupleIndecies(op.sinfo, this.m_emitter.registerResolvedTypeReference(restype).trkey, arg, op.indecies, trgt);
        }

        return [env.setExpressionResult(this.m_assembly, restype)];
    }

    private checkAccessFromName(env: TypeEnvironment, op: PostfixAccessFromName, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType())) {
            const rtype = this.getInfoForLoadFromPropertyName(texp, op.name);

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitLoadProperty(op.sinfo, this.m_emitter.registerResolvedTypeReference(rtype).trkey, arg, op.name, trgt);
            }

            return [env.setExpressionResult(this.m_assembly, rtype)];
        }
        else {
            const finfo = this.m_assembly.tryGetOOMemberDeclOptions(texp, "field", op.name);
            this.raiseErrorIf(op.sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");

            const topts = (finfo.decls as OOMemberLookupInfo[]).map((info) => this.resolveAndEnsureTypeOnly(op.sinfo, (info.decl as MemberFieldDecl).declaredType, info.binds));
            const rtype = this.m_assembly.typeUnion(topts);

            if (this.m_emitEnabled) {
                const fdeclinfo = finfo.root as OOMemberLookupInfo;
                const fkey = MIRKeyGenerator.generateFieldKey(fdeclinfo.contiainingType, fdeclinfo.binds, op.name);
                this.m_emitter.bodyEmitter.emitLoadField(op.sinfo, this.m_emitter.registerResolvedTypeReference(rtype).trkey, arg, fkey, trgt);
            }

            return [env.setExpressionResult(this.m_assembly, rtype)];
        }
    }

    private checkProjectFromNames(env: TypeEnvironment, op: PostfixProjectFromNames, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType())) {
            const resultOptions = texp.options.map((opt) => {
                let ttypes = op.names.map((name) => new ResolvedRecordAtomTypeEntry(name, this.getInfoForLoadFromPropertyName(ResolvedType.createSingle(opt), name), false));

                return ResolvedType.createSingle(ResolvedRecordAtomType.create(ttypes));
            });
            const restype = this.m_assembly.typeUnion(resultOptions);

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitProjectProperties(op.sinfo, this.m_emitter.registerResolvedTypeReference(restype).trkey, arg, op.names, trgt);
            }

            return [env.setExpressionResult(this.m_assembly, restype)];
        }
        else {
            const fieldkeys = op.names.map((f) => {
                const finfo = this.m_assembly.tryGetOOMemberDeclOptions(texp, "field", f);
                this.raiseErrorIf(op.sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");

                const fdeclinfo = finfo.root as OOMemberLookupInfo;
                return MIRKeyGenerator.generateFieldKey(fdeclinfo.contiainingType, fdeclinfo.binds, f);
            });

            const resultOptions = texp.options.map((atom) => {
                const oentries = op.names.map((f) => {
                    const finfo = this.m_assembly.tryGetOOMemberDeclUnique(ResolvedType.createSingle(atom), "field", f) as OOMemberLookupInfo;
                    const ftype = this.resolveAndEnsureTypeOnly(op.sinfo, (finfo.decl as MemberFieldDecl).declaredType, finfo.binds);
                    return new ResolvedRecordAtomTypeEntry(f, ftype, false);
                });

                return ResolvedType.createSingle(ResolvedRecordAtomType.create(oentries));
            });
            const restype = this.m_assembly.typeUnion(resultOptions);

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitProjectFields(op.sinfo, this.m_emitter.registerResolvedTypeReference(restype).trkey, arg, fieldkeys, trgt);
            }

            return [env.setExpressionResult(this.m_assembly, restype)];
        }
    }

    private checkProjectFromType(env: TypeEnvironment, op: PostfixProjectFromType, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        let resultOptions: ResolvedType[] = [];
        const opType = this.resolveAndEnsureTypeOnly(op.sinfo, op.ptype, env.terms);
        this.raiseErrorIf(op.sinfo, opType.options.length !== 1, "Invalid type");

        const ptype = opType.options[0];
        if (ptype instanceof ResolvedTupleAtomType) {
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialTupleConceptType()));

            resultOptions = texp.options.map((opt) => this.projectTupleAtom(op.sinfo, opt, ptype));

            if (this.m_emitEnabled) {
                const ttype = this.m_emitter.registerResolvedTypeReference(opType);
                const resultType = this.m_emitter.registerResolvedTypeReference(this.m_assembly.typeUnion(resultOptions));
                this.m_emitter.bodyEmitter.emitProjectFromTypeTuple(op.sinfo, resultType.trkey, arg, ttype.trkey, trgt);
            }
        }
        else if (ptype instanceof ResolvedRecordAtomType) {
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType()));

            resultOptions = texp.options.map((opt) => this.projectRecordAtom(op.sinfo, opt, ptype));

            if (this.m_emitEnabled) {
                const ttype = this.m_emitter.registerResolvedTypeReference(opType);
                const resultType = this.m_emitter.registerResolvedTypeReference(this.m_assembly.typeUnion(resultOptions));
                this.m_emitter.bodyEmitter.emitProjectFromTypeRecord(op.sinfo, resultType.trkey, arg, ttype.trkey, trgt);
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
                const resultType = this.m_emitter.registerResolvedTypeReference(this.m_assembly.typeUnion(resultOptions));
                this.m_emitter.bodyEmitter.emitProjectFromTypeConcept(op.sinfo, resultType.trkey, arg, ckeys, trgt);
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
        const rtuple = this.m_assembly.typeUnion(resultOptions);

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitModifyWithIndecies(op.sinfo, this.m_emitter.registerResolvedTypeReference(rtuple).trkey, arg, updates.map<[number, MIRArgument]>((update) => [update[0], update[2]]), trgt);
        }

        return [env.setExpressionResult(this.m_assembly, rtuple)];
    }

    private checkModifyWithNames(env: TypeEnvironment, op: PostfixModifyWithNames, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        const updates = op.updates.map<[string, ResolvedType, MIRTempRegister]>((update) => {
            const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            return [update[0], this.checkExpression(env, update[1], etreg).getExpressionResult().etype, etreg];
        });

        if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType())) {
            const resultOptions = texp.options.map((opt) => this.updateNamedPropertiesAtom(op.sinfo, opt, updates.map<[string, ResolvedType]>((update) => [update[0], update[1]])));
            const rrecord = this.m_assembly.typeUnion(resultOptions);

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitModifyWithProperties(op.sinfo, this.m_emitter.registerResolvedTypeReference(rrecord).trkey, arg, updates.map<[string, MIRArgument]>((update) => [update[0], update[2]]), trgt);
            }

            return [env.setExpressionResult(this.m_assembly, rrecord)];
        }
        else {
            const fieldupdates = updates.map<[MIRFieldKey, MIRTempRegister]>((update) => {
                const finfo = this.m_assembly.tryGetOOMemberDeclOptions(texp, "field", update[0]);
                this.raiseErrorIf(op.sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");

                const fdeclinfo = finfo.root as OOMemberLookupInfo;
                const decltype = this.m_assembly.normalizeTypeGeneral((fdeclinfo.decl as MemberFieldDecl).declaredType, fdeclinfo.binds) as ResolvedType;
                this.raiseErrorIf(op.sinfo, decltype.isEmptyType() || !this.m_assembly.subtypeOf(update[1], decltype));

                return [MIRKeyGenerator.generateFieldKey(fdeclinfo.contiainingType, fdeclinfo.binds, update[0]), update[2]];
            });
            
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitModifyWithFields(op.sinfo, this.m_emitter.registerResolvedTypeReference(texp).trkey, arg, fieldupdates, trgt);
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
                return mergeValue.options.map((tmerge) => this.appendIntoTupleAtom(op.sinfo, topt as ResolvedTupleAtomType, tmerge));
            }));
            const resulttype = this.m_assembly.typeUnion(resultOptions);

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitStructuredExtendTuple(op.sinfo, this.m_emitter.registerResolvedTypeReference(resulttype).trkey, arg, etreg, trgt);
            }

            return [env.setExpressionResult(this.m_assembly, resulttype)];
        }
        else if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType())) {
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(mergeValue, this.m_assembly.getSpecialRecordConceptType()), "Must be two Records to merge");

            resultOptions = resultOptions.concat(...texp.options.map((topt) => {
                return mergeValue.options.map((tmerge) => this.mergeIntoRecordAtom(op.sinfo, topt as ResolvedRecordAtomType, tmerge));
            }));
            const resulttype = this.m_assembly.typeUnion(resultOptions);

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitStructuredExtendRecord(op.sinfo, this.m_emitter.registerResolvedTypeReference(resulttype).trkey, arg, etreg, trgt);
            }

            return [env.setExpressionResult(this.m_assembly, this.m_assembly.typeUnion(resultOptions))];
        }
        else {
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialObjectConceptType()), "Can only merge onto Tuples/Records/Objects");
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(mergeValue, this.m_assembly.getSpecialRecordConceptType()), "Must be Record to merge into Object");

            let allnames = new Map<string, ResolvedType>();
            mergeValue.options.forEach((opt) => {
                const record = opt as ResolvedRecordAtomType;
                record.entries.forEach((entry) => {
                    allnames.set(entry.name, allnames.has(entry.name) ? entry.type : this.m_assembly.typeUnion([entry.type, allnames.get(entry.name) as ResolvedType]));
                });
            });

            const namel = [...allnames].map((np) => np[0]).sort();
            const fieldResolves = namel.map<[string, MIRFieldKey]>((pname) => {
                const finfo = this.m_assembly.tryGetOOMemberDeclOptions(texp, "field", pname);
                this.raiseErrorIf(op.sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");

                const fdeclinfo = finfo.root as OOMemberLookupInfo;
                const decltype = this.m_assembly.normalizeTypeGeneral((fdeclinfo.decl as MemberFieldDecl).declaredType, fdeclinfo.binds) as ResolvedType;
                this.raiseErrorIf(op.sinfo, decltype.isEmptyType() || !this.m_assembly.subtypeOf(allnames.get(pname) as ResolvedType, decltype));

                return [pname, MIRKeyGenerator.generateFieldKey(fdeclinfo.contiainingType, fdeclinfo.binds, pname)];
            });

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitStructuredExtendObject(op.sinfo, this.m_emitter.registerResolvedTypeReference(texp).trkey, arg, etreg, fieldResolves, trgt);
            }

            return [env.setExpressionResult(this.m_assembly, texp)];
        }
    }

    private checkInvoke(env: TypeEnvironment, op: PostfixInvoke, arg: MIRTempRegister, trgt: MIRTempRegister, optArgVar: string | undefined, refok: boolean): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        const specialcall = (op.name === "isNone" || op.name === "isSome" || op.name === "is" || op.name === "as" || op.name === "tryAs" || op.name === "defaultAs");

        if (!specialcall && (op.specificResolve !== undefined || (texp.isUniqueCallTargetType() && this.m_assembly.tryGetOOMemberDeclUnique(texp, "method", op.name)))) {
            const resolveType = op.specificResolve !== undefined ? this.resolveAndEnsureTypeOnly(op.sinfo, op.specificResolve, env.terms) : texp;

            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, resolveType), "This is not a subtype of specified resolve type");

            const mdecltry = this.m_assembly.tryGetOOMemberDeclUnique(resolveType, "method", op.name);
            this.raiseErrorIf(op.sinfo, mdecltry === undefined, `Method not defined for type '${resolveType.idStr}'`);

            const mdecl = mdecltry as OOMemberLookupInfo;

            const binds = this.m_assembly.resolveBindsForCall((mdecl.decl as MemberMethodDecl).invoke.terms, op.terms.targs, mdecl.binds, env.terms);
            this.raiseErrorIf(op.sinfo, binds === undefined, "Call bindings could not be resolved");

            const fsig = this.m_assembly.normalizeTypeFunction((mdecl.decl as MemberMethodDecl).invoke.generateSig(), binds as Map<string, ResolvedType>);
            this.raiseErrorIf(op.sinfo, fsig === undefined, "Invalid function signature");

            const eargs = this.checkArgumentsEvaluationWSig(env, fsig as ResolvedFunctionType, op.args, [resolveType, arg], refok);
            const margs = this.checkArgumentsSignature(op.sinfo, env, fsig as ResolvedFunctionType, eargs);

            this.checkRecursion(op.sinfo, fsig as ResolvedFunctionType, margs.pcodes, op.pragmas.recursive);

            if (this.m_emitEnabled) {
                this.m_emitter.registerTypeInstantiation(mdecl.contiainingType, mdecl.binds);
                const mkey = this.m_emitter.registerMethodCall(mdecl.contiainingType, mdecl.decl as MemberMethodDecl, mdecl.binds, (mdecl.decl as MemberMethodDecl).name, binds as Map<string, ResolvedType>, margs.pcodes, margs.cinfo);

                const [frtype, refinfo] = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, margs.refs);
                this.m_emitter.bodyEmitter.emitInvokeFixedFunction(this.m_emitter.masm, op.sinfo, frtype, mkey, margs.args, refinfo, trgt);
            }

            return [env.setExpressionResult(this.m_assembly, (fsig as ResolvedFunctionType).resultType)];
        }
        else {
            const vinfo = this.m_assembly.tryGetOOMemberDeclOptions(texp, "method", op.name);
            this.raiseErrorIf(op.sinfo, vinfo.root === undefined, "Multiple possible declarations of this method");

            const vopts = (vinfo.decls as OOMemberLookupInfo[]).map((opt) => {
                const mdecl = (opt.decl as MemberMethodDecl);
                const binds = this.m_assembly.resolveBindsForCall(mdecl.invoke.terms, op.terms.targs, opt.binds, env.terms) as Map<string, ResolvedType>;
                return this.m_assembly.normalizeTypeFunction(mdecl.invoke.generateSig(), binds) as ResolvedFunctionType;
            });

            const rootdecl = (vinfo.root as OOMemberLookupInfo).contiainingType.memberMethods.get(op.name) as MemberMethodDecl;
            const rootbinds = this.m_assembly.resolveBindsForCall(rootdecl.invoke.terms, op.terms.targs, (vinfo.root as OOMemberLookupInfo).binds, env.terms) as Map<string, ResolvedType>;
            const rootsig = this.m_assembly.normalizeTypeFunction(rootdecl.invoke.generateSig(), rootbinds) as ResolvedFunctionType;

            const lsigtry = this.m_assembly.computeUnifiedFunctionType(vopts, rootsig);
            this.raiseErrorIf(op.sinfo, lsigtry === undefined, "Ambigious signature for invoke");

            const lsig = lsigtry as ResolvedFunctionType;
            const eargs = this.checkArgumentsEvaluationWSig(env, lsig, op.args, [texp, arg], refok);
            const margs = this.checkArgumentsSignature(op.sinfo, env, lsig, eargs);

            this.checkRecursion(op.sinfo, lsig as ResolvedFunctionType, margs.pcodes, op.pragmas.recursive);

            if (this.m_emitEnabled) {
                let cbindsonly = this.m_assembly.resolveBindsForCall(rootdecl.invoke.terms, op.terms.targs, new Map<string, ResolvedType>(), env.terms) as Map<string, ResolvedType>;

                const specialm0type = this.m_emitter.registerResolvedTypeReference(margs.types.length === 1 ? margs.types[0] : this.m_assembly.getSpecialNoneType()).trkey;
                if (op.name === "isNone") {
                    this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()).trkey, specialm0type, margs.args[0]);
                }
                else if (op.name === "isSome") {
                    this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialSomeType()).trkey, specialm0type, margs.args[0]);
                }
                else if (op.name === "is" || op.name === "as" || op.name === "tryAs" || op.name === "defaultAs") {
                    const ttype = rootbinds.get("T") as ResolvedType;
                    const mt = this.m_emitter.registerResolvedTypeReference(ttype);

                    if (op.name === "is") {
                        this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, trgt, mt.trkey, specialm0type, margs.args[0]);
                    }
                    else if (op.name === "as") {
                        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Las_done");
                        const failblck = this.m_emitter.bodyEmitter.createNewBlock("Las_fail");
                        const creg = this.m_emitter.bodyEmitter.generateTmpRegister();
                        this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, creg, mt.trkey, specialm0type, margs.args[0]);
                        this.m_emitter.bodyEmitter.emitBoolJump(op.sinfo, creg, doneblck, failblck);

                        this.m_emitter.bodyEmitter.setActiveBlock(failblck);
                        this.m_emitter.bodyEmitter.emitAbort(op.sinfo, true, "as<T> fail");
                        this.m_emitter.bodyEmitter.emitDirectJump(op.sinfo, "exit");

                        this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
                        this.m_emitter.bodyEmitter.emitRegAssign(op.sinfo, margs.args[0], trgt);
                    }
                    else if (op.name === "tryAs") {
                        this.m_emitter.bodyEmitter.emitRegAssign(op.sinfo, margs.args[0], trgt);

                        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Ltryas_done");
                        const noneblck = this.m_emitter.bodyEmitter.createNewBlock("Ltryas_none");
                        const creg = this.m_emitter.bodyEmitter.generateTmpRegister();
                        this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, creg, mt.trkey, specialm0type, margs.args[0]);
                        this.m_emitter.bodyEmitter.emitBoolJump(op.sinfo, creg, doneblck, noneblck);

                        this.m_emitter.bodyEmitter.setActiveBlock(noneblck);
                        this.m_emitter.bodyEmitter.emitLoadConstNone(op.sinfo, trgt);
                        this.m_emitter.bodyEmitter.emitDirectJump(op.sinfo, doneblck);

                        this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
                    }
                    else {
                        this.m_emitter.bodyEmitter.emitRegAssign(op.sinfo, margs.args[0], trgt);

                        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Ldefaultas_done");
                        const noneblck = this.m_emitter.bodyEmitter.createNewBlock("Ldefaultas_none");
                        const creg = this.m_emitter.bodyEmitter.generateTmpRegister();
                        this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, creg, mt.trkey, specialm0type, margs.args[0]);
                        this.m_emitter.bodyEmitter.emitBoolJump(op.sinfo, creg, doneblck, noneblck);

                        this.m_emitter.bodyEmitter.setActiveBlock(noneblck);
                        this.m_emitter.bodyEmitter.emitLoadConstNone(op.sinfo, trgt);
                        this.m_emitter.bodyEmitter.emitRegAssign(op.sinfo, margs.args[1], trgt);

                        this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
                    }
                }
                else {
                    const vkey = this.m_emitter.registerVirtualMethodCall((vinfo.root as OOMemberLookupInfo).contiainingType, (vinfo.root as OOMemberLookupInfo).binds, op.name, cbindsonly, margs.pcodes, margs.cinfo);

                    const [frtype, refinfo] = this.generateRefInfoForCallEmit(lsig, margs.refs);
                    this.m_emitter.bodyEmitter.emitInvokeVirtualTarget(this.m_emitter.masm, op.sinfo, frtype, vkey, margs.args, refinfo, trgt);
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

    private checkPostfixExpression(env: TypeEnvironment, exp: PostfixOp, trgt: MIRTempRegister, refok: boolean): TypeEnvironment[] {
        const hasNoneCheck = exp.ops.some((op) => op.isElvis);
        const noneblck = hasNoneCheck && this.m_emitEnabled ? this.m_emitter.bodyEmitter.createNewBlock("Lelvis_none") : "[DISABLED]";
        const doneblck = hasNoneCheck && this.m_emitEnabled ? this.m_emitter.bodyEmitter.createNewBlock("Lelvis_done") : "[DISABLED]";

        let etgrt = this.m_emitter.bodyEmitter.generateTmpRegister();
        let eenv = this.checkExpressionMultiFlow(env, exp.rootExp, etgrt);

        if (exp.rootExp instanceof AccessVariableExpression && exp.ops.length === 1 && exp.ops[0] instanceof PostfixInvoke) {
            const [fflow, scflow] = this.checkElvisAction(exp.sinfo, eenv, exp.ops[0].isElvis, etgrt, noneblck);

            const res = this.checkInvoke(TypeEnvironment.join(this.m_assembly, ...fflow), exp.ops[0] as PostfixInvoke, etgrt, trgt, exp.rootExp.name, refok);

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
                    default:
                        this.raiseErrorIf(exp.sinfo, exp.ops[i].op !== PostfixOpTag.PostfixInvoke, "Unknown postfix op");
                        cenv = this.checkInvoke(nflow, exp.ops[i] as PostfixInvoke, etgrt, ntgrt, undefined, refok);
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
                this.m_emitter.bodyEmitter.emitTypeOf(exp.sinfo, trgt, chktype.trkey, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().etype).trkey, rhsreg);
            }
            else if (exp.rhs instanceof LiteralNoneExpression) {
                const chktype = this.m_emitter.registerResolvedTypeReference(exp.op === "==" ? this.m_assembly.getSpecialNoneType() : this.m_assembly.getSpecialSomeType());
                this.m_emitter.bodyEmitter.emitTypeOf(exp.sinfo, trgt, chktype.trkey, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().etype).trkey, lhsreg);
            }
            else {
                this.m_emitter.bodyEmitter.emitBinEq(exp.sinfo, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().etype).trkey, lhsreg, exp.op, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().etype).trkey, rhsreg, trgt);
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
            this.m_emitter.bodyEmitter.emitBinCmp(exp.sinfo, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().etype).trkey, lhsreg, exp.op, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().etype).trkey, rhsreg, trgt);
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

        //THIS IS WRONG -- in "true && x" the true is redundant but the rest of the expressions needs to be evaluated 
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

            //THIS IS WRONG -- in "x || false" the true is redundant but the rest of the expressions needs to be evaluated 
            //this.raiseErrorIf(exp.sinfo, rtflow.length === 0 || rfflow.length === 0, "Expression is never true/false and not needed");
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

            //THIS IS WRONG -- in "x && true" the true is redundant but the rest of the expressions needs to be evaluated 
            //this.raiseErrorIf(exp.sinfo, rtflow.length === 0 || rfflow.length === 0, "Expression is never true/false and not needed");
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

            //THIS IS WRONG -- in "x => true" the true is redundant but the rest of the expressions needs to be evaluated 
            //this.raiseErrorIf(exp.sinfo, rtflow.length === 0 || rfflow.length === 0, "Expression is never true/false and not needed");
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

    private checkOrExpression(env: TypeEnvironment, exp: ExpOrExpression, trgt: MIRTempRegister, extraok: { refok: boolean, orok: boolean }): TypeEnvironment[] {
        this.raiseErrorIf(exp.sinfo, !extraok.orok, "Or expression is not valid in this position");

        const scblck = this.m_emitter.bodyEmitter.createNewBlock("Lorcheck_return");
        const regularblck = this.m_emitter.bodyEmitter.createNewBlock("Lorcheck_regular");

        let evalue = this.checkExpressionMultiFlow(env, exp.exp, trgt, {refok: extraok.refok, orok: false});

        let normaltype: ResolvedType = this.m_assembly.typeUnion(evalue.map((ev) => ev.getExpressionResult().etype));
        let normalexps: TypeEnvironment[] = [];
        let terminaltype: ResolvedType = this.m_assembly.getSpecialNoneType();
        let terminalexps: TypeEnvironment[] = [];

        if (exp.cond !== undefined || exp.result !== undefined) {
            evalue = evalue.map((ev) => ev.pushLocalScope().addVar("_value_", true, ev.getExpressionResult().etype, true, ev.getExpressionResult().etype));
            if (this.m_emitEnabled) {
                const vtype = TypeEnvironment.join(this.m_assembly, ...evalue).getExpressionResult().etype;
                this.m_emitter.bodyEmitter.localLifetimeStart(exp.sinfo, "_value_", this.m_emitter.registerResolvedTypeReference(vtype).trkey);
                this.m_emitter.bodyEmitter.emitVarStore(exp.sinfo, trgt, "_value_");
            }
        }

        if (exp.cond === undefined) {
            let [enone, esome] = TypeEnvironment.convertToNoneSomeFlowsOnExpressionResult(this.m_assembly, evalue);
            this.raiseErrorIf(exp.sinfo, enone.length === 0, "Value is never equal to none");
            this.raiseErrorIf(exp.sinfo, esome.length === 0, "Value is always equal to none");

            if (exp.exp instanceof AccessVariableExpression) {
                const vname = (exp.exp as AccessVariableExpression).name;
                enone = enone.map((opt) => opt.assumeVar(vname, (opt.expressionResult as ExpressionReturnResult).etype));
                esome = esome.map((opt) => opt.assumeVar(vname, (opt.expressionResult as ExpressionReturnResult).etype));
            }

            normaltype = TypeEnvironment.join(this.m_assembly, ...esome).getExpressionResult().etype;
            terminaltype = TypeEnvironment.join(this.m_assembly, ...enone).getExpressionResult().etype;

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitNoneJump(exp.sinfo, trgt, scblck, regularblck);
                this.m_emitter.bodyEmitter.setActiveBlock(scblck);
            }

            normalexps = esome;
            terminalexps = enone;
        }
        else {
            const okType = this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);

            const treg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const tvalue = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...evalue), exp.cond, treg);

            this.raiseErrorIf(exp.sinfo, tvalue.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

            const [trueflow, falseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, tvalue);
            this.raiseErrorIf(exp.sinfo, trueflow.length === 0 || falseflow.length === 0, "Expression is always true/false expression test is redundant");

            normaltype = (TypeEnvironment.join(this.m_assembly, ...evalue).getLocalVarInfo("_value_") as VarInfo).flowType;
            terminaltype = (TypeEnvironment.join(this.m_assembly, ...evalue).getLocalVarInfo("_value_") as VarInfo).flowType;

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, treg, scblck, regularblck);
                this.m_emitter.bodyEmitter.setActiveBlock(scblck);
            }

            normalexps = falseflow.map((ev) => ev.popLocalScope());
            terminalexps = trueflow.map((ev) => ev.popLocalScope());
        }

        let rreg = trgt;
        if (exp.result !== undefined) {
            const tenv = TypeEnvironment.join(this.m_assembly, ...terminalexps);
            const rvalue = this.checkExpression(tenv, exp.result, rreg);
            terminaltype = rvalue.getExpressionResult().etype;
        }

        if (exp.cond !== undefined || exp.result !== undefined) {
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.localLifetimeEnd(exp.sinfo, "_value_");
            }
        }

        if (exp.action === "return") {
            this.raiseErrorIf(exp.sinfo, env.isInYieldBlock(), "Cannot use return statment inside an expression block");

            if (this.m_emitEnabled) {
                const rtuple = this.generateRefInfoForReturnEmit(terminaltype, env);
                this.m_emitter.bodyEmitter.emitReturnAssign(exp.sinfo, rtuple, env.refparams, rreg);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, "exit");

                this.m_emitter.bodyEmitter.setActiveBlock(regularblck);
            }

            return [...(normalexps.map((ev) => ev.setExpressionResult(this.m_assembly, normaltype))), env.setReturn(this.m_assembly, terminaltype)];
        }
        else {
            this.raiseErrorIf(exp.sinfo, !env.isInYieldBlock(), "Cannot use yield statment unless inside and expression block");

            if (this.m_emitEnabled) {
                const yinfo = env.getYieldTargetInfo();
                this.m_emitter.bodyEmitter.emitRegAssign(exp.sinfo, rreg, yinfo[0]);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, yinfo[1]);

                this.m_emitter.bodyEmitter.setActiveBlock(regularblck);
            }

            return [...(normalexps.map((ev) => ev.setExpressionResult(this.m_assembly, normaltype))), env.setYield(this.m_assembly, terminaltype)];
        }
    }

    private checkBlockExpression(env: TypeEnvironment, exp: BlockStatementExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const yblck = this.m_emitter.bodyEmitter.createNewBlock("Lyield");
        let cenv = env.freezeVars().pushLocalScope().pushYieldTarget(trgt, yblck);

        for (let i = 0; i < exp.ops.length; ++i) {
            if (!cenv.hasNormalFlow()) {
                break;
            }

            cenv = this.checkStatement(cenv, exp.ops[i]);
        }

        if (this.m_emitEnabled && cenv.hasNormalFlow()) {
            this.m_emitter.bodyEmitter.setActiveBlock(yblck);

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

    private checkExpression(env: TypeEnvironment, exp: Expression, trgt: MIRTempRegister, extraok?: { refok: boolean, orok: boolean }): TypeEnvironment {
        const res = this.checkExpressionMultiFlow(env, exp, trgt, extraok);
        this.raiseErrorIf(exp.sinfo, res.length === 0, "No feasible flow for expression");

        return TypeEnvironment.join(this.m_assembly, ...res);
    }

    private checkExpressionMultiFlow(env: TypeEnvironment, exp: Expression, trgt: MIRTempRegister, extraok?: { refok: boolean, orok: boolean }): TypeEnvironment[] {
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
                return this.checkConstructorPrimaryWithFactory(env, exp as ConstructorPrimaryWithFactoryExpression, trgt, (extraok && extraok.refok) || false);
            case ExpressionTag.ConstructorTupleExpression:
                return this.checkTupleConstructor(env, exp as ConstructorTupleExpression, trgt);
            case ExpressionTag.ConstructorRecordExpression:
                return this.checkRecordConstructor(env, exp as ConstructorRecordExpression, trgt);
            case ExpressionTag.CallNamespaceFunctionExpression:
                return this.checkCallNamespaceFunctionExpression(env, exp as CallNamespaceFunctionExpression, trgt, (extraok && extraok.refok) || false);
            case ExpressionTag.CallStaticFunctionExpression:
                return this.checkCallStaticFunctionExpression(env, exp as CallStaticFunctionExpression, trgt, (extraok && extraok.refok) || false);
            case ExpressionTag.PCodeInvokeExpression:
                return this.checkPCodeInvokeExpression(env, exp as PCodeInvokeExpression, trgt);
            case ExpressionTag.PostfixOpExpression:
                return this.checkPostfixExpression(env, exp as PostfixOp, trgt, (extraok && extraok.refok) || false);
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
            case ExpressionTag.ExpOrExpression:
                return this.checkOrExpression(env, exp as ExpOrExpression, trgt, extraok || { refok: false, orok: false });
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
        const venv = stmt.exp !== undefined ? this.checkExpression(env, stmt.exp, etreg, { refok: true, orok: true }) : undefined;
        this.raiseErrorIf(stmt.sinfo, venv === undefined && stmt.isConst, "Must define const var at declaration site");
        this.raiseErrorIf(stmt.sinfo, venv === undefined && stmt.vtype instanceof AutoTypeSignature, "Must define auto typed var at declaration site");

        const vtype = (stmt.vtype instanceof AutoTypeSignature) ? (venv as TypeEnvironment).getExpressionResult().etype : this.resolveAndEnsureTypeOnly(stmt.sinfo, stmt.vtype, env.terms);
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
        const venv = this.checkExpression(env, stmt.exp, etreg, { refok: true, orok: true });
        this.raiseErrorIf(stmt.sinfo, !this.m_assembly.subtypeOf(venv.getExpressionResult().etype, (vinfo as VarInfo).declaredType), "Assign value is not subtype of declared variable type");

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitVarStore(stmt.sinfo, etreg, stmt.name);
        }

        return env.setVar(stmt.name, venv.getExpressionResult().etype);
    }

    private checkStructuredAssign(sinfo: SourceInfo, env: TypeEnvironment, isopt: boolean, cpath: {p: (string|number), t: ResolvedType}[], assign: StructuredAssignment, expt: ResolvedType, allDeclared: [boolean, string, ResolvedType, {p: (string|number), t: ResolvedType}[], ResolvedType][], allAssigned: [string, {p: (string|number), t: ResolvedType}[], ResolvedType][]) {
        if (assign instanceof IgnoreTermStructuredAssignment) {
            this.raiseErrorIf(sinfo, isopt && !assign.isOptional, "Missing value for required entry");

            const itype = this.resolveAndEnsureTypeOnly(sinfo, assign.termType, env.terms);
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
                    ? this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.resolveAndEnsureTypeOnly(sinfo, assign.vtype, env.terms)])
                    : this.resolveAndEnsureTypeOnly(sinfo, assign.vtype, env.terms));

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
            const tuptype = ResolvedType.create(expt.options.map((opt) => {
                this.raiseErrorIf(sinfo, !(opt instanceof ResolvedTupleAtomType), "Cannot use 'Tuple' type in structured assignment");
                return opt as ResolvedTupleAtomType;
            }));

            for (let i = 0; i < assign.assigns.length; ++i) {
                const aopt = tuptype.options.some((atom) => (atom as ResolvedTupleAtomType).types.length < i || (atom as ResolvedTupleAtomType).types[i].isOptional);
                const ttype = this.getInfoForLoadFromIndex(tuptype, i);
                this.checkStructuredAssign(sinfo, env, aopt, [...cpath, {p: i, t: ttype}], assign.assigns[i], ttype, allDeclared, allAssigned);
            }

            this.raiseErrorIf(sinfo, tuptype.options.some((atom) => (atom as ResolvedTupleAtomType).types.length > assign.assigns.length), "More values in tuple that assignment");
        }
        else {
            this.raiseErrorIf(sinfo, !(assign instanceof RecordStructuredAssignment), "Unknown structured assignment type");

            this.raiseErrorIf(sinfo, isopt, "Missing value for required entry");
            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(expt, this.m_assembly.getSpecialRecordConceptType()), "Assign value is not subtype of declared variable type");
            const rectype = ResolvedType.create(expt.options.map((opt) =>  {
                this.raiseErrorIf(sinfo, !(opt instanceof ResolvedRecordAtomType), "Cannot use 'Record' type in structured assignment");
                return opt as ResolvedRecordAtomType;
            }));

            const rassign = assign as RecordStructuredAssignment;
            for (let i = 0; i < rassign.assigns.length; ++i) {
                const pname = rassign.assigns[i][0];
                const aopt = rectype.options.some((atom) => {
                    const entry = (atom as ResolvedRecordAtomType).entries.find((re) => re.name === pname);
                    return (entry === undefined || entry.isOptional);
                });
                const ttype = this.getInfoForLoadFromPropertyName(rectype, pname);
                this.checkStructuredAssign(sinfo, env, aopt, [...cpath, {p: pname, t: ttype}], rassign.assigns[i][1], ttype, allDeclared, allAssigned);
            }

            this.raiseErrorIf(sinfo, rectype.options.some((atom) => {
                return (atom as ResolvedRecordAtomType).entries.some((re) => {
                    const entry = rassign.assigns.find((e) => e[0] === re.name);
                    return entry === undefined;
                });
            }), "More values in record that assignment");
        }
    }

    private generateAssignOps(sinfo: SourceInfo, ereg: MIRTempRegister, assign: {p: (string|number), t: ResolvedType}[]): MIRTempRegister {
        let creg = ereg;
        for (let i = 0; i < assign.length; ++i) {
            const nreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const lt = this.m_emitter.registerResolvedTypeReference(assign[i].t).trkey;
            if (typeof (assign[i].p) === "number") {
                this.m_emitter.bodyEmitter.emitLoadTupleIndex(sinfo, lt, creg, assign[i].p as number, nreg);
            }
            else {
                this.m_emitter.bodyEmitter.emitLoadProperty(sinfo, lt, creg, assign[i].p as string, nreg);
            }
            creg = nreg;
        }
        return creg;
    }

    private generateEqualityOps(env: TypeEnvironment, sinfo: SourceInfo, ergtype: ResolvedType, ereg: MIRTempRegister, assign: {p: (string|number), t: ResolvedType}[], value: Expression): MIRTempRegister {
        let creg = ereg;
        let ctype = ergtype;
        for (let i = 0; i < assign.length; ++i) {
            const nreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const lt = this.m_emitter.registerResolvedTypeReference(assign[i].t).trkey;
            if (typeof (assign[i].p) === "number") {
                this.m_emitter.bodyEmitter.emitLoadTupleIndex(sinfo, lt, creg, assign[i].p as number, nreg);
            }
            else {
                this.m_emitter.bodyEmitter.emitLoadProperty(sinfo, lt, creg, assign[i].p as string, nreg);
            }
            creg = nreg;
            ctype = assign[i].t;
        }

        const vreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const vrenv = this.checkExpression(env, value, vreg);

        const rreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        this.m_emitter.bodyEmitter.emitBinEq(sinfo, this.m_emitter.registerResolvedTypeReference(ctype).trkey, creg, "==", this.m_emitter.registerResolvedTypeReference(vrenv.getExpressionResult().etype).trkey, vreg, rreg);

        return rreg;
    }

    private checkStructuredVariableAssignmentStatement(env: TypeEnvironment, stmt: StructuredVariableAssignmentStatement): TypeEnvironment {
        const expreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const eenv = this.checkExpression(env, stmt.exp, expreg, { refok: true, orok: true });

        let allDeclared: [boolean, string, ResolvedType, {p: (string|number), t: ResolvedType}[], ResolvedType][] = [];
        let allAssigned: [string, {p: (string|number), t: ResolvedType}[], ResolvedType][] = [];
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

    private checkStructuredMatch(sinfo: SourceInfo, env: TypeEnvironment, cpath: {p: (string|number), t: ResolvedType}[], assign: StructuredAssignment, expt: ResolvedType, allDeclared: [boolean, string, ResolvedType, {p: (string|number), t: ResolvedType}[], ResolvedType][], allAssigned: [string, {p: (string|number), t: ResolvedType}[], ResolvedType][], allEqChecks: [{p: (string|number), t: ResolvedType}[], Expression][]): [ResolvedType, boolean] {
        if (assign instanceof IgnoreTermStructuredAssignment) {
            return [this.resolveAndEnsureTypeOnly(sinfo, assign.termType, env.terms), assign.isOptional];
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
                    ? this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.resolveAndEnsureTypeOnly(sinfo, assign.vtype, env.terms)])
                    : this.resolveAndEnsureTypeOnly(sinfo, assign.vtype, env.terms));

            allDeclared.push([assign.isConst, assign.vname, vtype, [...cpath], vtype]);
            return [this.resolveAndEnsureTypeOnly(sinfo, assign.vtype, env.terms), assign.isOptional];
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
            const tupopts = expt.options.filter((opt) => opt instanceof ResolvedTupleAtomType);
            this.raiseErrorIf(sinfo, tupopts.length === 0, "Check will always fail");

            const tuptype = ResolvedType.create(tupopts);
            const tupcheck: ResolvedTupleAtomTypeEntry[] = [];
            for (let i = 0; i < assign.assigns.length; ++i) {
                const ttype = this.getInfoForLoadFromIndex(tuptype, i);
                const einfo = this.checkStructuredMatch(sinfo, env, [...cpath, {p: i, t: ttype}], assign.assigns[i], ttype, allDeclared, allAssigned, allEqChecks);
                tupcheck.push(new ResolvedTupleAtomTypeEntry(...einfo));
            }

            return [ResolvedType.createSingle(ResolvedTupleAtomType.create(tupcheck)), false];
        }
        else {
            this.raiseErrorIf(sinfo, !(assign instanceof RecordStructuredAssignment), "Unknown structured assignment type");

            const recopts = expt.options.filter((opt) => opt instanceof ResolvedRecordAtomType);
            this.raiseErrorIf(sinfo, recopts.length === 0, "Check will always fail");

            const rassign = assign as RecordStructuredAssignment;
            const rectype = ResolvedType.create(recopts);
            const reccheck: ResolvedRecordAtomTypeEntry[] = [];
            for (let i = 0; i < rassign.assigns.length; ++i) {
                const pname = rassign.assigns[i][0];
                const ttype = this.getInfoForLoadFromPropertyName(rectype, pname);
                const einfo = this.checkStructuredMatch(sinfo, env, [...cpath, {p: pname, t: ttype}], rassign.assigns[i][1], ttype, allDeclared, allAssigned, allEqChecks);
                reccheck.push(new ResolvedRecordAtomTypeEntry(pname, ...einfo));
            }

            return [ResolvedType.createSingle(ResolvedRecordAtomType.create(reccheck)), false];
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
            const tmatch = this.resolveAndEnsureTypeOnly(sinfo, guard.oftype, env.terms);

            if (this.m_emitEnabled) {
                const mt = this.m_emitter.registerResolvedTypeReference(tmatch);
                this.m_emitter.bodyEmitter.emitTypeOf(sinfo, mreg, mt.trkey, this.m_emitter.registerResolvedTypeReference(sexp).trkey, vreg);
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

            let allDeclared: [boolean, string, ResolvedType, {p: (string|number), t: ResolvedType}[], ResolvedType][] = [];
            let allAssigned: [string, {p: (string|number), t: ResolvedType}[], ResolvedType][] = [];
            let allEqChecks: [{p: (string|number), t: ResolvedType}[], Expression][] = [];
            const oftype = this.checkStructuredMatch(sinfo, env, [], sguard.match, sexp, allDeclared, allAssigned, allEqChecks)[0];

            if (this.m_emitEnabled) {
                const oft = this.m_emitter.registerResolvedTypeReference(oftype);
                const tcreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                this.m_emitter.bodyEmitter.emitTypeOf(sinfo, tcreg, oft.trkey, this.m_emitter.registerResolvedTypeReference(sexp).trkey, vreg);

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
                        const eqreg = this.generateEqualityOps(env, sinfo, sexp, vreg, allEqChecks[i][0], allEqChecks[i][1]);
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
        const venv = this.checkExpression(env, stmt.value, etreg, { refok: true, orok: false });

        this.raiseErrorIf(stmt.sinfo, env.isInYieldBlock(), "Cannot use return statment inside an expression block");

        if (this.m_emitEnabled) {
            const rtuple = this.generateRefInfoForReturnEmit(venv.getExpressionResult().etype, env);
            this.m_emitter.bodyEmitter.emitReturnAssign(stmt.sinfo, rtuple, env.refparams, etreg);
            this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, "exit");
        }

        return env.setReturn(this.m_assembly, venv.getExpressionResult().etype);
    }

    private checkYieldStatement(env: TypeEnvironment, stmt: YieldStatement): TypeEnvironment {
        const yinfo = env.getYieldTargetInfo();
        const venv = this.checkExpression(env, stmt.value, yinfo[0], { refok: true, orok: false });

        this.raiseErrorIf(stmt.sinfo, !env.isInYieldBlock(), "Cannot use yield statment outside expression blocks");

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, yinfo[1]);

            this.m_emitter.bodyEmitter.setActiveBlock(yinfo[1]);
        }

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

        if (this.m_emitEnabled && this.m_doAssertCheck) {
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

    private checkBody(env: TypeEnvironment, body: BodyImplementation, args: Map<string, MIRType>, resultType: ResolvedType): MIRBody | undefined {
        if (body.body instanceof Expression) {
            if (this.m_emitEnabled) {
                this.m_emitter.initializeBodyEmitter();
            }

            const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const evalue = this.checkExpression(env, body.body, etreg);

            if (this.m_emitEnabled) {
                const rtuple = this.generateRefInfoForReturnEmit(resultType, env);
                this.m_emitter.bodyEmitter.emitReturnAssign(body.body.sinfo, rtuple, env.refparams, etreg);
                this.m_emitter.bodyEmitter.emitDirectJump(body.body.sinfo, "exit");
            }

            this.raiseErrorIf(body.body.sinfo, !this.m_assembly.subtypeOf(evalue.getExpressionResult().etype, resultType), "Did not produce the expected return type");

            return this.m_emitEnabled ? this.m_emitter.bodyEmitter.getBody(this.m_file, body.body.sinfo, env.scope, args) : undefined;
        }
        else if (body.body instanceof BlockStatement) {
            if (this.m_emitEnabled) {
                this.m_emitter.initializeBodyEmitter();
            }

            const renv = this.checkBlock(env, body.body);
            this.raiseErrorIf(body.body.sinfo, renv.hasNormalFlow(), "Not all flow paths return a value!");
            this.raiseErrorIf(body.body.sinfo, !this.m_assembly.subtypeOf(renv.returnResult as ResolvedType, resultType), "Did not produce the expected return type");

            return this.m_emitEnabled ? this.m_emitter.bodyEmitter.getBody(this.m_file, body.body.sinfo, env.scope, args) : undefined;
        }
        else {
            return undefined;
        }
    }

    private checkExpressionAsBody(env: TypeEnvironment, bkey: MIRBodyKey, exp: Expression, ofType: ResolvedType): MIRBody {
        if (this.m_emitEnabled) {
            this.m_emitter.initializeBodyEmitter();
        }

        const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const evalue = this.checkExpression(env, exp, etreg);

        if (this.m_emitEnabled) {
            const rtuple = this.generateRefInfoForReturnEmit(ofType, env);
            this.m_emitter.bodyEmitter.emitReturnAssign(exp.sinfo, rtuple, env.refparams, etreg);
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, "exit");
        }

        this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(evalue.getExpressionResult().etype, ofType), "Did not produce the expected type");

        let argTypes: Map<string, MIRType> = new Map<string, MIRType>();
        (env.args as Map<string, VarInfo>).forEach((arg, name) => {
            const atype = this.m_emitter.registerResolvedTypeReference(arg.declaredType) as MIRType;
            argTypes.set(name, atype);
        });

        return this.m_emitter.bodyEmitter.getBody(this.m_file, exp.sinfo, bkey, argTypes);
    }

    private abortIfTooManyErrors() {
        if (this.m_errors.length > 20) {
            throw new Error("More than 20 errors ... halting type checker");
        }
    }

    private processPragmas(sinfo: SourceInfo, pragmas: [TypeSignature, string][]): [MIRType, string][] {
        const emptybinds = new Map<string, ResolvedType>();

        return pragmas.map((prg) => {
            const ptype = this.resolveAndEnsureTypeOnly(sinfo, prg[0], emptybinds);
            const pkey = this.m_emitter.registerResolvedTypeReference(ptype);
            return [pkey, prg[1]] as [MIRType, string];
        });
    }

    processOOType(tkey: MIRNominalTypeKey, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>) {
        try {
            this.m_file = tdecl.srcFile;

            let terms = new Map<string, MIRType>();
            tdecl.terms.forEach((term) => terms.set(term.name, this.m_emitter.registerResolvedTypeReference(binds.get(term.name) as ResolvedType)));

            const provides = tdecl.provides.map((provide) => {
                const ptype = this.resolveAndEnsureTypeOnly(new SourceInfo(0, 0, 0, 0), provide, binds);
                const cpt = ((ptype.options[0]) as ResolvedConceptAtomType).conceptTypes[0];

                this.m_emitter.registerTypeInstantiation(cpt.concept, cpt.binds);
                return this.m_emitter.registerResolvedTypeReference(ptype).trkey;
            });

            const invariants = this.m_doInvariantCheck
                ? tdecl.invariants.map((inv) => {
                    const thistype = ResolvedType.createSingle(tdecl instanceof EntityTypeDecl ? ResolvedEntityAtomType.create(tdecl, binds) : ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(tdecl as ConceptTypeDecl, binds)]));
                    const invscope = MIRKeyGenerator.generateBodyKey("invariant", tkey);
                    const invenv = TypeEnvironment.createInitialEnvForCall(invscope, binds, [], new Map<string, { pcode: PCode, captured: string[] }>(), new Map<string, VarInfo>().set("this", new VarInfo(thistype, true, false, true, thistype)));
                    return this.checkExpressionAsBody(invenv, invscope, inv, this.m_assembly.getSpecialBoolType());
                })
                : [];

            //
            //TODO: we need to check inheritance and provides rules here -- diamonds, virtual/abstract/override use, etc.
            //

            const fields: MIRFieldDecl[] = [];
            tdecl.memberFields.forEach((f) => {
                const fkey = MIRKeyGenerator.generateFieldKey(tdecl, binds, f.name);
                const fdscope = MIRKeyGenerator.generateBodyKey("fdefault", fkey);
                const fpragmas = this.processPragmas(f.sourceLocation, f.pragmas);
                const dtypeResolved = this.resolveAndEnsureTypeOnly(f.sourceLocation, f.declaredType, binds);
                const dtype = this.m_emitter.registerResolvedTypeReference(dtypeResolved);
                let value = undefined;
                if (f.value !== undefined) {
                    const fdenv = TypeEnvironment.createInitialEnvForCall(fdscope, binds, [], new Map<string, { pcode: PCode, captured: string[] }>(), new Map<string, VarInfo>());
                    value = this.checkExpressionAsBody(fdenv, fdscope, f.value, dtypeResolved);
                }

                const fname = `${tdecl.ns}::${tdecl.name}.${f.name}`;
                const mfield = new MIRFieldDecl(tkey, f.attributes, fname, f.sourceLocation, f.srcFile, fkey, fpragmas, f.name, dtype.trkey, value);
                fields.push(mfield);
                this.m_emitter.masm.fieldDecls.set(fkey, mfield);
            });

            const ooname = `${tdecl.ns}::${tdecl.name}`;
            const pragmas = this.processPragmas(tdecl.sourceLocation, tdecl.pragmas);

            if (tdecl instanceof EntityTypeDecl) {
                const mirentity = new MIREntityTypeDecl(ooname, tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, pragmas, tdecl.ns, tdecl.name, terms, provides, invariants, fields, tdecl.isTypeACollectionEntity(), tdecl.isTypeAMapEntity(), (tdecl as EntityTypeDecl).isEnum, (tdecl as EntityTypeDecl).isKey);
                this.m_emitter.masm.entityDecls.set(tkey, mirentity);
            }
            else {
                const mirconcept = new MIRConceptTypeDecl(ooname, tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, pragmas, tdecl.ns, tdecl.name, terms, provides, invariants, fields);
                this.m_emitter.masm.conceptDecls.set(tkey, mirconcept);
            }
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    processGlobal(gkey: MIRConstantKey, gdecl: NamespaceConstDecl) {
        try {
            const emptybinds = new Map<string, ResolvedType>();

            this.m_file = gdecl.srcFile;
            const gscope = MIRKeyGenerator.generateBodyKey("const", gkey);
            const pragmas = this.processPragmas(gdecl.sourceLocation, gdecl.pragmas);
            const ddecltype = this.resolveAndEnsureTypeOnly(gdecl.sourceLocation, gdecl.declaredType, emptybinds);
            const dtype = this.m_emitter.registerResolvedTypeReference(ddecltype);
            const genv = TypeEnvironment.createInitialEnvForCall(gscope, emptybinds, [], new Map<string, { pcode: PCode, captured: string[] }>(), new Map<string, VarInfo>());
            const vbody = this.checkExpressionAsBody(genv, gscope, gdecl.value, ddecltype);

            const mirglobal = new MIRConstantDecl(undefined, `${gdecl.ns}::${gdecl.name}`, gkey, pragmas, gdecl.sourceLocation, gdecl.srcFile, dtype.trkey, vbody);
            this.m_emitter.masm.constantDecls.set(gkey, mirglobal);
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    processConst(ckey: MIRConstantKey, containingDecl: OOPTypeDecl, cdecl: StaticMemberDecl, binds: Map<string, ResolvedType>) {
        try {
            this.m_file = cdecl.srcFile;
            const cscope = MIRKeyGenerator.generateBodyKey("const", ckey);
            const pragmas = this.processPragmas(cdecl.sourceLocation, cdecl.pragmas);
            const enclosingType = MIRKeyGenerator.generateTypeKey(containingDecl, binds);
            const ddecltype = this.resolveAndEnsureTypeOnly(cdecl.sourceLocation, cdecl.declaredType, binds);
            const dtype = this.m_emitter.registerResolvedTypeReference(ddecltype);
            const cenv = TypeEnvironment.createInitialEnvForCall(cscope, binds, [], new Map<string, { pcode: PCode, captured: string[] }>(), new Map<string, VarInfo>());
            const vbody = this.checkExpressionAsBody(cenv, cscope, cdecl.value as Expression, ddecltype);

            const mirconst = new MIRConstantDecl(enclosingType, `${enclosingType}::${cdecl.name}`, ckey, pragmas, cdecl.sourceLocation, cdecl.srcFile, dtype.trkey, vbody);
            this.m_emitter.masm.constantDecls.set(ckey, mirconst);
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    private processInvokeInfo(enclosingDecl: MIRNominalTypeKey | undefined, iname: string, ikey: MIRInvokeKey, sinfo: SourceInfo, invoke: InvokeDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], pargs: [string, ResolvedType][]): MIRInvokeDecl {
        this.checkInvokeDecl(sinfo, invoke, binds, pcodes);

        let terms = new Map<string, MIRType>();
        invoke.terms.forEach((term) => terms.set(term.name, this.m_emitter.registerResolvedTypeReference(binds.get(term.name) as ResolvedType)));

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && pcodes.some((pc) => pc.code.recursive === "yes"));
        const pragmas = this.processPragmas(invoke.sourceLocation, invoke.pragmas);

        let cargs = new Map<string, VarInfo>();
        let fargs = new Map<string, { pcode: PCode, captured: string[] }>();
        let argTypes: Map<string, MIRType> = new Map<string, MIRType>();
        let refNames: string[] = [];
        let params: MIRFunctionParameter[] = [];

        invoke.params.forEach((p) => {
            const pdecltype = this.m_assembly.normalizeTypeGeneral(p.type, binds);
            if (pdecltype instanceof ResolvedFunctionType) {
                const pcarg = { pcode: pcodes[fargs.size], captured: [...pcodes[fargs.size].captured].map((cc) => cc[0]).sort() };
                fargs.set(p.name, pcarg);
            }
            else {
                const ptype = p.isOptional ? this.m_assembly.typeUnion([pdecltype, this.m_assembly.getSpecialNoneType()]) : pdecltype;
                cargs.set(p.name, new VarInfo(ptype, !p.isRef, false, true, ptype));

                if (p.isRef) {
                    refNames.push(p.name);
                }

                const mtype = this.m_emitter.registerResolvedTypeReference(ptype);
                argTypes.set(p.name, mtype);
                params.push(new MIRFunctionParameter(p.name, mtype.trkey));
            }
        });

        if (invoke.optRestType !== undefined) {
            const rtype = this.resolveAndEnsureTypeOnly(sinfo, invoke.optRestType, binds);
            cargs.set(invoke.optRestName as string, new VarInfo(rtype, true, false, true, rtype));

            const resttype = this.m_emitter.registerResolvedTypeReference(rtype);
            argTypes.set(invoke.optRestName as string, resttype);
            params.push(new MIRFunctionParameter(invoke.optRestName as string, resttype.trkey));
        }

        for (let i = 0; i < pargs.length; ++i) {
            cargs.set(pargs[i][0], new VarInfo(pargs[i][1], true, true, true, pargs[i][1]));

            const ctype = this.m_emitter.registerResolvedTypeReference(pargs[i][1]);
            argTypes.set(this.m_emitter.bodyEmitter.generateCapturedVarName(pargs[i][0]), ctype);
            params.push(new MIRFunctionParameter(this.m_emitter.bodyEmitter.generateCapturedVarName(pargs[i][0]), ctype.trkey));
        }

        const resolvedResult = this.resolveAndEnsureTypeOnly(sinfo, invoke.resultType, binds);
        let resultType = this.m_emitter.registerResolvedTypeReference(resolvedResult);
        if (invoke.params.some((p) => p.isRef)) {
            const pout = invoke.params.filter((p) => p.isRef).map((p) => this.m_emitter.registerResolvedTypeReference(this.resolveAndEnsureTypeOnly(sinfo, p.type, binds)));
            resultType = MIRType.createSingle(MIRTupleType.create([resultType, ...pout].map((tt) => new MIRTupleTypeEntry(tt, false))));
        }

        const iscope = MIRKeyGenerator.generateBodyKey("invoke", ikey);
        const env = TypeEnvironment.createInitialEnvForCall(iscope, binds, refNames, fargs, cargs);

        const prescope = MIRKeyGenerator.generateBodyKey("pre", ikey);
        const preargs = new Map<string, VarInfo>(cargs);
        const preconds: [MIRBody, boolean][] = invoke.preconditions.filter((pre) => this.m_doPrePostCheck || pre[1]).map<[MIRBody, boolean]>((pre) => {
            const preenv = TypeEnvironment.createInitialEnvForCall(prescope, binds, [], fargs, preargs);
            return [this.checkExpressionAsBody(preenv, prescope, pre[0], this.m_assembly.getSpecialBoolType()), pre[1]];
        });

        const postscope = MIRKeyGenerator.generateBodyKey("post", ikey);
        const postargs = new Map<string, VarInfo>(cargs).set("_return_", new VarInfo(resolvedResult, true, false, true, resolvedResult));
        const postconds = invoke.postconditions.filter((post) => this.m_doPrePostCheck).map((post) => {
            const postenv = TypeEnvironment.createInitialEnvForCall(postscope, binds, [], fargs, postargs);
            return this.checkExpressionAsBody(postenv, postscope, post, this.m_assembly.getSpecialBoolType());
        });

        if (typeof ((invoke.body as BodyImplementation).body) === "string") {
            let mpc = new Map<string, MIRPCode>();
            fargs.forEach((v, k) => mpc.set(k, { code: MIRKeyGenerator.generatePCodeKey(v.pcode.code), cargs: [...v.captured].map((cname) => this.m_emitter.bodyEmitter.generateCapturedVarName(cname)) }));

            let mbinds = new Map<string, MIRResolvedTypeKey>();
            binds.forEach((v, k) => mbinds.set(k, this.m_emitter.registerResolvedTypeReference(v).trkey));

            return new MIRInvokePrimitiveDecl(enclosingDecl, iname, ikey, invoke.attributes, recursive, pragmas, sinfo, invoke.srcFile, mbinds, params, resultType.trkey, preconds, postconds, (invoke.body as BodyImplementation).body as string, mpc);
        }
        else {
            const mirbody = this.checkBody(env, invoke.body as BodyImplementation, argTypes, resolvedResult);
            this.raiseErrorIf(sinfo, mirbody === undefined, "Type check of body failed");

            return new MIRInvokeBodyDecl(enclosingDecl, iname, ikey, invoke.attributes, recursive, pragmas, sinfo, invoke.srcFile, params, resultType.trkey, preconds, postconds, mirbody as MIRBody);
        }
    }

    private processPCodeInfo(iname: string, ikey: MIRInvokeKey, sinfo: SourceInfo, pci: InvokeDecl, binds: Map<string, ResolvedType>, fsig: ResolvedFunctionType, pargs: [string, ResolvedType][]): MIRInvokeDecl {
        this.checkPCodeDecl(sinfo, fsig, pci.recursive);

        const pragmas = this.processPragmas(pci.sourceLocation, pci.pragmas);

        let cargs = new Map<string, VarInfo>();
        let fargs = new Map<string, { pcode: PCode, captured: string[] }>();
        let argTypes: Map<string, MIRType> = new Map<string, MIRType>();
        let refNames: string[] = [];
        let params: MIRFunctionParameter[] = [];

        for (let i = 0; i < pci.params.length; ++i) {
            const p = fsig.params[i];
            const ptype = p.isOptional ? this.m_assembly.typeUnion([p.type as ResolvedType, this.m_assembly.getSpecialNoneType()]) : p.type as ResolvedType;
            cargs.set(pci.params[i].name, new VarInfo(ptype, !p.isRef, false, true, ptype));

            if (p.isRef) {
                refNames.push(p.name);
            }

            const mtype = this.m_emitter.registerResolvedTypeReference(ptype);
            argTypes.set(pci.params[i].name, mtype);
            params.push(new MIRFunctionParameter(pci.params[i].name, mtype.trkey));
        }

        if (fsig.optRestParamType !== undefined) {
            cargs.set(pci.optRestName as string, new VarInfo(fsig.optRestParamType, true, false, true, fsig.optRestParamType));

            const resttype = this.m_emitter.registerResolvedTypeReference(fsig.optRestParamType);
            argTypes.set(pci.optRestName as string, resttype);
            params.push(new MIRFunctionParameter(pci.optRestName as string, resttype.trkey));
        }

        for (let i = 0; i < pargs.length; ++i) {
            cargs.set(pargs[i][0], new VarInfo(pargs[i][1], true, true, true, pargs[i][1]));

            const ctype = this.m_emitter.registerResolvedTypeReference(pargs[i][1]);
            argTypes.set(this.m_emitter.bodyEmitter.generateCapturedVarName(pargs[i][0]), ctype);
            params.push(new MIRFunctionParameter(this.m_emitter.bodyEmitter.generateCapturedVarName(pargs[i][0]), ctype.trkey));
        }

        let resultType = this.m_emitter.registerResolvedTypeReference(fsig.resultType);
        if (fsig.params.some((p) => p.isRef)) {
            const pout = fsig.params.filter((p) => p.isRef).map((p) => this.m_emitter.registerResolvedTypeReference(p.type as ResolvedType));
            resultType = MIRType.createSingle(MIRTupleType.create([resultType, ...pout].map((tt) => new MIRTupleTypeEntry(tt, false))));
        }

        const env = TypeEnvironment.createInitialEnvForCall(MIRKeyGenerator.generateBodyKey("invoke", ikey), binds, refNames, fargs, cargs);
        const mirbody = this.checkBody(env, pci.body as BodyImplementation, argTypes, fsig.resultType);
        this.raiseErrorIf(sinfo, mirbody === undefined, "Type check of body failed");

        return new MIRInvokeBodyDecl(undefined, iname, ikey, pci.attributes, pci.recursive === "yes", pragmas, sinfo, pci.srcFile, params, resultType.trkey, [], [], mirbody as MIRBody);
    }

    processNamespaceFunction(fkey: MIRInvokeKey, f: NamespaceFunctionDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
        try {
            this.m_file = f.srcFile;
            const iname = `${f.ns}::${f.name}`;
            const invinfo = this.processInvokeInfo(undefined, iname, fkey, f.sourceLocation, f.invoke, binds, pcodes, cargs);

            if (invinfo instanceof MIRInvokePrimitiveDecl) {
                this.m_emitter.masm.primitiveInvokeDecls.set(fkey, invinfo);
            }
            else {
                this.m_emitter.masm.invokeDecls.set(fkey, invinfo as MIRInvokeBodyDecl);
            }

            if (f.attributes.includes("entrypoint")) {
                this.m_emitter.masm.entryPoints.push(invinfo.key);
            }
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    processLambdaFunction(lkey: MIRInvokeKey, invoke: InvokeDecl, sigt: ResolvedFunctionType, binds: Map<string, ResolvedType>, cargs: [string, ResolvedType][]) {
        try {
            this.m_file = invoke.srcFile;
            const iname = `fn::${invoke.sourceLocation.line}`;
            const invinfo = this.processPCodeInfo(iname, lkey, invoke.sourceLocation, invoke, binds, sigt, cargs);

            if (invinfo instanceof MIRInvokePrimitiveDecl) {
                this.m_emitter.masm.primitiveInvokeDecls.set(lkey, invinfo);
            }
            else {
                this.m_emitter.masm.invokeDecls.set(lkey, invinfo as MIRInvokeBodyDecl);
            }
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    processStaticFunction(skey: MIRInvokeKey, ctype: OOPTypeDecl, cbinds: Map<string, ResolvedType>, sfdecl: StaticFunctionDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
        try {
            this.m_file = sfdecl.srcFile;
            const enclosingdecl = MIRKeyGenerator.generateTypeKey(ctype, cbinds);
            const iname = `${ctype.ns}::${ctype.name}::${sfdecl.name}`;
            const invinfo = this.processInvokeInfo(enclosingdecl, iname, skey, sfdecl.sourceLocation, sfdecl.invoke, binds, pcodes, cargs);

            if (invinfo instanceof MIRInvokePrimitiveDecl) {
                this.m_emitter.masm.primitiveInvokeDecls.set(skey, invinfo);
            }
            else {
                this.m_emitter.masm.invokeDecls.set(skey, invinfo as MIRInvokeBodyDecl);
            }
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    processMethodFunction(vkey: MIRVirtualMethodKey, mkey: MIRInvokeKey, ctype: OOPTypeDecl, cbinds: Map<string, ResolvedType>, mdecl: MemberMethodDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
        if (this.m_emitter.masm.primitiveInvokeDecls.has(mkey) || this.m_emitter.masm.invokeDecls.has(mkey)) {
            return;
        }

        try {
            this.m_file = mdecl.srcFile;
            const enclosingdecl = MIRKeyGenerator.generateTypeKey(ctype, cbinds);
            const iname = `${ctype.ns}::${ctype.name}->${mdecl.name}`;
            const invinfo = this.processInvokeInfo(enclosingdecl, iname, mkey, mdecl.sourceLocation, mdecl.invoke, binds, pcodes, cargs);

            if (invinfo instanceof MIRInvokePrimitiveDecl) {
                this.m_emitter.masm.primitiveInvokeDecls.set(mkey, invinfo);
            }
            else {
                this.m_emitter.masm.invokeDecls.set(mkey, invinfo as MIRInvokeBodyDecl);
            }

            const tkey = MIRKeyGenerator.generateTypeKey(ctype, cbinds);
            if (ctype instanceof EntityTypeDecl) {
                (this.m_emitter.masm.entityDecls.get(tkey) as MIROOTypeDecl).vcallMap.set(vkey, mkey);
            }
            else {
                (this.m_emitter.masm.conceptDecls.get(tkey) as MIROOTypeDecl).vcallMap.set(vkey, mkey);
            }
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }
}

export { TypeError, TypeChecker };
