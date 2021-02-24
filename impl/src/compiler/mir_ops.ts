//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo } from "../ast/parser";
import { topologicalOrder, computeBlockLinks, FlowLink } from "./mir_info";
import { BSQRegex } from "../ast/bsqregex";

import assert = require("assert");

type MIRGlobalKey = string; //$global_IKEY
type MIRFieldKey = string; //ns::name::field#binds
type MIRInvokeKey = string; //ns::[type]::func#binds%code

type MIRResolvedTypeKey = string; //idstr
type MIRVirtualMethodKey = string; //method#binds

//
//Probably want to declare a MIRSourceInfo class
//
function jemitsinfo(sinfo: SourceInfo): object {
    return { line: sinfo.line, column: sinfo.column, pos: sinfo.pos, span: sinfo.span };
}

function jparsesinfo(jobj: any): SourceInfo {
    return new SourceInfo(jobj.line, jobj.column, jobj.pos, jobj.span);
}

abstract class MIRGuard {
    abstract stringify(): string;
    abstract jemit(): object;

    static jparse(gg: any) : MIRGuard {
        if(gg.kind === "ArgGuard") {
            return MIRArgGuard.jparse(gg);
        }
        else {
            return MIRMaskGuard.jparse(gg);
        }
    }
}

class MIRArgGuard extends MIRGuard {
    greg: MIRArgument;

    constructor(greg: MIRArgument) {
        super();

        this.greg = greg;
    }

    stringify(): string {
        return this.greg.stringify();
    }

    jemit(): object {
        return { kind: "ArgGuard", greg: this.greg.jemit() };
    }

    static jparse(gg: any): MIRArgGuard {
        return new MIRArgGuard(MIRArgument.jparse(gg.greg));
    }
}

class MIRMaskGuard extends MIRGuard {
    readonly gmask: string;
    readonly gindex: number;
    readonly gsize: number;

    constructor(gmask: string, gindex: number, gsize: number) {
        super();

        this.gmask = gmask;
        this.gindex = gindex;
        this.gsize = gsize;
    }

    stringify(): string {
        return `${this.gmask}[${this.gindex}]`;
    }

    jemit(): object {
        return { kind: "MaskGuard", gmask: this.gmask, gindex: this.gindex, gsize: this.gsize };
    }

    static jparse(gg: any): MIRMaskGuard {
        return new MIRMaskGuard(gg.gmask, gg.gindex, gg.gsize);
    }
}

class MIRStatmentGuard {
    readonly guard: MIRGuard;
    readonly altvalue: MIRArgument | undefined;

    constructor(guard: MIRGuard, altvalue: MIRArgument | undefined) {
        this.guard = guard;
        this.altvalue = altvalue;
    }

    stringify(): string {
        return `${this.guard.stringify()} or ${this.altvalue !== undefined ? this.altvalue.stringify() : "UNINIT"}`;
    }

    jemit(): object {
        return { guard: this.guard.jemit(), altvalue: this.altvalue !== undefined ? this.altvalue.jemit() : undefined };
    }

    static jparse(gg: any): MIRStatmentGuard {
        return new MIRStatmentGuard(MIRGuard.jparse(gg.guard), gg.altvalue !== undefined ? MIRArgument.jparse(gg.altvalue) : undefined);
    }
}

abstract class MIRArgument {
    readonly nameID: string;

    constructor(nameID: string) {
        this.nameID = nameID;
    }

    abstract stringify(): string;

    abstract jemit(): object;

    static jparse(jobj: any): MIRArgument {
        if(jobj === null) {
            return new MIRConstantNone;
        }
        else if(typeof(jobj) === "boolean") {
            return jobj ? new MIRConstantTrue() : new MIRConstantFalse();
        }
        else if(typeof(jobj) === "string") {
            return new MIRConstantString(jobj);
        }
        else {
            const ckind = jobj.constkind;
            switch(ckind) {
                case "int":
                    return new MIRConstantInt(jobj.value);
                case "nat":
                    return new MIRConstantNat(jobj.value);
                case "bigint":
                    return new MIRConstantBigInt(jobj.value);
                case "bignat":
                    return new MIRConstantBigNat(jobj.value);
                case "rational":
                    return new MIRConstantRational(jobj.value);
                case "float":
                    return new MIRConstantFloat(jobj.value);
                case "decimal":
                    return new MIRConstantDecimal(jobj.value);
                case "stringof":
                    return new MIRConstantStringOf(jobj.value, jobj.oftype);
                case "datastring":
                    return new MIRConstantDataString(jobj.value, jobj.oftype);
                case "typednumber":
                    return new MIRConstantTypedNumber(MIRArgument.jparse(jobj.value), jobj.oftype);
                default:
                    return new MIRConstantRegex(jobj.value);
            }
        }
    }
}

class MIRRegisterArgument extends MIRArgument {
    readonly origname: string;

    constructor(nameID: string, origname?: string) {
        super(nameID);

        this.origname = origname || nameID;
    }

    stringify(): string {
        return this.nameID;
    }

    jemit(): object {
        return { tag: "register", nameID: this.nameID };
    }

    static jparse(jobj: any): MIRRegisterArgument {
        return new MIRRegisterArgument(jobj.nameID);
    }
}

class MIRGlobalVariable extends MIRArgument {
    readonly gkey: MIRGlobalKey;
    constructor(gkey: MIRGlobalKey) {
        super(gkey);

        this.gkey = gkey;
    }

    stringify(): string {
        return this.gkey;
    }

    jemit(): object {
        return { tag: "global", gkey: this.nameID };
    }

    static jparse(jobj: any): MIRGlobalVariable {
        return new MIRGlobalVariable(jobj.gkey);
    }
}

abstract class MIRConstantArgument extends MIRArgument {
    constructor(name: string) {
        super(name);
    }
}

class MIRConstantNone extends MIRConstantArgument {
    constructor() {
        super("=none=");
    }

    stringify(): string {
        return "none";
    }

    jemit(): any {
        return null;
    }
}

class MIRConstantTrue extends MIRConstantArgument {
    constructor() {
        super("=true=");
    }

    stringify(): string {
        return "true";
    }

    jemit(): any {
        return true;
    }
}

class MIRConstantFalse extends MIRConstantArgument {
    constructor() {
        super("=false=");
    }

    stringify(): string {
        return "false";
    }

    jemit(): any {
        return false;
    }
}

class MIRConstantInt extends MIRConstantArgument {
    readonly value: string;

    constructor(value: string) {
        super(`=int=${value}`);

        this.value = value;
    }

    stringify(): string {
        return this.value;
    }

    jemit(): any {
        return { constkind: "int", value: this.value };
    }
}

class MIRConstantNat extends MIRConstantArgument {
    readonly value: string;

    constructor(value: string) {
        super(`=nat=${value}`);

        this.value = value;
    }

    stringify(): string {
        return this.value;
    }

    jemit(): any {
        return { constkind: "nat", value: this.value };
    }
}

class MIRConstantBigInt extends MIRConstantArgument {
    readonly value: string;

    constructor(value: string) {
        super(`=bigint=${value}`);

        this.value = value;
    }

    stringify(): string {
        return this.value;
    }

    jemit(): any {
        return { constkind: "bigint", value: this.value };
    }
}

class MIRConstantBigNat extends MIRConstantArgument {
    readonly value: string;

    constructor(value: string) {
        super(`=bignat=${value}`);

        this.value = value;
    }

    stringify(): string {
        return this.value;
    }

    jemit(): any {
        return { constkind: "bignat", value: this.value };
    }
}

class MIRConstantRational extends MIRConstantArgument {
    readonly value: string;

    constructor(value: string) {
        super(`=rational=${value}`);

        this.value = value;
    }

    stringify(): string {
        return this.value;
    }

    jemit(): any {
        return { constkind: "rational", value: this.value };
    }
}

class MIRConstantFloat extends MIRConstantArgument {
    readonly value: string;

    constructor(value: string) {
        super(`=float=${value}`);

        this.value = value;
    }

    stringify(): string {
        return this.value;
    }

    jemit(): any {
        return { constkind: "float", value: this.value };
    }
}

class MIRConstantDecimal extends MIRConstantArgument {
    readonly value: string;

    constructor(value: string) {
        super(`=decimal=${value}`);

        this.value = value;
    }
    
    stringify(): string {
        return this.value;
    }

    jemit(): any {
        return { constkind: "decimal", value: this.value };
    }
}

class MIRConstantString extends MIRConstantArgument {
    readonly value: string;

    constructor(value: string) {
        super(`=string=${value}`);

        this.value = value;
    }

    stringify(): string {
        return this.value;
    }

    jemit(): any {
        return this.value;
    }
}

class MIRConstantRegex extends MIRConstantArgument {
    readonly value: BSQRegex;

    constructor(value: BSQRegex) {
        super(`=regex=${value.restr}`);

        this.value = value;
    }

    stringify(): string {
        return this.value.restr;
    }

    jemit(): any {
        return { constkind: "regex", value: this.value.jemit() };
    }
}

class MIRConstantStringOf extends MIRConstantArgument {
    readonly value: string;
    readonly tskey: MIRResolvedTypeKey;

    constructor(value: string, tskey: MIRResolvedTypeKey) {
        super(`=stringof=${tskey} of ${value}`);

        this.value = value;
        this.tskey = tskey;
    }

    stringify(): string {
        return `${this.tskey} of ${this.value}`;
    }

    jemit(): any {
        return { constkind: "stringof", value: this.value, oftype: this.tskey };
    }
}

class MIRConstantDataString extends MIRConstantArgument {
    readonly value: string;
    readonly tskey: MIRResolvedTypeKey;

    constructor(value: string, tskey: MIRResolvedTypeKey) {
        super(`=datastring=${tskey} of ${value}`);

        this.value = value;
        this.tskey = tskey;
    }

    stringify(): string {
        return `${this.tskey} of ${this.value}`;
    }

    jemit(): any {
        return { constkind: "datastring", value: this.value, oftype: this.tskey };
    }
}

class MIRConstantTypedNumber extends MIRConstantArgument {
    readonly value: MIRConstantArgument;
    readonly tnkey: MIRResolvedTypeKey;

    constructor(value: MIRConstantArgument, tnkey: MIRResolvedTypeKey) {
        super(`=typednumber=${tnkey} of ${value.stringify()}`);

        this.value = value;
        this.tnkey = tnkey;
    }

    stringify(): string {
        return `${this.tnkey} of ${this.value}`;
    }

    jemit(): any {
        return { constkind: "typednumber", value: this.value.jemit(), oftype: this.tnkey };
    }
}

enum MIROpTag {
    MIRNop = "MIRNop",
    MIRDeadFlow = "MIRDeadFlow",
    MIRAbort = "MIRAbort",
    MIRAssertCheck = "MIRAssertCheck",
    MIRDebug = "MIRDebug",

    MIRLoadUnintVariableValue = "MIRLoadUnintVariableValue",
    MIRDeclareGuardFlagLocation = "MIRDeclareGuardFlagLocation",
    MIRSetConstantGuardFlag = "MIRSetConstantGuardFlag",
    MIRConvertValue = "MIRConvertValue",

    MIRLoadConst = "MIRLoadConst",

    MIRTupleHasIndex = "MIRTupleHasIndex",
    MIRRecordHasProperty = "MIRRecordHasProperty",
    MIRLoadTupleIndex = "MIRLoadTupleIndex",
    MIRLoadTupleIndexSetGuard = "MIRLoadTupleIndexSetGuard",
    MIRLoadRecordProperty = "MIRLoadRecordProperty",
    MIRLoadRecordPropertySetGuard = "MIRLoadRecordPropertySetGuard",

    MIRLoadField = "MIRLoadField",

    MIRTupleProjectToEphemeral = "MIRTupleProjectToEphemeral",
    MIRRecordProjectToEphemeral = "MIRRecordProjectToEphemeral",
    MIREntityProjectToEphemeral = "MIREntityProjectToEphemeral",
    MIRTupleUpdate = "MIRTupleUpdate",
    MIRRecordUpdate = "MIRRecordUpdate",
    MIREntityUpdate = "MIREntityUpdate",

    MIRLoadFromEpehmeralList = "MIRLoadFromEpehmeralList",
    MIRMultiLoadFromEpehmeralList = "MIRMultiLoadFromEpehmeralList",
    MIRSliceEpehmeralList = "MIRSliceEpehmeralList",

    MIRInvokeFixedFunction = "MIRInvokeFixedFunction",
    MIRInvokeVirtualFunction = "MIRInvokeVirtualFunction",
    MIRInvokeVirtualOperator = "MIRInvokeVirtualOperator",

    MIRConstructorTuple = "MIRConstructorTuple",
    MIRConstructorTupleFromEphemeralList = "MIRConstructorTupleFromEphemeralList",
    MIRConstructorRecord = "MIRConstructorRecord",
    MIRConstructorRecordFromEphemeralList = "MIRConstructorRecordFromEphemeralList",
    MIRStructuredAppendTuple = "MIRStructuredAppendTuple",
    MIRStructuredJoinRecord = "MIRStructuredJoinRecord",
    MIRConstructorEphemeralList = "MIRConstructorEphemeralList",
    MIREphemeralListExtend = "MIREphemeralListExtend",

    MIRConstructorPrimaryCollectionEmpty = "MIRConstructorPrimaryCollectionEmpty",
    MIRConstructorPrimaryCollectionSingletons = "MIRConstructorPrimaryCollectionSingletons",
    MIRConstructorPrimaryCollectionCopies = "MIRConstructorPrimaryCollectionCopies",
    MIRConstructorPrimaryCollectionMixed = "MIRConstructorPrimaryCollectionMixed",

    MIRBinKeyEq = "MIRBinKeyEq",
    MIRBinKeyLess = "MIRBinKeyLess",
    MIRPrefixNotOp = "MIRPrefixNotOp",
    MIRAllTrue = "MIRAllTrue",
    MIRSomeTrue = "MIRSomeTrue",

    MIRIsTypeOf = "MIRIsTypeOf",

    MIRJump = "MIRJump",
    MIRJumpCond = "MIRJumpCond",
    MIRJumpNone = "MIRJumpNone",

    MIRRegisterAssign = "MIRRegisterAssign",
    MIRReturnAssign = "MIRReturnAssign",
    MIRReturnAssignOfCons = "MIRReturnAssignOfCons",
    MIRVarLifetimeStart = "MIRVarLifetimeStart",
    MIRVarLifetimeEnd = "MIRVarLifetimeEnd",

    MIRPhi = "MIRPhi"
}

function varsOnlyHelper(args: MIRArgument[]): MIRRegisterArgument[] {
    return args.filter((arg) => arg instanceof MIRRegisterArgument) as MIRRegisterArgument[];
}

abstract class MIROp {
    readonly tag: MIROpTag;
    readonly sinfo: SourceInfo;

    constructor(tag: MIROpTag, sinfo: SourceInfo) {
        this.tag = tag;
        this.sinfo = sinfo;
    }

    abstract getUsedVars(): MIRRegisterArgument[];
    abstract getModVars(): MIRRegisterArgument[];

    abstract stringify(): string;

    canRaise(implicitAssumesEnabled: boolean): boolean {
        return false;
    }

    protected jbemit(): object {
        return { tag: this.tag, sinfo: jemitsinfo(this.sinfo) };
    }

    abstract jemit(): object;

    static jparse(jobj: any & { tag: string }): MIROp {
        switch (jobj.tag) {
            case MIROpTag.MIRNop:
                return MIRNop.jparse(jobj);
            case MIROpTag.MIRDeadFlow:
                return MIRDeadFlow.jparse(jobj);
            case MIROpTag.MIRAbort:
                return MIRAbort.jparse(jobj);
            case MIROpTag.MIRAssertCheck:
                return MIRAssertCheck.jparse(jobj);
            case MIROpTag.MIRDebug:
                return MIRDebug.jparse(jobj);
            case MIROpTag.MIRLoadUnintVariableValue:
                return MIRLoadUnintVariableValue.jparse(jobj);
            case MIROpTag.MIRDeclareGuardFlagLocation:
                return MIRDeclareGuardFlagLocation.jparse(jobj);
            case MIROpTag.MIRSetConstantGuardFlag:
                return MIRSetConstantGuardFlag.jparse(jobj);
            case MIROpTag.MIRConvertValue:
                return MIRConvertValue.jparse(jobj);
            case MIROpTag.MIRLoadConst:
                return MIRLoadConst.jparse(jobj);
            case MIROpTag.MIRTupleHasIndex:
                return MIRTupleHasIndex.jparse(jobj);
            case MIROpTag.MIRRecordHasProperty:
                return MIRRecordHasProperty.jparse(jobj);
            case MIROpTag.MIRLoadTupleIndex:
                return MIRLoadTupleIndex.jparse(jobj);
            case MIROpTag.MIRLoadTupleIndexSetGuard:
                return MIRLoadTupleIndexSetGuard.jparse(jobj);
            case MIROpTag.MIRLoadRecordProperty:
                return MIRLoadRecordProperty.jparse(jobj);
            case MIROpTag.MIRLoadRecordPropertySetGuard:
                return MIRLoadRecordPropertySetGuard.jparse(jobj);
            case MIROpTag.MIRLoadField:
                return MIRLoadField.jparse(jobj);
            case MIROpTag.MIRTupleProjectToEphemeral:
                return MIRTupleProjectToEphemeral.jparse(jobj);
            case MIROpTag.MIRRecordProjectToEphemeral:
                return MIRRecordProjectToEphemeral.jparse(jobj);
            case MIROpTag.MIREntityProjectToEphemeral:
                return MIREntityProjectToEphemeral.jparse(jobj);
            case MIROpTag.MIRTupleUpdate:
                return MIRTupleUpdate.jparse(jobj);
            case MIROpTag.MIRRecordUpdate:
                return MIRRecordUpdate.jparse(jobj);
            case MIROpTag.MIREntityUpdate:
                return MIREntityUpdate.jparse(jobj);
            case MIROpTag.MIRLoadFromEpehmeralList:
                return MIRLoadFromEpehmeralList.jparse(jobj);
            case MIROpTag.MIRMultiLoadFromEpehmeralList:
                return MIRMultiLoadFromEpehmeralList.jparse(jobj);
            case MIROpTag.MIRSliceEpehmeralList:
                return MIRSliceEpehmeralList.jparse(jobj);
            case MIROpTag.MIRInvokeFixedFunction:
                return MIRInvokeFixedFunction.jparse(jobj);
            case MIROpTag.MIRInvokeVirtualFunction:
                return MIRInvokeVirtualFunction.jparse(jobj);
            case MIROpTag.MIRInvokeVirtualOperator:
                return MIRInvokeVirtualOperator.jparse(jobj); 
            case MIROpTag.MIRConstructorTuple:
                return MIRConstructorTuple.jparse(jobj);
            case MIROpTag.MIRConstructorTupleFromEphemeralList:
                return MIRConstructorTupleFromEphemeralList.jparse(jobj);
            case MIROpTag.MIRConstructorRecord:
                return MIRConstructorRecord.jparse(jobj);
            case MIROpTag.MIRConstructorRecordFromEphemeralList:
                return MIRConstructorRecordFromEphemeralList.jparse(jobj);
            case MIROpTag.MIRStructuredAppendTuple:
                return MIRStructuredAppendTuple.jparse(jobj);
            case MIROpTag.MIRStructuredJoinRecord:
                return MIRStructuredJoinRecord.jparse(jobj);
            case MIROpTag.MIRConstructorEphemeralList:
                return MIRConstructorEphemeralList.jparse(jobj);
            case MIROpTag.MIREphemeralListExtend:
                return MIREphemeralListExtend.jparse(jobj);
            case MIROpTag.MIRConstructorPrimaryCollectionEmpty:
                return MIRConstructorPrimaryCollectionEmpty.jparse(jobj);
            case MIROpTag.MIRConstructorPrimaryCollectionSingletons:
                return MIRConstructorPrimaryCollectionSingletons.jparse(jobj);
            case MIROpTag.MIRConstructorPrimaryCollectionCopies:
                return MIRConstructorPrimaryCollectionCopies.jparse(jobj);
            case MIROpTag.MIRConstructorPrimaryCollectionMixed:
                return MIRConstructorPrimaryCollectionMixed.jparse(jobj);
            case MIROpTag.MIRBinKeyEq:
                return MIRBinKeyEq.jparse(jobj);
            case MIROpTag.MIRBinKeyLess:
                return MIRBinKeyLess.jparse(jobj);
            case MIROpTag.MIRPrefixNotOp:
                return MIRPrefixNotOp.jparse(jobj);
            case MIROpTag.MIRAllTrue:
                return MIRAllTrue.jparse(jobj);
            case MIROpTag.MIRSomeTrue:
                return MIRSomeTrue.jparse(jobj);
            case MIROpTag.MIRIsTypeOf:
                return MIRIsTypeOf.jparse(jobj);
            case MIROpTag.MIRJump:
                return MIRJump.jparse(jobj);
            case MIROpTag.MIRJumpCond:
                return MIRJumpCond.jparse(jobj);
            case MIROpTag.MIRJumpNone:
                return MIRJumpNone.jparse(jobj);
            case MIROpTag.MIRRegisterAssign:
                return MIRRegisterAssign.jparse(jobj);
            case MIROpTag.MIRReturnAssign:
                return MIRReturnAssign.jparse(jobj);
            case MIROpTag.MIRReturnAssignOfCons:
                return MIRReturnAssignOfCons.jparse(jobj);
            case MIROpTag.MIRVarLifetimeStart:
                return MIRVarLifetimeStart.jparse(jobj);
            case MIROpTag.MIRVarLifetimeEnd:
                return MIRVarLifetimeEnd.jparse(jobj);
            default:
                assert(jobj.tag === MIROpTag.MIRPhi);
                return MIRPhi.jparse(jobj);
        }
    }
}

class MIRNop extends MIROp {
    constructor(sinfo: SourceInfo) {
        super(MIROpTag.MIRNop, sinfo);
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `nop`;
    }

    jemit(): object {
        return { ...this.jbemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRNop(jparsesinfo(jobj.sinfo));
    }
}

class MIRDeadFlow extends MIROp {
    constructor(sinfo: SourceInfo) {
        super(MIROpTag.MIRDeadFlow, sinfo);
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `dead-flow`;
    }

    jemit(): object {
        return { ...this.jbemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRNop(jparsesinfo(jobj.sinfo));
    }
}

class MIRAbort extends MIROp {
    readonly info: string;

    constructor(sinfo: SourceInfo, info: string) {
        super(MIROpTag.MIRAbort, sinfo);

        this.info = info;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `abort -- ${this.info}`;
    }

    canRaise(implicitAssumesEnabled: boolean): boolean {
        return true;
    }

    jemit(): object {
        return { ...this.jbemit(), info: this.info };
    }

    static jparse(jobj: any): MIROp {
        return new MIRAbort(jparsesinfo(jobj.sinfo), jobj.info);
    }
}

class MIRAssertCheck extends MIROp {
    readonly info: string;
    arg: MIRArgument;

    constructor(sinfo: SourceInfo, info: string, arg: MIRArgument) {
        super(MIROpTag.MIRAssertCheck, sinfo);

        this.info = info;
        this.arg = arg;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `assert ${this.arg.stringify()} -- ${this.info}`;
    }

    canRaise(implicitAssumesEnabled: boolean): boolean {
        return true;
    }

    jemit(): object {
        return { ...this.jbemit(), info: this.info, arg: this.arg.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRAssertCheck(jparsesinfo(jobj.sinfo), jobj.info, MIRArgument.jparse(jobj.arg));
    }
}

class MIRDebug extends MIROp {
    value: MIRArgument | undefined;

    constructor(sinfo: SourceInfo, value: MIRArgument | undefined) {
        super(MIROpTag.MIRDebug, sinfo);

        this.value = value;
    }

    getUsedVars(): MIRRegisterArgument[] { return this.value !== undefined ? varsOnlyHelper([this.value]) : []; }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        if (this.value === undefined) {
            return "_debug break";
        }
        else {
            return `_debug ${this.value.stringify()}`;
        }
    }

    jemit(): object {
        return { ...this.jbemit(), value: this.value ? [this.value.jemit()] : null };
    }

    static jparse(jobj: any): MIROp {
        return new MIRDebug(jparsesinfo(jobj.sinfo), jobj.value ? MIRArgument.jparse(jobj.value[0]) : undefined);
    }
}

class MIRLoadUnintVariableValue extends MIROp {
    trgt: MIRRegisterArgument;
    readonly oftype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, trgt: MIRRegisterArgument, oftype: MIRResolvedTypeKey) {
        super(MIROpTag.MIRLoadUnintVariableValue, sinfo);

        this.trgt = trgt;
        this.oftype = oftype;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.oftype}(*)`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt, oftype: this.oftype };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadUnintVariableValue(jparsesinfo(jobj.sinfo), MIRRegisterArgument.jparse(jobj.trgt), jobj.oftype);
    }
}

class MIRDeclareGuardFlagLocation extends MIROp {
    readonly name: string;
    readonly count: number;

    constructor(sinfo: SourceInfo, name: string, count: number) {
        super(MIROpTag.MIRDeclareGuardFlagLocation, sinfo);

        this.name = name;
        this.count = count;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `${this.name}[[${this.count}]]`;
    }

    jemit(): object {
        return { ...this.jbemit(), name: this.name, count: this.count };
    }

    static jparse(jobj: any): MIROp {
        return new MIRDeclareGuardFlagLocation(jparsesinfo(jobj.sinfo), jobj.name, jobj.count);
    }
}

class MIRSetConstantGuardFlag extends MIROp {
    readonly name: string;
    readonly position: number;
    readonly flag: boolean;

    constructor(sinfo: SourceInfo, name: string, position: number, flag: boolean) {
        super(MIROpTag.MIRSetConstantGuardFlag, sinfo);

        this.name = name;
        this.position = position;
        this.flag = flag;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `${this.name}[[${this.position}]] = ${this.flag}`;
    }

    jemit(): object {
        return { ...this.jbemit(), name: this.name, position: this.position, flag: this.flag };
    }

    static jparse(jobj: any): MIROp {
        return new MIRSetConstantGuardFlag(jparsesinfo(jobj.sinfo), jobj.name, jobj.position, jobj.flag);
    }
}

class MIRConvertValue extends MIROp {
    trgt: MIRRegisterArgument;
    readonly srctypelayout: MIRResolvedTypeKey;
    readonly srctypeflow: MIRResolvedTypeKey;
    readonly intotype: MIRResolvedTypeKey;
    src: MIRArgument;
    guard: MIRStatmentGuard | undefined;

    constructor(sinfo: SourceInfo, srctypelayout: MIRResolvedTypeKey, srctypeflow: MIRResolvedTypeKey, intotype: MIRResolvedTypeKey, src: MIRArgument, trgt: MIRRegisterArgument, guard: MIRStatmentGuard | undefined) {
        super(MIROpTag.MIRConvertValue, sinfo);

        this.trgt = trgt;
        this.srctypelayout = srctypelayout;
        this.srctypeflow = srctypeflow;
        this.intotype = intotype;
        this.src = src;
        this.guard = guard;
    }

    getUsedVars(): MIRRegisterArgument[] { return (this.guard !== undefined && this.guard instanceof MIRArgGuard) ? varsOnlyHelper([this.guard.greg, this.src]) : varsOnlyHelper([this.src]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        const gstring = this.guard !== undefined ? ` | ${this.guard.stringify()}` : "";
        return `${this.trgt.stringify()} = ${this.src} convert ${this.intotype}${gstring}`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), srctypelayout: this.srctypelayout, srctypeflow: this.srctypeflow, intotype: this.intotype, src: this.src.jemit(), guard: this.guard !== undefined ? this.guard.jemit() : undefined };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConvertValue(jparsesinfo(jobj.sinfo), jobj.srctypelayout, jobj.srctypeflow, jobj.intotype, MIRArgument.jparse(jobj.src), MIRRegisterArgument.jparse(jobj.trgt), jobj.guard !== undefined ? MIRStatmentGuard.jparse(jobj.guard) : undefined);
    }
}

class MIRLoadConst extends MIROp {
    trgt: MIRRegisterArgument;
    readonly src: MIRConstantArgument;
    readonly consttype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, src: MIRConstantArgument, consttype: MIRResolvedTypeKey, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRLoadConst, sinfo);

        this.trgt = trgt;
        this.src = src;
        this.consttype = consttype;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.src.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), consttype: this.consttype, src: this.src.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadConst(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src) as MIRConstantArgument, jobj.consttype, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRTupleHasIndex extends MIROp {
    trgt: MIRRegisterArgument;
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    readonly idx: number;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, idx: number, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRTupleHasIndex, sinfo);

        this.trgt = trgt;
        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.idx = idx;
    }
    
    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.hasIndex<${this.idx}>()`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, idx: this.idx };
    }

    static jparse(jobj: any): MIROp {
        return new MIRTupleHasIndex(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, jobj.idx, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRRecordHasProperty extends MIROp {
    trgt: MIRRegisterArgument;
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    readonly pname: string;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, pname: string, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRRecordHasProperty, sinfo);

        this.trgt = trgt;
        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.pname = pname;
    }
    
    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.hasProperty<${this.pname}>()`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, pname: this.pname };
    }

    static jparse(jobj: any): MIROp {
        return new MIRRecordHasProperty(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, jobj.pname, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRLoadTupleIndex extends MIROp {
    trgt: MIRRegisterArgument;
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    readonly idx: number;
    readonly isvirtual: boolean;
    readonly resulttype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, idx: number, isvirtual: boolean, resulttype: MIRResolvedTypeKey, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRLoadTupleIndex, sinfo);

        this.trgt = trgt;
        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.idx = idx;
        this.isvirtual = isvirtual;
        this.resulttype = resulttype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.${this.idx}`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, idx: this.idx, isvirtual: this.isvirtual, resulttype: this.resulttype };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadTupleIndex(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, jobj.idx, jobj.isvirtual, jobj.resulttype, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRLoadTupleIndexSetGuard extends MIROp {
    trgt: MIRRegisterArgument;
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    readonly idx: number;
    readonly isvirtual: boolean; 
    readonly resulttype: MIRResolvedTypeKey;
    guard: MIRGuard;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, idx: number, isvirtual: boolean, resulttype: MIRResolvedTypeKey, trgt: MIRRegisterArgument, guard: MIRGuard) {
        super(MIROpTag.MIRLoadTupleIndexSetGuard, sinfo);

        this.trgt = trgt;
        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.idx = idx;
        this.isvirtual = isvirtual;
        this.resulttype = resulttype;
        this.guard = guard;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return varsOnlyHelper(this.guard instanceof MIRArgGuard ? [this.trgt, this.guard.greg] : [this.trgt]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.${this.idx} | ${this.guard.stringify()}]`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, idx: this.idx, isvirtual: this.isvirtual, resulttype: this.resulttype, guard: this.guard.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadTupleIndexSetGuard(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, jobj.idx, jobj.isvirtual, jobj.resulttype, MIRRegisterArgument.jparse(jobj.trgt), MIRGuard.jparse(jobj.guard));
    }
}

class MIRLoadRecordProperty extends MIROp {
    trgt: MIRRegisterArgument;
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    readonly pname: string;
    readonly isvirtual: boolean;
    readonly resulttype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, pname: string, isvirtual: boolean, resulttype: MIRResolvedTypeKey, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRLoadRecordProperty, sinfo);
        
        this.trgt = trgt;
        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.pname = pname;
        this.isvirtual = isvirtual;
        this.resulttype = resulttype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.${this.pname}`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, pname: this.pname, isvirtual: this.isvirtual, resulttype: this.resulttype };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadRecordProperty(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, jobj.pname, jobj.isvirtual, jobj.resulttype, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRLoadRecordPropertySetGuard extends MIROp {
    trgt: MIRRegisterArgument;
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    readonly pname: string;
    readonly isvirtual: boolean; 
    readonly resulttype: MIRResolvedTypeKey;
    guard: MIRGuard;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, pname: string, isvirtual: boolean, resulttype: MIRResolvedTypeKey, trgt: MIRRegisterArgument, guard: MIRGuard) {
        super(MIROpTag.MIRLoadRecordPropertySetGuard, sinfo);

        this.trgt = trgt;
        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.pname = pname;
        this.isvirtual = isvirtual;
        this.resulttype = resulttype;
        this.guard = guard;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return varsOnlyHelper(this.guard instanceof MIRArgGuard ? [this.trgt, this.guard.greg] : [this.trgt]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.${this.pname} | ${this.guard.stringify()}]`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, pname: this.pname, isvirtual: this.isvirtual, resulttype: this.resulttype, guard: this.guard.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadRecordPropertySetGuard(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, jobj.pname, jobj.isvirtual, jobj.resulttype, MIRRegisterArgument.jparse(jobj.trgt), MIRGuard.jparse(jobj.guard));
    }
}

class MIRLoadField extends MIROp {
    trgt: MIRRegisterArgument;
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    readonly field: MIRFieldKey;
    readonly isvirtual: boolean;
    readonly resulttype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, field: MIRFieldKey, isvirtual: boolean, resulttype: MIRResolvedTypeKey, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRLoadField, sinfo);

        this.trgt = trgt;
        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.field = field;
        this.isvirtual = isvirtual;
        this.resulttype = resulttype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.${this.field}`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, field: this.field, isvirtual: this.isvirtual, resulttype: this.resulttype };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadField(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, jobj.field, jobj.isvirtual, jobj.resulttype, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRTupleProjectToEphemeral extends MIROp {
    trgt: MIRRegisterArgument;
    arg: MIRArgument; 
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    readonly indecies: number[];
    readonly isvirtual: boolean;
    readonly epht: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, indecies: number[], isvirtual: boolean, epht: MIRResolvedTypeKey, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRTupleProjectToEphemeral, sinfo);

        this.trgt = trgt;
        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.indecies = indecies;
        this.isvirtual = isvirtual;
        this.epht = epht;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        const idx = this.indecies.map((i) => `${i}`);
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.(|${idx.join(", ")}|)`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, indecies: this.indecies, isvirtual: this.isvirtual, epht: this.epht };
    }

    static jparse(jobj: any): MIROp {
        return new MIRTupleProjectToEphemeral(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, jobj.indecies, jobj.isvirtual, jobj.epht, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRRecordProjectToEphemeral extends MIROp {
    trgt: MIRRegisterArgument;
    arg: MIRArgument; 
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    readonly properties: string[];
    readonly isvirtual: boolean;
    readonly epht: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, properties: string[], isvirtual: boolean, epht: MIRResolvedTypeKey, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRRecordProjectToEphemeral, sinfo);

        this.trgt = trgt;
        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.properties = properties;
        this.isvirtual = isvirtual;
        this.epht = epht;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.(|${this.properties.join(", ")}|)`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, properties: this.properties, isvirtual: this.isvirtual, epht: this.epht };
    }

    static jparse(jobj: any): MIROp {
        return new MIRRecordProjectToEphemeral(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, jobj.properties, jobj.isvirtual, jobj.epht, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIREntityProjectToEphemeral extends MIROp {
    trgt: MIRRegisterArgument;
    arg: MIRArgument; 
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    readonly fields: MIRFieldKey[];
    readonly isvirtual: boolean;
    readonly epht: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, fields: MIRFieldKey[], isvirtual: boolean, epht: MIRResolvedTypeKey, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIREntityProjectToEphemeral, sinfo);

        this.trgt = trgt;
        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.fields = fields;
        this.isvirtual = isvirtual;
        this.epht = epht;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.(|${this.fields.join(", ")}|)`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, fields: this.fields, isvirtual: this.isvirtual, epht: this.epht };
    }

    static jparse(jobj: any): MIROp {
        return new MIREntityProjectToEphemeral(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, jobj.fields, jobj.isvirtual, jobj.epht, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRTupleUpdate extends MIROp {
    trgt: MIRRegisterArgument;
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    updates: [number, MIRArgument, MIRResolvedTypeKey][];
    readonly isvirtual: boolean;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, updates: [number, MIRArgument, MIRResolvedTypeKey][], isvirtual: boolean, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRTupleUpdate, sinfo);

        this.trgt = trgt;
        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.updates = updates;
        this.isvirtual = isvirtual;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg, ...this.updates.map((upd) => upd[1])]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        const upds = this.updates.map((upd) => `${upd[0]}=${upd[1].stringify()}`);
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.[${upds.join(", ")}]`;
    }

    jemit(): object {
        const upds = this.updates.map((upd) => [upd[0], upd[1].jemit(), upd[2]]);
        return { ...this.jbemit(), trgt: this.trgt.jemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, updates: upds, isvirtual: this.isvirtual };
    }

    static jparse(jobj: any): MIROp {
        const upds = jobj.updates.map((upd: any) => [upd[0], MIRArgument.jparse(upd[1]), upd[2]]);
        return new MIRTupleUpdate(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, upds, jobj.isvirtual, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRRecordUpdate extends MIROp {
    trgt: MIRRegisterArgument;
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    updates: [string, MIRArgument, MIRResolvedTypeKey][];
    readonly isvirtual: boolean;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, updates: [string, MIRArgument, MIRResolvedTypeKey][], isvirtual: boolean, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRRecordUpdate, sinfo);

        this.trgt = trgt;
        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.updates = updates;
        this.isvirtual = isvirtual;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg, ...this.updates.map((upd) => upd[1])]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        const upds = this.updates.map((upd) => `${upd[0]}=${upd[1].stringify()}`);
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.{${upds.join(", ")}}`;
    }

    jemit(): object {
        const upds = this.updates.map((upd) => [upd[0], upd[1].jemit(), upd[2]]);
        return { ...this.jbemit(), trgt: this.trgt.jemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, updates: upds, isvirtual: this.isvirtual };
    }

    static jparse(jobj: any): MIROp {
        const upds = jobj.updates.map((upd: any) => [upd[0], MIRArgument.jparse(upd[1]), upd[2]]);
        return new MIRRecordUpdate(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, upds, jobj.isvirtual, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIREntityUpdate extends MIROp {
    trgt: MIRRegisterArgument;
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    updates: [MIRFieldKey, MIRArgument, MIRResolvedTypeKey][];
    readonly isvirtual: boolean;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, updates: [MIRFieldKey, MIRArgument, MIRResolvedTypeKey][], isvirtual: boolean, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIREntityUpdate, sinfo);

        this.trgt = trgt;
        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.updates = updates;
        this.isvirtual = isvirtual;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg, ...this.updates.map((upd) => upd[1])]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        const upds = this.updates.map((upd) => `${upd[0]}=${upd[1].stringify()}`);
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.{${upds.join(", ")}}`;
    }

    jemit(): object {
        const upds = this.updates.map((upd) => [upd[0], upd[1].jemit(), upd[2]]);
        return { ...this.jbemit(), trgt: this.trgt.jemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, updates: upds, isvirtual: this.isvirtual };
    }

    static jparse(jobj: any): MIROp {
        const upds = jobj.updates.map((upd: any) => [upd[0], MIRArgument.jparse(upd[1]), upd[2]]);
        return new MIREntityUpdate(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, upds, jobj.isvirtual, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRLoadFromEpehmeralList extends MIROp {
    trgt: MIRRegisterArgument;
    arg: MIRArgument;
    readonly argtype: MIRResolvedTypeKey;
    readonly idx: number;
    readonly resulttype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRResolvedTypeKey, idx: number, resulttype: MIRResolvedTypeKey, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRLoadFromEpehmeralList, sinfo);

        this.trgt = trgt;
        this.arg = arg;
        this.argtype = argtype;
        this.idx = idx;
        this.resulttype = resulttype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}(|${this.idx}|)`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), arg: this.arg.jemit(), argtype: this.argtype, idx: this.idx, resulttype: this.resulttype };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadFromEpehmeralList(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.argtype, jobj.idx, jobj.resulttype, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRMultiLoadFromEpehmeralList extends MIROp {
    trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRResolvedTypeKey }[];
    arg: MIRArgument;
    readonly argtype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRResolvedTypeKey, trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRResolvedTypeKey }[]) {
        super(MIROpTag.MIRMultiLoadFromEpehmeralList, sinfo);
        
        this.trgts = trgts;
        this.arg = arg;
        this.argtype = argtype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return this.trgts.map((trgt) => trgt.into); }

    stringify(): string {
        const lhs = this.trgts.map((trgt) => trgt.into.stringify());
        const ops = this.trgts.map((trgt) => trgt.pos);
        return `${lhs.join(", ")} = ${this.arg.stringify()}(|${ops.join(", ")}|)`;
    }

    jemit(): object {
        const etrgts = this.trgts.map((trgt) => {
            return { pos: trgt.pos, into: trgt.into.jemit(), oftype: trgt.oftype };
        });
        return { ...this.jbemit(), trgts: etrgts, arg: this.arg.jemit(), argtype: this.argtype };
    }

    static jparse(jobj: any): MIROp {
        const etrgts = jobj.etrgts.map((trgt: any) => {
            return { pos: trgt.pos, into: MIRRegisterArgument.jparse(trgt.into), oftype: trgt.oftype as MIRResolvedTypeKey };
        });
        return new MIRMultiLoadFromEpehmeralList(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.argtype, etrgts);
    }
}

class MIRSliceEpehmeralList extends MIROp {
    trgt: MIRRegisterArgument;
    arg: MIRArgument;
    readonly argtype: MIRResolvedTypeKey;
    readonly sltype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRResolvedTypeKey, sltype: MIRResolvedTypeKey, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRSliceEpehmeralList, sinfo);

        this.trgt = trgt;
        this.arg = arg;
        this.argtype = argtype;
        this.sltype = sltype;
        
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}(|${this.sltype}|)`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit(), argtype: this.argtype, sltype: this.sltype, trgt: this.trgt.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRSliceEpehmeralList(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), jobj.argtype, jobj.sltype, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRInvokeFixedFunction extends MIROp {
    trgt: MIRRegisterArgument;
    readonly resultType: MIRResolvedTypeKey;
    readonly mkey: MIRInvokeKey;
    args: MIRArgument[]; //this is args[0] for methods
    optmask: string | undefined;
    guard: MIRStatmentGuard | undefined;

    constructor(sinfo: SourceInfo, resultType: MIRResolvedTypeKey, mkey: MIRInvokeKey, args: MIRArgument[], optmask: string | undefined, trgt: MIRRegisterArgument, guard: MIRStatmentGuard | undefined) {
        super(MIROpTag.MIRInvokeFixedFunction, sinfo,);

        this.trgt = trgt;
        this.resultType = resultType;
        this.mkey = mkey;
        this.args = args;
        this.optmask = optmask;
        this.guard = guard;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper((this.guard !== undefined && this.guard instanceof MIRArgGuard) ? [this.guard.greg, ...this.args] : [...this.args]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        const gstring = this.guard !== undefined ? ` | ${this.guard.stringify()}` : "";
        const oinfo = this.optmask !== undefined ? `, ${this.optmask}` : "";
        return `${this.trgt.stringify()} = ${this.mkey}::(${this.args.map((arg) => arg.stringify()).join(", ")}${oinfo})${gstring}`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), resultType: this.resultType, mkey: this.mkey, args: this.args.map((arg) => arg.jemit()), optmask: this.optmask, guard: this.guard !== undefined ? this.guard.jemit() : undefined };
    }

    static jparse(jobj: any): MIROp {
        return new MIRInvokeFixedFunction(jparsesinfo(jobj.sinfo), jobj.resultType, jobj.mkey, jobj.args.map((arg: any) => MIRArgument.jparse(arg)), jobj.optmask, MIRRegisterArgument.jparse(jobj.trgt), jobj.guard !== undefined ? MIRStatmentGuard.jparse(jobj.guard) : undefined);
    }
}

class MIRInvokeVirtualFunction extends MIROp {
    trgt: MIRRegisterArgument;
    readonly resultType: MIRResolvedTypeKey
    readonly vresolve: MIRVirtualMethodKey;
    readonly rcvrlayouttype: MIRResolvedTypeKey;
    readonly rcvrflowtype: MIRResolvedTypeKey;
    args: MIRArgument[];
    readonly optmask: string | undefined;

    constructor(sinfo: SourceInfo, resultType: MIRResolvedTypeKey, vresolve: MIRVirtualMethodKey, rcvrlayouttype: MIRResolvedTypeKey, rcvrflowtype: MIRResolvedTypeKey, args: MIRArgument[], optmask: string | undefined, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRInvokeVirtualFunction, sinfo);

        this.trgt = trgt;
        this.resultType = resultType;
        this.vresolve = vresolve;
        this.rcvrlayouttype = rcvrlayouttype;
        this.rcvrflowtype = rcvrflowtype;
        this.args = args;
        this.optmask = optmask;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.args[0].stringify()}.${this.vresolve}(${[...this.args].slice(1).map((arg) => arg.stringify()).join(", ")})`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), resultType: this.resultType, vresolve: this.vresolve, rcvrlayouttype: this.rcvrlayouttype, rcvrflowtype: this.rcvrflowtype, args: this.args.map((arg) => arg.jemit()), optmask: this.optmask };
    }

    static jparse(jobj: any): MIROp {
        return new MIRInvokeVirtualFunction(jparsesinfo(jobj.sinfo), jobj.resultType, jobj.vresolve, jobj.rcvrlayouttype, jobj.rcvrflowtype, jobj.args.map((arg: any) => MIRArgument.jparse(arg)), jobj.optmask, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRInvokeVirtualOperator extends MIROp {
    trgt: MIRRegisterArgument;
    readonly resultType: MIRResolvedTypeKey;
    readonly vresolve: MIRVirtualMethodKey;
    args: { arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, arg: MIRArgument }[];

    constructor(sinfo: SourceInfo, resultType: MIRResolvedTypeKey, vresolve: MIRVirtualMethodKey, args: { arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, arg: MIRArgument }[], trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRInvokeVirtualOperator, sinfo);

        this.trgt = trgt;
        this.resultType = resultType;
        this.vresolve = vresolve;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args.map((arg) => arg.arg)]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.vresolve}(${this.args.map((arg) => arg.arg.stringify()).join(", ")})`;
    }

    jemit(): object {
        const eargs = this.args.map((arg) => {
            return { arglayouttype: arg.arglayouttype, argflowtype: arg.argflowtype, arg: arg.arg.jemit() };
        });
        return { ...this.jbemit(), trgt: this.trgt.jemit(), resultType: this.resultType, vresolve: this.vresolve, args: eargs };
    }

    static jparse(jobj: any): MIROp {
        const eargs = jobj.args.map((arg: any) => {
            return { arglayouttype: arg.arglayouttype, argflowtype: arg.argflowtype, arg: MIRArgument.jparse(arg.arg) };
        });
        return new MIRInvokeVirtualOperator(jparsesinfo(jobj.sinfo), jobj.resultType, jobj.vresolve, eargs, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRConstructorTuple extends MIROp {
    trgt: MIRRegisterArgument;
    readonly resultTupleType: MIRResolvedTypeKey;
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, resultTupleType: MIRResolvedTypeKey, args: MIRArgument[], trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRConstructorTuple, sinfo);

        this.trgt = trgt;
        this.resultTupleType = resultTupleType;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = [${this.args.map((arg) => arg.stringify()).join(", ")}]`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), resultTupleType: this.resultTupleType, args: this.args.map((arg) => arg.jemit()) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorTuple(jparsesinfo(jobj.sinfo), jobj.resultTupleType, jobj.args.map((jarg: any) => MIRArgument.jparse(jarg)), MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRConstructorTupleFromEphemeralList extends MIROp {
    trgt: MIRRegisterArgument;
    readonly resultTupleType: MIRResolvedTypeKey;
    arg: MIRArgument;
    readonly elistType: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, resultTupleType: MIRResolvedTypeKey, arg: MIRArgument, elistType: MIRResolvedTypeKey, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRConstructorTupleFromEphemeralList, sinfo);

        this.trgt = trgt;
        this.resultTupleType = resultTupleType;
        this.arg = arg;
        this.elistType = elistType;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = [...${this.arg.stringify()}]`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), resultTupleType: this.resultTupleType, arg: this.arg.jemit(), elistType: this.elistType };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorTupleFromEphemeralList(jparsesinfo(jobj.sinfo), jobj.resultTupleType, MIRArgument.jparse(jobj.arg), jobj.elistType, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRConstructorRecord extends MIROp {
    trgt: MIRRegisterArgument;
    readonly resultRecordType: MIRResolvedTypeKey;
    args: [string, MIRArgument][];

    constructor(sinfo: SourceInfo, resultRecordType: MIRResolvedTypeKey, args: [string, MIRArgument][], trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRConstructorRecord, sinfo);

        this.trgt = trgt;
        this.resultRecordType = resultRecordType;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper(this.args.map((tv) => tv[1])); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = {${this.args.map((arg) => `${arg[0]}=${arg[1].stringify()}`).join(", ")}}`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt, resultRecordType: this.resultRecordType, args: this.args.map((arg) => [arg[0], arg[1].jemit()]) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorRecord(jparsesinfo(jobj.sinfo), jobj.resultRecordType, jobj.args.map((jarg: any) => [jarg[0], MIRArgument.jparse(jarg[1])]), MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRConstructorRecordFromEphemeralList extends MIROp {
    trgt: MIRRegisterArgument;
    readonly resultRecordType: MIRResolvedTypeKey;
    arg: MIRArgument;
    readonly elistType: MIRResolvedTypeKey;
    readonly propertyPositions: string[]; 


    constructor(sinfo: SourceInfo, resultRecordType: MIRResolvedTypeKey, arg: MIRArgument, elistType: MIRResolvedTypeKey, propertyPositions: string[], trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRConstructorRecordFromEphemeralList, sinfo);

        this.trgt = trgt;
        this.resultRecordType = resultRecordType;
        this.arg = arg;
        this.elistType = elistType
        this.propertyPositions = propertyPositions;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = {...${this.arg.stringify()}}`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt, resultRecordType: this.resultRecordType, arg: this.arg.jemit(), elistType: this.elistType, propertyPositions: this.propertyPositions };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorRecordFromEphemeralList(jparsesinfo(jobj.sinfo), jobj.resultRecordType, MIRArgument.jparse(jobj.arg), jobj.elistType, jobj.propertyPositions, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRStructuredAppendTuple extends MIROp {
    trgt: MIRRegisterArgument;
    readonly resultTupleType: MIRResolvedTypeKey;
    args: MIRArgument[];
    readonly ttypes: { layout: MIRResolvedTypeKey, flow: MIRResolvedTypeKey }[];

    constructor(sinfo: SourceInfo, resultTupleType: MIRResolvedTypeKey, args: MIRArgument[], ttypes: {layout: MIRResolvedTypeKey, flow: MIRResolvedTypeKey}[], trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRStructuredAppendTuple, sinfo);

        this.trgt = trgt;
        this.resultTupleType = resultTupleType;
        this.args = args;
        this.ttypes = ttypes;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper(this.args); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = [${this.args.map((arg) => "..." + arg.stringify()).join(", ")}]`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt, resultTupleType: this.resultTupleType, args: this.args.map((arg) => arg.jemit()), ttypes: this.ttypes };
    }

    static jparse(jobj: any): MIROp {
        return new MIRStructuredAppendTuple(jparsesinfo(jobj.sinfo), jobj.resultTupleType, jobj.args.map((jarg: any) => MIRArgument.jparse(jarg)), jobj.ttypes, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRStructuredJoinRecord extends MIROp {
    trgt: MIRRegisterArgument;
    readonly resultRecordType: MIRResolvedTypeKey;
    args: MIRArgument[];
    readonly ttypes: { layout: MIRResolvedTypeKey, flow: MIRResolvedTypeKey }[];

    constructor(sinfo: SourceInfo, resultRecordType: MIRResolvedTypeKey, args: MIRArgument[], ttypes: {layout: MIRResolvedTypeKey, flow: MIRResolvedTypeKey}[], trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRStructuredJoinRecord, sinfo);

        this.trgt = trgt;
        this.resultRecordType = resultRecordType;
        this.args = args;
        this.ttypes = ttypes;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper(this.args); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = [${this.args.map((arg) => "..." + arg.stringify()).join(", ")}]`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt, resultRecordType: this.resultRecordType, args: this.args.map((arg) => arg.jemit()), ttypes: this.ttypes };
    }

    static jparse(jobj: any): MIROp {
        return new MIRStructuredJoinRecord(jparsesinfo(jobj.sinfo), jobj.resultRecordType, jobj.args.map((jarg: any) => MIRArgument.jparse(jarg)), jobj.ttypes, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRConstructorEphemeralList extends MIROp {
    trgt: MIRRegisterArgument
    readonly resultEphemeralListType: MIRResolvedTypeKey;
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, resultEphemeralListType: MIRResolvedTypeKey, args: MIRArgument[], trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRConstructorEphemeralList, sinfo);

        this.trgt = trgt;
        this.resultEphemeralListType = resultEphemeralListType;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = [${this.args.map((arg) => arg.stringify()).join(", ")}]`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), resultEphemeralListType: this.resultEphemeralListType, args: this.args.map((arg) => arg.jemit()) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorEphemeralList(jparsesinfo(jobj.sinfo), jobj.resultEphemeralListType, jobj.args.map((jarg: any) => MIRArgument.jparse(jarg)), MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIREphemeralListExtend extends MIROp {
    trgt: MIRRegisterArgument;
    arg: MIRArgument;
    argtype: MIRResolvedTypeKey
    ext: MIRArgument[];
    readonly resultType: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRResolvedTypeKey, ext: MIRArgument[], resultType: MIRResolvedTypeKey, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIREphemeralListExtend, sinfo);

        this.trgt = trgt;
        this.arg = arg;
        this.argtype = argtype;
        this.ext = ext;
        this.resultType = resultType;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg, ...this.ext]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.resultType}@(|...${this.arg.stringify()}, ${this.ext.map((e) => e.stringify()).join(", ")}|)`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), arg: this.arg.jemit(), argtype: this.argtype, ext: this.ext.map((e) => e.jemit()), resultType: this.resultType };
    }

    static jparse(jobj: any): MIROp {
        return new MIREphemeralListExtend(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.argtype, jobj.ext.map((e: string) => MIRArgument.jparse(e)), jobj.resultType, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRConstructorPrimaryCollectionEmpty extends MIROp {
    trgt: MIRRegisterArgument;
    readonly tkey: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, tkey: MIRResolvedTypeKey, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRConstructorPrimaryCollectionEmpty, sinfo);

        this.trgt = trgt;
        this.tkey = tkey;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tkey}{}`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), tkey: this.tkey };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorPrimaryCollectionEmpty(jparsesinfo(jobj.sinfo), jobj.tkey, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRConstructorPrimaryCollectionSingletons extends MIROp {
    trgt: MIRRegisterArgument;
    readonly tkey: MIRResolvedTypeKey;
    args: [MIRResolvedTypeKey, MIRArgument][];

    constructor(sinfo: SourceInfo, tkey: MIRResolvedTypeKey, args: [MIRResolvedTypeKey, MIRArgument][], trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRConstructorPrimaryCollectionSingletons, sinfo);

        this.trgt = trgt;
        this.tkey = tkey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args.map((arg) => arg[1])]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tkey}{${this.args.map((arg) => arg[1].stringify()).join(", ")}}`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), tkey: this.tkey, args: this.args.map((arg) => [arg[0], arg[1].jemit()]) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorPrimaryCollectionSingletons(jparsesinfo(jobj.sinfo), jobj.tkey, jobj.args.map((jarg: any) => [jarg[0], MIRArgument.jparse(jarg[1])]), MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRConstructorPrimaryCollectionCopies extends MIROp {
    trgt: MIRRegisterArgument;
    readonly tkey: MIRResolvedTypeKey;
    args: [MIRResolvedTypeKey, MIRArgument][];

    constructor(sinfo: SourceInfo, tkey: MIRResolvedTypeKey, args: [MIRResolvedTypeKey, MIRArgument][], trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRConstructorPrimaryCollectionCopies, sinfo);

        this.trgt = trgt;
        this.tkey = tkey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args.map((arg) => arg[1])]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    canRaise(implicitAssumesEnabled: boolean): boolean {
        //on map we fail on duplicate keys
        return true;
    }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tkey}{${this.args.map((arg) => `expand(${arg[1].stringify()})`).join(", ")}`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), tkey: this.tkey, args: this.args.map((arg) => [arg[0], arg[1].jemit()]) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorPrimaryCollectionCopies(jparsesinfo(jobj.sinfo), jobj.tkey, jobj.args.map((jarg: any) => [jarg[0], MIRArgument.jparse(jarg[1])]), MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRConstructorPrimaryCollectionMixed extends MIROp {
    trgt: MIRRegisterArgument;
    readonly tkey: MIRResolvedTypeKey;
    args: [boolean, MIRResolvedTypeKey, MIRArgument][];

    constructor(sinfo: SourceInfo, tkey: MIRResolvedTypeKey, args: [boolean, MIRResolvedTypeKey, MIRArgument][], trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRConstructorPrimaryCollectionMixed, sinfo,);

        this.trgt = trgt;
        this.tkey = tkey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper(this.args.map((tv) => tv[2])); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tkey}{${this.args.map((arg) => arg[0] ? `expand(${arg[2].stringify()})` : arg[2].stringify()).join(", ")}`;
    }

    canRaise(implicitAssumesEnabled: boolean): boolean {
        //on map we fail on duplicate keys
        return true;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), tkey: this.tkey, args: this.args.map((arg) => [arg[0], arg[1], arg[2].jemit()]) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorPrimaryCollectionMixed(jparsesinfo(jobj.sinfo), jobj.tkey, jobj.args.map((jarg: any) => [jarg[0], jarg[1], MIRArgument.jparse(jarg[2])]), MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRBinKeyEq extends MIROp {
    trgt: MIRRegisterArgument;
    readonly lhslayouttype: MIRResolvedTypeKey;
    readonly lhsflowtype: MIRResolvedTypeKey;
    lhs: MIRArgument;
    readonly rhslayouttype: MIRResolvedTypeKey;
    readonly rhsflowtype: MIRResolvedTypeKey
    rhs: MIRArgument;

    constructor(sinfo: SourceInfo, lhslayouttype: MIRResolvedTypeKey, lhsflowtype: MIRResolvedTypeKey, lhs: MIRArgument, rhslayouttype: MIRResolvedTypeKey, rhsflowtype: MIRResolvedTypeKey, rhs: MIRArgument, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRBinKeyEq, sinfo);

        this.trgt = trgt;
        this.lhslayouttype = lhslayouttype;
        this.lhsflowtype = lhsflowtype;
        this.lhs = lhs;
        this.rhslayouttype = rhslayouttype;
        this.rhsflowtype = rhsflowtype;
        this.rhs = rhs;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.lhs, this.rhs]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.lhs.stringify()} Key== ${this.rhs.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), lhslayouttype: this.lhslayouttype, lhsflowtype: this.lhsflowtype, lhs: this.lhs.jemit(), rhslayouttype: this.rhslayouttype, rhsflowtype: this.rhsflowtype, rhs: this.rhs.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRBinKeyEq(jparsesinfo(jobj.sinfo), jobj.lhslayouttype, jobj.lhsflowtype, MIRArgument.jparse(jobj.lhs), jobj.rhslayouttype, jobj.rhsflowtype, MIRArgument.jparse(jobj.rhs), MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRBinKeyLess extends MIROp {
    trgt: MIRRegisterArgument;
    readonly lhslayouttype: MIRResolvedTypeKey;
    readonly lhsflowtype: MIRResolvedTypeKey;
    lhs: MIRArgument;
    readonly rhslayouttype: MIRResolvedTypeKey;
    readonly rhsflowtype: MIRResolvedTypeKey
    rhs: MIRArgument;

    constructor(sinfo: SourceInfo, lhslayouttype: MIRResolvedTypeKey, lhsflowtype: MIRResolvedTypeKey, lhs: MIRArgument, rhslayouttype: MIRResolvedTypeKey, rhsflowtype: MIRResolvedTypeKey, rhs: MIRArgument, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRBinKeyLess, sinfo);

        this.trgt = trgt;
        this.lhslayouttype = lhslayouttype;
        this.lhsflowtype = lhsflowtype;
        this.lhs = lhs;
        this.rhslayouttype = rhslayouttype;
        this.rhsflowtype = rhsflowtype;
        this.rhs = rhs;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.lhs, this.rhs]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.lhs.stringify()} Key< ${this.rhs.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), lhslayouttype: this.lhslayouttype, lhsflowtype: this.lhsflowtype, lhs: this.lhs.jemit(), rhslayouttype: this.rhslayouttype, rhsflowtype: this.rhsflowtype, rhs: this.rhs.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRBinKeyLess(jparsesinfo(jobj.sinfo), jobj.lhslayouttype, jobj.lhsflowtype, MIRArgument.jparse(jobj.lhs), jobj.rhslayouttype, jobj.rhsflowtype, MIRArgument.jparse(jobj.rhs), MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRPrefixNotOp extends MIROp {
    trgt: MIRRegisterArgument;
    arg: MIRArgument;

    constructor(sinfo: SourceInfo, arg: MIRArgument, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRPrefixNotOp, sinfo);
        
        this.trgt = trgt;
        this.arg = arg;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = !${this.arg.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), arg: this.arg.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRPrefixNotOp(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRAllTrue extends MIROp {
    trgt: MIRRegisterArgument;
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, args: MIRArgument[], trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRAllTrue, sinfo);
        
        this.trgt = trgt;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper(this.args); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.args.map((arg) => arg.stringify()).join(" & ")}`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), args: this.args.map((arg) => arg.jemit()) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRAllTrue(jparsesinfo(jobj.sinfo), jobj.args.map((jarg: any) => MIRArgument.jparse(jarg)), MIRRegisterArgument.jparse(jobj.trgt));
    }
}


class MIRSomeTrue extends MIROp {
    trgt: MIRRegisterArgument;
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, args: MIRArgument[], trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRSomeTrue, sinfo);
        
        this.trgt = trgt;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper(this.args); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.args.map((arg) => arg.stringify()).join(" | ")}`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), args: this.args.map((arg) => arg.jemit()) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRSomeTrue(jparsesinfo(jobj.sinfo), jobj.args.map((jarg: any) => MIRArgument.jparse(jarg)), MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRIsTypeOf extends MIROp {
    trgt: MIRRegisterArgument;
    readonly chktype: MIRResolvedTypeKey;
    arg: MIRArgument;
    readonly srclayouttype: MIRResolvedTypeKey;
    readonly srcflowtype: MIRResolvedTypeKey;
    guard: MIRStatmentGuard | undefined;

    constructor(sinfo: SourceInfo, trgt: MIRRegisterArgument, chktype: MIRResolvedTypeKey, src: MIRArgument, srclayouttype: MIRResolvedTypeKey, srcflowtype: MIRResolvedTypeKey, guard: MIRStatmentGuard | undefined) {
        super(MIROpTag.MIRIsTypeOf, sinfo);

        this.trgt = trgt;
        this.chktype = chktype;
        this.arg = src;
        this.srclayouttype = srclayouttype;
        this.srcflowtype = srcflowtype;
        this.guard = guard;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper((this.guard !== undefined && this.guard instanceof MIRArgGuard) ? [this.arg, this.guard.greg] : [this.arg]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        const gstring = this.guard !== undefined ? ` | ${this.guard.stringify()}` : "";
        return `${this.trgt.stringify()} = $isTypeOf(${this.arg.stringify()}, ${this.chktype})${gstring}`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgt: this.trgt.jemit(), chktype: this.chktype, arg: this.arg.jemit(), srclayouttype: this.srclayouttype, srcflowtype: this.srcflowtype, guard: this.guard !== undefined ? this.guard.jemit() : undefined };
    }

    static jparse(jobj: any): MIROp {
        return new MIRIsTypeOf(jparsesinfo(jobj.sinfo), MIRRegisterArgument.jparse(jobj.trgt), jobj.chktype, MIRArgument.jparse(jobj.arg), jobj.srclayouttype, jobj.srcflowtype, jobj.guard !== undefined ? MIRStatmentGuard.jparse(jobj.guard) : undefined);
    }
}

class MIRRegisterAssign extends MIROp {
    trgt: MIRRegisterArgument;
    src: MIRArgument;
    readonly layouttype: MIRResolvedTypeKey;
    guard: MIRStatmentGuard | undefined;

    constructor(sinfo: SourceInfo, src: MIRArgument, trgt: MIRRegisterArgument, layouttype: MIRResolvedTypeKey, guard: MIRStatmentGuard | undefined) {
        super(MIROpTag.MIRRegisterAssign, sinfo);

        this.trgt = trgt;
        this.src = src;
        this.layouttype = layouttype;
        this.guard = guard;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper((this.guard !== undefined && this.guard instanceof MIRArgGuard) ? [this.src, this.guard.greg] : [this.src]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        const gstring = this.guard !== undefined ? ` | ${this.guard.stringify()}` : "";
        return `${this.trgt.stringify()} = ${this.src.stringify()}${gstring}`;
    }

    jemit(): object {
        return { ...this.jbemit(), src: this.src.jemit(), layouttype: this.layouttype, trgt: this.trgt.jemit(), guard: this.guard !== undefined ? this.guard.jemit() : undefined };
    }

    static jparse(jobj: any): MIROp {
        return new MIRRegisterAssign(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), MIRRegisterArgument.jparse(jobj.trgt), jobj.layouttype, jobj.guard !== undefined ? MIRStatmentGuard.jparse(jobj.guard) : undefined);
    }
}

class MIRJump extends MIROp {
    readonly trgtblock: string;

    constructor(sinfo: SourceInfo, blck: string) {
        super(MIROpTag.MIRJump, sinfo);
        this.trgtblock = blck;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `jump ${this.trgtblock}`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgtblock: this.trgtblock };
    }

    static jparse(jobj: any): MIROp {
        return new MIRJump(jparsesinfo(jobj.sinfo), jobj.trgtblock);
    }
}


class MIRJumpCond extends MIROp {
    arg: MIRArgument;
    readonly trueblock: string;
    readonly falseblock: string;

    constructor(sinfo: SourceInfo, arg: MIRArgument, trueblck: string, falseblck: string) {
        super(MIROpTag.MIRJumpCond, sinfo);
        this.arg = arg;
        this.trueblock = trueblck;
        this.falseblock = falseblck;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `cjump ${this.arg.stringify()} ${this.trueblock} ${this.falseblock}`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit(), trueblock: this.trueblock, falseblock: this.falseblock };
    }

    static jparse(jobj: any): MIROp {
        return new MIRJumpCond(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.trueblock, jobj.falseblock);
    }
}

class MIRJumpNone extends MIROp {
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly noneblock: string;
    readonly someblock: string;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, noneblck: string, someblck: string) {
        super(MIROpTag.MIRJumpNone, sinfo);
        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.noneblock = noneblck;
        this.someblock = someblck;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `njump ${this.arg.stringify()} ${this.noneblock} ${this.someblock}`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, noneblock: this.noneblock, someblock: this.someblock };
    }

    static jparse(jobj: any): MIROp {
        return new MIRJumpNone(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.noneblock, jobj.someblock);
    }
}

class MIRReturnAssign extends MIROp {
    readonly oftype: MIRResolvedTypeKey
    src: MIRArgument;
    name: MIRRegisterArgument;

    constructor(sinfo: SourceInfo, src: MIRArgument, oftype: MIRResolvedTypeKey, name?: MIRRegisterArgument) {
        super(MIROpTag.MIRReturnAssign, sinfo);

        this.src = src;
        this.name = name || new MIRRegisterArgument("$__ir_ret__");
        this.oftype = oftype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.src]); }
    getModVars(): MIRRegisterArgument[] { return [this.name]; }

    stringify(): string {
        return `${this.name.stringify()} = ${this.src.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), src: this.src.jemit(), oftype: this.oftype, name: this.name.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRReturnAssign(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), jobj.oftype, MIRRegisterArgument.jparse(jobj.name));
    }
}

class MIRReturnAssignOfCons extends MIROp {
    readonly oftype: MIRResolvedTypeKey; 
    args: MIRArgument[];
    name: MIRRegisterArgument;

    constructor(sinfo: SourceInfo, oftype: MIRResolvedTypeKey, args: MIRArgument[], name?: MIRRegisterArgument) {
        super(MIROpTag.MIRReturnAssignOfCons, sinfo);

        this.oftype = oftype;
        this.args = args;
        this.name = name || new MIRRegisterArgument("$__ir_ret__");
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper(this.args); }
    getModVars(): MIRRegisterArgument[] { return [this.name]; }

    stringify(): string {
        return `${this.name.stringify()} = ${this.oftype}(${this.args.map((arg) => arg.stringify()).join(", ")})`;
    }

    jemit(): object {
        return { ...this.jbemit(), oftype: this.oftype, args: this.args.map((arg) => arg.jemit()), name: this.name.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRReturnAssignOfCons(jparsesinfo(jobj.sinfo), jobj.oftype, jobj.args.map((jarg: any) => MIRArgument.jparse(jarg)), MIRRegisterArgument.jparse(jobj.name));
    }
}

class MIRVarLifetimeStart extends MIROp {
    readonly name: string;
    readonly rtype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, name: string, rtype: MIRResolvedTypeKey) {
        super(MIROpTag.MIRVarLifetimeStart, sinfo);

        this.name = name;
        this.rtype = rtype;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `v-begin ${this.name}`;
    }

    jemit(): object {
        return { ...this.jbemit(), name: this.name, rtype: this.rtype };
    }

    static jparse(jobj: any): MIROp {
        return new MIRVarLifetimeStart(jparsesinfo(jobj.sinfo), jobj.name, jobj.rtype);
    }
}

class MIRVarLifetimeEnd extends MIROp {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string) {
        super(MIROpTag.MIRVarLifetimeEnd, sinfo);

        this.name = name;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `v-end ${this.name}`;
    }

    jemit(): object {
        return { ...this.jbemit(), name: this.name };
    }

    static jparse(jobj: any): MIROp {
        return new MIRVarLifetimeEnd(jparsesinfo(jobj.sinfo), jobj.name);
    }
}

class MIRPhi extends MIROp {
    src: Map<string, MIRRegisterArgument>;
    trgt: MIRRegisterArgument;
    readonly layouttype: MIRResolvedTypeKey

    constructor(sinfo: SourceInfo, src: Map<string, MIRRegisterArgument>, layouttype: MIRResolvedTypeKey, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRPhi, sinfo);

        this.src = src;
        this.trgt = trgt;
        this.layouttype = layouttype;
    }

    getUsedVars(): MIRRegisterArgument[] {
        let phis: MIRRegisterArgument[] = [];
        this.src.forEach((v) => phis.push(v));

        return phis;
    }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        let phis: string[] = [];
        this.src.forEach((v, k) => phis.push(`${v.stringify()} -- ${k}`));
        phis.sort();

        return `${this.trgt.stringify()} = (${phis.join(", ")})`;
    }

    jemit(): object {
        const phis = [...this.src].map((phi) => [phi[0], phi[1].jemit()]);
        return { ...this.jbemit(), src: phis, layouttype: this.layouttype, trgt: this.trgt.jemit() };
    }

    static jparse(jobj: any): MIROp {
        let phis = new Map<string, MIRRegisterArgument>();
        jobj.src.forEach((phi: [string, any]) => phis.set(phi[0], MIRRegisterArgument.jparse(phi[1])));
        return new MIRPhi(jparsesinfo(jobj.sinfo), phis, jobj.layouttype, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRBasicBlock {
    readonly label: string;
    ops: MIROp[];

    constructor(label: string, ops: MIROp[]) {
        this.label = label;
        this.ops = ops;
    }

    jsonify(): { label: string, line: number, ops: string[] } {
        const jblck = {
            label: this.label,
            line: (this.ops.length !== 0) ? this.ops[0].sinfo.line : -1,
            ops: this.ops.map((op) => op.stringify())
        };

        return jblck;
    }

    jemit(): object {
        return { label: this.label, ops: this.ops.map((op) => op.jemit()) };
    }

    static jparse(jobj: any): MIRBasicBlock {
        return new MIRBasicBlock(jobj.label, jobj.ops.map((op: any) => MIROp.jparse(op)));
    }
}

class MIRBody {
    readonly file: string;
    readonly sinfo: SourceInfo;

    body: Map<string, MIRBasicBlock>;

    constructor(file: string, sinfo: SourceInfo, body: Map<string, MIRBasicBlock>) {
        this.file = file;
        this.sinfo = sinfo;

        this.body = body;
    }

    jsonify(): any {
        let blocks: any[] = [];
        topologicalOrder(this.body).forEach((v, k) => blocks.push(v.jsonify()));

        return blocks;
    }

    dgmlify(siginfo: string): string {
        const blocks = topologicalOrder(this.body);
        const flow = computeBlockLinks(this.body);

        const xmlescape = (str: string) => {
            return str.replace(/&/g, "&amp;")
                .replace(/</g, "&lt;")
                .replace(/>/g, "&gt;")
                .replace(/"/g, "&quot;")
                .replace(/'/g, "&apos;");
        };

        let nodes: string[] = [`<Node Id="fdecl" Label="${siginfo}"/>`];
        let links: string[] = [`<Link Source="fdecl" Target="entry"/>`];
        blocks.forEach((b) => {
            const ndata = b.jsonify();
            const dstring = `L: ${ndata.label} &#10;  ` + ndata.ops.map((op) => xmlescape(op)).join("&#10;  ");
            nodes.push(`<Node Id="${ndata.label}" Label="${dstring}"/>`);

            (flow.get(ndata.label) as FlowLink).succs.forEach((succ) => {
                links.push(`<Link Source="${ndata.label}" Target="${succ}"/>`);
            });
        });

        return `<?xml version="1.0" encoding="utf-8"?>
        <DirectedGraph Title="DrivingTest" xmlns="http://schemas.microsoft.com/vs/2009/dgml">
           <Nodes>
                ${nodes.join("\n")}
           </Nodes>
           <Links>
                ${links.join("\n")}
           </Links>
        </DirectedGraph>`;
    }

    jemit(): object {
        const blocks = topologicalOrder(this.body).map((blck) => blck.jemit());
        return { file: this.file, sinfo: jemitsinfo(this.sinfo), blocks: blocks };
    }

    static jparse(jobj: any): MIRBody {
        let body = new Map<string, MIRBasicBlock>();
        jobj.blocks.map((blck: any) => MIRBasicBlock.jparse(blck)).forEach((blck: MIRBasicBlock) => body.set(blck.label, blck));

        
        return new MIRBody(jobj.file, jparsesinfo(jobj.sinfo), body);
    }
}

export {
    MIRGlobalKey, MIRFieldKey, MIRInvokeKey, MIRResolvedTypeKey, MIRVirtualMethodKey,
    MIRGuard, MIRMaskGuard, MIRArgGuard, MIRStatmentGuard,
    MIRArgument, MIRRegisterArgument, MIRGlobalVariable, 
    MIRConstantArgument, MIRConstantNone, MIRConstantTrue, MIRConstantFalse, MIRConstantInt, MIRConstantNat, MIRConstantBigInt, MIRConstantBigNat, MIRConstantRational, MIRConstantFloat, MIRConstantDecimal, MIRConstantString, MIRConstantRegex, MIRConstantStringOf, MIRConstantDataString, MIRConstantTypedNumber,
    MIROpTag, MIROp, MIRNop, MIRDeadFlow, MIRAbort, MIRAssertCheck, MIRDebug,
    MIRLoadUnintVariableValue, MIRDeclareGuardFlagLocation, MIRSetConstantGuardFlag, MIRConvertValue,
    MIRLoadConst,
    MIRTupleHasIndex, MIRRecordHasProperty,
    MIRLoadTupleIndex, MIRLoadTupleIndexSetGuard, MIRLoadRecordProperty, MIRLoadRecordPropertySetGuard,
    MIRRegisterAssign,
    MIRLoadField,
    MIRTupleProjectToEphemeral, MIRRecordProjectToEphemeral, MIREntityProjectToEphemeral,
    MIRTupleUpdate, MIRRecordUpdate, MIREntityUpdate,
    MIRLoadFromEpehmeralList, MIRMultiLoadFromEpehmeralList, MIRSliceEpehmeralList,
    MIRInvokeFixedFunction, MIRInvokeVirtualFunction, MIRInvokeVirtualOperator,
    MIRConstructorTuple, MIRConstructorTupleFromEphemeralList, MIRConstructorRecord, MIRConstructorRecordFromEphemeralList, MIRStructuredAppendTuple, MIRStructuredJoinRecord, MIRConstructorEphemeralList, MIREphemeralListExtend,
    MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionSingletons, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionMixed,
    MIRBinKeyEq, MIRBinKeyLess, MIRPrefixNotOp, MIRAllTrue, MIRSomeTrue,
    MIRIsTypeOf,
    MIRJump, MIRJumpCond, MIRJumpNone,
    MIRReturnAssign, MIRReturnAssignOfCons,
    MIRVarLifetimeStart, MIRVarLifetimeEnd,
    MIRPhi,
    MIRBasicBlock, MIRBody
};
