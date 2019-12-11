//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo } from "../ast/parser";
import { topologicalOrder, computeBlockLinks, FlowLink } from "./mir_info";
import assert = require("assert");

type MIRConstantKey = string; //ns::[type]::const#binds
type MIRFieldKey = string; //ns::name::field#binds
type MIRInvokeKey = string; //ns::[type]::func#binds%code

type MIRNominalTypeKey = string; //ns::name#binds
type MIRResolvedTypeKey = string; //idstr
type MIRVirtualMethodKey = string; //method#binds

type MIRBodyKey = string; //pfx$$key -- pfx \in {invoke, pre, post, invariant, const, fdefault}

function extractMirBodyKeyPrefix(bkey: MIRBodyKey): "invoke" | "pre" | "post" | "invariant" | "const" | "fdefault" {
    return bkey.substring(0, bkey.indexOf("::")) as "invoke" | "pre" | "post" | "invariant" | "const" | "fdefault";
}

function extractMirBodyKeyData(bkey: MIRBodyKey): MIRInvokeKey | MIRNominalTypeKey | MIRConstantKey | MIRFieldKey {
    return bkey.substring(bkey.indexOf("::") + 2) as MIRInvokeKey | MIRNominalTypeKey | MIRConstantKey | MIRFieldKey;
}

//
//Probably want to declare a MIRSourceInfo class
//
function jemitsinfo(sinfo: SourceInfo): object {
    return { line: sinfo.line, column: sinfo.column, pos: sinfo.pos, span: sinfo.span };
}

function jparsesinfo(jobj: any): SourceInfo {
    return new SourceInfo(jobj.line, jobj.column, jobj.pos, jobj.span);
}

abstract class MIRArgument {
    readonly nameID: string;

    constructor(nameID: string) {
        this.nameID = nameID;
    }

    abstract stringify(): string;

    abstract jemit(): object;

    static jparse(jobj: any): MIRArgument {
        if (jobj === null) {
            return new MIRConstantNone();
        }
        else if (jobj === true || jobj === false) {
            return jobj ? new MIRConstantTrue() : new MIRConstantFalse();
        }
        else {
            if (typeof (jobj) === "string") {
                return new MIRConstantInt(jobj);
            }
            else if (Array.isArray(jobj)) {
                return new MIRConstantString(jobj[0]);
            }
            else {
                if (jobj.tag === "temp") {
                    return MIRTempRegister.jparse(jobj);
                }
                else {
                    assert(jobj.tag === "var");
                    return MIRVariable.jparse(jobj);
                }
            }
        }
    }
}

abstract class MIRRegisterArgument extends MIRArgument {
    constructor(nameID: string) {
        super(nameID);
    }

    stringify(): string {
        return this.nameID;
    }
}

class MIRTempRegister extends MIRRegisterArgument {
    readonly regID: number;
    constructor(regID: number, forcename?: string) {
        super(forcename || `#tmp_${regID}`);
        this.regID = regID;
    }

    jemit(): object {
        return { tag: "temp", regID: this.regID, nameID: this.nameID };
    }

    static jparse(jobj: any): MIRTempRegister {
        return new MIRTempRegister(jobj.regID, jobj.nameID);
    }
}

class MIRVariable extends MIRRegisterArgument {
    readonly lname: string;

    constructor(name: string, forcename?: string) {
        super(forcename || name);
        this.lname = name;
    }

    jemit(): any {
        return { tag: "var", lname: this.lname, nameID: this.nameID };
    }

    static jparse(jobj: any): MIRVariable {
        return new MIRVariable(jobj.lname, jobj.nameID);
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
        return this.value;
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
        return [this.value];
    }
}

enum MIROpTag {
    MIRLoadConst = "MIRLoadConst",
    MIRLoadConstTypedString = "MIRLoadConstTypedString",

    MIRAccessConstantValue = "MIRAccessConstantValue",
    MIRLoadFieldDefaultValue = "MIRLoadFieldDefaultValue",
    MIRAccessArgVariable = "MIRAccessArgVariable",
    MIRAccessLocalVariable = "MIRAccessLocalVariable",

    MIRConstructorPrimary = "MIRConstructorPrimary",
    MIRConstructorPrimaryCollectionEmpty = "MIRConstructorPrimaryCollectionEmpty",
    MIRConstructorPrimaryCollectionSingletons = "MIRConstructorPrimaryCollectionSingletons",
    MIRConstructorPrimaryCollectionCopies = "MIRConstructorPrimaryCollectionCopies",
    MIRConstructorPrimaryCollectionMixed = "MIRConstructorPrimaryCollectionMixed",
    MIRConstructorTuple = "MIRConstructorTuple",
    MIRConstructorRecord = "MIRConstructorRecord",

    MIRAccessFromIndex = "MIRAccessFromIndex",
    MIRProjectFromIndecies = "MIRProjectFromIndecies",
    MIRAccessFromProperty = "MIRAccessFromProperty",
    MIRProjectFromProperties = "MIRProjectFromProperties",
    MIRAccessFromField = "MIRAccessFromField",
    MIRProjectFromFields = "MIRProjectFromFields",
    MIRProjectFromTypeTuple = "MIRProjectFromTypeTuple",
    MIRProjectFromTypeRecord = "MIRProjectFromTypeRecord",
    MIRProjectFromTypeConcept = "MIRProjectFromTypeConcept",
    MIRModifyWithIndecies = "MIRModifyWithIndecies",
    MIRModifyWithProperties = "MIRModifyWithProperties",
    MIRModifyWithFields = "MIRModifyWithFields",
    MIRStructuredExtendTuple = "MIRStructuredExtendTuple",
    MIRStructuredExtendRecord = "MIRStructuredExtendRecord",
    MIRStructuredExtendObject = "MIRStructuredExtendObject",

    MIRInvokeFixedFunction = "MIRInvokeFixedFunction",
    MIRInvokeVirtualTarget = "MIRInvokeVirtualTarget",

    MIRPrefixOp = "MIRPrefixOp",

    MIRBinOp = "MIRBinOp",
    MIRGetKey = "MIRGetKey",
    MIRBinEq = "MIRBinEq",
    MIRBinCmp = "MIRBinCmp",

    MIRIsTypeOfNone = "MIRIsTypeOfNone",
    MIRIsTypeOfSome = "MIRIsTypeOfSome",
    MIRIsTypeOf = "MIRIsTypeOf",

    MIRRegAssign = "MIRRegAssign",
    MIRTruthyConvert = "MIRTruthyConvert",
    MIRLogicStore = "MIRLogicStore",
    MIRVarStore = "MIRVarStore",
    MIRReturnAssign = "MIRReturnAssign",

    MIRAbort = "MIRAbort",
    MIRDebug = "MIRDebug",

    MIRJump = "MIRJump",
    MIRJumpCond = "MIRJumpCond",
    MIRJumpNone = "MIRJumpNone",

    MIRPhi = "MIRPhi",

    MIRVarLifetimeStart = "MIRVarLifetimeStart",
    MIRVarLifetimeEnd = "MIRVarLifetimeEnd"
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

    protected jbemit(): object {
        return { tag: this.tag, sinfo: jemitsinfo(this.sinfo) };
    }

    abstract jemit(): object;

    static jparse(jobj: any & { tag: string }): MIROp {
        switch (jobj.tag) {
            case MIROpTag.MIRLoadConst:
                return MIRLoadConst.jparse(jobj);
            case MIROpTag.MIRLoadConstTypedString:
                return MIRLoadConstTypedString.jparse(jobj);
            case MIROpTag.MIRAccessConstantValue:
                return MIRAccessConstantValue.jparse(jobj);
            case MIROpTag.MIRLoadFieldDefaultValue:
                return MIRLoadFieldDefaultValue.jparse(jobj);
            case MIROpTag.MIRAccessArgVariable:
                return MIRAccessArgVariable.jparse(jobj);
            case MIROpTag.MIRAccessLocalVariable:
                return MIRAccessLocalVariable.jparse(jobj);
            case MIROpTag.MIRConstructorPrimary:
                return MIRConstructorPrimary.jparse(jobj);
            case MIROpTag.MIRConstructorPrimaryCollectionEmpty:
                return MIRConstructorPrimaryCollectionEmpty.jparse(jobj);
            case MIROpTag.MIRConstructorPrimaryCollectionSingletons:
                return MIRConstructorPrimaryCollectionSingletons.jparse(jobj);
            case MIROpTag.MIRConstructorPrimaryCollectionCopies:
                return MIRConstructorPrimaryCollectionCopies.jparse(jobj);
            case MIROpTag.MIRConstructorPrimaryCollectionMixed:
                return MIRConstructorPrimaryCollectionMixed.jparse(jobj);
            case MIROpTag.MIRConstructorTuple:
                return MIRConstructorTuple.jparse(jobj);
            case MIROpTag.MIRConstructorRecord:
                return MIRConstructorRecord.jparse(jobj);
            case MIROpTag.MIRAccessFromIndex:
                return MIRAccessFromIndex.jparse(jobj);
            case MIROpTag.MIRProjectFromIndecies:
                return MIRProjectFromIndecies.jparse(jobj);
            case MIROpTag.MIRAccessFromProperty:
                return MIRAccessFromProperty.jparse(jobj);
            case MIROpTag.MIRProjectFromProperties:
                return MIRProjectFromProperties.jparse(jobj);
            case MIROpTag.MIRAccessFromField:
                return MIRAccessFromField.jparse(jobj);
            case MIROpTag.MIRProjectFromFields:
                return MIRProjectFromFields.jparse(jobj);
            case MIROpTag.MIRProjectFromTypeTuple:
                return MIRProjectFromTypeTuple.jparse(jobj);
            case MIROpTag.MIRProjectFromTypeRecord:
                return MIRProjectFromTypeRecord.jparse(jobj);
            case MIROpTag.MIRProjectFromTypeConcept:
                return MIRProjectFromTypeConcept.jparse(jobj);
            case MIROpTag.MIRModifyWithIndecies:
                return MIRModifyWithIndecies.jparse(jobj);
            case MIROpTag.MIRModifyWithProperties:
                return MIRModifyWithProperties.jparse(jobj);
            case MIROpTag.MIRModifyWithFields:
                return MIRModifyWithFields.jparse(jobj);
            case MIROpTag.MIRStructuredExtendTuple:
                return MIRStructuredExtendTuple.jparse(jobj);
            case MIROpTag.MIRStructuredExtendRecord:
                return MIRStructuredExtendRecord.jparse(jobj);
            case MIROpTag.MIRStructuredExtendObject:
                return MIRStructuredExtendObject.jparse(jobj);
            case MIROpTag.MIRInvokeFixedFunction:
                return MIRInvokeFixedFunction.jparse(jobj);
            case MIROpTag.MIRInvokeVirtualTarget:
                return MIRInvokeVirtualFunction.jparse(jobj);
            case MIROpTag.MIRPrefixOp:
                return MIRPrefixOp.jparse(jobj);
            case MIROpTag.MIRBinOp:
                return MIRBinOp.jparse(jobj);
            case MIROpTag.MIRGetKey:
                return MIRGetKey.jparse(jobj);
            case MIROpTag.MIRBinEq:
                return MIRBinEq.jparse(jobj);
            case MIROpTag.MIRBinCmp:
                return MIRBinCmp.jparse(jobj);
            case MIROpTag.MIRIsTypeOfNone:
                return MIRIsTypeOfNone.jparse(jobj);
            case MIROpTag.MIRIsTypeOfSome:
                return MIRIsTypeOfSome.jparse(jobj);
            case MIROpTag.MIRIsTypeOf:
                return MIRIsTypeOf.jparse(jobj);
            case MIROpTag.MIRRegAssign:
                return MIRRegAssign.jparse(jobj);
            case MIROpTag.MIRTruthyConvert:
                return MIRTruthyConvert.jparse(jobj);
            case MIROpTag.MIRLogicStore:
                return MIRLogicStore.jparse(jobj);
            case MIROpTag.MIRVarStore:
                return MIRVarStore.jparse(jobj);
            case MIROpTag.MIRReturnAssign:
                return MIRReturnAssign.jparse(jobj);
            case MIROpTag.MIRAbort:
                return MIRAbort.jparse(jobj);
            case MIROpTag.MIRDebug:
                return MIRDebug.jparse(jobj);
            case MIROpTag.MIRJump:
                return MIRJump.jparse(jobj);
            case MIROpTag.MIRJumpCond:
                return MIRJumpCond.jparse(jobj);
            case MIROpTag.MIRJumpNone:
                return MIRJumpNone.jparse(jobj);
            case MIROpTag.MIRPhi:
                return MIRPhi.jparse(jobj);
            case MIROpTag.MIRVarLifetimeStart:
                return MIRVarLifetimeStart.jparse(jobj);
            default:
                assert(jobj.tag === MIROpTag.MIRVarLifetimeEnd);
                return MIRVarLifetimeEnd.jparse(jobj);
        }
    }
}

abstract class MIRValueOp extends MIROp {
    trgt: MIRTempRegister;

    constructor(tag: MIROpTag, sinfo: SourceInfo, trgt: MIRTempRegister) {
        super(tag, sinfo);
        this.trgt = trgt;
    }

    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    protected jbemit(): object {
        return {...super.jbemit(), trgt: this.trgt.jemit() };
    }
}

abstract class MIRFlowOp extends MIROp {
    constructor(tag: MIROpTag, sinfo: SourceInfo) {
        super(tag, sinfo);
    }
}

abstract class MIRJumpOp extends MIROp {
    constructor(tag: MIROpTag, sinfo: SourceInfo) {
        super(tag, sinfo);
    }
}

class MIRLoadConst extends MIRValueOp {
    readonly src: MIRConstantArgument;

    constructor(sinfo: SourceInfo, src: MIRConstantArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRLoadConst, sinfo, trgt);
        this.src = src;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.src.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), src: this.src.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadConst(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src) as MIRConstantArgument, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRLoadConstTypedString extends MIRValueOp {
    readonly ivalue: string;
    readonly tkey: MIRNominalTypeKey;
    readonly tskey: MIRResolvedTypeKey;
    readonly pfunckey: MIRInvokeKey;

    constructor(sinfo: SourceInfo, ivalue: string, tkey: MIRNominalTypeKey, tskey: MIRResolvedTypeKey, pfunckey: MIRInvokeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRLoadConstTypedString, sinfo, trgt);
        this.ivalue = ivalue;
        this.tkey = tkey;
        this.tskey = tskey;
        this.pfunckey = pfunckey;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.ivalue}#${this.tkey}`;
    }

    jemit(): object {
        return { ...this.jbemit(), ivalue: this.ivalue, tkey: this.tkey, tskey: this.tskey, pfunckey: this.pfunckey };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadConstTypedString(jparsesinfo(jobj.sinfo), jobj.ivalue, jobj.tkey, jobj.tskey, jobj.pfunckey, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRAccessConstantValue extends MIRValueOp {
    readonly ckey: MIRConstantKey;

    constructor(sinfo: SourceInfo, ckey: MIRConstantKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRAccessConstantValue, sinfo, trgt);
        this.ckey = ckey;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.ckey}`;
    }

    jemit(): object {
        return { ...this.jbemit(), ckey: this.ckey };
    }

    static jparse(jobj: any): MIROp {
        return new MIRAccessConstantValue(jparsesinfo(jobj.sinfo), jobj.ckey, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRLoadFieldDefaultValue extends MIRValueOp {
    readonly fkey: MIRFieldKey;

    constructor(sinfo: SourceInfo, fkey: MIRFieldKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRLoadFieldDefaultValue, sinfo, trgt);
        this.fkey = fkey;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `${this.trgt.stringify()} = default(${this.fkey})`;
    }

    jemit(): object {
        return { ...this.jbemit(), fkey: this.fkey };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadFieldDefaultValue(jparsesinfo(jobj.sinfo), jobj.fkey, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRAccessArgVariable extends MIRValueOp {
    readonly name: MIRVariable;

    constructor(sinfo: SourceInfo, name: MIRVariable, trgt: MIRTempRegister) {
        super(MIROpTag.MIRAccessArgVariable, sinfo, trgt);
        this.name = name;
    }

    getUsedVars(): MIRRegisterArgument[] { return [this.name]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.name.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), name: this.name.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRAccessArgVariable(jparsesinfo(jobj.sinfo), MIRVariable.jparse(jobj.name), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRAccessLocalVariable extends MIRValueOp {
    name: MIRVariable;

    constructor(sinfo: SourceInfo, name: MIRVariable, trgt: MIRTempRegister) {
        super(MIROpTag.MIRAccessLocalVariable, sinfo, trgt);
        this.name = name;
    }

    getUsedVars(): MIRRegisterArgument[] { return [this.name]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.name.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), name: this.name.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRAccessLocalVariable(jparsesinfo(jobj.sinfo), MIRVariable.jparse(jobj.name), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRConstructorPrimary extends MIRValueOp {
    readonly tkey: MIRNominalTypeKey;
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, tkey: MIRNominalTypeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRConstructorPrimary, sinfo, trgt);
        this.tkey = tkey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tkey}@(${this.args.map((arg) => arg.stringify()).join(", ")})`;
    }

    jemit(): object {
        return { ...this.jbemit(), tkey: this.tkey, args: this.args.map((arg) => arg.jemit()) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorPrimary(jparsesinfo(jobj.sinfo), jobj.tkey, jobj.args.map((jarg: any) => MIRArgument.jparse(jarg)), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRConstructorPrimaryCollectionEmpty extends MIRValueOp {
    readonly tkey: MIRNominalTypeKey;

    constructor(sinfo: SourceInfo, tkey: MIRNominalTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRConstructorPrimaryCollectionEmpty, sinfo, trgt);
        this.tkey = tkey;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tkey}{}`;
    }

    jemit(): object {
        return { ...this.jbemit(), tkey: this.tkey };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorPrimaryCollectionEmpty(jparsesinfo(jobj.sinfo), jobj.tkey, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRConstructorPrimaryCollectionSingletons extends MIRValueOp {
    readonly tkey: MIRNominalTypeKey;
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, tkey: MIRNominalTypeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRConstructorPrimaryCollectionSingletons, sinfo, trgt);
        this.tkey = tkey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tkey}{${this.args.map((arg) => arg.stringify()).join(", ")}}`;
    }

    jemit(): object {
        return { ...this.jbemit(), tkey: this.tkey, args: this.args.map((arg) => arg.jemit()) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorPrimaryCollectionSingletons(jparsesinfo(jobj.sinfo), jobj.tkey, jobj.args.map((jarg: any) => MIRArgument.jparse(jarg)), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRConstructorPrimaryCollectionCopies extends MIRValueOp {
    readonly tkey: MIRNominalTypeKey;
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, tkey: MIRNominalTypeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRConstructorPrimaryCollectionCopies, sinfo, trgt);
        this.tkey = tkey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tkey}{${this.args.map((arg) => `expand(${arg.stringify()})`).join(", ")}`;
    }

    jemit(): object {
        return { ...this.jbemit(), tkey: this.tkey, args: this.args.map((arg) => arg.jemit()) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorPrimaryCollectionCopies(jparsesinfo(jobj.sinfo), jobj.tkey, jobj.args.map((jarg: any) => MIRArgument.jparse(jarg)), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRConstructorPrimaryCollectionMixed extends MIRValueOp {
    readonly tkey: MIRNominalTypeKey;
    args: [boolean, MIRArgument][];

    constructor(sinfo: SourceInfo, tkey: MIRNominalTypeKey, args: [boolean, MIRArgument][], trgt: MIRTempRegister) {
        super(MIROpTag.MIRConstructorPrimaryCollectionMixed, sinfo, trgt);
        this.tkey = tkey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper(this.args.map((tv) => tv[1])); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tkey}{${this.args.map((arg) => arg[0] ? `expand(${arg[1].stringify()})` : arg[1].stringify()).join(", ")}`;
    }

    jemit(): object {
        return { ...this.jbemit(), tkey: this.tkey, args: this.args.map((arg) => [arg[0], arg[1].jemit()]) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorPrimaryCollectionMixed(jparsesinfo(jobj.sinfo), jobj.tkey, jobj.args.map((jarg: any) => [jarg[0], MIRArgument.jparse(jarg[1])]), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRConstructorTuple extends MIRValueOp {
    resultTupleType: MIRResolvedTypeKey;
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, resultTupleType: MIRResolvedTypeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRConstructorTuple, sinfo, trgt);
        this.resultTupleType = resultTupleType;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = [${this.args.map((arg) => arg.stringify()).join(", ")}]`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultTupleType: this.resultTupleType, args: this.args.map((arg) => arg.jemit()) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorTuple(jparsesinfo(jobj.sinfo), jobj.resultTupleType, jobj.args.map((jarg: any) => MIRArgument.jparse(jarg)), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRConstructorRecord extends MIRValueOp {
    resultRecordType: MIRResolvedTypeKey;
    args: [string, MIRArgument][];

    constructor(sinfo: SourceInfo, resultRecordType: MIRResolvedTypeKey, args: [string, MIRArgument][], trgt: MIRTempRegister) {
        super(MIROpTag.MIRConstructorRecord, sinfo, trgt);
        this.resultRecordType = resultRecordType;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper(this.args.map((tv) => tv[1])); }

    stringify(): string {
        return `${this.trgt.stringify()} = {${this.args.map((arg) => `${arg[0]}=${arg[1].stringify()}`).join(", ")}}`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultRecordType: this.resultRecordType, args: this.args.map((arg) => [arg[0], arg[1].jemit()]) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorRecord(jparsesinfo(jobj.sinfo), jobj.resultRecordType, jobj.args.map((jarg: any) => [jarg[0], MIRArgument.jparse(jarg[1])]), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRAccessFromIndex extends MIRValueOp {
    resultAccessType: MIRResolvedTypeKey;
    arg: MIRArgument;
    readonly idx: number;

    constructor(sinfo: SourceInfo, resultAccessType: MIRResolvedTypeKey, arg: MIRArgument, idx: number, trgt: MIRTempRegister) {
        super(MIROpTag.MIRAccessFromIndex, sinfo, trgt);
        this.resultAccessType = resultAccessType;
        this.arg = arg;
        this.idx = idx;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}[${this.idx}]`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultAccessType: this.resultAccessType, arg: this.arg.jemit(), idx: this.idx };
    }

    static jparse(jobj: any): MIROp {
        return new MIRAccessFromIndex(jparsesinfo(jobj.sinfo), jobj.resultAccessType, MIRArgument.jparse(jobj.arg), jobj.idx, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRProjectFromIndecies extends MIRValueOp {
    resultProjectType: MIRResolvedTypeKey;
    arg: MIRArgument;
    readonly indecies: number[];

    constructor(sinfo: SourceInfo, resultProjectType: MIRResolvedTypeKey, arg: MIRArgument, indecies: number[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRProjectFromIndecies, sinfo, trgt);
        this.resultProjectType = resultProjectType;
        this.arg = arg;
        this.indecies = indecies;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}@[${this.indecies.map((i) => i.toString()).join(", ")}]`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultProjectType: this.resultProjectType, arg: this.arg.jemit(), indecies: this.indecies };
    }

    static jparse(jobj: any): MIROp {
        return new MIRProjectFromIndecies(jparsesinfo(jobj.sinfo), jobj.resultProjectType, MIRArgument.jparse(jobj.arg), jobj.indecies, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRAccessFromProperty extends MIRValueOp {
    resultAccessType: MIRResolvedTypeKey;
    arg: MIRArgument;
    readonly property: string;

    constructor(sinfo: SourceInfo, resultAccessType: MIRResolvedTypeKey, arg: MIRArgument, property: string, trgt: MIRTempRegister) {
        super(MIROpTag.MIRAccessFromProperty, sinfo, trgt);
        this.resultAccessType = resultAccessType;
        this.arg = arg;
        this.property = property;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.${this.property}`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultAccessType: this.resultAccessType, arg: this.arg.jemit(), property: this.property };
    }

    static jparse(jobj: any): MIROp {
        return new MIRAccessFromProperty(jparsesinfo(jobj.sinfo), jobj.resultAccessType, MIRArgument.jparse(jobj.arg), jobj.property, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRProjectFromProperties extends MIRValueOp {
    resultProjectType: MIRResolvedTypeKey;
    arg: MIRArgument;
    readonly properties: string[];

    constructor(sinfo: SourceInfo, resultProjectType: MIRResolvedTypeKey, arg: MIRArgument, properties: string[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRProjectFromProperties, sinfo, trgt);
        this.resultProjectType = resultProjectType;
        this.arg = arg;
        this.properties = properties;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}{${this.properties.join(", ")}}`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultProjectType: this.resultProjectType, arg: this.arg.jemit(), properties: this.properties };
    }

    static jparse(jobj: any): MIROp {
        return new MIRProjectFromProperties(jparsesinfo(jobj.sinfo), jobj.resultProjectType, MIRArgument.jparse(jobj.arg), jobj.properties, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRAccessFromField extends MIRValueOp {
    resultAccessType: MIRResolvedTypeKey;
    arg: MIRArgument;
    readonly field: string;

    constructor(sinfo: SourceInfo, resultAccessType: MIRResolvedTypeKey, arg: MIRArgument, field: string, trgt: MIRTempRegister) {
        super(MIROpTag.MIRAccessFromField, sinfo, trgt);
        this.resultAccessType = resultAccessType;
        this.arg = arg;
        this.field = field;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.${this.field}`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultAccessType: this.resultAccessType, arg: this.arg.jemit(), field: this.field };
    }

    static jparse(jobj: any): MIROp {
        return new MIRAccessFromField(jparsesinfo(jobj.sinfo), jobj.resultAccessType, MIRArgument.jparse(jobj.arg), jobj.field, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRProjectFromFields extends MIRValueOp {
    resultProjectType: MIRResolvedTypeKey;
    arg: MIRArgument;
    readonly fields: string[];

    constructor(sinfo: SourceInfo, resultProjectType: MIRResolvedTypeKey, arg: MIRArgument, fields: string[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRProjectFromFields, sinfo, trgt);
        this.resultProjectType = resultProjectType;
        this.arg = arg;
        this.fields = fields;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}{${this.fields.join(", ")}}`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultProjectType: this.resultProjectType, arg: this.arg.jemit(), fields: this.fields };
    }

    static jparse(jobj: any): MIROp {
        return new MIRProjectFromFields(jparsesinfo(jobj.sinfo), jobj.resultProjectType, MIRArgument.jparse(jobj.arg), jobj.fields, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRProjectFromTypeTuple extends MIRValueOp {
    resultProjectType: MIRResolvedTypeKey;
    arg: MIRArgument;
    readonly ptype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, resultProjectType: MIRResolvedTypeKey, arg: MIRArgument, ptype: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRProjectFromTypeTuple, sinfo, trgt);
        this.resultProjectType = resultProjectType;
        this.arg = arg;
        this.ptype = ptype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}#${this.ptype}`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultProjectType: this.resultProjectType, arg: this.arg.jemit(), ptype: this.ptype };
    }

    static jparse(jobj: any): MIROp {
        return new MIRProjectFromTypeTuple(jparsesinfo(jobj.sinfo), jobj.resultProjectType, MIRArgument.jparse(jobj.arg), jobj.ptype, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRProjectFromTypeRecord extends MIRValueOp {
    resultProjectType: MIRResolvedTypeKey;
    arg: MIRArgument;
    readonly ptype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, resultProjectType: MIRResolvedTypeKey, arg: MIRArgument, ptype: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRProjectFromTypeRecord, sinfo, trgt);
        this.resultProjectType = resultProjectType;
        this.arg = arg;
        this.ptype = ptype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}#${this.ptype}`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultProjectType: this.resultProjectType, arg: this.arg.jemit(), ptype: this.ptype };
    }

    static jparse(jobj: any): MIROp {
        return new MIRProjectFromTypeRecord(jparsesinfo(jobj.sinfo), jobj.resultProjectType, MIRArgument.jparse(jobj.arg), jobj.ptype, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRProjectFromTypeConcept extends MIRValueOp {
    resultProjectType: MIRResolvedTypeKey;
    arg: MIRArgument;
    readonly ctypes: MIRNominalTypeKey[];

    constructor(sinfo: SourceInfo, resultProjectType: MIRResolvedTypeKey, arg: MIRArgument, ctypes: MIRNominalTypeKey[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRProjectFromTypeConcept, sinfo, trgt);
        this.resultProjectType = resultProjectType;
        this.arg = arg;
        this.ctypes = ctypes;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}#${this.ctypes.join("&")}`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultProjectType: this.resultProjectType, arg: this.arg.jemit(), ctypes: this.ctypes };
    }

    static jparse(jobj: any): MIROp {
        return new MIRProjectFromTypeConcept(jparsesinfo(jobj.sinfo), jobj.resultProjectType, MIRArgument.jparse(jobj.arg), jobj.ctypes, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRModifyWithIndecies extends MIRValueOp {
    resultTupleType: MIRResolvedTypeKey;
    arg: MIRArgument;
    updates: [number, MIRArgument][];

    constructor(sinfo: SourceInfo, resultTupleType: MIRResolvedTypeKey, arg: MIRArgument, updates: [number, MIRArgument][], trgt: MIRTempRegister) {
        super(MIROpTag.MIRModifyWithIndecies, sinfo, trgt);
        this.resultTupleType = resultTupleType;
        this.arg = arg;
        this.updates = updates;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg, ...this.updates.map((u) => u[1])]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}<~${this.updates.map((u) => `${u[0]}=${u[1].stringify()}`).join(", ")}]`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultTupleType: this.resultTupleType, arg: this.arg.jemit(), udpates: this.updates.map((update) => [update[0], update[1].jemit()]) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRModifyWithIndecies(jparsesinfo(jobj.sinfo), jobj.resultTupleType, MIRArgument.jparse(jobj.arg), jobj.updates.map((update: any) => [update[0], MIRArgument.jparse(update[1])]), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRModifyWithProperties extends MIRValueOp {
    resultRecordType: MIRResolvedTypeKey;
    arg: MIRArgument;
    updates: [string, MIRArgument][];

    constructor(sinfo: SourceInfo, resultRecordType: MIRResolvedTypeKey, arg: MIRArgument, updates: [string, MIRArgument][], trgt: MIRTempRegister) {
        super(MIROpTag.MIRModifyWithProperties, sinfo, trgt);
        this.resultRecordType = resultRecordType;
        this.arg = arg;
        this.updates = updates;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg, ...this.updates.map((u) => u[1])]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}<~${this.updates.map((u) => `${u[0]}=${u[1].stringify()}`).join(", ")}]`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultRecordType: this.resultRecordType, arg: this.arg.jemit(), udpates: this.updates.map((update) => [update[0], update[1].jemit()]) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRModifyWithProperties(jparsesinfo(jobj.sinfo), jobj.resultRecordType, MIRArgument.jparse(jobj.arg), jobj.updates.map((update: any) => [update[0], MIRArgument.jparse(update[1])]), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRModifyWithFields extends MIRValueOp {
    resultNominalType: MIRResolvedTypeKey;
    arg: MIRArgument;
    updates: [string, MIRArgument][];

    constructor(sinfo: SourceInfo, resultNominalType: MIRResolvedTypeKey, arg: MIRArgument, updates: [string, MIRArgument][], trgt: MIRTempRegister) {
        super(MIROpTag.MIRModifyWithFields, sinfo, trgt);
        this.resultNominalType = resultNominalType;
        this.arg = arg;
        this.updates = updates;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg, ...this.updates.map((u) => u[1])]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}<~${this.updates.map((u) => `${u[0]}=${u[1].stringify()}`).join(", ")}]`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultNominalType: this.resultNominalType, arg: this.arg.jemit(), updates: this.updates.map((update) => [update[0], update[1].jemit()]) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRModifyWithFields(jparsesinfo(jobj.sinfo), jobj.resultNominalType, MIRArgument.jparse(jobj.arg), jobj.updates.map((update: any) => [update[0], MIRArgument.jparse(update[1])]), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRStructuredExtendTuple extends MIRValueOp {
    resultTupleType: MIRResolvedTypeKey;
    arg: MIRArgument;
    update: MIRArgument;

    constructor(sinfo: SourceInfo, resultTupleType: MIRResolvedTypeKey, arg: MIRArgument, update: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRStructuredExtendTuple, sinfo, trgt);
        this.resultTupleType = resultTupleType;
        this.arg = arg;
        this.update = update;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg, this.update]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}<+(${this.update.stringify()})`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultTupleType: this.resultTupleType, arg: this.arg.jemit(), udpate: this.update.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRStructuredExtendTuple(jparsesinfo(jobj.sinfo), jobj.resultTupleType, MIRArgument.jparse(jobj.arg), MIRArgument.jparse(jobj.update), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRStructuredExtendRecord extends MIRValueOp {
    resultRecordType: MIRResolvedTypeKey;
    arg: MIRArgument;
    update: MIRArgument;

    constructor(sinfo: SourceInfo, resultRecordType: MIRResolvedTypeKey, arg: MIRArgument, update: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRStructuredExtendRecord, sinfo, trgt);
        this.resultRecordType = resultRecordType;
        this.arg = arg;
        this.update = update;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg, this.update]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}<+(${this.update.stringify()})`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultRecordType: this.resultRecordType, arg: this.arg.jemit(), udpate: this.update.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRStructuredExtendRecord(jparsesinfo(jobj.sinfo), jobj.resultRecordType, MIRArgument.jparse(jobj.arg), MIRArgument.jparse(jobj.update), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRStructuredExtendObject extends MIRValueOp {
    resultNominalType: MIRResolvedTypeKey;
    arg: MIRArgument;
    update: MIRArgument;

    constructor(sinfo: SourceInfo, resultNominalType: MIRResolvedTypeKey, arg: MIRArgument, update: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRStructuredExtendObject, sinfo, trgt);
        this.resultNominalType = resultNominalType;
        this.arg = arg;
        this.update = update;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg, this.update]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}<+(${this.update.stringify()})`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultNominalType: this.resultNominalType, arg: this.arg.jemit(), udpate: this.update.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRStructuredExtendObject(jparsesinfo(jobj.sinfo), jobj.resultNominalType, MIRArgument.jparse(jobj.arg), MIRArgument.jparse(jobj.update), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRInvokeFixedFunction extends MIRValueOp {
    resultType: MIRResolvedTypeKey;
    readonly mkey: MIRInvokeKey;
    args: MIRArgument[]; //this is args[0] for methods

    constructor(sinfo: SourceInfo, resultType: MIRResolvedTypeKey, mkey: MIRInvokeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRInvokeFixedFunction, sinfo, trgt);
        this.resultType = resultType;
        this.mkey = mkey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.mkey}::(${this.args.map((arg) => arg.stringify()).join(", ")})`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultType: this.resultType, mkey: this.mkey, args: this.args.map((arg) => arg.jemit()) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRInvokeFixedFunction(jparsesinfo(jobj.sinfo), jobj.resultType, jobj.mkey, jobj.args.map((arg: any) => MIRArgument.jparse(arg)), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRInvokeVirtualFunction extends MIRValueOp {
    resultType: MIRResolvedTypeKey;
    readonly vresolve: MIRVirtualMethodKey;
    args: MIRArgument[]; //this is args[0]

    constructor(sinfo: SourceInfo, resultType: MIRResolvedTypeKey, vresolve: MIRVirtualMethodKey, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRInvokeVirtualTarget, sinfo, trgt);
        this.resultType = resultType;
        this.vresolve = vresolve;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.args[0].stringify()}->${this.vresolve}(${[...this.args].slice(1).map((arg) => arg.stringify()).join(", ")})`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultType: this.resultType, vresolve: this.vresolve, args: this.args.map((arg) => arg.jemit()) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRInvokeVirtualFunction(jparsesinfo(jobj.sinfo), jobj.resultType, jobj.vresolve, jobj.args.map((arg: any) => MIRArgument.jparse(arg)), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRPrefixOp extends MIRValueOp {
    readonly op: string; //+, -, !
    arg: MIRArgument;

    constructor(sinfo: SourceInfo, op: string, arg: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRPrefixOp, sinfo, trgt);
        this.op = op;
        this.arg = arg;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.op}${this.arg.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), op: this.op, arg: this.arg.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRPrefixOp(jparsesinfo(jobj.sinfo), jobj.op, MIRArgument.jparse(jobj.arg), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRBinOp extends MIRValueOp {
    lhs: MIRArgument;
    readonly op: string; //+, -, *, /, %
    rhs: MIRArgument;

    constructor(sinfo: SourceInfo, lhs: MIRArgument, op: string, rhs: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRBinOp, sinfo, trgt);
        this.lhs = lhs;
        this.op = op;
        this.rhs = rhs;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.lhs, this.rhs]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.lhs.stringify()}${this.op}${this.rhs.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), lhs: this.lhs.jemit(), op: this.op, rhs: this.rhs.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRBinOp(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.lhs), jobj.op, MIRArgument.jparse(jobj.rhs), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRGetKey extends MIRValueOp {
    readonly argInferType: MIRResolvedTypeKey;
    arg: MIRArgument;
    readonly resultKeyType: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, argInferType: MIRResolvedTypeKey, arg: MIRArgument, resultKeyType: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRGetKey, sinfo, trgt);
        this.argInferType = argInferType;
        this.arg = arg;
        this.resultKeyType = resultKeyType;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = Indexable::getKey(${this.arg.stringify()})`;
    }

    jemit(): object {
        return { ...this.jbemit(), argInferType: this.argInferType, arg: this.arg.jemit(), resultKeyType: this.resultKeyType };
    }

    static jparse(jobj: any): MIROp {
        return new MIRGetKey(jparsesinfo(jobj.sinfo), jobj.argInferType, MIRArgument.jparse(jobj.arg), jobj.resultKeyType, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRBinEq extends MIRValueOp {
    readonly lhsInferType: MIRResolvedTypeKey;
    lhs: MIRArgument;
    readonly op: string; //==, !=
    readonly rhsInferType: MIRResolvedTypeKey;
    rhs: MIRArgument;

    constructor(sinfo: SourceInfo, lhsInferType: MIRResolvedTypeKey, lhs: MIRArgument, op: string, rhsInferType: MIRResolvedTypeKey, rhs: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRBinEq, sinfo, trgt);
        this.lhsInferType = lhsInferType;
        this.lhs = lhs;
        this.op = op;
        this.rhsInferType = rhsInferType;
        this.rhs = rhs;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.lhs, this.rhs]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.lhs.stringify()}${this.op}${this.rhs.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), lhsInferType: this.lhsInferType, lhs: this.lhs.jemit(), op: this.op, rhsInferType: this.rhsInferType, rhs: this.rhs.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRBinEq(jparsesinfo(jobj.sinfo), jobj.lhsInferType, MIRArgument.jparse(jobj.lhs), jobj.op, jobj.rhsInferType, MIRArgument.jparse(jobj.rhs), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRBinCmp extends MIRValueOp {
    readonly lhsInferType: MIRResolvedTypeKey;
    lhs: MIRArgument;
    readonly op: string; //<, >, <=, >=
    rhs: MIRArgument;
    readonly rhsInferType: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, lhsInferType: MIRResolvedTypeKey, lhs: MIRArgument, op: string, rhsInferType: MIRResolvedTypeKey, rhs: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRBinCmp, sinfo, trgt);
        this.lhsInferType = lhsInferType;
        this.lhs = lhs;
        this.op = op;
        this.rhsInferType = rhsInferType;
        this.rhs = rhs;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.lhs, this.rhs]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.lhs.stringify()}${this.op}${this.rhs.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), lhsInferType: this.lhsInferType, lhs: this.lhs.jemit(), op: this.op, rhsInferType: this.rhsInferType, rhs: this.rhs.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRBinCmp(jparsesinfo(jobj.sinfo), jobj.lhsInferType, MIRArgument.jparse(jobj.lhs), jobj.op, jobj.rhsInferType, MIRArgument.jparse(jobj.rhs), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRIsTypeOfNone extends MIRValueOp {
    arg: MIRArgument;

    constructor(sinfo: SourceInfo, arg: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRIsTypeOfNone, sinfo, trgt);
        this.arg = arg;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = $isNoneType(${this.arg.stringify()})`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRIsTypeOfNone(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRIsTypeOfSome extends MIRValueOp {
    arg: MIRArgument;

    constructor(sinfo: SourceInfo, arg: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRIsTypeOfSome, sinfo, trgt);
        this.arg = arg;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = $isSomeType(${this.arg.stringify()})`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRIsTypeOfSome(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRIsTypeOf extends MIRValueOp {
    readonly argInferType: MIRResolvedTypeKey;
    arg: MIRArgument;
    readonly oftype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, argInferType: MIRResolvedTypeKey, arg: MIRArgument, oftype: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRIsTypeOf, sinfo, trgt);
        this.argInferType = argInferType;
        this.arg = arg;
        this.oftype = oftype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = $isTypeOf(${this.arg.stringify()}, ${this.oftype})`;
    }

    jemit(): object {
        return { ...this.jbemit(), argInferType: this.argInferType, arg: this.arg.jemit(), oftype: this.oftype };
    }

    static jparse(jobj: any): MIROp {
        return new MIRIsTypeOf(jparsesinfo(jobj.sinfo), jobj.argInferType, MIRArgument.jparse(jobj.arg), jobj.oftype, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRRegAssign extends MIRFlowOp {
    src: MIRArgument;
    trgt: MIRTempRegister;

    constructor(sinfo: SourceInfo, src: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRRegAssign, sinfo);
        this.src = src;
        this.trgt = trgt;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.src]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.src.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), src: this.src.jemit(), trgt: this.trgt.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRRegAssign(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRTruthyConvert extends MIRFlowOp {
    src: MIRArgument;
    trgt: MIRTempRegister;

    constructor(sinfo: SourceInfo, src: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRTruthyConvert, sinfo);
        this.src = src;
        this.trgt = trgt;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.src]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = $truthy(${this.src.stringify()})`;
    }

    jemit(): object {
        return { ...this.jbemit(), src: this.src.jemit(), trgt: this.trgt.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRTruthyConvert(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRLogicStore extends MIRFlowOp {
    lhs: MIRArgument;
    readonly op: string;
    rhs: MIRArgument;
    trgt: MIRTempRegister;

    constructor(sinfo: SourceInfo, lhs: MIRArgument, op: string, rhs: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRLogicStore, sinfo);
        this.lhs = lhs;
        this.op = op;
        this.rhs = rhs;
        this.trgt = trgt;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.lhs, this.rhs]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.lhs.stringify()} ${this.op} ${this.rhs.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), lhs: this.lhs.jemit(), op: this.op, rhs: this.rhs.jemit(), trgt: this.trgt.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLogicStore(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.lhs), jobj.op, MIRArgument.jparse(jobj.rhs), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRVarStore extends MIRFlowOp {
    src: MIRArgument;
    name: MIRVariable;

    constructor(sinfo: SourceInfo, src: MIRArgument, name: MIRVariable) {
        super(MIROpTag.MIRVarStore, sinfo);
        this.src = src;
        this.name = name;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.src]); }
    getModVars(): MIRRegisterArgument[] { return [this.name]; }

    stringify(): string {
        return `${this.name.stringify()} = ${this.src.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), src: this.src.jemit(), name: this.name.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRVarStore(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), MIRVariable.jparse(jobj.name));
    }
}

class MIRReturnAssign extends MIRFlowOp {
    src: MIRArgument;
    name: MIRVariable;

    constructor(sinfo: SourceInfo, src: MIRArgument, name?: MIRVariable) {
        super(MIROpTag.MIRReturnAssign, sinfo);
        this.src = src;
        this.name = name || new MIRVariable("__ir_ret__");
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.src]); }
    getModVars(): MIRRegisterArgument[] { return [this.name]; }

    stringify(): string {
        return `${this.name.stringify()} = ${this.src.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), src: this.src.jemit(), name: this.name.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRReturnAssign(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), MIRVariable.jparse(jobj.name));
    }
}

class MIRAbort extends MIRFlowOp {
    readonly releaseEnable: boolean;
    readonly info: string;

    constructor(sinfo: SourceInfo, releaseEnable: boolean, info: string) {
        super(MIROpTag.MIRAbort, sinfo);
        this.releaseEnable = releaseEnable;
        this.info = info;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `abort${this.releaseEnable ? "" : "_debug"} -- ${this.info}`;
    }

    jemit(): object {
        return { ...this.jbemit(), releaseEnable: this.releaseEnable, info: this.info };
    }

    static jparse(jobj: any): MIROp {
        return new MIRAbort(jparsesinfo(jobj.sinfo), jobj.releaseEnable, jobj.info);
    }
}

class MIRDebug extends MIRFlowOp {
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

class MIRJump extends MIRJumpOp {
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

class MIRVarLifetimeStart extends MIRJumpOp {
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

class MIRVarLifetimeEnd extends MIRJumpOp {
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

class MIRJumpCond extends MIRJumpOp {
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

class MIRJumpNone extends MIRJumpOp {
    arg: MIRArgument;
    readonly noneblock: string;
    readonly someblock: string;

    constructor(sinfo: SourceInfo, arg: MIRArgument, noneblck: string, someblck: string) {
        super(MIROpTag.MIRJumpNone, sinfo);
        this.arg = arg;
        this.noneblock = noneblck;
        this.someblock = someblck;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `njump ${this.arg.stringify()} ${this.noneblock} ${this.someblock}`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit(), noneblock: this.noneblock, someblock: this.someblock };
    }

    static jparse(jobj: any): MIROp {
        return new MIRJumpNone(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.noneblock, jobj.someblock);
    }
}

class MIRPhi extends MIRFlowOp {
    src: Map<string, MIRRegisterArgument>;
    trgt: MIRRegisterArgument;

    constructor(sinfo: SourceInfo, src: Map<string, MIRRegisterArgument>, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRPhi, sinfo);
        this.src = src;
        this.trgt = trgt;
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
        return { ...this.jbemit(), src: phis, trgt: this.trgt.jemit() };
    }

    static jparse(jobj: any): MIROp {
        let phis = new Map<string, MIRRegisterArgument>();
        jobj.src.forEach((phi: [string, any]) => phis.set(phi[0], MIRRegisterArgument.jparse(phi[1])));
        return new MIRPhi(jparsesinfo(jobj.sinfo), phis, MIRRegisterArgument.jparse(jobj.trgt));
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
    readonly bkey: MIRBodyKey;

    body: Map<string, MIRBasicBlock>;
    vtypes: Map<string, MIRResolvedTypeKey> | undefined;

    constructor(file: string, sinfo: SourceInfo, bkey: MIRBodyKey, body: Map<string, MIRBasicBlock>, vtypes?: Map<string, MIRResolvedTypeKey>) {
        this.file = file;
        this.sinfo = sinfo;
        this.bkey = bkey;

        this.body = body;
        this.vtypes = vtypes;
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
        const vtypes = this.vtypes !== undefined ? ([...this.vtypes].sort((a, b) => a[0].localeCompare(b[0]))) : undefined;
        return { file: this.file, sinfo: jemitsinfo(this.sinfo), bkey: this.bkey, blocks: blocks, vtypes: vtypes };
    }

    static jparse(jobj: any): MIRBody {
        let body = new Map<string, MIRBasicBlock>();
        jobj.blocks.map((blck: any) => MIRBasicBlock.jparse(blck)).forEach((blck: MIRBasicBlock) => body.set(blck.label, blck));

        if (jobj.vtypes === undefined) {
            return new MIRBody(jobj.file, jparsesinfo(jobj.sinfo), jobj.bkey, body);
        }
        else {
            let vtypes = new Map<string, MIRResolvedTypeKey>();
            jobj.vtypes.forEach((vtype: [string, string]) => vtypes.set(vtype[0], vtype[1]));

            return new MIRBody(jobj.file, jparsesinfo(jobj.sinfo), jobj.bkey, body, vtypes);
        }
    }
}

export {
    MIRConstantKey, MIRFieldKey, MIRInvokeKey, MIRNominalTypeKey, MIRResolvedTypeKey, MIRVirtualMethodKey,
    MIRBodyKey, extractMirBodyKeyPrefix, extractMirBodyKeyData,
    MIRArgument, MIRRegisterArgument, MIRTempRegister, MIRVariable, MIRConstantArgument, MIRConstantNone, MIRConstantTrue, MIRConstantFalse, MIRConstantInt, MIRConstantString,
    MIROpTag, MIROp, MIRValueOp, MIRFlowOp, MIRJumpOp,
    MIRLoadConst, MIRLoadConstTypedString,
    MIRAccessConstantValue, MIRLoadFieldDefaultValue, MIRAccessArgVariable, MIRAccessLocalVariable,
    MIRConstructorPrimary, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionSingletons, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionMixed, MIRConstructorTuple, MIRConstructorRecord,
    MIRAccessFromIndex, MIRProjectFromIndecies, MIRAccessFromProperty, MIRProjectFromProperties, MIRAccessFromField, MIRProjectFromFields, MIRProjectFromTypeTuple, MIRProjectFromTypeRecord, MIRProjectFromTypeConcept, MIRModifyWithIndecies, MIRModifyWithProperties, MIRModifyWithFields, MIRStructuredExtendTuple, MIRStructuredExtendRecord, MIRStructuredExtendObject,
    MIRInvokeFixedFunction, MIRInvokeVirtualFunction,
    MIRPrefixOp, MIRBinOp, MIRGetKey, MIRBinEq, MIRBinCmp,
    MIRIsTypeOfNone, MIRIsTypeOfSome, MIRIsTypeOf,
    MIRRegAssign, MIRTruthyConvert, MIRLogicStore, MIRVarStore, MIRReturnAssign,
    MIRAbort, MIRDebug,
    MIRJump, MIRJumpCond, MIRJumpNone,
    MIRPhi,
    MIRVarLifetimeStart, MIRVarLifetimeEnd,
    MIRBasicBlock, MIRBody
};
