//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo } from "../ast/parser";
import { topologicalOrder, computeBlockLinks, FlowLink } from "./mir_info";

type MIRTypeKey = string; //ns::name#binds
type MIRGlobalKey = string; //ns::global
type MIRConstKey = string; //ns::name::const#binds
type MIRFieldKey = string; //ns::name::field#binds
type MIRLambdaKey = string; //enclosingkey$line$column#binds
type MIRFunctionKey = string; //ns::func#binds
type MIRStaticKey = string; //ns::name::static#binds
type MIRMethodKey = string; //ns::name::method#binds

type MIRResolvedTypeKey = string; //idstr
type MIRVirtualMethodKey = string; //method#binds

abstract class MIRArgument {
    readonly nameID: string;

    constructor(nameID: string) {
        this.nameID = nameID;
    }

    abstract stringify(): string;
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
}

class MIRVarCaptured extends MIRRegisterArgument {
    constructor(name: string) {
        super(name);
    }
}

class MIRVarParameter extends MIRRegisterArgument {
    constructor(name: string) {
        super(name);
    }
}

class MIRVarLocal extends MIRRegisterArgument {
    readonly lname: string;

    constructor(name: string, forcename?: string) {
        super(forcename || name);
        this.lname = name;
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
}

class MIRConstantTrue extends MIRConstantArgument {
    constructor() {
        super("=true=");
    }

    stringify(): string {
        return "true";
    }
}

class MIRConstantFalse extends MIRConstantArgument {
    constructor() {
        super("=false=");
    }

    stringify(): string {
        return "false";
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
}

//
//TODO: constant typed string and enum here for copy prop etc.
//

enum MIROpTag {
    LoadConst = "LoadConst",
    LoadConstTypedString = "LoadConstTypedString",

    AccessNamespaceConstant = "AccessNamespaceConstant",
    AccessConstField = " AccessConstField",
    LoadFieldDefaultValue = "LoadFieldDefaultValue",
    AccessCapturedVariable = "AccessCapturedVariable",
    AccessArgVariable = "AccessArgVariable",
    AccessLocalVariable = "AccessLocalVariable",

    ConstructorPrimary = "ConstructorPrimary",
    ConstructorPrimaryCollectionEmpty = "ConstructorPrimaryCollectionEmpty",
    ConstructorPrimaryCollectionSingletons = "ConstructorPrimaryCollectionSingletons",
    ConstructorPrimaryCollectionCopies = "ConstructorPrimaryCollectionCopies",
    ConstructorPrimaryCollectionMixed = "ConstructorPrimaryCollectionMixed",
    ConstructorTuple = "ConstructorTuple",
    ConstructorRecord = "ConstructorRecord",
    ConstructorLambda = "ConstructorLambda",

    CallNamespaceFunction = "CallNamespaceFunction",
    CallStaticFunction = "CallStaticFunction",

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
    MIRInvokeKnownTarget = "MIRInvokeKnownTarget",
    MIRInvokeVirtualTarget = "MIRInvokeVirtualTarget",
    MIRCallLambda = "MIRCallLambda",

    MIRPrefixOp = "MIRPrefixOp",

    MIRBinOp = "MIRBinOp",
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
}

abstract class MIRValueOp extends MIROp {
    trgt: MIRTempRegister;

    constructor(tag: MIROpTag, sinfo: SourceInfo, trgt: MIRTempRegister) {
        super(tag, sinfo);
        this.trgt = trgt;
    }

    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }
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
        super(MIROpTag.LoadConst, sinfo, trgt);
        this.src = src;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.src.stringify()}`;
    }
}

class MIRLoadConstTypedString extends MIRValueOp {
    readonly ivalue: string;
    readonly tkey: MIRTypeKey;
    readonly tskey: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, ivalue: string, tkey: MIRTypeKey, tskey: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.LoadConstTypedString, sinfo, trgt);
        this.ivalue = ivalue;
        this.tkey = tkey;
        this.tskey = tskey;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.ivalue}#${this.tkey}`;
    }
}

class MIRAccessNamespaceConstant extends MIRValueOp {
    readonly gkey: MIRGlobalKey;

    constructor(sinfo: SourceInfo, gkey: MIRGlobalKey, trgt: MIRTempRegister) {
        super(MIROpTag.AccessNamespaceConstant, sinfo, trgt);
        this.gkey = gkey;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.gkey}`;
    }
}

class MIRAccessConstField extends MIRValueOp {
    readonly ckey: MIRConstKey;

    constructor(sinfo: SourceInfo, ckey: MIRConstKey, trgt: MIRTempRegister) {
        super(MIROpTag.AccessConstField, sinfo, trgt);
        this.ckey = ckey;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.ckey}`;
    }
}

class MIRLoadFieldDefaultValue extends MIRValueOp {
    readonly fkey: MIRFieldKey;

    constructor(sinfo: SourceInfo, fkey: MIRFieldKey, trgt: MIRTempRegister) {
        super(MIROpTag.LoadFieldDefaultValue, sinfo, trgt);
        this.fkey = fkey;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `${this.trgt.stringify()} = default(${this.fkey})`;
    }
}

class MIRAccessCapturedVariable extends MIRValueOp {
    readonly name: MIRVarCaptured;

    constructor(sinfo: SourceInfo, name: MIRVarCaptured, trgt: MIRTempRegister) {
        super(MIROpTag.AccessCapturedVariable, sinfo, trgt);
        this.name = name;
    }

    getUsedVars(): MIRRegisterArgument[] { return [this.name]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.name.stringify()}`;
    }
}

class MIRAccessArgVariable extends MIRValueOp {
    readonly name: MIRVarParameter;

    constructor(sinfo: SourceInfo, name: MIRVarParameter, trgt: MIRTempRegister) {
        super(MIROpTag.AccessArgVariable, sinfo, trgt);
        this.name = name;
    }

    getUsedVars(): MIRRegisterArgument[] { return [this.name]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.name.stringify()}`;
    }
}

class MIRAccessLocalVariable extends MIRValueOp {
    name: MIRVarLocal;

    constructor(sinfo: SourceInfo, name: MIRVarLocal, trgt: MIRTempRegister) {
        super(MIROpTag.AccessLocalVariable, sinfo, trgt);
        this.name = name;
    }

    getUsedVars(): MIRRegisterArgument[] { return [this.name]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.name.stringify()}`;
    }
}

class MIRConstructorPrimary extends MIRValueOp {
    readonly tkey: MIRTypeKey;
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, tkey: MIRTypeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.ConstructorPrimary, sinfo, trgt);
        this.tkey = tkey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tkey}@(${this.args.map((arg) => arg.stringify()).join(", ")})`;
    }
}

class MIRConstructorPrimaryCollectionEmpty extends MIRValueOp {
    readonly tkey: MIRTypeKey;

    constructor(sinfo: SourceInfo, tkey: MIRTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.ConstructorPrimaryCollectionEmpty, sinfo, trgt);
        this.tkey = tkey;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tkey}@{}`;
    }
}

class MIRConstructorPrimaryCollectionSingletons extends MIRValueOp {
    readonly tkey: MIRTypeKey;
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, tkey: MIRTypeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.ConstructorPrimaryCollectionSingletons, sinfo, trgt);
        this.tkey = tkey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tkey}@{${this.args.map((arg) => arg.stringify()).join(", ")}}`;
    }
}

class MIRConstructorPrimaryCollectionCopies extends MIRValueOp {
    readonly tkey: MIRTypeKey;
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, tkey: MIRTypeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.ConstructorPrimaryCollectionCopies, sinfo, trgt);
        this.tkey = tkey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tkey}@{${this.args.map((arg) => `expand(${arg.stringify()})`).join(", ")}`;
    }
}

class MIRConstructorPrimaryCollectionMixed extends MIRValueOp {
    readonly tkey: MIRTypeKey;
    args: [boolean, MIRArgument][];

    constructor(sinfo: SourceInfo, tkey: MIRTypeKey, args: [boolean, MIRArgument][], trgt: MIRTempRegister) {
        super(MIROpTag.ConstructorPrimaryCollectionMixed, sinfo, trgt);
        this.tkey = tkey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper(this.args.map((tv) => tv[1])); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tkey}@{${this.args.map((arg) => arg[0] ? `expand(${arg[1].stringify()})` : arg[1].stringify()).join(", ")}`;
    }
}

class MIRConstructorTuple extends MIRValueOp {
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.ConstructorTuple, sinfo, trgt);
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = @[${this.args.map((arg) => arg.stringify()).join(", ")}]`;
    }
}

class MIRConstructorRecord extends MIRValueOp {
    args: [string, MIRArgument][];

    constructor(sinfo: SourceInfo, args: [string, MIRArgument][], trgt: MIRTempRegister) {
        super(MIROpTag.ConstructorRecord, sinfo, trgt);
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper(this.args.map((tv) => tv[1])); }

    stringify(): string {
        return `${this.trgt.stringify()} = @{${this.args.map((arg) => `${arg[0]}=${arg[1].stringify()}`).join(", ")}}`;
    }
}

class MIRConstructorLambda extends MIRValueOp {
    readonly lkey: MIRLambdaKey;
    readonly lsigkey: MIRResolvedTypeKey;
    captured: Map<string, MIRRegisterArgument>;

    constructor(sinfo: SourceInfo, lkey: MIRLambdaKey, lsigkey: MIRResolvedTypeKey, captured: Map<string, MIRRegisterArgument>, trgt: MIRTempRegister) {
        super(MIROpTag.ConstructorLambda, sinfo, trgt);
        this.lkey = lkey;
        this.lsigkey = lsigkey;
        this.captured = captured;
    }

    getUsedVars(): MIRRegisterArgument[] {
        let margs: MIRRegisterArgument[] = [];
        this.captured.forEach((v) => margs.push(v));

        return margs;
    }

    stringify(): string {
        return `${this.trgt.stringify()} = fn(${this.lkey})`;
    }
}

class MIRCallNamespaceFunction extends MIRValueOp {
    readonly fkey: MIRFunctionKey;
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, fkey: MIRFunctionKey, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.CallNamespaceFunction, sinfo, trgt);
        this.fkey = fkey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.fkey}(${this.args.map((arg) => arg.stringify()).join(", ")})`;
    }
}

class MIRCallStaticFunction extends MIRValueOp {
    readonly skey: MIRStaticKey;
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, skey: MIRStaticKey, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.CallStaticFunction, sinfo, trgt);
        this.skey = skey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.skey}(${this.args.map((arg) => arg.stringify()).join(", ")})`;
    }
}

class MIRAccessFromIndex extends MIRValueOp {
    arg: MIRArgument;
    readonly idx: number;

    constructor(sinfo: SourceInfo, arg: MIRArgument, idx: number, trgt: MIRTempRegister) {
        super(MIROpTag.MIRAccessFromIndex, sinfo, trgt);
        this.arg = arg;
        this.idx = idx;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}[${this.idx}]`;
    }
}

class MIRProjectFromIndecies extends MIRValueOp {
    arg: MIRArgument;
    readonly indecies: number[];

    constructor(sinfo: SourceInfo, arg: MIRArgument, indecies: number[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRProjectFromIndecies, sinfo, trgt);
        this.arg = arg;
        this.indecies = indecies;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}@[${this.indecies.map((i) => i.toString()).join(", ")}]`;
    }
}

class MIRAccessFromProperty extends MIRValueOp {
    arg: MIRArgument;
    readonly property: string;

    constructor(sinfo: SourceInfo, arg: MIRArgument, property: string, trgt: MIRTempRegister) {
        super(MIROpTag.MIRAccessFromProperty, sinfo, trgt);
        this.arg = arg;
        this.property = property;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.${this.property}`;
    }
}

class MIRProjectFromProperties extends MIRValueOp {
    arg: MIRArgument;
    readonly properties: string[];

    constructor(sinfo: SourceInfo, arg: MIRArgument, properties: string[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRProjectFromProperties, sinfo, trgt);
        this.arg = arg;
        this.properties = properties;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}@{${this.properties.join(", ")}}`;
    }
}

class MIRAccessFromField extends MIRValueOp {
    arg: MIRArgument;
    readonly field: string;

    constructor(sinfo: SourceInfo, arg: MIRArgument, field: string, trgt: MIRTempRegister) {
        super(MIROpTag.MIRAccessFromField, sinfo, trgt);
        this.arg = arg;
        this.field = field;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.${this.field}`;
    }
}

class MIRProjectFromFields extends MIRValueOp {
    arg: MIRArgument;
    readonly fields: string[];

    constructor(sinfo: SourceInfo, arg: MIRArgument, fields: string[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRProjectFromFields, sinfo, trgt);
        this.arg = arg;
        this.fields = fields;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}@{${this.fields.join(", ")}}`;
    }
}

class MIRProjectFromTypeTuple extends MIRValueOp {
    arg: MIRArgument;
    readonly ptype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, arg: MIRArgument, ptype: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRProjectFromTypeTuple, sinfo, trgt);
        this.arg = arg;
        this.ptype = ptype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}#${this.ptype}`;
    }
}

class MIRProjectFromTypeRecord extends MIRValueOp {
    arg: MIRArgument;
    readonly ptype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, arg: MIRArgument, ptype: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRProjectFromTypeRecord, sinfo, trgt);
        this.arg = arg;
        this.ptype = ptype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}#${this.ptype}`;
    }
}

class MIRProjectFromTypeConcept extends MIRValueOp {
    arg: MIRArgument;
    readonly ctypes: MIRTypeKey[];

    constructor(sinfo: SourceInfo, arg: MIRArgument, ctypes: MIRTypeKey[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRProjectFromTypeConcept, sinfo, trgt);
        this.arg = arg;
        this.ctypes = ctypes;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}#${this.ctypes.join("&")}`;
    }
}

class MIRModifyWithIndecies extends MIRValueOp {
    arg: MIRArgument;
    updates: [number, MIRArgument][];

    constructor(sinfo: SourceInfo, arg: MIRArgument, updates: [number, MIRArgument][], trgt: MIRTempRegister) {
        super(MIROpTag.MIRModifyWithIndecies, sinfo, trgt);
        this.arg = arg;
        this.updates = updates;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg, ...this.updates.map((u) => u[1])]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}<~${this.updates.map((u) => `${u[0]}=${u[1].stringify()}`).join(", ")}]`;
    }
}

class MIRModifyWithProperties extends MIRValueOp {
    arg: MIRArgument;
    updates: [string, MIRArgument][];

    constructor(sinfo: SourceInfo, arg: MIRArgument, updates: [string, MIRArgument][], trgt: MIRTempRegister) {
        super(MIROpTag.MIRModifyWithProperties, sinfo, trgt);
        this.arg = arg;
        this.updates = updates;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg, ...this.updates.map((u) => u[1])]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}<~${this.updates.map((u) => `${u[0]}=${u[1].stringify()}`).join(", ")}]`;
    }
}

class MIRModifyWithFields extends MIRValueOp {
    arg: MIRArgument;
    updates: [string, MIRArgument][];

    constructor(sinfo: SourceInfo, arg: MIRArgument, updates: [string, MIRArgument][], trgt: MIRTempRegister) {
        super(MIROpTag.MIRModifyWithFields, sinfo, trgt);
        this.arg = arg;
        this.updates = updates;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg, ...this.updates.map((u) => u[1])]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}<~${this.updates.map((u) => `${u[0]}=${u[1].stringify()}`).join(", ")}]`;
    }
}

class MIRStructuredExtendTuple extends MIRValueOp {
    arg: MIRArgument;
    update: MIRArgument;

    constructor(sinfo: SourceInfo, arg: MIRArgument, update: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRStructuredExtendTuple, sinfo, trgt);
        this.arg = arg;
        this.update = update;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg, this.update]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}<+(${this.update.stringify()})`;
    }
}

class MIRStructuredExtendRecord extends MIRValueOp {
    arg: MIRArgument;
    update: MIRArgument;

    constructor(sinfo: SourceInfo, arg: MIRArgument, update: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRStructuredExtendRecord, sinfo, trgt);
        this.arg = arg;
        this.update = update;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg, this.update]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}<+(${this.update.stringify()})`;
    }
}

class MIRStructuredExtendObject extends MIRValueOp {
    arg: MIRArgument;
    update: MIRArgument;

    constructor(sinfo: SourceInfo, arg: MIRArgument, update: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRStructuredExtendObject, sinfo, trgt);
        this.arg = arg;
        this.update = update;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg, this.update]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}<+(${this.update.stringify()})`;
    }
}

class MIRInvokeKnownTarget extends MIRValueOp {
    readonly mkey: MIRMethodKey;
    args: MIRArgument[]; //this is args[0]

    constructor(sinfo: SourceInfo, mkey: MIRMethodKey, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRInvokeKnownTarget, sinfo, trgt);
        this.mkey = mkey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.args[0].stringify()}->::${this.mkey}::(${[...this.args].slice(1).map((arg) => arg.stringify()).join(", ")})`;
    }
}

class MIRInvokeVirtualTarget extends MIRValueOp {
    readonly vresolve: MIRVirtualMethodKey;
    args: MIRArgument[]; //this is args[0]

    constructor(sinfo: SourceInfo, vresolve: MIRVirtualMethodKey, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRInvokeVirtualTarget, sinfo, trgt);
        this.vresolve = vresolve;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.args[0].stringify()}->${this.vresolve}(${[...this.args].slice(1).map((arg) => arg.stringify()).join(", ")})`;
    }
}

class MIRCallLambda extends MIRValueOp {
    lambda: MIRArgument;
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, lambda: MIRArgument, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRCallLambda, sinfo, trgt);
        this.lambda = lambda;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.lambda, ...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.lambda.stringify()}(${this.args.map((arg) => arg.stringify()).join(", ")})`;
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
}

class MIRBinEq extends MIRValueOp {
    lhs: MIRArgument;
    readonly op: string; //==, !=
    rhs: MIRArgument;

    constructor(sinfo: SourceInfo, lhs: MIRArgument, op: string, rhs: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRBinEq, sinfo, trgt);
        this.lhs = lhs;
        this.op = op;
        this.rhs = rhs;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.lhs, this.rhs]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.lhs.stringify()}${this.op}${this.rhs.stringify()}`;
    }
}

class MIRBinCmp extends MIRValueOp {
    lhs: MIRArgument;
    readonly op: string; //<, >, <=, >=
    rhs: MIRArgument;

    constructor(sinfo: SourceInfo, lhs: MIRArgument, op: string, rhs: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRBinCmp, sinfo, trgt);
        this.lhs = lhs;
        this.op = op;
        this.rhs = rhs;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.lhs, this.rhs]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.lhs.stringify()}${this.op}${this.rhs.stringify()}`;
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
}

class MIRIsTypeOf extends MIRValueOp {
    arg: MIRArgument;
    readonly oftype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, arg: MIRArgument, oftype: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRIsTypeOf, sinfo, trgt);
        this.arg = arg;
        this.oftype = oftype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = $isTypeOf(${this.arg.stringify()}, ${this.oftype})`;
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
}

class MIRVarStore extends MIRFlowOp {
    src: MIRArgument;
    name: MIRVarLocal;

    constructor(sinfo: SourceInfo, src: MIRArgument, name: MIRVarLocal) {
        super(MIROpTag.MIRVarStore, sinfo);
        this.src = src;
        this.name = name;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.src]); }
    getModVars(): MIRRegisterArgument[] { return [this.name]; }

    stringify(): string {
        return `${this.name.stringify()} = ${this.src.stringify()}`;
    }
}

class MIRReturnAssign extends MIRFlowOp {
    src: MIRArgument;
    name: MIRVarLocal;

    constructor(sinfo: SourceInfo, src: MIRArgument) {
        super(MIROpTag.MIRReturnAssign, sinfo);
        this.src = src;
        this.name = new MIRVarLocal("_ir_ret_");
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.src]); }
    getModVars(): MIRRegisterArgument[] { return [this.name]; }

    stringify(): string {
        return `${this.name.stringify()} = ${this.src.stringify()}`;
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
}

class MIRPhi extends MIRFlowOp {
    src: Map<string, MIRRegisterArgument>;
    trgt: MIRTempRegister | MIRVarLocal;

    constructor(sinfo: SourceInfo, src: Map<string, MIRRegisterArgument>, trgt: MIRTempRegister | MIRVarLocal) {
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
}

class MIRBody {
    readonly file: string;
    readonly sinfo: SourceInfo;

    body: string | Map<string, MIRBasicBlock>;

    constructor(file: string, sinfo: SourceInfo, body: string | Map<string, MIRBasicBlock>) {
        this.file = file;
        this.sinfo = sinfo;
        this.body = body;
    }

    jsonify(): any {
        if (typeof (this.body) === "string") {
            return this.body;
        }
        else {
            let blocks: any[] = [];
            topologicalOrder(this.body).forEach((v, k) => blocks.push(v.jsonify()));

            return blocks;
        }
    }

    dgmlify(siginfo: string): string {
        if (typeof (this.body) === "string") {
            return this.body;
        }
        else {
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
    }
}

export {
    MIRTypeKey, MIRGlobalKey, MIRConstKey, MIRFieldKey, MIRLambdaKey, MIRFunctionKey, MIRStaticKey, MIRMethodKey, MIRResolvedTypeKey, MIRVirtualMethodKey,
    MIRArgument, MIRRegisterArgument, MIRTempRegister, MIRVarCaptured, MIRVarParameter, MIRVarLocal, MIRConstantArgument, MIRConstantNone, MIRConstantTrue, MIRConstantFalse, MIRConstantInt, MIRConstantString,
    MIROpTag, MIROp, MIRValueOp, MIRFlowOp, MIRJumpOp,
    MIRLoadConst, MIRLoadConstTypedString,
    MIRAccessNamespaceConstant, MIRAccessConstField, MIRLoadFieldDefaultValue, MIRAccessCapturedVariable, MIRAccessArgVariable, MIRAccessLocalVariable,
    MIRConstructorPrimary, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionSingletons, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionMixed, MIRConstructorTuple, MIRConstructorRecord, MIRConstructorLambda,
    MIRCallNamespaceFunction, MIRCallStaticFunction,
    MIRAccessFromIndex, MIRProjectFromIndecies, MIRAccessFromProperty, MIRProjectFromProperties, MIRAccessFromField, MIRProjectFromFields, MIRProjectFromTypeTuple, MIRProjectFromTypeRecord, MIRProjectFromTypeConcept, MIRModifyWithIndecies, MIRModifyWithProperties, MIRModifyWithFields, MIRStructuredExtendTuple, MIRStructuredExtendRecord, MIRStructuredExtendObject, MIRInvokeKnownTarget, MIRInvokeVirtualTarget, MIRCallLambda,
    MIRPrefixOp, MIRBinOp, MIRBinEq, MIRBinCmp,
    MIRIsTypeOfNone, MIRIsTypeOfSome, MIRIsTypeOf,
    MIRRegAssign, MIRTruthyConvert, MIRLogicStore, MIRVarStore, MIRReturnAssign,
    MIRAbort, MIRDebug,
    MIRJump, MIRJumpCond, MIRJumpNone,
    MIRPhi,
    MIRVarLifetimeStart, MIRVarLifetimeEnd,
    MIRBasicBlock, MIRBody
};
