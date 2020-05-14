"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const parser_1 = require("../ast/parser");
const mir_info_1 = require("./mir_info");
const assert = require("assert");
//
//Probably want to declare a MIRSourceInfo class
//
function jemitsinfo(sinfo) {
    return { line: sinfo.line, column: sinfo.column, pos: sinfo.pos, span: sinfo.span };
}
function jparsesinfo(jobj) {
    return new parser_1.SourceInfo(jobj.line, jobj.column, jobj.pos, jobj.span);
}
class MIRArgument {
    constructor(nameID) {
        this.nameID = nameID;
    }
    static jparse(jobj) {
        if (jobj === null) {
            return new MIRConstantNone();
        }
        else if (jobj === true || jobj === false) {
            return jobj ? new MIRConstantTrue() : new MIRConstantFalse();
        }
        else {
            if (typeof (jobj) === "string") {
                if (jobj.endsWith("n")) {
                    return new MIRConstantBigInt(jobj);
                }
                else if (jobj.includes(".")) {
                    return new MIRConstantFloat64(jobj);
                }
                else {
                    return new MIRConstantInt(jobj);
                }
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
exports.MIRArgument = MIRArgument;
class MIRRegisterArgument extends MIRArgument {
    constructor(nameID) {
        super(nameID);
    }
    stringify() {
        return this.nameID;
    }
}
exports.MIRRegisterArgument = MIRRegisterArgument;
class MIRTempRegister extends MIRRegisterArgument {
    constructor(regID, forcename) {
        super(forcename || `#tmp_${regID}`);
        this.regID = regID;
    }
    jemit() {
        return { tag: "temp", regID: this.regID, nameID: this.nameID };
    }
    static jparse(jobj) {
        return new MIRTempRegister(jobj.regID, jobj.nameID);
    }
}
exports.MIRTempRegister = MIRTempRegister;
class MIRVariable extends MIRRegisterArgument {
    constructor(name, forcename) {
        super(forcename || name);
        this.lname = name;
    }
    jemit() {
        return { tag: "var", lname: this.lname, nameID: this.nameID };
    }
    static jparse(jobj) {
        return new MIRVariable(jobj.lname, jobj.nameID);
    }
}
exports.MIRVariable = MIRVariable;
class MIRConstantArgument extends MIRArgument {
    constructor(name) {
        super(name);
    }
}
exports.MIRConstantArgument = MIRConstantArgument;
class MIRConstantNone extends MIRConstantArgument {
    constructor() {
        super("=none=");
    }
    stringify() {
        return "none";
    }
    jemit() {
        return null;
    }
}
exports.MIRConstantNone = MIRConstantNone;
class MIRConstantTrue extends MIRConstantArgument {
    constructor() {
        super("=true=");
    }
    stringify() {
        return "true";
    }
    jemit() {
        return true;
    }
}
exports.MIRConstantTrue = MIRConstantTrue;
class MIRConstantFalse extends MIRConstantArgument {
    constructor() {
        super("=false=");
    }
    stringify() {
        return "false";
    }
    jemit() {
        return false;
    }
}
exports.MIRConstantFalse = MIRConstantFalse;
class MIRConstantInt extends MIRConstantArgument {
    constructor(value) {
        super(`=int=${value}`);
        this.value = value;
    }
    stringify() {
        return this.value;
    }
    jemit() {
        return this.value;
    }
}
exports.MIRConstantInt = MIRConstantInt;
class MIRConstantBigInt extends MIRConstantArgument {
    constructor(value) {
        super(`=bigint=${value}`);
        this.value = value;
    }
    digits() {
        return this.value.slice(0, this.value.length - 1);
    }
    stringify() {
        return this.value;
    }
    jemit() {
        return this.value;
    }
}
exports.MIRConstantBigInt = MIRConstantBigInt;
class MIRConstantFloat64 extends MIRConstantArgument {
    constructor(value) {
        super(`=float64=${value}`);
        this.value = value;
    }
    digits() {
        return this.value.slice(0, this.value.length - 1);
    }
    stringify() {
        return this.value;
    }
    jemit() {
        return this.value;
    }
}
exports.MIRConstantFloat64 = MIRConstantFloat64;
class MIRConstantString extends MIRConstantArgument {
    constructor(value) {
        super(`=string=${value}`);
        this.value = value;
    }
    stringify() {
        return this.value;
    }
    jemit() {
        return [this.value];
    }
}
exports.MIRConstantString = MIRConstantString;
var MIROpTag;
(function (MIROpTag) {
    MIROpTag["MIRLoadConst"] = "MIRLoadConst";
    MIROpTag["MIRLoadConstRegex"] = "MIRLoadConstRegex";
    MIROpTag["MIRLoadConstSafeString"] = "MIRLoadConstSafeString";
    MIROpTag["MIRLoadConstTypedString"] = "MIRLoadConstTypedString";
    MIROpTag["MIRAccessConstantValue"] = "MIRAccessConstantValue";
    MIROpTag["MIRLoadFieldDefaultValue"] = "MIRLoadFieldDefaultValue";
    MIROpTag["MIRAccessArgVariable"] = "MIRAccessArgVariable";
    MIROpTag["MIRAccessLocalVariable"] = "MIRAccessLocalVariable";
    MIROpTag["MIRInvokeInvariantCheckDirect"] = "MIRInvokeInvariantCheckDirect";
    MIROpTag["MIRInvokeInvariantCheckVirtualTarget"] = "MIRInvokeInvariantCheckVirtualTarget";
    MIROpTag["MIRConstructorPrimary"] = "MIRConstructorPrimary";
    MIROpTag["MIRConstructorPrimaryCollectionEmpty"] = "MIRConstructorPrimaryCollectionEmpty";
    MIROpTag["MIRConstructorPrimaryCollectionSingletons"] = "MIRConstructorPrimaryCollectionSingletons";
    MIROpTag["MIRConstructorPrimaryCollectionCopies"] = "MIRConstructorPrimaryCollectionCopies";
    MIROpTag["MIRConstructorPrimaryCollectionMixed"] = "MIRConstructorPrimaryCollectionMixed";
    MIROpTag["MIRConstructorTuple"] = "MIRConstructorTuple";
    MIROpTag["MIRConstructorRecord"] = "MIRConstructorRecord";
    MIROpTag["MIRConstructorEphemeralValueList"] = "MIRConstructorEphemeralValueList";
    MIROpTag["MIRAccessFromIndex"] = "MIRAccessFromIndex";
    MIROpTag["MIRProjectFromIndecies"] = "MIRProjectFromIndecies";
    MIROpTag["MIRAccessFromProperty"] = "MIRAccessFromProperty";
    MIROpTag["MIRProjectFromProperties"] = "MIRProjectFromProperties";
    MIROpTag["MIRAccessFromField"] = "MIRAccessFromField";
    MIROpTag["MIRProjectFromFields"] = "MIRProjectFromFields";
    MIROpTag["MIRProjectFromTypeTuple"] = "MIRProjectFromTypeTuple";
    MIROpTag["MIRProjectFromTypeRecord"] = "MIRProjectFromTypeRecord";
    MIROpTag["MIRProjectFromTypeNominal"] = "MIRProjectFromTypeNominal";
    MIROpTag["MIRModifyWithIndecies"] = "MIRModifyWithIndecies";
    MIROpTag["MIRModifyWithProperties"] = "MIRModifyWithProperties";
    MIROpTag["MIRModifyWithFields"] = "MIRModifyWithFields";
    MIROpTag["MIRStructuredExtendTuple"] = "MIRStructuredExtendTuple";
    MIROpTag["MIRStructuredExtendRecord"] = "MIRStructuredExtendRecord";
    MIROpTag["MIRStructuredExtendObject"] = "MIRStructuredExtendObject";
    MIROpTag["MIRLoadFromEpehmeralList"] = "MIRLoadFromEpehmeralList";
    MIROpTag["MIRInvokeFixedFunction"] = "MIRInvokeFixedFunction";
    MIROpTag["MIRInvokeVirtualTarget"] = "MIRInvokeVirtualTarget";
    MIROpTag["MIRPrefixOp"] = "MIRPrefixOp";
    MIROpTag["MIRBinOp"] = "MIRBinOp";
    MIROpTag["MIRBinEq"] = "MIRBinEq";
    MIROpTag["MIRBinLess"] = "MIRBinLess";
    MIROpTag["MIRBinCmp"] = "MIRBinCmp";
    MIROpTag["MIRIsTypeOfNone"] = "MIRIsTypeOfNone";
    MIROpTag["MIRIsTypeOfSome"] = "MIRIsTypeOfSome";
    MIROpTag["MIRIsTypeOf"] = "MIRIsTypeOf";
    MIROpTag["MIRRegAssign"] = "MIRRegAssign";
    MIROpTag["MIRTruthyConvert"] = "MIRTruthyConvert";
    MIROpTag["MIRVarStore"] = "MIRVarStore";
    MIROpTag["MIRPackSlice"] = "MIRPackSlice";
    MIROpTag["MIRPackExtend"] = "MIRPackExtend";
    MIROpTag["MIRReturnAssign"] = "MIRReturnAssign";
    MIROpTag["MIRAbort"] = "MIRAbort";
    MIROpTag["MIRDebug"] = "MIRDebug";
    MIROpTag["MIRJump"] = "MIRJump";
    MIROpTag["MIRJumpCond"] = "MIRJumpCond";
    MIROpTag["MIRJumpNone"] = "MIRJumpNone";
    MIROpTag["MIRPhi"] = "MIRPhi";
    MIROpTag["MIRVarLifetimeStart"] = "MIRVarLifetimeStart";
    MIROpTag["MIRVarLifetimeEnd"] = "MIRVarLifetimeEnd";
})(MIROpTag || (MIROpTag = {}));
exports.MIROpTag = MIROpTag;
function varsOnlyHelper(args) {
    return args.filter((arg) => arg instanceof MIRRegisterArgument);
}
class MIROp {
    constructor(tag, sinfo) {
        this.tag = tag;
        this.sinfo = sinfo;
    }
    jbemit() {
        return { tag: this.tag, sinfo: jemitsinfo(this.sinfo) };
    }
    static jparse(jobj) {
        switch (jobj.tag) {
            case MIROpTag.MIRLoadConst:
                return MIRLoadConst.jparse(jobj);
            case MIROpTag.MIRLoadConstRegex:
                return MIRLoadConstRegex.jparse(jobj);
            case MIROpTag.MIRLoadConstSafeString:
                return MIRLoadConstSafeString.jparse(jobj);
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
            case MIROpTag.MIRInvokeInvariantCheckDirect:
                return MIRInvokeInvariantCheckDirect.jparse(jobj);
            case MIROpTag.MIRInvokeInvariantCheckVirtualTarget:
                return MIRInvokeInvariantCheckVirtualTarget.jparse(jobj);
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
            case MIROpTag.MIRConstructorEphemeralValueList:
                return MIRConstructorEphemeralValueList.jparse(jobj);
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
            case MIROpTag.MIRProjectFromTypeNominal:
                return MIRProjectFromTypeNominal.jparse(jobj);
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
            case MIROpTag.MIRLoadFromEpehmeralList:
                return MIRLoadFromEpehmeralList.jparse(jobj);
            case MIROpTag.MIRInvokeFixedFunction:
                return MIRInvokeFixedFunction.jparse(jobj);
            case MIROpTag.MIRInvokeVirtualTarget:
                return MIRInvokeVirtualFunction.jparse(jobj);
            case MIROpTag.MIRPrefixOp:
                return MIRPrefixOp.jparse(jobj);
            case MIROpTag.MIRBinOp:
                return MIRBinOp.jparse(jobj);
            case MIROpTag.MIRBinEq:
                return MIRBinEq.jparse(jobj);
            case MIROpTag.MIRBinLess:
                return MIRBinLess.jparse(jobj);
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
            case MIROpTag.MIRVarStore:
                return MIRVarStore.jparse(jobj);
            case MIROpTag.MIRPackSlice:
                return MIRPackSlice.jparse(jobj);
            case MIROpTag.MIRPackExtend:
                return MIRPackExtend.jparse(jobj);
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
exports.MIROp = MIROp;
class MIRValueOp extends MIROp {
    constructor(tag, sinfo, trgt) {
        super(tag, sinfo);
        this.trgt = trgt;
    }
    getModVars() { return [this.trgt]; }
    jbemit() {
        return Object.assign(Object.assign({}, super.jbemit()), { trgt: this.trgt.jemit() });
    }
}
exports.MIRValueOp = MIRValueOp;
class MIRFlowOp extends MIROp {
    constructor(tag, sinfo) {
        super(tag, sinfo);
    }
}
exports.MIRFlowOp = MIRFlowOp;
class MIRJumpOp extends MIROp {
    constructor(tag, sinfo) {
        super(tag, sinfo);
    }
}
exports.MIRJumpOp = MIRJumpOp;
class MIRLoadConst extends MIRValueOp {
    constructor(sinfo, src, trgt) {
        super(MIROpTag.MIRLoadConst, sinfo, trgt);
        this.src = src;
    }
    getUsedVars() { return []; }
    stringify() {
        return `${this.trgt.stringify()} = ${this.src.stringify()}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { src: this.src.jemit() });
    }
    static jparse(jobj) {
        return new MIRLoadConst(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRLoadConst = MIRLoadConst;
class MIRLoadConstRegex extends MIRValueOp {
    constructor(sinfo, restr, trgt) {
        super(MIROpTag.MIRLoadConstRegex, sinfo, trgt);
        this.restr = restr;
    }
    getUsedVars() { return []; }
    stringify() {
        return `${this.trgt.stringify()} = /${this.restr}/`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { src: this.restr });
    }
    static jparse(jobj) {
        return new MIRLoadConstRegex(jparsesinfo(jobj.sinfo), jobj.restr, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRLoadConstRegex = MIRLoadConstRegex;
class MIRLoadConstSafeString extends MIRValueOp {
    constructor(sinfo, ivalue, tkey, tskey, trgt) {
        super(MIROpTag.MIRLoadConstSafeString, sinfo, trgt);
        this.ivalue = ivalue;
        this.tkey = tkey;
        this.tskey = tskey;
    }
    getUsedVars() { return []; }
    stringify() {
        return `${this.trgt.stringify()} = ${this.ivalue}#${this.tkey}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { ivalue: this.ivalue, tkey: this.tkey, tskey: this.tskey });
    }
    static jparse(jobj) {
        return new MIRLoadConstSafeString(jparsesinfo(jobj.sinfo), jobj.ivalue, jobj.tkey, jobj.tskey, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRLoadConstSafeString = MIRLoadConstSafeString;
class MIRLoadConstTypedString extends MIRValueOp {
    constructor(sinfo, ivalue, tkey, tskey, pfunckey, errtype, trgt) {
        super(MIROpTag.MIRLoadConstTypedString, sinfo, trgt);
        this.ivalue = ivalue;
        this.tkey = tkey;
        this.tskey = tskey;
        this.pfunckey = pfunckey;
        this.errtype = errtype;
    }
    getUsedVars() { return []; }
    stringify() {
        return `${this.trgt.stringify()} = ${this.ivalue}#${this.tkey}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { ivalue: this.ivalue, tkey: this.tkey, tskey: this.tskey, pfunckey: this.pfunckey, errtype: this.errtype });
    }
    static jparse(jobj) {
        return new MIRLoadConstTypedString(jparsesinfo(jobj.sinfo), jobj.ivalue, jobj.tkey, jobj.tskey, jobj.pfunckey, jobj.errtype, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRLoadConstTypedString = MIRLoadConstTypedString;
class MIRAccessConstantValue extends MIRValueOp {
    constructor(sinfo, ckey, trgt) {
        super(MIROpTag.MIRAccessConstantValue, sinfo, trgt);
        this.ckey = ckey;
    }
    getUsedVars() { return []; }
    stringify() {
        return `${this.trgt.stringify()} = ${this.ckey}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { ckey: this.ckey });
    }
    static jparse(jobj) {
        return new MIRAccessConstantValue(jparsesinfo(jobj.sinfo), jobj.ckey, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRAccessConstantValue = MIRAccessConstantValue;
class MIRLoadFieldDefaultValue extends MIRValueOp {
    constructor(sinfo, fkey, trgt) {
        super(MIROpTag.MIRLoadFieldDefaultValue, sinfo, trgt);
        this.fkey = fkey;
    }
    getUsedVars() { return []; }
    stringify() {
        return `${this.trgt.stringify()} = default(${this.fkey})`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { fkey: this.fkey });
    }
    static jparse(jobj) {
        return new MIRLoadFieldDefaultValue(jparsesinfo(jobj.sinfo), jobj.fkey, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRLoadFieldDefaultValue = MIRLoadFieldDefaultValue;
class MIRAccessArgVariable extends MIRValueOp {
    constructor(sinfo, name, trgt) {
        super(MIROpTag.MIRAccessArgVariable, sinfo, trgt);
        this.name = name;
    }
    getUsedVars() { return [this.name]; }
    stringify() {
        return `${this.trgt.stringify()} = ${this.name.stringify()}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { name: this.name.jemit() });
    }
    static jparse(jobj) {
        return new MIRAccessArgVariable(jparsesinfo(jobj.sinfo), MIRVariable.jparse(jobj.name), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRAccessArgVariable = MIRAccessArgVariable;
class MIRAccessLocalVariable extends MIRValueOp {
    constructor(sinfo, name, trgt) {
        super(MIROpTag.MIRAccessLocalVariable, sinfo, trgt);
        this.name = name;
    }
    getUsedVars() { return [this.name]; }
    stringify() {
        return `${this.trgt.stringify()} = ${this.name.stringify()}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { name: this.name.jemit() });
    }
    static jparse(jobj) {
        return new MIRAccessLocalVariable(jparsesinfo(jobj.sinfo), MIRVariable.jparse(jobj.name), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRAccessLocalVariable = MIRAccessLocalVariable;
class MIRInvokeInvariantCheckDirect extends MIRValueOp {
    constructor(sinfo, ikey, tkey, rcvr, trgt) {
        super(MIROpTag.MIRInvokeInvariantCheckDirect, sinfo, trgt);
        this.ikey = ikey;
        this.tkey = tkey;
        this.rcvr = rcvr;
    }
    getUsedVars() { return varsOnlyHelper([this.rcvr]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.ikey}(${this.rcvr})`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { ikey: this.ikey, tkey: this.tkey, rcvr: this.rcvr.jemit() });
    }
    static jparse(jobj) {
        return new MIRInvokeInvariantCheckDirect(jparsesinfo(jobj.sinfo), jobj.ikey, jobj.tkey, MIRArgument.jparse(jobj.rcvr), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRInvokeInvariantCheckDirect = MIRInvokeInvariantCheckDirect;
class MIRInvokeInvariantCheckVirtualTarget extends MIRValueOp {
    constructor(sinfo, infertype, rcvr, trgt) {
        super(MIROpTag.MIRInvokeInvariantCheckVirtualTarget, sinfo, trgt);
        this.infertype = infertype;
        this.rcvr = rcvr;
    }
    getUsedVars() { return varsOnlyHelper([this.rcvr]); }
    stringify() {
        return `${this.trgt.stringify()} = @@invariant(${this.rcvr})`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { infertype: this.infertype, rcvr: this.rcvr.jemit() });
    }
    static jparse(jobj) {
        return new MIRInvokeInvariantCheckVirtualTarget(jparsesinfo(jobj.sinfo), jobj.infertype, MIRArgument.jparse(jobj.rcvr), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRInvokeInvariantCheckVirtualTarget = MIRInvokeInvariantCheckVirtualTarget;
class MIRConstructorPrimary extends MIRValueOp {
    constructor(sinfo, tkey, args, trgt) {
        super(MIROpTag.MIRConstructorPrimary, sinfo, trgt);
        this.tkey = tkey;
        this.args = args;
    }
    getUsedVars() { return varsOnlyHelper([...this.args]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.tkey}@(${this.args.map((arg) => arg.stringify()).join(", ")})`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { tkey: this.tkey, args: this.args.map((arg) => arg.jemit()) });
    }
    static jparse(jobj) {
        return new MIRConstructorPrimary(jparsesinfo(jobj.sinfo), jobj.tkey, jobj.args.map((jarg) => MIRArgument.jparse(jarg)), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRConstructorPrimary = MIRConstructorPrimary;
class MIRConstructorPrimaryCollectionEmpty extends MIRValueOp {
    constructor(sinfo, tkey, trgt) {
        super(MIROpTag.MIRConstructorPrimaryCollectionEmpty, sinfo, trgt);
        this.tkey = tkey;
    }
    getUsedVars() { return []; }
    stringify() {
        return `${this.trgt.stringify()} = ${this.tkey}{}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { tkey: this.tkey });
    }
    static jparse(jobj) {
        return new MIRConstructorPrimaryCollectionEmpty(jparsesinfo(jobj.sinfo), jobj.tkey, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRConstructorPrimaryCollectionEmpty = MIRConstructorPrimaryCollectionEmpty;
class MIRConstructorPrimaryCollectionSingletons extends MIRValueOp {
    constructor(sinfo, tkey, args, trgt) {
        super(MIROpTag.MIRConstructorPrimaryCollectionSingletons, sinfo, trgt);
        this.tkey = tkey;
        this.args = args;
    }
    getUsedVars() { return varsOnlyHelper([...this.args]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.tkey}{${this.args.map((arg) => arg.stringify()).join(", ")}}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { tkey: this.tkey, args: this.args.map((arg) => arg.jemit()) });
    }
    static jparse(jobj) {
        return new MIRConstructorPrimaryCollectionSingletons(jparsesinfo(jobj.sinfo), jobj.tkey, jobj.args.map((jarg) => MIRArgument.jparse(jarg)), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRConstructorPrimaryCollectionSingletons = MIRConstructorPrimaryCollectionSingletons;
class MIRConstructorPrimaryCollectionCopies extends MIRValueOp {
    constructor(sinfo, tkey, args, trgt) {
        super(MIROpTag.MIRConstructorPrimaryCollectionCopies, sinfo, trgt);
        this.tkey = tkey;
        this.args = args;
    }
    getUsedVars() { return varsOnlyHelper([...this.args]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.tkey}{${this.args.map((arg) => `expand(${arg.stringify()})`).join(", ")}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { tkey: this.tkey, args: this.args.map((arg) => arg.jemit()) });
    }
    static jparse(jobj) {
        return new MIRConstructorPrimaryCollectionCopies(jparsesinfo(jobj.sinfo), jobj.tkey, jobj.args.map((jarg) => MIRArgument.jparse(jarg)), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRConstructorPrimaryCollectionCopies = MIRConstructorPrimaryCollectionCopies;
class MIRConstructorPrimaryCollectionMixed extends MIRValueOp {
    constructor(sinfo, tkey, args, trgt) {
        super(MIROpTag.MIRConstructorPrimaryCollectionMixed, sinfo, trgt);
        this.tkey = tkey;
        this.args = args;
    }
    getUsedVars() { return varsOnlyHelper(this.args.map((tv) => tv[1])); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.tkey}{${this.args.map((arg) => arg[0] ? `expand(${arg[1].stringify()})` : arg[1].stringify()).join(", ")}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { tkey: this.tkey, args: this.args.map((arg) => [arg[0], arg[1].jemit()]) });
    }
    static jparse(jobj) {
        return new MIRConstructorPrimaryCollectionMixed(jparsesinfo(jobj.sinfo), jobj.tkey, jobj.args.map((jarg) => [jarg[0], MIRArgument.jparse(jarg[1])]), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRConstructorPrimaryCollectionMixed = MIRConstructorPrimaryCollectionMixed;
class MIRConstructorTuple extends MIRValueOp {
    constructor(sinfo, resultTupleType, args, trgt) {
        super(MIROpTag.MIRConstructorTuple, sinfo, trgt);
        this.resultTupleType = resultTupleType;
        this.args = args;
    }
    getUsedVars() { return varsOnlyHelper([...this.args]); }
    stringify() {
        return `${this.trgt.stringify()} = [${this.args.map((arg) => arg.stringify()).join(", ")}]`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultTupleType: this.resultTupleType, args: this.args.map((arg) => arg.jemit()) });
    }
    static jparse(jobj) {
        return new MIRConstructorTuple(jparsesinfo(jobj.sinfo), jobj.resultTupleType, jobj.args.map((jarg) => MIRArgument.jparse(jarg)), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRConstructorTuple = MIRConstructorTuple;
class MIRConstructorRecord extends MIRValueOp {
    constructor(sinfo, resultRecordType, args, trgt) {
        super(MIROpTag.MIRConstructorRecord, sinfo, trgt);
        this.resultRecordType = resultRecordType;
        this.args = args;
    }
    getUsedVars() { return varsOnlyHelper(this.args.map((tv) => tv[1])); }
    stringify() {
        return `${this.trgt.stringify()} = {${this.args.map((arg) => `${arg[0]}=${arg[1].stringify()}`).join(", ")}}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultRecordType: this.resultRecordType, args: this.args.map((arg) => [arg[0], arg[1].jemit()]) });
    }
    static jparse(jobj) {
        return new MIRConstructorRecord(jparsesinfo(jobj.sinfo), jobj.resultRecordType, jobj.args.map((jarg) => [jarg[0], MIRArgument.jparse(jarg[1])]), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRConstructorRecord = MIRConstructorRecord;
class MIRConstructorEphemeralValueList extends MIRValueOp {
    constructor(sinfo, resultEphemeralListType, args, trgt) {
        super(MIROpTag.MIRConstructorEphemeralValueList, sinfo, trgt);
        this.resultEphemeralListType = resultEphemeralListType;
        this.args = args;
    }
    getUsedVars() { return varsOnlyHelper([...this.args]); }
    stringify() {
        return `${this.trgt.stringify()} = [${this.args.map((arg) => arg.stringify()).join(", ")}]`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultEphemeralListType: this.resultEphemeralListType, args: this.args.map((arg) => arg.jemit()) });
    }
    static jparse(jobj) {
        return new MIRConstructorEphemeralValueList(jparsesinfo(jobj.sinfo), jobj.resultEphemeralListType, jobj.args.map((jarg) => MIRArgument.jparse(jarg)), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRConstructorEphemeralValueList = MIRConstructorEphemeralValueList;
class MIRAccessFromIndex extends MIRValueOp {
    constructor(sinfo, resultAccessType, arg, argInferType, idx, trgt) {
        super(MIROpTag.MIRAccessFromIndex, sinfo, trgt);
        this.resultAccessType = resultAccessType;
        this.arg = arg;
        this.argInferType = argInferType;
        this.idx = idx;
    }
    getUsedVars() { return varsOnlyHelper([this.arg]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}[${this.idx}]`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultAccessType: this.resultAccessType, arg: this.arg.jemit(), argInferType: this.argInferType, idx: this.idx });
    }
    static jparse(jobj) {
        return new MIRAccessFromIndex(jparsesinfo(jobj.sinfo), jobj.resultAccessType, MIRArgument.jparse(jobj.arg), jobj.argInferType, jobj.idx, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRAccessFromIndex = MIRAccessFromIndex;
class MIRProjectFromIndecies extends MIRValueOp {
    constructor(sinfo, resultProjectType, arg, argInferType, indecies, trgt) {
        super(MIROpTag.MIRProjectFromIndecies, sinfo, trgt);
        this.resultProjectType = resultProjectType;
        this.arg = arg;
        this.argInferType = argInferType;
        this.indecies = indecies;
    }
    getUsedVars() { return varsOnlyHelper([this.arg]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}@[${this.indecies.map((i) => i.toString()).join(", ")}]`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultProjectType: this.resultProjectType, arg: this.arg.jemit(), argInferType: this.argInferType, indecies: this.indecies });
    }
    static jparse(jobj) {
        return new MIRProjectFromIndecies(jparsesinfo(jobj.sinfo), jobj.resultProjectType, MIRArgument.jparse(jobj.arg), jobj.argInferType, jobj.indecies, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRProjectFromIndecies = MIRProjectFromIndecies;
class MIRAccessFromProperty extends MIRValueOp {
    constructor(sinfo, resultAccessType, arg, argInferType, property, trgt) {
        super(MIROpTag.MIRAccessFromProperty, sinfo, trgt);
        this.resultAccessType = resultAccessType;
        this.arg = arg;
        this.argInferType = argInferType;
        this.property = property;
    }
    getUsedVars() { return varsOnlyHelper([this.arg]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.${this.property}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultAccessType: this.resultAccessType, arg: this.arg.jemit(), argInferType: this.argInferType, property: this.property });
    }
    static jparse(jobj) {
        return new MIRAccessFromProperty(jparsesinfo(jobj.sinfo), jobj.resultAccessType, MIRArgument.jparse(jobj.arg), jobj.argInferType, jobj.property, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRAccessFromProperty = MIRAccessFromProperty;
class MIRProjectFromProperties extends MIRValueOp {
    constructor(sinfo, resultProjectType, arg, argInferType, properties, trgt) {
        super(MIROpTag.MIRProjectFromProperties, sinfo, trgt);
        this.resultProjectType = resultProjectType;
        this.arg = arg;
        this.argInferType = argInferType;
        this.properties = properties;
    }
    getUsedVars() { return varsOnlyHelper([this.arg]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}{${this.properties.join(", ")}}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultProjectType: this.resultProjectType, arg: this.arg.jemit(), argInferType: this.argInferType, properties: this.properties });
    }
    static jparse(jobj) {
        return new MIRProjectFromProperties(jparsesinfo(jobj.sinfo), jobj.resultProjectType, MIRArgument.jparse(jobj.arg), jobj.argInferType, jobj.properties, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRProjectFromProperties = MIRProjectFromProperties;
class MIRAccessFromField extends MIRValueOp {
    constructor(sinfo, resultAccessType, arg, argInferType, field, trgt) {
        super(MIROpTag.MIRAccessFromField, sinfo, trgt);
        this.resultAccessType = resultAccessType;
        this.arg = arg;
        this.argInferType = argInferType;
        this.field = field;
    }
    getUsedVars() { return varsOnlyHelper([this.arg]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.${this.field}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultAccessType: this.resultAccessType, arg: this.arg.jemit(), argInferType: this.argInferType, field: this.field });
    }
    static jparse(jobj) {
        return new MIRAccessFromField(jparsesinfo(jobj.sinfo), jobj.resultAccessType, MIRArgument.jparse(jobj.arg), jobj.argInferType, jobj.field, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRAccessFromField = MIRAccessFromField;
class MIRProjectFromFields extends MIRValueOp {
    constructor(sinfo, resultProjectType, arg, argInferType, fields, trgt) {
        super(MIROpTag.MIRProjectFromFields, sinfo, trgt);
        this.resultProjectType = resultProjectType;
        this.arg = arg;
        this.argInferType = argInferType;
        this.fields = fields;
    }
    getUsedVars() { return varsOnlyHelper([this.arg]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}{${this.fields.join(", ")}}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultProjectType: this.resultProjectType, arg: this.arg.jemit(), argInferType: this.argInferType, fields: this.fields });
    }
    static jparse(jobj) {
        return new MIRProjectFromFields(jparsesinfo(jobj.sinfo), jobj.resultProjectType, MIRArgument.jparse(jobj.arg), jobj.argInferType, jobj.fields, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRProjectFromFields = MIRProjectFromFields;
class MIRProjectFromTypeTuple extends MIRValueOp {
    constructor(sinfo, resultProjectType, arg, istry, argInferType, ptype, trgt) {
        super(MIROpTag.MIRProjectFromTypeTuple, sinfo, trgt);
        this.resultProjectType = resultProjectType;
        this.arg = arg;
        this.istry = istry;
        this.argInferType = argInferType;
        this.ptype = ptype;
    }
    getUsedVars() { return varsOnlyHelper([this.arg]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}#${this.ptype}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultProjectType: this.resultProjectType, arg: this.arg.jemit(), istry: this.istry, argInferType: this.argInferType, ptype: this.ptype });
    }
    static jparse(jobj) {
        return new MIRProjectFromTypeTuple(jparsesinfo(jobj.sinfo), jobj.resultProjectType, MIRArgument.jparse(jobj.arg), jobj.istry, jobj.argInferType, jobj.ptype, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRProjectFromTypeTuple = MIRProjectFromTypeTuple;
class MIRProjectFromTypeRecord extends MIRValueOp {
    constructor(sinfo, resultProjectType, arg, istry, argInferType, ptype, trgt) {
        super(MIROpTag.MIRProjectFromTypeRecord, sinfo, trgt);
        this.resultProjectType = resultProjectType;
        this.arg = arg;
        this.istry = istry;
        this.argInferType = argInferType;
        this.ptype = ptype;
    }
    getUsedVars() { return varsOnlyHelper([this.arg]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}#${this.ptype}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultProjectType: this.resultProjectType, arg: this.arg.jemit(), istry: this.istry, argInferType: this.argInferType, ptype: this.ptype });
    }
    static jparse(jobj) {
        return new MIRProjectFromTypeRecord(jparsesinfo(jobj.sinfo), jobj.resultProjectType, MIRArgument.jparse(jobj.arg), jobj.istry, jobj.argInferType, jobj.ptype, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRProjectFromTypeRecord = MIRProjectFromTypeRecord;
class MIRProjectFromTypeNominal extends MIRValueOp {
    constructor(sinfo, resultProjectType, arg, istry, argInferType, ptype, cfields, trgt) {
        super(MIROpTag.MIRProjectFromTypeNominal, sinfo, trgt);
        this.resultProjectType = resultProjectType;
        this.arg = arg;
        this.istry = istry;
        this.argInferType = argInferType;
        this.ptype = ptype;
        this.cfields = cfields;
    }
    getUsedVars() { return varsOnlyHelper([this.arg]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}#${this.ptype}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultProjectType: this.resultProjectType, arg: this.arg.jemit(), istry: this.istry, argInferType: this.argInferType, ptype: this.ptype, cfields: this.cfields });
    }
    static jparse(jobj) {
        return new MIRProjectFromTypeNominal(jparsesinfo(jobj.sinfo), jobj.resultProjectType, MIRArgument.jparse(jobj.arg), jobj.istry, jobj.argInferType, jobj.ptype, jobj.cfields, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRProjectFromTypeNominal = MIRProjectFromTypeNominal;
class MIRModifyWithIndecies extends MIRValueOp {
    constructor(sinfo, resultTupleType, arg, argInferType, updates, trgt) {
        super(MIROpTag.MIRModifyWithIndecies, sinfo, trgt);
        this.resultTupleType = resultTupleType;
        this.arg = arg;
        this.argInferType = argInferType;
        this.updates = updates;
    }
    getUsedVars() { return varsOnlyHelper([this.arg, ...this.updates.map((u) => u[1])]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}<~${this.updates.map((u) => `${u[0]}=${u[1].stringify()}`).join(", ")}]`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultTupleType: this.resultTupleType, arg: this.arg.jemit(), argInferType: this.argInferType, udpates: this.updates.map((update) => [update[0], update[1].jemit()]) });
    }
    static jparse(jobj) {
        return new MIRModifyWithIndecies(jparsesinfo(jobj.sinfo), jobj.resultTupleType, MIRArgument.jparse(jobj.arg), jobj.argInferType, jobj.updates.map((update) => [update[0], MIRArgument.jparse(update[1])]), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRModifyWithIndecies = MIRModifyWithIndecies;
class MIRModifyWithProperties extends MIRValueOp {
    constructor(sinfo, resultRecordType, arg, argInferType, updates, trgt) {
        super(MIROpTag.MIRModifyWithProperties, sinfo, trgt);
        this.resultRecordType = resultRecordType;
        this.arg = arg;
        this.argInferType = argInferType;
        this.updates = updates;
    }
    getUsedVars() { return varsOnlyHelper([this.arg, ...this.updates.map((u) => u[1])]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}<~${this.updates.map((u) => `${u[0]}=${u[1].stringify()}`).join(", ")}]`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultRecordType: this.resultRecordType, arg: this.arg.jemit(), argInferType: this.argInferType, udpates: this.updates.map((update) => [update[0], update[1].jemit()]) });
    }
    static jparse(jobj) {
        return new MIRModifyWithProperties(jparsesinfo(jobj.sinfo), jobj.resultRecordType, MIRArgument.jparse(jobj.arg), jobj.argInferType, jobj.updates.map((update) => [update[0], MIRArgument.jparse(update[1])]), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRModifyWithProperties = MIRModifyWithProperties;
class MIRModifyWithFields extends MIRValueOp {
    constructor(sinfo, resultNominalType, arg, argInferType, updates, trgt) {
        super(MIROpTag.MIRModifyWithFields, sinfo, trgt);
        this.resultNominalType = resultNominalType;
        this.arg = arg;
        this.argInferType = argInferType;
        this.updates = updates;
    }
    getUsedVars() { return varsOnlyHelper([this.arg, ...this.updates.map((u) => u[1])]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}<~${this.updates.map((u) => `${u[0]}=${u[1].stringify()}`).join(", ")}]`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultNominalType: this.resultNominalType, arg: this.arg.jemit(), argInferType: this.argInferType, updates: this.updates.map((update) => [update[0], update[1].jemit()]) });
    }
    static jparse(jobj) {
        return new MIRModifyWithFields(jparsesinfo(jobj.sinfo), jobj.resultNominalType, MIRArgument.jparse(jobj.arg), jobj.argInferType, jobj.updates.map((update) => [update[0], MIRArgument.jparse(update[1])]), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRModifyWithFields = MIRModifyWithFields;
class MIRStructuredExtendTuple extends MIRValueOp {
    constructor(sinfo, resultTupleType, arg, argInferType, update, updateInferType, trgt) {
        super(MIROpTag.MIRStructuredExtendTuple, sinfo, trgt);
        this.resultTupleType = resultTupleType;
        this.arg = arg;
        this.argInferType = argInferType;
        this.update = update;
        this.updateInferType = updateInferType;
    }
    getUsedVars() { return varsOnlyHelper([this.arg, this.update]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}<+(${this.update.stringify()})`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultTupleType: this.resultTupleType, arg: this.arg.jemit(), argInferType: this.argInferType, udpate: this.update.jemit(), updateInferType: this.updateInferType });
    }
    static jparse(jobj) {
        return new MIRStructuredExtendTuple(jparsesinfo(jobj.sinfo), jobj.resultTupleType, MIRArgument.jparse(jobj.arg), jobj.argInferType, MIRArgument.jparse(jobj.update), jobj.updateInferType, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRStructuredExtendTuple = MIRStructuredExtendTuple;
class MIRStructuredExtendRecord extends MIRValueOp {
    constructor(sinfo, resultRecordType, arg, argInferType, update, updateInferType, trgt) {
        super(MIROpTag.MIRStructuredExtendRecord, sinfo, trgt);
        this.resultRecordType = resultRecordType;
        this.arg = arg;
        this.argInferType = argInferType;
        this.update = update;
        this.updateInferType = updateInferType;
    }
    getUsedVars() { return varsOnlyHelper([this.arg, this.update]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}<+(${this.update.stringify()})`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultRecordType: this.resultRecordType, arg: this.arg.jemit(), argInferType: this.argInferType, udpate: this.update.jemit(), updateInferType: this.updateInferType });
    }
    static jparse(jobj) {
        return new MIRStructuredExtendRecord(jparsesinfo(jobj.sinfo), jobj.resultRecordType, MIRArgument.jparse(jobj.arg), jobj.argInferType, MIRArgument.jparse(jobj.update), jobj.updateInferType, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRStructuredExtendRecord = MIRStructuredExtendRecord;
class MIRStructuredExtendObject extends MIRValueOp {
    constructor(sinfo, resultNominalType, arg, argInferType, update, updateInferType, fieldResolves, trgt) {
        super(MIROpTag.MIRStructuredExtendObject, sinfo, trgt);
        this.resultNominalType = resultNominalType;
        this.arg = arg;
        this.argInferType = argInferType;
        this.update = update;
        this.updateInferType = updateInferType;
        this.fieldResolves = fieldResolves;
    }
    getUsedVars() { return varsOnlyHelper([this.arg, this.update]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}<+(${this.update.stringify()})`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultNominalType: this.resultNominalType, arg: this.arg.jemit(), argInferType: this.argInferType, udpate: this.update.jemit(), updateInferType: this.updateInferType, fieldResolves: this.fieldResolves });
    }
    static jparse(jobj) {
        return new MIRStructuredExtendObject(jparsesinfo(jobj.sinfo), jobj.resultNominalType, MIRArgument.jparse(jobj.arg), jobj.argInferType, MIRArgument.jparse(jobj.update), jobj.updateInferType, jobj.fieldResolves, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRStructuredExtendObject = MIRStructuredExtendObject;
class MIRLoadFromEpehmeralList extends MIRValueOp {
    constructor(sinfo, arg, argInferType, idx, trgt) {
        super(MIROpTag.MIRLoadFromEpehmeralList, sinfo, trgt);
        this.arg = arg;
        this.argInferType = argInferType;
        this.idx = idx;
    }
    getUsedVars() { return varsOnlyHelper([this.arg]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}(|${this.idx}|)`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { arg: this.arg.jemit(), argInferType: this.argInferType, idx: this.idx });
    }
    static jparse(jobj) {
        return new MIRLoadFromEpehmeralList(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.argInferType, jobj.idx, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRLoadFromEpehmeralList = MIRLoadFromEpehmeralList;
class MIRInvokeFixedFunction extends MIRValueOp {
    constructor(sinfo, resultType, mkey, args, trgt) {
        super(MIROpTag.MIRInvokeFixedFunction, sinfo, trgt);
        this.resultType = resultType;
        this.mkey = mkey;
        this.args = args;
    }
    getUsedVars() { return varsOnlyHelper([...this.args]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.mkey}::(${this.args.map((arg) => arg.stringify()).join(", ")})`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultType: this.resultType, mkey: this.mkey, args: this.args.map((arg) => arg.jemit()) });
    }
    static jparse(jobj) {
        return new MIRInvokeFixedFunction(jparsesinfo(jobj.sinfo), jobj.resultType, jobj.mkey, jobj.args.map((arg) => MIRArgument.jparse(arg)), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRInvokeFixedFunction = MIRInvokeFixedFunction;
class MIRInvokeVirtualFunction extends MIRValueOp {
    constructor(sinfo, resultType, vresolve, args, thisInferType, trgt) {
        super(MIROpTag.MIRInvokeVirtualTarget, sinfo, trgt);
        this.resultType = resultType;
        this.vresolve = vresolve;
        this.args = args;
        this.thisInferType = thisInferType;
    }
    getUsedVars() { return varsOnlyHelper([...this.args]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.args[0].stringify()}->${this.vresolve}(${[...this.args].slice(1).map((arg) => arg.stringify()).join(", ")})`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { resultType: this.resultType, vresolve: this.vresolve, args: this.args.map((arg) => arg.jemit()), thisInferType: this.thisInferType });
    }
    static jparse(jobj) {
        return new MIRInvokeVirtualFunction(jparsesinfo(jobj.sinfo), jobj.resultType, jobj.vresolve, jobj.args.map((arg) => MIRArgument.jparse(arg)), jobj.thisInferType, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRInvokeVirtualFunction = MIRInvokeVirtualFunction;
class MIRPrefixOp extends MIRValueOp {
    constructor(sinfo, op, arg, trgt) {
        super(MIROpTag.MIRPrefixOp, sinfo, trgt);
        this.op = op;
        this.arg = arg;
    }
    getUsedVars() { return varsOnlyHelper([this.arg]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.op}${this.arg.stringify()}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { op: this.op, arg: this.arg.jemit() });
    }
    static jparse(jobj) {
        return new MIRPrefixOp(jparsesinfo(jobj.sinfo), jobj.op, MIRArgument.jparse(jobj.arg), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRPrefixOp = MIRPrefixOp;
class MIRBinOp extends MIRValueOp {
    constructor(sinfo, lhsInferType, lhs, op, rhsInferType, rhs, trgt) {
        super(MIROpTag.MIRBinOp, sinfo, trgt);
        this.lhsInferType = lhsInferType;
        this.lhs = lhs;
        this.op = op;
        this.rhsInferType = rhsInferType;
        this.rhs = rhs;
    }
    getUsedVars() { return varsOnlyHelper([this.lhs, this.rhs]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.lhs.stringify()}${this.op}${this.rhs.stringify()}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { lhsInferType: this.lhsInferType, lhs: this.lhs.jemit(), op: this.op, rhsInferType: this.rhsInferType, rhs: this.rhs.jemit() });
    }
    static jparse(jobj) {
        return new MIRBinOp(jparsesinfo(jobj.sinfo), jobj.lhsInferType, MIRArgument.jparse(jobj.lhs), jobj.op, jobj.rhsInferType, MIRArgument.jparse(jobj.rhs), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRBinOp = MIRBinOp;
class MIRBinEq extends MIRValueOp {
    constructor(sinfo, lhsInferType, lhs, op, rhsInferType, rhs, trgt, relaxed) {
        super(MIROpTag.MIRBinEq, sinfo, trgt);
        this.lhsInferType = lhsInferType;
        this.lhs = lhs;
        this.op = op;
        this.rhsInferType = rhsInferType;
        this.rhs = rhs;
        this.relaxed = relaxed;
    }
    getUsedVars() { return varsOnlyHelper([this.lhs, this.rhs]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.lhs.stringify()}${this.op}${this.rhs.stringify()}${this.relaxed ? " | relaxed" : ""}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { lhsInferType: this.lhsInferType, lhs: this.lhs.jemit(), op: this.op, rhsInferType: this.rhsInferType, rhs: this.rhs.jemit(), relaxed: this.relaxed });
    }
    static jparse(jobj) {
        return new MIRBinEq(jparsesinfo(jobj.sinfo), jobj.lhsInferType, MIRArgument.jparse(jobj.lhs), jobj.op, jobj.rhsInferType, MIRArgument.jparse(jobj.rhs), MIRTempRegister.jparse(jobj.trgt), jobj.relaxed);
    }
}
exports.MIRBinEq = MIRBinEq;
class MIRBinLess extends MIRValueOp {
    constructor(sinfo, lhsInferType, lhs, rhsInferType, rhs, trgt, relaxed) {
        super(MIROpTag.MIRBinLess, sinfo, trgt);
        this.lhsInferType = lhsInferType;
        this.lhs = lhs;
        this.rhsInferType = rhsInferType;
        this.rhs = rhs;
        this.relaxed = relaxed;
    }
    getUsedVars() { return varsOnlyHelper([this.lhs, this.rhs]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.lhs.stringify()} < ${this.rhs.stringify()}${this.relaxed ? " | relaxed" : ""}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { lhsInferType: this.lhsInferType, lhs: this.lhs.jemit(), rhsInferType: this.rhsInferType, rhs: this.rhs.jemit(), relaxed: this.relaxed });
    }
    static jparse(jobj) {
        return new MIRBinLess(jparsesinfo(jobj.sinfo), jobj.lhsInferType, MIRArgument.jparse(jobj.lhs), jobj.rhsInferType, MIRArgument.jparse(jobj.rhs), MIRTempRegister.jparse(jobj.trgt), jobj.relaxed);
    }
}
exports.MIRBinLess = MIRBinLess;
class MIRBinCmp extends MIRValueOp {
    constructor(sinfo, lhsInferType, lhs, op, rhsInferType, rhs, trgt) {
        super(MIROpTag.MIRBinCmp, sinfo, trgt);
        this.lhsInferType = lhsInferType;
        this.lhs = lhs;
        this.op = op;
        this.rhsInferType = rhsInferType;
        this.rhs = rhs;
    }
    getUsedVars() { return varsOnlyHelper([this.lhs, this.rhs]); }
    stringify() {
        return `${this.trgt.stringify()} = ${this.lhs.stringify()}${this.op}${this.rhs.stringify()}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { lhsInferType: this.lhsInferType, lhs: this.lhs.jemit(), op: this.op, rhsInferType: this.rhsInferType, rhs: this.rhs.jemit() });
    }
    static jparse(jobj) {
        return new MIRBinCmp(jparsesinfo(jobj.sinfo), jobj.lhsInferType, MIRArgument.jparse(jobj.lhs), jobj.op, jobj.rhsInferType, MIRArgument.jparse(jobj.rhs), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRBinCmp = MIRBinCmp;
class MIRIsTypeOfNone extends MIRValueOp {
    constructor(sinfo, arg, trgt) {
        super(MIROpTag.MIRIsTypeOfNone, sinfo, trgt);
        this.arg = arg;
    }
    getUsedVars() { return varsOnlyHelper([this.arg]); }
    stringify() {
        return `${this.trgt.stringify()} = $isNoneType(${this.arg.stringify()})`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { arg: this.arg.jemit() });
    }
    static jparse(jobj) {
        return new MIRIsTypeOfNone(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRIsTypeOfNone = MIRIsTypeOfNone;
class MIRIsTypeOfSome extends MIRValueOp {
    constructor(sinfo, arg, trgt) {
        super(MIROpTag.MIRIsTypeOfSome, sinfo, trgt);
        this.arg = arg;
    }
    getUsedVars() { return varsOnlyHelper([this.arg]); }
    stringify() {
        return `${this.trgt.stringify()} = $isSomeType(${this.arg.stringify()})`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { arg: this.arg.jemit() });
    }
    static jparse(jobj) {
        return new MIRIsTypeOfSome(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRIsTypeOfSome = MIRIsTypeOfSome;
class MIRIsTypeOf extends MIRValueOp {
    constructor(sinfo, argInferType, arg, oftype, trgt) {
        super(MIROpTag.MIRIsTypeOf, sinfo, trgt);
        this.argInferType = argInferType;
        this.arg = arg;
        this.oftype = oftype;
    }
    getUsedVars() { return varsOnlyHelper([this.arg]); }
    stringify() {
        return `${this.trgt.stringify()} = $isTypeOf(${this.arg.stringify()}, ${this.oftype})`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { argInferType: this.argInferType, arg: this.arg.jemit(), oftype: this.oftype });
    }
    static jparse(jobj) {
        return new MIRIsTypeOf(jparsesinfo(jobj.sinfo), jobj.argInferType, MIRArgument.jparse(jobj.arg), jobj.oftype, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRIsTypeOf = MIRIsTypeOf;
class MIRRegAssign extends MIRFlowOp {
    constructor(sinfo, src, trgt) {
        super(MIROpTag.MIRRegAssign, sinfo);
        this.src = src;
        this.trgt = trgt;
    }
    getUsedVars() { return varsOnlyHelper([this.src]); }
    getModVars() { return [this.trgt]; }
    stringify() {
        return `${this.trgt.stringify()} = ${this.src.stringify()}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { src: this.src.jemit(), trgt: this.trgt.jemit() });
    }
    static jparse(jobj) {
        return new MIRRegAssign(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRRegAssign = MIRRegAssign;
class MIRTruthyConvert extends MIRFlowOp {
    constructor(sinfo, src, trgt) {
        super(MIROpTag.MIRTruthyConvert, sinfo);
        this.src = src;
        this.trgt = trgt;
    }
    getUsedVars() { return varsOnlyHelper([this.src]); }
    getModVars() { return [this.trgt]; }
    stringify() {
        return `${this.trgt.stringify()} = $truthy(${this.src.stringify()})`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { src: this.src.jemit(), trgt: this.trgt.jemit() });
    }
    static jparse(jobj) {
        return new MIRTruthyConvert(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRTruthyConvert = MIRTruthyConvert;
class MIRVarStore extends MIRFlowOp {
    constructor(sinfo, src, name) {
        super(MIROpTag.MIRVarStore, sinfo);
        this.src = src;
        this.name = name;
    }
    getUsedVars() { return varsOnlyHelper([this.src]); }
    getModVars() { return [this.name]; }
    stringify() {
        return `${this.name.stringify()} = ${this.src.stringify()}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { src: this.src.jemit(), name: this.name.jemit() });
    }
    static jparse(jobj) {
        return new MIRVarStore(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), MIRVariable.jparse(jobj.name));
    }
}
exports.MIRVarStore = MIRVarStore;
class MIRPackSlice extends MIRFlowOp {
    constructor(sinfo, src, sltype, trgt) {
        super(MIROpTag.MIRPackSlice, sinfo);
        this.src = src;
        this.sltype = sltype;
        this.trgt = trgt;
    }
    getUsedVars() { return varsOnlyHelper([this.src]); }
    getModVars() { return [this.trgt]; }
    stringify() {
        return `${this.trgt.stringify()} = ${this.src.stringify()}[${this.sltype}]`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { src: this.src.jemit(), sltype: this.sltype, trgt: this.trgt.jemit() });
    }
    static jparse(jobj) {
        return new MIRPackSlice(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), jobj.sltype, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRPackSlice = MIRPackSlice;
class MIRPackExtend extends MIRFlowOp {
    constructor(sinfo, basepack, ext, sltype, trgt) {
        super(MIROpTag.MIRPackExtend, sinfo);
        this.basepack = basepack;
        this.ext = ext;
        this.sltype = sltype;
        this.trgt = trgt;
    }
    getUsedVars() { return varsOnlyHelper([this.basepack, ...this.ext]); }
    getModVars() { return [this.trgt]; }
    stringify() {
        return `${this.trgt.stringify()} = ${this.sltype}@(|${this.basepack.stringify()}, ${this.ext.map((e) => e.stringify()).join(", ")}|)`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { basepack: this.basepack.jemit(), ext: this.ext.map((e) => e.jemit()), sltype: this.sltype, trgt: this.trgt.jemit() });
    }
    static jparse(jobj) {
        return new MIRPackExtend(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.basepack), jobj.ext.map((e) => MIRArgument.jparse(e)), jobj.sltype, MIRTempRegister.jparse(jobj.trgt));
    }
}
exports.MIRPackExtend = MIRPackExtend;
class MIRReturnAssign extends MIRFlowOp {
    constructor(sinfo, src, name) {
        super(MIROpTag.MIRReturnAssign, sinfo);
        this.src = src;
        this.name = name || new MIRVariable("$__ir_ret__");
    }
    getUsedVars() { return varsOnlyHelper([this.src]); }
    getModVars() { return [this.name]; }
    stringify() {
        return `${this.name.stringify()} = ${this.src.stringify()}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { src: this.src.jemit(), name: this.name.jemit() });
    }
    static jparse(jobj) {
        return new MIRReturnAssign(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), MIRVariable.jparse(jobj.name));
    }
}
exports.MIRReturnAssign = MIRReturnAssign;
class MIRAbort extends MIRFlowOp {
    constructor(sinfo, info) {
        super(MIROpTag.MIRAbort, sinfo);
        this.info = info;
    }
    getUsedVars() { return []; }
    getModVars() { return []; }
    stringify() {
        return `abort -- ${this.info}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { info: this.info });
    }
    static jparse(jobj) {
        return new MIRAbort(jparsesinfo(jobj.sinfo), jobj.info);
    }
}
exports.MIRAbort = MIRAbort;
class MIRDebug extends MIRFlowOp {
    constructor(sinfo, value) {
        super(MIROpTag.MIRDebug, sinfo);
        this.value = value;
    }
    getUsedVars() { return this.value !== undefined ? varsOnlyHelper([this.value]) : []; }
    getModVars() { return []; }
    stringify() {
        if (this.value === undefined) {
            return "_debug break";
        }
        else {
            return `_debug ${this.value.stringify()}`;
        }
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { value: this.value ? [this.value.jemit()] : null });
    }
    static jparse(jobj) {
        return new MIRDebug(jparsesinfo(jobj.sinfo), jobj.value ? MIRArgument.jparse(jobj.value[0]) : undefined);
    }
}
exports.MIRDebug = MIRDebug;
class MIRJump extends MIRJumpOp {
    constructor(sinfo, blck) {
        super(MIROpTag.MIRJump, sinfo);
        this.trgtblock = blck;
    }
    getUsedVars() { return []; }
    getModVars() { return []; }
    stringify() {
        return `jump ${this.trgtblock}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { trgtblock: this.trgtblock });
    }
    static jparse(jobj) {
        return new MIRJump(jparsesinfo(jobj.sinfo), jobj.trgtblock);
    }
}
exports.MIRJump = MIRJump;
class MIRVarLifetimeStart extends MIRJumpOp {
    constructor(sinfo, name, rtype) {
        super(MIROpTag.MIRVarLifetimeStart, sinfo);
        this.name = name;
        this.rtype = rtype;
    }
    getUsedVars() { return []; }
    getModVars() { return []; }
    stringify() {
        return `v-begin ${this.name}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { name: this.name, rtype: this.rtype });
    }
    static jparse(jobj) {
        return new MIRVarLifetimeStart(jparsesinfo(jobj.sinfo), jobj.name, jobj.rtype);
    }
}
exports.MIRVarLifetimeStart = MIRVarLifetimeStart;
class MIRVarLifetimeEnd extends MIRJumpOp {
    constructor(sinfo, name) {
        super(MIROpTag.MIRVarLifetimeEnd, sinfo);
        this.name = name;
    }
    getUsedVars() { return []; }
    getModVars() { return []; }
    stringify() {
        return `v-end ${this.name}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { name: this.name });
    }
    static jparse(jobj) {
        return new MIRVarLifetimeEnd(jparsesinfo(jobj.sinfo), jobj.name);
    }
}
exports.MIRVarLifetimeEnd = MIRVarLifetimeEnd;
class MIRJumpCond extends MIRJumpOp {
    constructor(sinfo, arg, trueblck, falseblck) {
        super(MIROpTag.MIRJumpCond, sinfo);
        this.arg = arg;
        this.trueblock = trueblck;
        this.falseblock = falseblck;
    }
    getUsedVars() { return varsOnlyHelper([this.arg]); }
    getModVars() { return []; }
    stringify() {
        return `cjump ${this.arg.stringify()} ${this.trueblock} ${this.falseblock}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { arg: this.arg.jemit(), trueblock: this.trueblock, falseblock: this.falseblock });
    }
    static jparse(jobj) {
        return new MIRJumpCond(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.trueblock, jobj.falseblock);
    }
}
exports.MIRJumpCond = MIRJumpCond;
class MIRJumpNone extends MIRJumpOp {
    constructor(sinfo, arg, noneblck, someblck) {
        super(MIROpTag.MIRJumpNone, sinfo);
        this.arg = arg;
        this.noneblock = noneblck;
        this.someblock = someblck;
    }
    getUsedVars() { return varsOnlyHelper([this.arg]); }
    getModVars() { return []; }
    stringify() {
        return `njump ${this.arg.stringify()} ${this.noneblock} ${this.someblock}`;
    }
    jemit() {
        return Object.assign(Object.assign({}, this.jbemit()), { arg: this.arg.jemit(), noneblock: this.noneblock, someblock: this.someblock });
    }
    static jparse(jobj) {
        return new MIRJumpNone(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.noneblock, jobj.someblock);
    }
}
exports.MIRJumpNone = MIRJumpNone;
class MIRPhi extends MIRFlowOp {
    constructor(sinfo, src, trgt) {
        super(MIROpTag.MIRPhi, sinfo);
        this.src = src;
        this.trgt = trgt;
    }
    getUsedVars() {
        let phis = [];
        this.src.forEach((v) => phis.push(v));
        return phis;
    }
    getModVars() { return [this.trgt]; }
    stringify() {
        let phis = [];
        this.src.forEach((v, k) => phis.push(`${v.stringify()} -- ${k}`));
        phis.sort();
        return `${this.trgt.stringify()} = (${phis.join(", ")})`;
    }
    jemit() {
        const phis = [...this.src].map((phi) => [phi[0], phi[1].jemit()]);
        return Object.assign(Object.assign({}, this.jbemit()), { src: phis, trgt: this.trgt.jemit() });
    }
    static jparse(jobj) {
        let phis = new Map();
        jobj.src.forEach((phi) => phis.set(phi[0], MIRRegisterArgument.jparse(phi[1])));
        return new MIRPhi(jparsesinfo(jobj.sinfo), phis, MIRRegisterArgument.jparse(jobj.trgt));
    }
}
exports.MIRPhi = MIRPhi;
class MIRBasicBlock {
    constructor(label, ops) {
        this.label = label;
        this.ops = ops;
    }
    jsonify() {
        const jblck = {
            label: this.label,
            line: (this.ops.length !== 0) ? this.ops[0].sinfo.line : -1,
            ops: this.ops.map((op) => op.stringify())
        };
        return jblck;
    }
    jemit() {
        return { label: this.label, ops: this.ops.map((op) => op.jemit()) };
    }
    static jparse(jobj) {
        return new MIRBasicBlock(jobj.label, jobj.ops.map((op) => MIROp.jparse(op)));
    }
}
exports.MIRBasicBlock = MIRBasicBlock;
class MIRBody {
    constructor(file, sinfo, body, vtypes) {
        this.file = file;
        this.sinfo = sinfo;
        this.body = body;
        this.vtypes = vtypes;
    }
    jsonify() {
        let blocks = [];
        mir_info_1.topologicalOrder(this.body).forEach((v, k) => blocks.push(v.jsonify()));
        return blocks;
    }
    dgmlify(siginfo) {
        const blocks = mir_info_1.topologicalOrder(this.body);
        const flow = mir_info_1.computeBlockLinks(this.body);
        const xmlescape = (str) => {
            return str.replace(/&/g, "&amp;")
                .replace(/</g, "&lt;")
                .replace(/>/g, "&gt;")
                .replace(/"/g, "&quot;")
                .replace(/'/g, "&apos;");
        };
        let nodes = [`<Node Id="fdecl" Label="${siginfo}"/>`];
        let links = [`<Link Source="fdecl" Target="entry"/>`];
        blocks.forEach((b) => {
            const ndata = b.jsonify();
            const dstring = `L: ${ndata.label} &#10;  ` + ndata.ops.map((op) => xmlescape(op)).join("&#10;  ");
            nodes.push(`<Node Id="${ndata.label}" Label="${dstring}"/>`);
            flow.get(ndata.label).succs.forEach((succ) => {
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
    jemit() {
        const blocks = mir_info_1.topologicalOrder(this.body).map((blck) => blck.jemit());
        const vtypes = this.vtypes !== undefined ? ([...this.vtypes].sort((a, b) => a[0].localeCompare(b[0]))) : undefined;
        return { file: this.file, sinfo: jemitsinfo(this.sinfo), blocks: blocks, vtypes: vtypes };
    }
    static jparse(jobj) {
        let body = new Map();
        jobj.blocks.map((blck) => MIRBasicBlock.jparse(blck)).forEach((blck) => body.set(blck.label, blck));
        if (jobj.vtypes === undefined) {
            return new MIRBody(jobj.file, jparsesinfo(jobj.sinfo), body);
        }
        else {
            let vtypes = new Map();
            jobj.vtypes.forEach((vtype) => vtypes.set(vtype[0], vtype[1]));
            return new MIRBody(jobj.file, jparsesinfo(jobj.sinfo), body, vtypes);
        }
    }
}
exports.MIRBody = MIRBody;
//# sourceMappingURL=mir_ops.js.map