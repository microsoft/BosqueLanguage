//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "common.h"

#include "assembly/bsqtype.h"
#include "assembly/bsqop.h"

#include "runtime/environment.h"

class Evaluator
{
private:
    std::wstring* getCurrentFile();
    uint64_t getCurrentLine();
    uint64_t getCurrentColumn();

    StorageLocationPtr evalConstArgument(Argument arg);

    inline StorageLocationPtr evalArgument(Argument arg)
    {
        if(arg.kind == ArgumentTag::Register)
        {
            return xxx;
        }
        else if(arg.kind == ArgumentTag::Argument)
        {
            return xxx;
        }
        else 
        {
            return evalConstArgument(arg);
        }
    }

    inline StorageLocationPtr evalTargetVar(TargetVar trgt)
    {
        return xxx;
    }

    void evalDeadFlow();
    void evalAbort(const AbortOp* op);
    void evalAssertCheck(const AssertOp* op);
    void evalDebug(const DebugOp* op);

    void evalLoadUnintVariableValue(const LoadUnintVariableValueOp* op);
    void evalConvertValue(const ConvertValueOp* op);

    void evalLoadConst(const LoadConstOp* op);

    void evalTupleHasIndex(const TupleHasIndexOp* op);
    void evalRecordHasProperty(const RecordHasPropertyOp* op);
    void evalLoadTupleIndex(const LoadTupleIndexOp* op);
    void evalLoadTupleIndexSetGuard(const LoadTupleIndexSetGuardOp* op);
    void evalLoadRecordProperty(const LoadRecordPropertyOp* op);
    void evalLoadRecordPropertySetGuard(const LoadRecordPropertySetGuardOp* op);

    void evalLoadField(const LoadFieldOp* op);
};

/*
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
    */