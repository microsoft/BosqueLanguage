//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "common.h"

#include "assembly/bsqtype.h"
#include "assembly/bsqop.h"

#include "core/bsqmemory.h"
#include "core/bsqvalue.h"
#include "runtime/environment.h"

#define LOAD_FROM(T, L) (*((T*)L))
#define STORE_TO(T, L, V) ((*((T*)L)) = V)

SLValue evalArgument(Argument arg);

void evalDeadFlow();
void evalAbort();
void evalAssertCheck();
void evalDebug();

void evalLoadUnintVariableValue();
void evalDeclareGuardFlagLocation();
void evalSetConstantGuardFlag();
void evalConvertValue();

/*
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
    */