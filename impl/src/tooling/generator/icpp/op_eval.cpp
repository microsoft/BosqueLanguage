//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "op_eval.h"

std::wstring* Evaluator::getCurrentFile()
{
    return xxx;
}

uint64_t Evaluator::getCurrentLine()
{
    return xxxx;
}

uint64_t Evaluator::getCurrentColumn()
{
    return xxxx;
}

SLValue Evaluator::evalConstArgument(Argument arg)
{
    switch (arg.kind)
    {
    case ArgumentTag::ConstNone:
        return &Environment::g_constNone;
    case ArgumentTag::ConstTrue:
        return &Environment::g_constTrue;
    case ArgumentTag::ConstFalse:
        return &Environment::g_constFalse;
    case ArgumentTag::ConstNat:
        return Environment::g_constNats + arg.location;
    case ArgumentTag::ConstInt:
        return Environment::g_constInts + arg.location;
    case ArgumentTag::ConstBigNat:
        return Environment::g_constBigNats + arg.location;
    case ArgumentTag::ConstBigInt:
        return Environment::g_constBigInts + arg.location;
    case ArgumentTag::ConstRational:
        return Environment::g_constRationals + arg.location;
    case ArgumentTag::ConstFloat:
        return Environment::g_constFloats + arg.location;
    case ArgumentTag::ConstDecimal:
        return Environment::g_constDecimals + arg.location;
    case ArgumentTag::ConstString:
        return Environment::g_constStrings + arg.location;
    case ArgumentTag::ConstRegex:
        return Environment::g_constRegexs + arg.location;
    default: {
            const ConstValueLoad loadfp = Environment::g_constLoads[arg.location];
            return loadfp();
        }
    }
}

void Evaluator::evalDeadFlow()
{
    //This should be unreachable
    BSQ_INTERNAL_ASSERT(false);
}

void Evaluator::evalAbort(const AbortOp *op)
{
    BSQ_LANGUAGE_ABORT(op->msg, this.getCurrentFile(), this.getCurrentLine());
}

void Evaluator::evalAssertCheck(const AssertOp *op)
{
    auto val = Evaluator::evalArgument(op->arg);
    if (!SLVALUE_LOAD_FROM(BSQBool, val))
    {
        BSQ_LANGUAGE_ABORT(op->msg, this.getCurrentFile(), this.getCurrentLine());
    }
}

void Evaluator::evalDebug(const DebugOp *op)
{
    if(op->arg.kind == ArgumentTag::InvalidOp)
    {
        //TODO: debugger break here
        assert(false);
    }
    else
    {
        auto val = SLVALUE_LOAD_FROM(BoxedConceptValue, Evaluator::evalArgument(op->arg));
        auto ttype = GET_TYPE_META_DATA(val);
        auto dval = ttype->fpDisplay(val);

        wprintf(L"%s\n", dval.c_str());
        fflush(stdout);
    }
}

void Evaluator::evalLoadUnintVariableValue(const LoadUnintVariableValueOp* op)
{
    SLVALUE_CLEAR(op->oftype, op->trgt);
}

void Evaluator::evalConvertValue(const ConvertValueOp* op)
{
    xxxx;
}

void Evaluator::evalLoadConst(const LoadConstOp* op)
{
    xxxx;
}

void Evaluator::evalTupleHasIndex(const TupleHasIndexOp* op)
{
    xxxx;
}

void Evaluator::evalRecordHasProperty(const RecordHasPropertyOp* op)
{
    xxxx;
}

void Evaluator::evalLoadTupleIndex(const LoadTupleIndexOp* op)
{
    xxxx;
}

void Evaluator::evalLoadTupleIndexSetGuard(const LoadTupleIndexSetGuardOp* op)
{
    xxxx;
}

void Evaluator::evalLoadRecordProperty(const LoadRecordPropertyOp* op)
{
    xxxx;
}

void Evaluator::evalLoadRecordPropertySetGuard(const LoadRecordPropertySetGuardOp* op)
{
    xxxx;
}

void Evaluator::evalLoadField(const LoadFieldOp* op)
{
    xxxx;
}







