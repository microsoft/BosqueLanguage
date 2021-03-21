//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "op_eval.h"

SLValue evalArgument(Argument arg)
{
    if(arg.kind == ArgumentTag::Register)
    {
        return xxx;
    }
    else 
    {
        switch(arg.kind)
        {
            case ArgumentTag::ConstNone:
                return &Environment::g_constNone;
            case ArgumentTag::ConstTrue:
                return arg.location != 0 &Environment::g_constTrue;
            case ArgumentTag::ConstFalse:
                return &Environment::g_constFalse;
            case ArgumentTag::ConstNat:
            case ArgumentTag::ConstInt:
            case ArgumentTag::ConstBigNat:
            case ArgumentTag::ConstBigInt:
            case ArgumentTag::ConstRational:
            case ArgumentTag::ConstFloat:
            case ArgumentTag::ConstDecimal:
            case ArgumentTag::ConstString:
            case ArgumentTag::ConstStringOf:
            case ArgumentTag::ConstDataString:
            case ArgumentTag::ConstRegex:
            default: {

            }
        }
    }
}

void evalDeadFlow()
{
    //This should be unreachable
    BSQ_INTERNAL_ASSERT(false);
}

void evalAbort(const AbortOp* op)
{
    BSQ_LANGUAGE_ABORT(op->msg, Environment::cfile, op->sinfo.line);
}

void evalAssertCheck(const AssertOp* op)
{
    auto val = evalArgument(op->arg);
    if(!LOAD_FROM(BSQBool, val))
    {
        BSQ_LANGUAGE_ABORT(op->msg, Environment::cfile, op->sinfo.line);
    }
}

void evalDebug();

void evalLoadUnintVariableValue();
void evalDeclareGuardFlagLocation();
void evalSetConstantGuardFlag();
void evalConvertValue();