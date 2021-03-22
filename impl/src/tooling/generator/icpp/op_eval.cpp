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
            case ArgumentTag::ConstStringOf:
                return Environment::g_constStringOfs + arg.location;
            case ArgumentTag::ConstDataString:
                return Environment::g_constDataStrings + arg.location;
            case ArgumentTag::ConstRegex:
                return Environment::g_constRegexes + arg.location;
            default: {
                xxxx;
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