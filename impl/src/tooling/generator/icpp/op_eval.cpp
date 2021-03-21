//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "op_eval.h"

InterpValue evalArgument(Argument arg)
{
    if(arg.kind == ArgumentTag::Register)
    {
        return xxx;
    }
    else 
    {
        switch(arg.kind)
        {
            case
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
    BSQ_LANGUAGE_ABORT(op->msg, Environment::GlobalEnv.cfile, op->sinfo.line);
}

void evalAssertCheck(const AssertOp* op)
{
    auto val = evalArgument(op->arg);
    if(!LOAD_FROM(BSQBool, val))
    {
        BSQ_LANGUAGE_ABORT(op->msg, Environment::GlobalEnv.cfile, op->sinfo.line);
    }
}

void evalDebug();

void evalLoadUnintVariableValue();
void evalDeclareGuardFlagLocation();
void evalSetConstantGuardFlag();
void evalConvertValue();