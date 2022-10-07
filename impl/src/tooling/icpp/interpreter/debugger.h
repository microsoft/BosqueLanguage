//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#ifdef BSQ_DEBUG_BUILD

#include "op_eval.h"

bool initializeDebuggerIO();
void closeDebuggerIO();

std::pair<DebuggerCmd, std::string> readDebugCmd();
void writeDebugResult(std::string data);

void debuggerStepAction(Evaluator* vv);

#endif
