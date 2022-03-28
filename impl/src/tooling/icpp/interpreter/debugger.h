//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#ifdef BSQ_DEBUG_BUILD

#include "op_eval.h"

class DebuggerException
{
private:
    //An integer code to describe the reason for the abort -- 0 invalid, 1 end of log, 2 request etime move, 3 uncaught exception (propagate to top-level)
    const uint32_t m_abortCode;

    //An optional target event time -- intent is interpreted based on the abort code
    const int64_t m_optEventTime;

    //An optional move mode value -- should be built by host we just propagate it
    const int64_t m_optMoveMode;

    //An optional -- and static string message to include
    const char* m_staticAbortMessage;

    DebuggerException(uint32_t abortCode, int64_t optEventTime, int64_t optMoveMode, const char* staticAbortMessage);

    public:
        ~DebuggerException();

        static DebuggerException CreateAbortEndOfLog(const char* staticMessage);
        static DebuggerException CreateTopLevelAbortRequest(int64_t targetEventTime, int64_t moveMode, const char* staticMessage);
        static DebuggerException CreateUncaughtExceptionAbortRequest(int64_t targetEventTime, const char* staticMessage);

        bool IsEndOfLog() const;
        bool IsEventTimeMove() const;
        bool IsTopLevelException() const;

        int64_t GetTargetEventTime() const;
        int64_t GetMoveMode() const;

        const char* GetStaticAbortMessage() const;
    };

void stepAction(Evaluator* vv)
{
    
}

#endif
