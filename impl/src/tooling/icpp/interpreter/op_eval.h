//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "common.h"
#include "runtime/bsqop.h"
#include "runtime/bsqinvoke.h"

#include "runtime/bsqvalue.h"
#include "runtime/bsqlist.h"

#include "collection_eval.h"

class Evaluator;
typedef void (*DebuggerActionFP)(Evaluator* vv);

enum class StepMode
{
    Run,
    Step,
    StepInto
};

enum class DebuggerCmd
{
    Invalid,
    Help,
    PrintFunction,
    CallStack,
    LocalDisplay,
    ExpDisplay,
    Step,
    StepInto,
    Continue,
    ReverseStep,
    ReverseStepInto,
    ReverseContinue,
    ListBreakPoint,
    AddBreakPoint,
    DeleteBreakpoint,
    Quit
};

class BreakPoint
{
public:
    const BSQInvokeDecl* invk;
    int64_t line;
    int64_t callCount;

    bool isValid() const
    {
        return this->invk != nullptr;
    }
};

enum class DebuggerExceptionMode
{
    EndOfReplay,
    MoveToBP,
    ErrorPreTime
};

class DebuggerException
{
public:
    const DebuggerExceptionMode m_abortMode;
    const BreakPoint m_eTime;

private:
    DebuggerException(DebuggerExceptionMode abortMode, BreakPoint eTime);

    public:
        ~DebuggerException();

        static DebuggerException CreateAbortEndOfLog();
        static DebuggerException CreateMoveToBP(BreakPoint eTime);
        static DebuggerException CreateErrorAbortRequest(BreakPoint eTime);
};

class VariableHomeLocationInfo
{
public:
    std::string vname;
    const BSQType* vtype;
    Argument location;
};

class EvaluatorFrame
{
public:
#ifdef BSQ_DEBUG_BUILD
    std::pair<int64_t, BreakPoint> dbg_prevreturnbp;
    BreakPoint dbg_prevbp;
    int64_t dbg_currentline;
    StepMode dbg_step_mode;
    std::map<std::string, VariableHomeLocationInfo> dbg_locals;
#endif

    const BSQInvokeDecl* invoke;

    uint8_t* scalarbase;
    uint8_t* mixedbase;
    BSQBool* argmask;
    BSQBool* masksbase;

    const std::vector<InterpOp*>* ops;
    std::vector<InterpOp*>::const_iterator cpos;
    std::vector<InterpOp*>::const_iterator epos;
};

class Evaluator
{
public:
    static jmp_buf g_entrybuff;
    static EvaluatorFrame g_callstack[BSQ_MAX_STACK];
    static uint8_t* g_constantbuffer;

    static std::map<BSQTypeID, const BSQRegex*> g_validators;
    static std::map<std::string, const BSQRegex*> g_regexs;

private:
    EvaluatorFrame* cframe = nullptr;
    int32_t cpos = -1;

public:
    inline StorageLocationPtr evalConstArgument(Argument arg)
    {
        return (StorageLocationPtr)(Evaluator::g_constantbuffer + arg.location);
    }

    inline StorageLocationPtr evalArgument(Argument arg)
    {
        if(arg.kind == ArgumentTag::ScalarVal)
        {
            return this->cframe->scalarbase + arg.location;
        }
        else if(arg.kind == ArgumentTag::MixedVal)
        {
            return this->cframe->mixedbase + arg.location;
        }
        else 
        {
            return evalConstArgument(arg);
        }
    }

    inline StorageLocationPtr evalTargetVar(TargetVar trgt)
    {
        if(trgt.kind == ArgumentTag::ScalarVal)
        {
            return this->cframe->scalarbase + trgt.offset;
        }
        else
        {
            return this->cframe->mixedbase + trgt.offset;
        }
    }

    static inline StorageLocationPtr evalParameterInfo(ParameterInfo pinfo, uint8_t* scalarbase, uint8_t* mixedbase)
    {
        if(pinfo.kind == ArgumentTag::ScalarVal)
        {
            return scalarbase + pinfo.poffset;
        }
        else 
        {
            return mixedbase + pinfo.poffset;
        }
    }

#ifdef BSQ_DEBUG_BUILD
public:
    static DebuggerActionFP fpDebuggerAction;

    int32_t dbg_getCPos()
    { 
        return this->cpos;
    }

    EvaluatorFrame* dbg_getCFrame()
    { 
        return this->cframe;
    }

    int64_t call_count = 0;
    bool debuggerattached = false;
    BreakPoint ttdBreakpoint = {nullptr, 0, -1};
    BreakPoint ttdBreakpoint_LastHit = {nullptr, 0, -1};
    std::vector<BreakPoint> breakpoints;

    std::vector<std::pair<DebuggerCmd, std::string>> dbg_history;

    void reset()
    {

        this->cframe = nullptr;
        this->cpos = -1;

        this->call_count = 0;
        this->ttdBreakpoint_LastHit = {nullptr, 0, -1};          
    }

private:
    bool advanceLineAndProcsssBP(InterpOp* op)
    {
        if(!this->cframe->invoke->isUserCode)
        {
            return false;
        }

        if(op == nullptr || op->sinfo.line == -1)
        {
            return false;
        }

        if(op->sinfo.line == this->cframe->dbg_currentline)
        {
            if(op->tag == OpCodeTag::InvokeFixedFunctionOp || op->tag == OpCodeTag::InvokeVirtualFunctionOp || op->tag == OpCodeTag::InvokeVirtualOperatorOp)
            {
                if(this->cframe->dbg_step_mode == StepMode::StepInto)
                {
                    return true;
                }

                if(this->ttdBreakpoint.line == this->cframe->dbg_currentline && this->call_count == ttdBreakpoint.callCount)
                {
                    this->cframe->dbg_step_mode = StepMode::Step;
                    this->ttdBreakpoint = {nullptr, 0, -1};

                    for(int32_t i = 0; i <= this->cpos; ++i)
                    {
                        if(Evaluator::g_callstack[i].invoke->isUserCode)
                        {
                            Evaluator::g_callstack[i].dbg_step_mode = StepMode::Step;
                        }
                    }

                    return true;
                }
            }

            return false;
        }
        else
        {
            if(this->cframe->dbg_currentline != -1)
            {
                this->cframe->dbg_prevbp = {this->cframe->invoke, this->cframe->dbg_currentline, this->call_count};
            }
            this->cframe->dbg_currentline = (*this->cframe->cpos)->sinfo.line;

            if(this->cframe->dbg_step_mode == StepMode::Step || this->cframe->dbg_step_mode == StepMode::StepInto)
            {
                return true;
            }

            if(this->ttdBreakpoint.line == this->cframe->dbg_currentline && this->call_count == ttdBreakpoint.callCount)
            {
                this->cframe->dbg_step_mode = StepMode::Step;
                this->ttdBreakpoint = {nullptr, 0, -1};

                for(int32_t i = 0; i <= this->cpos; ++i)
                {
                    if(Evaluator::g_callstack[i].invoke->isUserCode)
                    {
                        Evaluator::g_callstack[i].dbg_step_mode = StepMode::Step;
                    }
                }

                return true;
            }

            auto fbp = std::find_if(breakpoints.cbegin(), breakpoints.cend(), [this](const BreakPoint& bp) {
                return bp.line == this->cframe->dbg_currentline && bp.invk->srcFile == this->cframe->invoke->srcFile;
            });

            if(fbp != breakpoints.cend())
            {
                this->ttdBreakpoint_LastHit = {this->cframe->invoke, this->cframe->dbg_currentline, this->call_count};

                if(!this->ttdBreakpoint.isValid())
                {
                    this->cframe->dbg_step_mode = StepMode::Step;

                    for(int32_t i = 0; i < this->cpos; ++i)
                    {
                        if(Evaluator::g_callstack[i].invoke->isUserCode)
                        {
                            Evaluator::g_callstack[i].dbg_step_mode = StepMode::Step;
                        }
                    }

                    return true;
                }
            }

            return false;
        }
    }

    StepMode computeCallIntoStepMode()
    {
        if(this->cframe == nullptr)
        {
            //main entrypoint so do break if debugger is attached
            if(this->debuggerattached && this->ttdBreakpoint.invk == nullptr)
            {
                return StepMode::Step;
            }
            else
            {
                return StepMode::Run;
            }
        }
        else
        {
            if(this->cframe->dbg_step_mode == StepMode::Step)
            {
                return StepMode::Run;
            }
            else if(this->cframe->dbg_step_mode == StepMode::StepInto)
            {
                return StepMode::Step;
            }
            else
            {
                return StepMode::Run;
            }
        }
    }

    BreakPoint computeCurrentBreakpoint() const
    {
        if(this->cframe == nullptr)
        {
            return {nullptr, -1, 0};
        }
        else
        {
            return {this->cframe->invoke, this->cframe->dbg_currentline, this->call_count};
        }
    }

    void computePreviousPositionOnCallReturn()
    {
        if(this->cpos == 0)
        {
            return;
        }

        Evaluator::g_callstack[this->cpos - 1].dbg_prevreturnbp = std::make_pair(Evaluator::g_callstack[this->cpos - 1].dbg_currentline, BreakPoint{this->cframe->invoke, this->cframe->dbg_currentline, this->call_count});
    }

    inline void pushFrame(StepMode smode, const BreakPoint& callerpos, const BSQInvokeDecl* invk, uint8_t* scalarbase, uint8_t* mixedbase, BSQBool* argmask, BSQBool* masksbase, const std::vector<InterpOp*>* ops)
    {
        this->call_count++;

        this->cpos++;
        auto cf = Evaluator::g_callstack + this->cpos;

        cf->dbg_currentline = -1;
        cf->dbg_prevbp = callerpos;
        cf->dbg_prevreturnbp = std::make_pair(-1, callerpos);

        cf->dbg_step_mode = smode;
        
        cf->invoke = invk;
        cf->scalarbase = scalarbase;
        cf->mixedbase = mixedbase;
        cf->argmask = argmask;
        cf->masksbase = masksbase;
        cf->ops = ops;

        cf->cpos = cf->ops->cbegin();
        cf->epos = cf->ops->cend();

        this->cframe = Evaluator::g_callstack + this->cpos;
    }
#else
    inline void pushFrame(const BSQInvokeDecl* invk, uint8_t* scalarbase, uint8_t* mixedbase, BSQBool* argmask, BSQBool* masksbase, const std::vector<InterpOp*>* ops) 
    {
        this->cpos++;

        auto cf = Evaluator::g_callstack + cpos;
        cf->invoke = invk;
        cf->scalarbase = scalarbase;
        cf->mixedbase = mixedbase;
        cf->argmask = argmask;
        cf->masksbase = masksbase;
        cf->ops = ops;

        if constexpr(!isbultin) 
        {
            cf->cpos = cf->ops->cbegin();
            cf->epos = cf->ops->cend();
        }

        this->cframe = Evaluator::g_callstack + this->cpos;
    }
#endif

    inline void popFrame()
    {
        this->cpos--;
        if(this->cpos == -1)
        {
            this->cframe = nullptr;
        }
        else
        {
            this->cframe = Evaluator::g_callstack + this->cpos;
        }
    }

    inline InterpOp* getCurrentOp()
    {
        return *this->cframe->cpos;
    }

    inline bool hasMoreOps() const
    {
        return this->cframe->cpos != this->cframe->epos;
    }

    inline InterpOp* advanceCurrentOp(uint32_t offset)
    {
        this->cframe->cpos += offset;

        if(this->cframe->cpos == this->cframe->epos)
        {
            return nullptr;
        }
        else
        {
            return *this->cframe->cpos;
        }
    }

    inline InterpOp* advanceCurrentOp()
    {
        this->cframe->cpos++;
        return *this->cframe->cpos;
    }

    inline BSQBool* evalMaskLocation(int32_t gmaskoffset)
    {
        if(gmaskoffset < 0)
        {
            return this->cframe->argmask;
        }
        else
        {
            return this->cframe->masksbase + gmaskoffset;
        }
    }

    inline StorageLocationPtr evalGuardVar(int32_t gvaroffset)
    {
        assert(gvaroffset >= 0);

        return this->cframe->scalarbase + gvaroffset;
    }

    inline BSQBool evalGuardStmt(const BSQGuard& guard)
    {
        if(guard.gindex != -1)
        {
            auto maskptr = this->evalMaskLocation(guard.gmaskoffset);
            return maskptr[guard.gindex];
        }
        else {
            return SLPTR_LOAD_CONTENTS_AS(BSQBool, this->evalGuardVar(guard.gvaroffset));
        }
    }

    inline void evalStoreAltValueForGuardStmt(TargetVar trgt, Argument arg, const BSQType* oftype)
    {
        //If this is a clear then the arg should evaluate to the empty constant location
        oftype->storeValue(this->evalTargetVar(trgt), this->evalArgument(arg));
    }

    inline bool tryProcessGuardStmt(TargetVar trgt, const BSQType* trgttype, const BSQStatementGuard& sguard)
    {
        auto gval = this->evalGuardStmt(sguard.guard);
        auto dodefault = !!(sguard.usedefaulton ? gval : !gval);

        if(dodefault)
        {
            this->evalStoreAltValueForGuardStmt(trgt, sguard.defaultvar, trgttype);
        }

        return !dodefault;
    }

    void evalDeadFlowOp();
    void evalAbortOp(const AbortOp* op);
    void evalAssertCheckOp(const AssertOp* op);
    void evalDebugOp(const DebugOp* op);

    void evalLoadUnintVariableValueOp(const LoadUnintVariableValueOp* op);
    void evalNoneInitUnionOp(const NoneInitUnionOp* op);
    void evalStoreConstantMaskValueOp(const StoreConstantMaskValueOp* op);

    template <bool isGuarded>
    void evalDirectAssignOp(const DirectAssignOp* op);

    template <bool isGuarded>
    void evalBoxOp(const BoxOp* op);

    template <bool isGuarded>
    void evalExtractOp(const ExtractOp* op);

    void evalLoadConstOp(const LoadConstOp* op);

    void processTupleDirectLoadAndStore(StorageLocationPtr src, const BSQType* srctype, size_t slotoffset, TargetVar dst, const BSQType* dsttype);
    void processTupleVirtualLoadAndStore(StorageLocationPtr src, const BSQUnionType* srctype, BSQTupleIndex idx, TargetVar dst, const BSQType* dsttype);
    void processRecordDirectLoadAndStore(StorageLocationPtr src, const BSQType* srctype, size_t slotoffset, TargetVar dst, const BSQType* dsttype);
    void processRecordVirtualLoadAndStore(StorageLocationPtr src, const BSQUnionType* srctype, BSQRecordPropertyID propId, TargetVar dst, const BSQType* dsttype);
    void processEntityDirectLoadAndStore(StorageLocationPtr src, const BSQType* srctype, size_t slotoffset, TargetVar dst, const BSQType* dsttype);
    void processEntityVirtualLoadAndStore(StorageLocationPtr src, const BSQUnionType* srctype, BSQFieldID fldId, TargetVar dst, const BSQType* dsttype);

    void processGuardVarStore(const BSQGuard& gv, BSQBool f);

    void evalTupleHasIndexOp(const TupleHasIndexOp* op);
    void evalRecordHasPropertyOp(const RecordHasPropertyOp* op);
    
    void evalLoadTupleIndexDirectOp(const LoadTupleIndexDirectOp* op);
    void evalLoadTupleIndexVirtualOp(const LoadTupleIndexVirtualOp* op);
    void evalLoadTupleIndexSetGuardDirectOp(const LoadTupleIndexSetGuardDirectOp* op);
    void evalLoadTupleIndexSetGuardVirtualOp(const LoadTupleIndexSetGuardVirtualOp* op);

    void evalLoadRecordPropertyDirectOp(const LoadRecordPropertyDirectOp* op);
    void evalLoadRecordPropertyVirtualOp(const LoadRecordPropertyVirtualOp* op);
    void evalLoadRecordPropertySetGuardDirectOp(const LoadRecordPropertySetGuardDirectOp* op);
    void evalLoadRecordPropertySetGuardVirtualOp(const LoadRecordPropertySetGuardVirtualOp* op);

    void evalLoadDirectFieldOp(const LoadEntityFieldDirectOp* op);
    void evalLoadVirtualFieldOp(const LoadEntityFieldVirtualOp* op);

    void evalProjectTupleOp(const ProjectTupleOp* op);
    void evalProjectRecordOp(const ProjectRecordOp* op);
    void evalProjectEntityOp(const ProjectEntityOp* op);

    void evalUpdateTupleOp(const UpdateTupleOp* op);
    void evalUpdateRecordOp(const UpdateRecordOp* op);
    void evalUpdateEntityOp(const UpdateEntityOp* op);

    void evalLoadFromEpehmeralListOp(const LoadFromEpehmeralListOp* op);
    void evalMultiLoadFromEpehmeralListOp(const MultiLoadFromEpehmeralListOp* op);
    void evalSliceEphemeralListOp(const SliceEphemeralListOp* op);

    template <bool isGuarded>
    void evalInvokeFixedFunctionOp(const InvokeFixedFunctionOp* op);

    void evalInvokeVirtualFunctionOp(const InvokeVirtualFunctionOp* op);
    void evalInvokeVirtualOperatorOp(const InvokeVirtualOperatorOp* op);

    void evalConstructorTupleOp(const ConstructorTupleOp* op);
    void evalConstructorTupleFromEphemeralListOp(const ConstructorTupleFromEphemeralListOp* op);
    void evalConstructorRecordOp(const ConstructorRecordOp* op);
    void evalConstructorRecordFromEphemeralListOp(const ConstructorRecordFromEphemeralListOp* op);
    void evalEphemeralListExtendOp(const EphemeralListExtendOp* op);
    void evalConstructorEphemeralListOp(const ConstructorEphemeralListOp* op);
    void evalConstructorEntityDirectOp(const ConstructorEntityDirectOp* op);

    void evalPrefixNotOp(const PrefixNotOp* op);
    void evalAllTrueOp(const AllTrueOp* op);
    void evalSomeTrueOp(const SomeTrueOp* op);

    template <bool isGuarded>
    void evalBinKeyEqFastOp(const BinKeyEqFastOp* op);

    template <bool isGuarded>
    void evalBinKeyEqStaticOp(const BinKeyEqStaticOp* op);
    
    template <bool isGuarded>
    void evalBinKeyEqVirtualOp(const BinKeyEqVirtualOp* op);
    
    void evalBinKeyLessFastOp(const BinKeyLessFastOp* op);
    void evalBinKeyLessStaticOp(const BinKeyLessStaticOp* op);
    void evalBinKeyLessVirtualOp(const BinKeyLessVirtualOp* op);

    template <bool isGuarded>
    void evalIsNoneOp(const TypeIsNoneOp* op);

    template <bool isGuarded>
    void evalIsSomeOp(const TypeIsSomeOp* op);

    template <bool isGuarded>
    void evalIsNothingOp(const TypeIsNothingOp* op);

    template <bool isGuarded>
    void evalTypeTagIsOp(const TypeTagIsOp* op);

    template <bool isGuarded>
    void evalTypeTagSubtypeOfOp(const TypeTagSubtypeOfOp* op);

    InterpOp* evalJumpOp(const JumpOp* op);
    InterpOp* evalJumpCondOp(const JumpCondOp* op);
    InterpOp* evalJumpNoneOp(const JumpNoneOp* op);

    template <bool isGuarded>
    void evalRegisterAssignOp(const RegisterAssignOp* op);

    void evalReturnAssignOp(const ReturnAssignOp* op);
    void evalReturnAssignOfConsOp(const ReturnAssignOfConsOp* op);

    void evalVarLifetimeStartOp(const VarLifetimeStartOp* op);
    void evalVarLifetimeEndOp(const VarLifetimeEndOp* op);
    void evalVarHomeLocationValueUpdate(const VarHomeLocationValueUpdate* op);
    void evaluateOpCode(const InterpOp* op);

    void evaluateOpCodeBlocks();
    void evaluateBody(StorageLocationPtr resultsl, const BSQType* restype, Argument resarg);
    
    void invoke(const BSQInvokeDecl* call, const std::vector<Argument>& args, StorageLocationPtr resultsl, BSQBool* optmask);
    void vinvoke(const BSQInvokeBodyDecl* call, StorageLocationPtr rcvr, const std::vector<Argument>& args, StorageLocationPtr resultsl, BSQBool* optmask);
    
    void invokePrelude(const BSQInvokeBodyDecl* invk, uint8_t* cstack, uint8_t* maskslots, BSQBool* optmask);
    void invokePostlude();

    void evaluatePrimitiveBody(const BSQInvokePrimitiveDecl* invk, const std::vector<StorageLocationPtr>& params, StorageLocationPtr resultsl, const BSQType* restype);

public:
    void invokeGlobalCons(const BSQInvokeBodyDecl* invk, StorageLocationPtr resultsl, const BSQType* restype, Argument resarg);

    static size_t initialMainStackSize(const BSQInvokeBodyDecl* invk);
    void invokeMain(const BSQInvokeBodyDecl* invk, uint8_t* istack, StorageLocationPtr resultsl, const BSQType* restype, Argument resarg);

    void linvoke(const BSQInvokeBodyDecl* call, const std::vector<StorageLocationPtr>& args, StorageLocationPtr resultsl);
    bool iinvoke(const BSQInvokeBodyDecl* call, const std::vector<StorageLocationPtr>& args, BSQBool* optmask);
    void cinvoke(const BSQInvokeBodyDecl* call, const std::vector<StorageLocationPtr>& args, BSQBool* optmask, StorageLocationPtr resultsl);
};

class ICPPParseJSON : public ApiManagerJSON<StorageLocationPtr, Evaluator>
{
private:
    std::vector<std::pair<void*, const BSQType*>> tuplestack;
    std::vector<std::pair<void*, const BSQType*>> recordstack;
    std::vector<std::pair<void*, const BSQType*>> entitystack;
    std::vector<BSQBool*> entitymaskstack;

    std::vector<std::pair<const BSQType*, uint64_t>> containerstack;

    std::vector<std::list<StorageLocationPtr>> parsecontainerstack;
    std::vector<std::list<StorageLocationPtr>::iterator> parsecontainerstackiter;

public:
    ICPPParseJSON(): 
        ApiManagerJSON(), tuplestack(), recordstack(), entitystack(), entitymaskstack(), containerstack(), parsecontainerstack(), parsecontainerstackiter()
    {;}

    virtual ~ICPPParseJSON() {;}

    virtual bool checkInvokeOk(const std::string& checkinvoke, StorageLocationPtr value, Evaluator& ctx) override final;

    virtual bool parseNoneImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual bool parseNothingImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual bool parseBoolImpl(const APIModule* apimodule, const IType* itype, bool b, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual bool parseNatImpl(const APIModule* apimodule, const IType* itype, uint64_t n, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual bool parseIntImpl(const APIModule* apimodule, const IType* itype, int64_t i, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual bool parseBigNatImpl(const APIModule* apimodule, const IType* itype, std::string n, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual bool parseBigIntImpl(const APIModule* apimodule, const IType* itype, std::string i, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual bool parseFloatImpl(const APIModule* apimodule, const IType* itype, std::string f, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual bool parseDecimalImpl(const APIModule* apimodule, const IType* itype, std::string d, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual bool parseRationalImpl(const APIModule* apimodule, const IType* itype, std::string n, uint64_t d, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual bool parseStringImpl(const APIModule* apimodule, const IType* itype, std::string s, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual bool parseByteBufferImpl(const APIModule* apimodule, const IType* itype, uint8_t compress, uint8_t format, std::vector<uint8_t>& data, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual bool parseDateTimeImpl(const APIModule* apimodule, const IType* itype, DateTime t, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual bool parseTickTimeImpl(const APIModule* apimodule, const IType* itype, uint64_t t, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual bool parseLogicalTimeImpl(const APIModule* apimodule, const IType* itype, uint64_t j, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual bool parseUUIDImpl(const APIModule* apimodule, const IType* itype, std::vector<uint8_t> v, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual bool parseContentHashImpl(const APIModule* apimodule, const IType* itype, std::vector<uint8_t> v, StorageLocationPtr value, Evaluator& ctx) override final;
    
    virtual void prepareParseTuple(const APIModule* apimodule, const IType* itype, Evaluator& ctx) override final;
    virtual StorageLocationPtr getValueForTupleIndex(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, size_t i, Evaluator& ctx) override final;
    virtual void completeParseTuple(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;

    virtual void prepareParseRecord(const APIModule* apimodule, const IType* itype, Evaluator& ctx) override final;
    virtual StorageLocationPtr getValueForRecordProperty(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, std::string pname, Evaluator& ctx) override final;
    virtual void completeParseRecord(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;

    virtual void prepareParseContainer(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, size_t count, Evaluator& ctx) override final;
    virtual StorageLocationPtr getValueForContainerElementParse(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, size_t i, Evaluator& ctx) override final;
    virtual void completeParseContainer(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;

    virtual void prepareParseEntity(const APIModule* apimodule, const IType* itype, Evaluator& ctx) override final;
    virtual void prepareParseEntityMask(const APIModule* apimodule, const IType* itype, Evaluator& ctx) override final;
    virtual StorageLocationPtr getValueForEntityField(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, std::pair<std::string, std::string> fnamefkey, Evaluator& ctx) override final;
    virtual void completeParseEntity(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;

    virtual void setMaskFlag(const APIModule* apimodule, StorageLocationPtr flagloc, size_t i, bool flag, Evaluator& ctx) override final;

    virtual StorageLocationPtr parseUnionChoice(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, size_t pick, Evaluator& ctx) override final;

    virtual std::optional<bool> extractBoolImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual std::optional<uint64_t> extractNatImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual std::optional<int64_t> extractIntImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual std::optional<std::string> extractBigNatImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual std::optional<std::string> extractBigIntImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual std::optional<std::string> extractFloatImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual std::optional<std::string> extractDecimalImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual std::optional<std::pair<std::string, uint64_t>> extractRationalImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual std::optional<std::string> extractStringImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual std::optional<std::pair<std::vector<uint8_t>, std::pair<uint8_t, uint8_t>>> extractByteBufferImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual std::optional<DateTime> extractDateTimeImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual std::optional<uint64_t> extractTickTimeImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual std::optional<uint64_t> extractLogicalTimeImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual std::optional<std::vector<uint8_t>> extractUUIDImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual std::optional<std::vector<uint8_t>> extractContentHashImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
    
    virtual StorageLocationPtr extractValueForTupleIndex(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, size_t i, Evaluator& ctx) override final;
    virtual StorageLocationPtr extractValueForRecordProperty(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, std::string pname, Evaluator& ctx) override final;
    virtual StorageLocationPtr extractValueForEntityField(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, std::pair<std::string, std::string> fnamefkey, Evaluator& ctx) override final;

    virtual void prepareExtractContainer(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual std::optional<size_t> extractLengthForContainer(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
    virtual StorageLocationPtr extractValueForContainer(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, size_t i, Evaluator& ctx) override final;
    virtual void completeExtractContainer(const APIModule* apimodule, const IType* itype, Evaluator& ctx) override final;

    virtual std::optional<size_t> extractUnionChoice(const APIModule* apimodule, const IType* itype, StorageLocationPtr intoloc, Evaluator& ctx) override final;
    virtual StorageLocationPtr extractUnionValue(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx) override final;
};
