//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "runner.h"

#include <chrono>
#include <iostream>
#include <fstream>

#include <boost/json/src.hpp>

bool loadJSONFromStdIn(const std::string& filename, boost::json::value& jval, boost::json::value& jargs)
{
    std::vector<char> contents;
    std::string line;
    while(getline(std::cin, line))
    {
        std::copy(line.cbegin(), line.cend(), std::back_inserter(contents));
        line.clear();
    }

    auto jv = boost::json::parse(std::string(contents.cbegin(), contents.cend()));
    jval = jv.as_object().at("code");
    jargs = jv.as_object().at("args");

    return true;
}

bool loadJSONFromFile(const std::string& filename, boost::json::value& jval)
{
    std::vector<char> contents;
    std::ifstream file(filename);
    if(!file.is_open())
    {
        return false;
    }

    std::string line;
    while(getline(file, line))
    {
        std::copy(line.cbegin(), line.cend(), std::back_inserter(contents));
        line.clear();
    }
    file.close();

    jval = boost::json::parse(std::string(contents.cbegin(), contents.cend()));
    return true;
}

void initialize(size_t typecount, size_t cbuffsize, const RefMask cmask)
{
    BSQType::g_typetable = (const BSQType**)malloc((BSQ_TYPE_ID_BUILTIN_MAX + typecount) * sizeof(const BSQType*));
    BSQType::g_typetable[BSQ_TYPE_ID_NONE] = BSQType::g_typeNone;
    BSQType::g_typetable[BSQ_TYPE_ID_BOOL] = BSQType::g_typeBool;
    BSQType::g_typetable[BSQ_TYPE_ID_NAT] = BSQType::g_typeNat;
    BSQType::g_typetable[BSQ_TYPE_ID_INT] = BSQType::g_typeInt;
    BSQType::g_typetable[BSQ_TYPE_ID_BIGNAT] = BSQType::g_typeBigNat;
    BSQType::g_typetable[BSQ_TYPE_ID_BIGINT] = BSQType::g_typeBigInt;
    BSQType::g_typetable[BSQ_TYPE_ID_FLOAT] = BSQType::g_typeFloat;
    BSQType::g_typetable[BSQ_TYPE_ID_DECIMAL] = BSQType::g_typeDecimal;
    BSQType::g_typetable[BSQ_TYPE_ID_RATIONAL] = BSQType::g_typeRational;
    BSQType::g_typetable[BSQ_TYPE_ID_STRINGITERATOR] = BSQType::g_typeStringPos;
    BSQType::g_typetable[BSQ_TYPE_ID_STRING] = BSQType::g_typeString;
    BSQType::g_typetable[BSQ_TYPE_ID_BYTEBUFFER] = BSQType::g_typeByteBuffer;
    BSQType::g_typetable[BSQ_TYPE_ID_ISOTIME] = BSQType::g_typeISOTime;
    BSQType::g_typetable[BSQ_TYPE_ID_LOGICALTIME] = BSQType::g_typeLogicalTime;
    BSQType::g_typetable[BSQ_TYPE_ID_UUID] = BSQType::g_typeUUID;
    BSQType::g_typetable[BSQ_TYPE_ID_CONTENTHASH] = BSQType::g_typeContentHash;
    BSQType::g_typetable[BSQ_TYPE_ID_REGEX] = BSQType::g_typeRegex;

    Environment::g_typenameToIDMap["NSCore::None"] = BSQ_TYPE_ID_NONE;
    Environment::g_typenameToIDMap["NSCore::Bool"] = BSQ_TYPE_ID_BOOL;
    Environment::g_typenameToIDMap["NSCore::Nat"] = BSQ_TYPE_ID_NAT;
    Environment::g_typenameToIDMap["NSCore::Int"] = BSQ_TYPE_ID_INT;
    Environment::g_typenameToIDMap["NSCore::BigNat"] = BSQ_TYPE_ID_BIGNAT;
    Environment::g_typenameToIDMap["NSCore::BigInt"] = BSQ_TYPE_ID_BIGINT;
    Environment::g_typenameToIDMap["NSCore::Float"] = BSQ_TYPE_ID_FLOAT;
    Environment::g_typenameToIDMap["NSCore::Decimal"] = BSQ_TYPE_ID_DECIMAL;
    Environment::g_typenameToIDMap["NSCore::Rational"] = BSQ_TYPE_ID_RATIONAL;
    Environment::g_typenameToIDMap["NSCore::StringPos"] = BSQ_TYPE_ID_STRINGITERATOR;
    Environment::g_typenameToIDMap["NSCore::String"] = BSQ_TYPE_ID_STRING;
    Environment::g_typenameToIDMap["NSCore::ByteBuffer"] = BSQ_TYPE_ID_BYTEBUFFER;
    Environment::g_typenameToIDMap["NSCore::ISOTime"] = BSQ_TYPE_ID_ISOTIME;
    Environment::g_typenameToIDMap["NSCore::LogicalTime"] = BSQ_TYPE_ID_LOGICALTIME;
    Environment::g_typenameToIDMap["NSCore::UUID"] = BSQ_TYPE_ID_UUID;
    Environment::g_typenameToIDMap["NSCore::ContentHash"] = BSQ_TYPE_ID_CONTENTHASH;
    Environment::g_typenameToIDMap["NSCore::Regex"] = BSQ_TYPE_ID_REGEX;

    Environment::g_constantbuffer = (uint8_t*)malloc(cbuffsize);
    GC_MEM_ZERO(Environment::g_constantbuffer, cbuffsize);

    Allocator::GlobalAllocator.setGlobalsMemory(Environment::g_constantbuffer, cmask);
}

void initializeLiteral(size_t storageOffset, const BSQType* gtype, std::string& lval)
{
    StorageLocationPtr sl = Environment::g_constantbuffer + storageOffset;
    switch (gtype->tid)
    {
    case BSQ_TYPE_ID_NONE: {
        dynamic_cast<const BSQNoneType*>(BSQType::g_typeNone)->storeValueDirect(sl, BSQNoneValue);
        break;
    }
    case BSQ_TYPE_ID_BOOL: {
        dynamic_cast<const BSQBoolType*>(BSQType::g_typeBool)->storeValueDirect(sl, (BSQBool)(lval == "true"));
        break;
    }
    case BSQ_TYPE_ID_NAT: {
        dynamic_cast<const BSQNatType*>(BSQType::g_typeNat)->storeValueDirect(sl, std::stoull(lval.substr(0, lval.size() - 1)));
        break;
    }
    case BSQ_TYPE_ID_INT: {
        dynamic_cast<const BSQIntType*>(BSQType::g_typeInt)->storeValueDirect(sl, std::stoll(lval.substr(0, lval.size() - 1)));
        break;
    }
    case BSQ_TYPE_ID_BIGNAT: {
        BSQBigNat bn(lval.substr(0, lval.size() - 1));
        dynamic_cast<const BSQBigNatType*>(BSQType::g_typeBigNat)->storeValueDirect(sl, bn);
        break;
    }
    case BSQ_TYPE_ID_BIGINT: {
        BSQBigInt bi(lval.substr(0, lval.size() - 1));
        dynamic_cast<const BSQBigIntType*>(BSQType::g_typeBigInt)->storeValueDirect(sl, bi);
        break;
    }
    case BSQ_TYPE_ID_FLOAT: {
        dynamic_cast<const BSQFloatType*>(BSQType::g_typeFloat)->storeValueDirect(sl, std::stod(lval.substr(0, lval.size() - 1)));
        break;
    }
    case BSQ_TYPE_ID_DECIMAL: {
        dynamic_cast<const BSQDecimalType*>(BSQType::g_typeDecimal)->storeValueDirect(sl, std::stod(lval.substr(0, lval.size() - 1)));
        break;
    }
    case BSQ_TYPE_ID_RATIONAL: {
        assert(false);
        break;
    }
    case BSQ_TYPE_ID_STRING: {
        std::string sstr = lval.substr(1, lval.size() - 2);
        //
        //TODO: need to string unescape here
        //

        BSQString s = g_emptyString;
        if(sstr.size() == 0)
        {
            //already empty
        }
        else if(sstr.size() < 16) 
        {
            s.u_inlineString = BSQInlineString::create((const uint8_t*)sstr.c_str(), sstr.size());
        }
        else if(sstr.size() <= 256)
        {
            auto stp = std::find_if(BSQType::g_typeStringKCons, BSQType::g_typeStringKCons + sizeof(BSQType::g_typeStringKCons), [&sstr](const std::pair<size_t, const BSQType*>& cc) {
                return cc.first >= sstr.size();
            });
            s.u_data = Allocator::GlobalAllocator.allocateDynamic(stp->second);
            BSQ_MEM_COPY(s.u_data, sstr.c_str(), sstr.size());
        }
        else
        {
            //
            //TODO: split the string into multiple parts
            //
            assert(false);
        }

        dynamic_cast<const BSQStringType*>(BSQType::g_typeString)->storeValueDirect(sl, s);
    }
    case BSQ_TYPE_ID_REGEX: {
        assert(false);
        break;
    }
    default:
        assert(false);
        break;
    }
}

void initializeConst(Evaluator& runner, size_t storageOffset, BSQInvokeID ikey, const BSQType* gtype)
{
    auto ccall = dynamic_cast<BSQInvokeBodyDecl*>(Environment::g_invokes[ikey]);
    runner.invokeGlobalCons(ccall, Environment::g_constantbuffer + storageOffset, gtype, ccall->resultArg);
}

std::string loadAssembly(const boost::json::value jv, Evaluator& runner)
{
    ////
    //Initialize builtin stuff
    auto gmaskstr = jsonGetAsString(jv, "cmask");
    auto gmask = (char*)malloc(gmaskstr.size() + 1);
    GC_MEM_COPY(gmask, gmaskstr.c_str(), gmaskstr.size());
    gmask[gmaskstr.size()] = '\0';

    auto typecount = (size_t)jv.as_object().at("typecount").as_int64();
    auto cbuffsize = (size_t)jv.as_object().at("cbuffsize").as_int64();
    initialize(typecount, cbuffsize, gmask);
    
    ////
    //Get all of our name to map ids setup
    auto bultintypecount = Environment::g_typenameToIDMap.size();
    auto tnlist = jv.as_object().at("typenames").as_array();
    std::for_each(tnlist.cbegin(), tnlist.cend(), [bultintypecount](boost::json::value tname) {
        auto tstr = std::string(tname.as_string().c_str());
        if(Environment::g_typenameToIDMap.find(tstr) == Environment::g_typenameToIDMap.cend())
        {
            Environment::g_typenameToIDMap[tstr] = (Environment::g_typenameToIDMap.size() + BSQ_TYPE_ID_BUILTIN_MAX) - bultintypecount;
        }
    });
    
    auto pnlist = jv.as_object().at("propertynames").as_array();
    std::for_each(pnlist.cbegin(), pnlist.cend(), [](boost::json::value pname) {
        auto tstr = std::string(pname.as_string().c_str());
        Environment::g_propertynameToIDMap[tstr] = Environment::g_propertynameToIDMap.size();
        BSQType::g_propertymap[Environment::g_propertynameToIDMap[tstr]] = tstr;
    });

    auto fnlist = jv.as_object().at("fieldnames").as_array();
    std::for_each(fnlist.cbegin(), fnlist.cend(), [](boost::json::value ttype) {
        auto tstr = std::string(ttype.as_string().c_str());
        Environment::g_fieldnameToIDMap[tstr] = Environment::g_fieldnameToIDMap.size();
        BSQType::g_fieldmap[Environment::g_fieldnameToIDMap[tstr]] = tstr;
    });

    auto inlist = jv.as_object().at("invokenames").as_array();
    std::for_each(inlist.cbegin(), inlist.cend(), [](boost::json::value tname) {
        auto tstr = std::string(tname.as_string().c_str());
        Environment::g_invokenameToIDMap[tstr] = Environment::g_invokenameToIDMap.size();
    });

    auto vnlist = jv.as_object().at("vinvokenames").as_array();
    std::for_each(vnlist.cbegin(), vnlist.cend(), [](boost::json::value tname) {
        auto tstr = std::string(tname.as_string().c_str());
        Environment::g_vinvokenameToIDMap[tstr] = Environment::g_vinvokenameToIDMap.size();
    });

    ////
    //Load Types
    auto tdlist = jv.as_object().at("typedecls").as_array();
    std::for_each(tdlist.cbegin(), tdlist.cend(), [](boost::json::value tdecl) {
        jsonLoadBSQTypeDecl(tdecl);
    });

    ////
    //Load Functions
    Environment::g_invokes.resize(Environment::g_invokenameToIDMap.size());
    auto idlist = jv.as_object().at("invdecls").as_array();
    std::for_each(idlist.cbegin(), idlist.cend(), [](boost::json::value idecl) {
        BSQInvokeDecl::jsonLoad(idecl);
    });

    ////
    //Load Literals
    auto ldlist = jv.as_object().at("litdecls").as_array();
    std::for_each(ldlist.cbegin(), ldlist.cend(), [](boost::json::value ldecl) {
        size_t storageOffset;
        const BSQType* gtype; 
        std::string lval;

        jsonLoadBSQLiteralDecl(ldecl, storageOffset, gtype, lval);
        initializeLiteral(storageOffset, gtype, lval);
    });

    ////
    //Load Constants
    auto cdlist = jv.as_object().at("constdecls").as_array();
    std::for_each(cdlist.cbegin(), cdlist.cend(), [&runner](boost::json::value ldecl) {
        size_t storageOffset;
        BSQInvokeID ikey;
        const BSQType* gtype; 
        
        jsonLoadBSQConstantDecl(ldecl, storageOffset, ikey, gtype);
        initializeConst(runner, storageOffset, ikey, gtype);
    });

    auto entrypoint = jsonGetAsString(jv, "entrypoint");
    return entrypoint;
}

BSQInvokeBodyDecl* resolveInvokeForMainName(const std::string& main)
{
    return dynamic_cast<BSQInvokeBodyDecl*>(Environment::g_invokes[Environment::g_invokenameToIDMap[main]]);
}

bool parseJSONArgs(const boost::json::value args, const std::vector<BSQFunctionParameter>& params, uint8_t* argsroot, const std::map<size_t, size_t>& pposmap, std::vector<StorageLocationPtr>& argslocs)
{
    for(size_t i = 0; i < params.size(); ++i)
    {
        StorageLocationPtr trgt = (argsroot + pposmap.at(i));
        bool ok = params[i].ptype->consops.fpJSONParse(params[i].ptype, args.as_array().at(i), trgt);
        if(!ok)
        {
            return false;
        }

        argslocs.push_back(trgt);
    }
    return true;
}

void genRandomArgs(RandGenerator& rnd, const std::vector<BSQFunctionParameter>& params, uint8_t* argsroot, const std::map<size_t, size_t>& pposmap, std::vector<StorageLocationPtr>& argslocs)
{
    for(size_t i = 0; i < params.size(); ++i)
    {
        StorageLocationPtr trgt = (argsroot + pposmap.at(i));
        params[i].ptype->consops.fpGenerateRandom(params[i].ptype, rnd, trgt);

        argslocs.push_back(trgt);
    }
}

bool run(Evaluator& runner, const std::string& main, const boost::json::value& args, std::string& res)
{
    auto filename = std::string("[MAIN INITIALIZE]");
    BSQInvokeBodyDecl* call = resolveInvokeForMainName(main);
    BSQ_LANGUAGE_ASSERT(call != nullptr, &filename, -1, "Could not load given entrypoint");

    size_t argsbytes = call->resultType->allocinfo.inlinedatasize;
    std::string argsmask = call->resultType->allocinfo.inlinedmask;
    std::map<size_t, size_t> pposmap;
    for(size_t i = 0; i < call->params.size(); ++i)
    {
        pposmap[i] = argsbytes;

        argsbytes += call->params[i].ptype->allocinfo.inlinedatasize;
        argsmask += call->params[i].ptype->allocinfo.inlinedmask;
    }

    uint8_t* mframe = (uint8_t*)BSQ_STACK_SPACE_ALLOC(argsbytes);
    GCStack::pushFrame((void**)mframe, argsmask.c_str());

    std::vector<void*> argslocs;
    uint8_t* argsroot = mframe;

    if(setjmp(Environment::g_entrybuff) > 0)
    {
        return false;
    }
    else
    {
        bool argsok = parseJSONArgs(args, call->params, argsroot, pposmap, argslocs);
        BSQ_LANGUAGE_ASSERT(argsok, &filename, -1, "Could not parse entrypoint arguments");

        runner.invokeMain(call, argslocs, mframe, call->resultType, call->resultArg);

        res = call->resultType->fpDisplay(call->resultType, mframe);
        return true;
    }
}

bool fuzzrun(Evaluator& runner, RandGenerator& rnd, BSQInvokeBodyDecl* call, uint8_t* argsroot, const std::map<size_t, size_t>& pposmap, uint8_t* mframe)
{
    if(setjmp(Environment::g_entrybuff) > 0)
    {
        fprintf(stderr, "---Triggered Assertion---\n");
        std::string args = "[";
        for(size_t i = 0; i < call->params.size(); ++i)
        {
            if(i != 0)
            {
                args += ", ";
            }

            auto pp = call->params[i].ptype->fpDisplay(call->params[i].ptype, argsroot + pposmap.at(i));
            args += pp;
        }
        args += "]";

        fprintf(stderr, "%s\n", args.c_str());

        return false;
    }
    else
    {
        std::vector<void*> argslocs;
        genRandomArgs(rnd, call->params, argsroot, pposmap, argslocs);
        runner.invokeMain(call, argslocs, mframe, call->resultType, call->resultArg);

        return true;
    }
}

void fuzz(Evaluator& runner, RandGenerator& rnd, const std::string& main)
{
    auto filename = std::string("[MAIN INITIALIZE]");
    BSQInvokeBodyDecl* call = resolveInvokeForMainName(main);
    BSQ_LANGUAGE_ASSERT(call != nullptr, &filename, -1, "Could not load given entrypoint");

    size_t argsbytes = call->resultType->allocinfo.inlinedatasize;
    std::string argsmask = call->resultType->allocinfo.inlinedmask;
    std::map<size_t, size_t> pposmap;
    for(size_t i = 0; i < call->params.size(); ++i)
    {
        pposmap[i] = argsbytes;

        argsbytes += call->params[i].ptype->allocinfo.inlinedatasize;
        argsmask += call->params[i].ptype->allocinfo.inlinedmask;
    }

    uint8_t* mframe = (uint8_t*)BSQ_STACK_SPACE_ALLOC(argsbytes);
    GCStack::pushFrame((void**)mframe, argsmask.c_str());
 
    uint8_t* argsroot = mframe;

    unsigned failcount = 0;
    for(size_t icount = 0; icount < 10; ++icount)
    {
        bool ok = fuzzrun(runner, rnd, call, argsroot, pposmap, mframe);
        if(!ok)
        {
            failcount++;
        }
    }

    fprintf(stderr, "Ran 10 tests -- %u failures\n", failcount);
}

void parseArgs(int argc, char** argv, std::string& mode, std::string& prog, std::string& input)
{
    if(argc == 2 && std::string(argv[1]) == std::string("stream"))
    {
        mode = "stream";
    }
    else if(argc == 3)
    {
        mode = "run";
        prog = std::string(argv[1]);
        input = std::string(argv[2]);
    }
    else if(argc == 4 && std::string(argv[1]) == std::string("fuzz"))
    {
        mode = "fuzz";
        prog = std::string(argv[2]);
        input = std::string(argv[3]);
    }
    else if(argc == 4 && std::string(argv[1]) == std::string("run"))
    {
        mode = "run";
        prog = std::string(argv[2]);
        input = std::string(argv[3]);
    }
    else
    {
        fprintf(stderr, "Usage: icpp [run] bytecode.bsqir args[]\n");
        fprintf(stderr, "Usage: icpp fuzz bytecode.bsqir\n");
        fflush(stderr);
        exit(1);
    }
}

int main(int argc, char** argv)
{
    std::string mode; 
    std::string prog;
    std::string input;
    parseArgs(argc, argv, mode, prog, input);

    if(mode == "stream")
    {
        boost::json::value jcode;
        boost::json::value jargs;
        bool ok = loadJSONFromStdIn(prog, jcode, jargs);
        if(!ok)
        {
            fprintf(stderr, "Failed to load JSON...\n");
            fflush(stderr);
            exit(1);
        }

        Evaluator runner;
        std::string main = loadAssembly(jcode, runner);

        std::string res;
        bool success = run(runner, main, jargs, res);
        if(success)
        {
            printf("%s", res.c_str());
        }
        else
        {
            printf("!ERROR!");
        }

        return 0;
    }
    else
    {
        boost::json::value jcode;
        bool ok = loadJSONFromFile(prog, jcode);
        if(!ok)
        {
            fprintf(stderr, "Failed to load file %s\n", argv[1]);
            fflush(stderr);
            exit(1);
        }

        Evaluator runner;
        std::string main = loadAssembly(jcode, runner);

        if(mode == "run")
        {
            auto jargs = boost::json::parse(input);

            std::string res;
            auto start = std::chrono::system_clock::now();
            bool success = run(runner, main, jargs, res);
            auto end = std::chrono::system_clock::now();

            auto delta_ms = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
            if(success)
            {
                printf("> %s\n", res.c_str());
            }
            else
            {
                printf("!ERROR!\n");
            }
            printf("Elapsed time %lli...\n", delta_ms);
        }
        else
        {
            unsigned seed = std::chrono::system_clock::now().time_since_epoch().count();
            printf("Fuzzing with seed %u...\n", seed);

            RandGenerator rnd(seed);
            fuzz(runner, rnd, main);
        }

        return 0;
    }
}
