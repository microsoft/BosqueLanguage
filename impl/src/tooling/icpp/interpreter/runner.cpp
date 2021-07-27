//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "runner.h"

#include <chrono>
#include <iostream>
#include <fstream>

std::optional<json> getIRFromStdIn()
{
    try
    {
        json payload;
        std::cin >> payload;

        return std::make_optional(payload);
    }
    catch(...)
    {
        return std::nullopt;
    }
}

std::optional<json> getIRFromFile(const std::string& file)
{
    try
    {
        json payload;
        std::ifstream infile(file);
        infile >> payload;

        return std::make_optional(payload);
    }
    catch(const std::exception& e)
    {
        return std::nullopt;
    }
}

void initialize(size_t typecount, size_t cbuffsize, const RefMask cmask)
{
    Environment::g_typenameToIDMap["NSCore::None"] = {BSQ_TYPE_ID_NONE, BSQType::g_typeNone};
    Environment::g_typenameToIDMap["NSCore::Bool"] = {BSQ_TYPE_ID_BOOL, BSQType::g_typeBool};
    Environment::g_typenameToIDMap["NSCore::Nat"] = {BSQ_TYPE_ID_NAT, BSQType::g_typeNat};
    Environment::g_typenameToIDMap["NSCore::Int"] = {BSQ_TYPE_ID_INT, BSQType::g_typeInt};
    Environment::g_typenameToIDMap["NSCore::BigNat"] = {BSQ_TYPE_ID_BIGNAT, BSQType::g_typeBigNat};
    Environment::g_typenameToIDMap["NSCore::BigInt"] = {BSQ_TYPE_ID_BIGINT, BSQType::g_typeBigInt};
    Environment::g_typenameToIDMap["NSCore::Float"] = {BSQ_TYPE_ID_FLOAT, BSQType::g_typeFloat};
    Environment::g_typenameToIDMap["NSCore::Decimal"] = {BSQ_TYPE_ID_DECIMAL, BSQType::g_typeDecimal};
    Environment::g_typenameToIDMap["NSCore::Rational"] = {BSQ_TYPE_ID_RATIONAL, BSQType::g_typeRational};
    Environment::g_typenameToIDMap["NSCore::StringPos"] = {BSQ_TYPE_ID_STRINGITERATOR, BSQType::g_typeStringPos};
    Environment::g_typenameToIDMap["NSCore::String"] = {BSQ_TYPE_ID_STRING, BSQType::g_typeString};
    Environment::g_typenameToIDMap["NSCore::ByteBuffer"] = {BSQ_TYPE_ID_BYTEBUFFER, BSQType::g_typeByteBuffer};
    Environment::g_typenameToIDMap["NSCore::ISOTime"] = {BSQ_TYPE_ID_ISOTIME, BSQType::g_typeISOTime};
    Environment::g_typenameToIDMap["NSCore::LogicalTime"] = {BSQ_TYPE_ID_LOGICALTIME, BSQType::g_typeLogicalTime};
    Environment::g_typenameToIDMap["NSCore::UUID"] = {BSQ_TYPE_ID_UUID, BSQType::g_typeUUID};
    Environment::g_typenameToIDMap["NSCore::ContentHash"] = {BSQ_TYPE_ID_CONTENTHASH, BSQType::g_typeContentHash};
    Environment::g_typenameToIDMap["NSCore::Regex"] = {BSQ_TYPE_ID_REGEX, BSQType::g_typeRegex};

    Environment::g_typenameToIDMap["[STR_K16]"] = {BSQ_TYPE_ID_STRINGREPR_K16, BSQType::g_typeStringKRepr16};
    Environment::g_typenameToIDMap["[STR_K32]"] = {BSQ_TYPE_ID_STRINGREPR_K32, BSQType::g_typeStringKRepr32};
    Environment::g_typenameToIDMap["[STR_K64]"] = {BSQ_TYPE_ID_STRINGREPR_K64, BSQType::g_typeStringKRepr64};
    Environment::g_typenameToIDMap["[STR_K96]"] = {BSQ_TYPE_ID_STRINGREPR_K96, BSQType::g_typeStringKRepr96};
    Environment::g_typenameToIDMap["[STR_K128]"] = {BSQ_TYPE_ID_STRINGREPR_K128, BSQType::g_typeStringKRepr128};
    Environment::g_typenameToIDMap["[STR_K256]"] = {BSQ_TYPE_ID_STRINGREPR_K256, BSQType::g_typeStringKRepr256};
    Environment::g_typenameToIDMap["[STR_SLICE]"] = {BSQ_TYPE_ID_STRINGREPR_SLICE, BSQType::g_typeStringSliceRepr};
    Environment::g_typenameToIDMap["[STR_CONCAT]"] = {BSQ_TYPE_ID_STRINGREPR_CONCAT, BSQType::g_typeStringConcatRepr};

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
        dynamic_cast<const BSQBigNatType*>(BSQType::g_typeBigNat)->storeValueDirect(sl, std::stoull(lval.substr(0, lval.size() - 1)));
        break;
    }
    case BSQ_TYPE_ID_BIGINT: {
        dynamic_cast<const BSQBigIntType*>(BSQType::g_typeBigInt)->storeValueDirect(sl, std::stoll(lval.substr(0, lval.size() - 1)));
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
                return cc.first > sstr.size();
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
        break;
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

std::string loadAssembly(json j, Evaluator& runner)
{
    ////
    //Initialize builtin stuff
    auto gmaskstr = j["cmask"].get<std::string>();
    auto gmask = (char*)malloc(gmaskstr.size() + 1);
    GC_MEM_COPY(gmask, gmaskstr.c_str(), gmaskstr.size());
    gmask[gmaskstr.size()] = '\0';

    auto typecount = j["typecount"].get<size_t>();
    auto cbuffsize = j["cbuffsize"].get<size_t>();
    initialize(typecount, cbuffsize, gmask);
    
    ////
    //Get all of our name to map ids setup
    auto tnlist = j["typenames"];
    std::for_each(tnlist.cbegin(), tnlist.cend(), [](json tname) {
        auto tstr = tname.get<std::string>();
        if(Environment::g_typenameToIDMap.find(tstr) == Environment::g_typenameToIDMap.cend())
        {
            Environment::g_typenameToIDMap[tstr] = {(BSQTypeID)Environment::g_typenameToIDMap.size(), nullptr};
        }
    });
    
    auto pnlist = j["propertynames"];
    std::for_each(pnlist.cbegin(), pnlist.cend(), [](json pname) {
        auto tstr = pname.get<std::string>();
        Environment::g_propertynameToIDMap[tstr] = Environment::g_propertynameToIDMap.size();
        BSQType::g_propertymap[Environment::g_propertynameToIDMap[tstr]] = tstr;
    });

    auto fnlist = j["fieldnames"];
    std::for_each(fnlist.cbegin(), fnlist.cend(), [](json fname) {
        auto tstr = fname.get<std::string>();
        Environment::g_fieldnameToIDMap[tstr] = Environment::g_fieldnameToIDMap.size();
        BSQType::g_fieldmap[Environment::g_fieldnameToIDMap[tstr]] = tstr;
    });

    auto inlist = j["invokenames"];
    std::for_each(inlist.cbegin(), inlist.cend(), [](json iname) {
        auto tstr = iname.get<std::string>();
        Environment::g_invokenameToIDMap[tstr] = Environment::g_invokenameToIDMap.size();
    });

    auto vnlist = j["vinvokenames"];
    std::for_each(vnlist.cbegin(), vnlist.cend(), [](json vname) {
        auto tstr = vname.get<std::string>();
        Environment::g_vinvokenameToIDMap[tstr] = Environment::g_vinvokenameToIDMap.size();
    });

    ////
    //Load Types
    auto tdlist = j["typedecls"];
    std::for_each(tdlist.cbegin(), tdlist.cend(), [](json tdecl) {
        jsonLoadBSQTypeDecl(tdecl);
    });

    BSQType::g_typetable = (const BSQType**)mi_zalloc(Environment::g_typenameToIDMap.size() * sizeof(const BSQType*));
    std::for_each(Environment::g_typenameToIDMap.cbegin(), Environment::g_typenameToIDMap.cend(), [](const std::pair<std::string, std::pair<BSQTypeID, const BSQType*>>& entry) {
        BSQType::g_typetable[entry.second.first] = entry.second.second;
    });

    ////
    //Load Functions
    Environment::g_invokes.resize(Environment::g_invokenameToIDMap.size());
    auto idlist = j["invdecls"];
    std::for_each(idlist.cbegin(), idlist.cend(), [](json idecl) {
        BSQInvokeDecl::jsonLoad(idecl);
    });

    ////
    //Load Literals
    auto ldlist = j["litdecls"];
    std::for_each(ldlist.cbegin(), ldlist.cend(), [](json ldecl) {
        size_t storageOffset;
        const BSQType* gtype; 
        std::string lval;

        jsonLoadBSQLiteralDecl(ldecl, storageOffset, gtype, lval);
        initializeLiteral(storageOffset, gtype, lval);
    });

    ////
    //Load Constants
    auto cdlist = j["constdecls"];
    std::for_each(cdlist.cbegin(), cdlist.cend(), [&runner](json ldecl) {
        size_t storageOffset;
        BSQInvokeID ikey;
        const BSQType* gtype; 
        
        jsonLoadBSQConstantDecl(ldecl, storageOffset, ikey, gtype);
        initializeConst(runner, storageOffset, ikey, gtype);
    });

    auto entrypoint = j["entrypoint"].get<std::string>();
    return entrypoint;
}

BSQInvokeBodyDecl* resolveInvokeForMainName(const std::string& main)
{
    return dynamic_cast<BSQInvokeBodyDecl*>(Environment::g_invokes[Environment::g_invokenameToIDMap[main]]);
}

bool parseJSONArgs(json args, const std::vector<BSQFunctionParameter>& params, uint8_t* argsroot, const std::map<size_t, size_t>& pposmap, std::vector<StorageLocationPtr>& argslocs)
{
    for(size_t i = 0; i < params.size(); ++i)
    {
        StorageLocationPtr trgt = (argsroot + pposmap.at(i));
        auto pptype = params[i].ptype;
        bool ok = pptype->consops.fpJSONParse(pptype, args[i], trgt);
        if(!ok)
        {
            return false;
        }

        argslocs.push_back(trgt);
    }
    return true;
}

bool run(Evaluator& runner, const std::string& main, json args, std::string& res)
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

void parseArgs(int argc, char** argv, std::string& mode, std::string& prog, std::string& input)
{
    if(argc == 2 && std::string(argv[1]) == std::string("--stream"))
    {
        mode = "stream";
    }
    else if(argc == 3)
    {
        mode = "run";
        prog = std::string(argv[1]);
        input = std::string(argv[2]);
    }
    else
    {
        fprintf(stderr, "Usage: icpp bytecode.bsqir args[]\n");
        fprintf(stderr, "Usage: icpp --stream\n");
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
        auto payload = getIRFromStdIn();
        if(!payload.has_value() || !payload.value().contains("code") || !payload.value().contains("args"))
        {
            fprintf(stderr, "Failed to load JSON...\n");
            fflush(stderr);
            exit(1);
        }

        json jcode = payload.value()["code"];
        json jargs = payload.value()["args"];

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
        auto cc = getIRFromFile(prog);
        if(!cc.has_value())
        {
            fprintf(stderr, "Failed to load file %s\n", argv[1]);
            fflush(stderr);
            exit(1);
        }

        json jcode = cc.value();

        Evaluator runner;
        std::string main = loadAssembly(jcode, runner);

        auto jargs = json::parse(input);

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
        printf("Elapsed time %i...\n", (int)delta_ms);

        return 0;
    }
}
