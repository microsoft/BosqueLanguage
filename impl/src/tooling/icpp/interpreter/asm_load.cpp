//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "asm_load.h"

const BSQType* jsonLoadBoxedStructType(json v)
{
    auto tstr = v["tkey"].get<std::string>();
    auto tid = MarshalEnvironment::g_typenameToIdMap.find(tstr)->second;

    auto name = v["name"].get<std::string>();

    auto oftypeid = v["oftype"].get<BSQTypeID>();
    auto oftype = dynamic_cast<const BSQStructType*>(BSQType::g_typetable[oftypeid]);

    return new BSQBoxedStructType(tid, oftype, name);
}

void initialize(size_t cbuffsize, const RefMask cmask)
{
    MarshalEnvironment::g_typenameToIdMap["None"] = BSQ_TYPE_ID_NONE;
    MarshalEnvironment::g_typenameToIdMap["Nothing"] = BSQ_TYPE_ID_NOTHING;
    MarshalEnvironment::g_typenameToIdMap["Bool"] = BSQ_TYPE_ID_BOOL;
    MarshalEnvironment::g_typenameToIdMap["Nat"] = BSQ_TYPE_ID_NAT;
    MarshalEnvironment::g_typenameToIdMap["Int"] = BSQ_TYPE_ID_INT;
    MarshalEnvironment::g_typenameToIdMap["BigNat"] = BSQ_TYPE_ID_BIGNAT;
    MarshalEnvironment::g_typenameToIdMap["BigInt"] = BSQ_TYPE_ID_BIGINT;
    MarshalEnvironment::g_typenameToIdMap["Float"] = BSQ_TYPE_ID_FLOAT;
    MarshalEnvironment::g_typenameToIdMap["Decimal"] = BSQ_TYPE_ID_DECIMAL;
    MarshalEnvironment::g_typenameToIdMap["Rational"] = BSQ_TYPE_ID_RATIONAL;
    MarshalEnvironment::g_typenameToIdMap["String"] = BSQ_TYPE_ID_STRING;
    MarshalEnvironment::g_typenameToIdMap["@ByteBufferLeaf"] = BSQ_TYPE_ID_BYTEBUFFER_LEAF;
    MarshalEnvironment::g_typenameToIdMap["@ByteBufferNode"] = BSQ_TYPE_ID_BYTEBUFFER_NODE;
    MarshalEnvironment::g_typenameToIdMap["ByteBuffer"] = BSQ_TYPE_ID_BYTEBUFFER;
    MarshalEnvironment::g_typenameToIdMap["DateTime"] = BSQ_TYPE_ID_DATETIME;
    MarshalEnvironment::g_typenameToIdMap["TickTime"] = BSQ_TYPE_ID_TICKTIME;
    MarshalEnvironment::g_typenameToIdMap["LogicalTime"] = BSQ_TYPE_ID_LOGICALTIME;
    MarshalEnvironment::g_typenameToIdMap["UUID"] = BSQ_TYPE_ID_UUID;
    MarshalEnvironment::g_typenameToIdMap["ContentHash"] = BSQ_TYPE_ID_CONTENTHASH;
    MarshalEnvironment::g_typenameToIdMap["Regex"] = BSQ_TYPE_ID_REGEX;

    MarshalEnvironment::g_typenameToIdMap["@StringK16"] = BSQ_TYPE_ID_STRINGREPR_K16;
    MarshalEnvironment::g_typenameToIdMap["@StringK32"] = BSQ_TYPE_ID_STRINGREPR_K32;
    MarshalEnvironment::g_typenameToIdMap["@StringK64"] = BSQ_TYPE_ID_STRINGREPR_K64;
    MarshalEnvironment::g_typenameToIdMap["@StringK96"] = BSQ_TYPE_ID_STRINGREPR_K96;
    MarshalEnvironment::g_typenameToIdMap["@StringK128"] = BSQ_TYPE_ID_STRINGREPR_K128;
    MarshalEnvironment::g_typenameToIdMap["@StringTree"] = BSQ_TYPE_ID_STRINGREPR_TREE;

    Evaluator::g_constantbuffer = (uint8_t*)mi_zalloc(cbuffsize);
    GC_MEM_ZERO(Evaluator::g_constantbuffer, cbuffsize);

    Allocator::GlobalAllocator.setGlobalsMemory(Evaluator::g_constantbuffer, cmask);
}

void initializeLiteral(size_t storageOffset, const BSQType* gtype, std::string& lval)
{
    StorageLocationPtr sl = Evaluator::g_constantbuffer + storageOffset;
    switch (gtype->tid)
    {
    case BSQ_TYPE_ID_NONE: {
        dynamic_cast<const BSQRegisterType<BSQNone>*>(BSQWellKnownType::g_typeNone)->storeValueDirect(sl, BSQNoneValue);
        break;
    }
    case BSQ_TYPE_ID_NOTHING: {
        dynamic_cast<const BSQRegisterType<BSQNothing>*>(BSQWellKnownType::g_typeNothing)->storeValueDirect(sl, BSQNoneValue);
        break;
    }
    case BSQ_TYPE_ID_BOOL: {
        dynamic_cast<const BSQRegisterType<BSQBool>*>(BSQWellKnownType::g_typeBool)->storeValueDirect(sl, (BSQBool)(lval == "true"));
        break;
    }
    case BSQ_TYPE_ID_NAT: {
        dynamic_cast<const BSQRegisterType<BSQNat>*>(BSQWellKnownType::g_typeNat)->storeValueDirect(sl, std::stoull(lval.substr(0, lval.size() - 1)));
        break;
    }
    case BSQ_TYPE_ID_INT: {
        dynamic_cast<const BSQRegisterType<BSQInt>*>(BSQWellKnownType::g_typeInt)->storeValueDirect(sl, std::stoll(lval.substr(0, lval.size() - 1)));
        break;
    }
    case BSQ_TYPE_ID_BIGNAT: {
        dynamic_cast<const BSQBigNumType<BSQBigNat>*>(BSQWellKnownType::g_typeBigNat)->storeValueDirect(sl, std::stoull(lval.substr(0, lval.size() - 1)));
        break;
    }
    case BSQ_TYPE_ID_BIGINT: {
        dynamic_cast<const BSQBigNumType<BSQBigInt>*>(BSQWellKnownType::g_typeBigInt)->storeValueDirect(sl, std::stoll(lval.substr(0, lval.size() - 1)));
        break;
    }
    case BSQ_TYPE_ID_FLOAT: {
        dynamic_cast<const  BSQRegisterType<BSQFloat>*>(BSQWellKnownType::g_typeFloat)->storeValueDirect(sl, std::stod(lval.substr(0, lval.size() - 1)));
        break;
    }
    case BSQ_TYPE_ID_DECIMAL: {
        dynamic_cast<const  BSQRegisterType<BSQDecimal>*>(BSQWellKnownType::g_typeDecimal)->storeValueDirect(sl, std::stod(lval.substr(0, lval.size() - 1)));
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
        else if(sstr.size() <= 128)
        {
            auto stp = BSQStringKReprTypeAbstract::selectKReprForSize(sstr.size());

            s.u_data = Allocator::GlobalAllocator.allocateDynamic(stp);
            BSQ_MEM_COPY(s.u_data, sstr.c_str(), sstr.size());
        }
        else
        {
            //
            //TODO: split the string into multiple parts
            //
            assert(false);
        }

        dynamic_cast<const BSQStringImplType*>(BSQWellKnownType::g_typeString)->storeValueDirect(sl, s);
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
    auto ccall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[ikey]);
    runner.invokeGlobalCons(ccall, Evaluator::g_constantbuffer + storageOffset, gtype, ccall->resultArg);
}

void loadAssembly(json j, Evaluator& ee)
{
    ////
    //Initialize builtin stuff
    auto gmaskstr = j["cmask"].get<std::string>();
    auto gmask = (char*)malloc(gmaskstr.size() + 1);
    GC_MEM_COPY(gmask, gmaskstr.c_str(), gmaskstr.size());
    gmask[gmaskstr.size()] = '\0';

    auto cbuffsize = j["cbuffsize"].get<size_t>();
    initialize(cbuffsize, gmask);
    
    ////
    //Get all of our name to map ids setup
    auto tnlist = j["typenames"];
    std::for_each(tnlist.cbegin(), tnlist.cend(), [](json tname) {
        auto tstr = tname.get<std::string>();
        if(MarshalEnvironment::g_typenameToIdMap.find(tstr) == MarshalEnvironment::g_typenameToIdMap.cend())
        {
            MarshalEnvironment::g_typenameToIdMap[tstr] = (BSQTypeID)MarshalEnvironment::g_typenameToIdMap.size();
        }
    });
    
    auto pnlist = j["propertynames"];
    std::for_each(pnlist.cbegin(), pnlist.cend(), [](json pname) {
        auto tstr = pname.get<std::string>();
        MarshalEnvironment::g_propertyToIdMap[tstr] = MarshalEnvironment::g_propertyToIdMap.size();
        BSQRecordInfo::g_propertynamemap[MarshalEnvironment::g_propertyToIdMap[tstr]] = tstr;
    });

    auto fnlist = j["fieldnames"];
    std::for_each(fnlist.cbegin(), fnlist.cend(), [](json fname) {
        auto tstr = fname.get<std::string>();
        MarshalEnvironment::g_fieldToIdMap[tstr] = MarshalEnvironment::g_fieldToIdMap.size();
    });

    auto fdecls = j["fielddecls"];
    std::for_each(fdecls.cbegin(), fdecls.cend(), [](json fdecl) {
        xxxx;
    });

    auto inlist = j["invokenames"];
    std::for_each(inlist.cbegin(), inlist.cend(), [](json iname) {
        auto tstr = iname.get<std::string>();
        MarshalEnvironment::g_invokeToIdMap[tstr] = MarshalEnvironment::g_invokeToIdMap.size();
    });

    auto vnlist = j["vinvokenames"];
    std::for_each(vnlist.cbegin(), vnlist.cend(), [](json vname) {
        auto tstr = vname.get<std::string>();
        MarshalEnvironment::g_vinvokeToIdMap[tstr] = MarshalEnvironment::g_vinvokeToIdMap.size();
    });

    ////
    //Load Types
    BSQType::g_typetable = (const BSQType**)mi_zalloc(MarshalEnvironment::g_typenameToIdMap.size() * sizeof(const BSQType*));
    BSQType::g_typetable[BSQ_TYPE_ID_NONE] = BSQWellKnownType::g_typeNone;
    BSQType::g_typetable[BSQ_TYPE_ID_NOTHING] = BSQWellKnownType::g_typeNothing;
    BSQType::g_typetable[BSQ_TYPE_ID_BOOL] = BSQWellKnownType::g_typeBool;
    BSQType::g_typetable[BSQ_TYPE_ID_NAT] = BSQWellKnownType::g_typeNat;
    BSQType::g_typetable[BSQ_TYPE_ID_INT] = BSQWellKnownType::g_typeInt;
    BSQType::g_typetable[BSQ_TYPE_ID_BIGNAT] = BSQWellKnownType::g_typeBigNat;
    BSQType::g_typetable[BSQ_TYPE_ID_BIGINT] = BSQWellKnownType::g_typeBigInt;
    BSQType::g_typetable[BSQ_TYPE_ID_FLOAT] = BSQWellKnownType::g_typeFloat;
    BSQType::g_typetable[BSQ_TYPE_ID_DECIMAL] = BSQWellKnownType::g_typeDecimal;
    BSQType::g_typetable[BSQ_TYPE_ID_RATIONAL] = BSQWellKnownType::g_typeRational;
    BSQType::g_typetable[BSQ_TYPE_ID_STRING] = BSQWellKnownType::g_typeString;
    BSQType::g_typetable[BSQ_TYPE_ID_BYTEBUFFER_LEAF] = BSQWellKnownType::g_typeByteBufferLeaf;
    BSQType::g_typetable[BSQ_TYPE_ID_BYTEBUFFER_NODE] = BSQWellKnownType::g_typeByteBufferNode;
    BSQType::g_typetable[BSQ_TYPE_ID_BYTEBUFFER] = BSQWellKnownType::g_typeByteBuffer;
    BSQType::g_typetable[BSQ_TYPE_ID_DATETIME] = BSQWellKnownType::g_typeDateTime;
    BSQType::g_typetable[BSQ_TYPE_ID_TICKTIME] = BSQWellKnownType::g_typeTickTime;
    BSQType::g_typetable[BSQ_TYPE_ID_LOGICALTIME] = BSQWellKnownType::g_typeLogicalTime;
    BSQType::g_typetable[BSQ_TYPE_ID_UUID] = BSQWellKnownType::g_typeUUID;
    BSQType::g_typetable[BSQ_TYPE_ID_CONTENTHASH] = BSQWellKnownType::g_typeContentHash;
    BSQType::g_typetable[BSQ_TYPE_ID_REGEX] = BSQWellKnownType::g_typeRegex;

    BSQType::g_typetable[BSQ_TYPE_ID_STRINGREPR_K16] = BSQWellKnownType::g_typeStringKRepr16;
    BSQType::g_typetable[BSQ_TYPE_ID_STRINGREPR_K32] = BSQWellKnownType::g_typeStringKRepr32;
    BSQType::g_typetable[BSQ_TYPE_ID_STRINGREPR_K64] = BSQWellKnownType::g_typeStringKRepr64;
    BSQType::g_typetable[BSQ_TYPE_ID_STRINGREPR_K96] = BSQWellKnownType::g_typeStringKRepr96;
    BSQType::g_typetable[BSQ_TYPE_ID_STRINGREPR_K128] = BSQWellKnownType::g_typeStringKRepr128; 
    BSQType::g_typetable[BSQ_TYPE_ID_STRINGREPR_TREE] = BSQWellKnownType::g_typeStringTreeRepr;

    auto tdlist = j["typedecls"];
    std::for_each(tdlist.cbegin(), tdlist.cend(), [](json tdecl) {
        jsonLoadBSQTypeDecl(tdecl);
    });

    auto boxedlist = j["boxeddecls"];
    std::for_each(boxedlist.cbegin(), boxedlist.cend(), [](json tdecl) {
        jsonLoadBoxedStructType(tdecl);
    });

    auto lflavoflist = j["listflavors"];
    std::for_each(lflavoflist.cbegin(), lflavoflist.cend(), [](json tdecl) {
        xxxx;
    });

    auto mflavorlist = j["mapflavors"];
    std::for_each(mflavorlist.cbegin(), mflavorlist.cend(), [](json tdecl) {
        xxxx;
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