//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "bsqtype.h"
#include "bsqop.h"

void jsonLoadBSQTypeDecl(boost::json::value v);

void jsonLoadBSQLiteralDecl(boost::json::value v, size_t& storageOffset, const BSQType*& gtype, std::string& lval);
void jsonLoadBSQConstantDecl(boost::json::value v, size_t& storageOffset, BSQInvokeID& ikey, const BSQType*& gtype);

class BSQFunctionParameter 
{
public:
    const std::string name;
    const BSQType* ptype;

    BSQFunctionParameter(std::string name, const BSQType* ptype): name(name), ptype(ptype) {;}
    ~BSQFunctionParameter() {;}
};

class BSQInvokeDecl 
{
public:
    const std::string name;
    const BSQInvokeID ikey;

    const std::string srcFile;
    const SourceInfo sinfo;
    
    const bool recursive;

    const std::vector<BSQFunctionParameter> params;
    const BSQType* resultType;

    const size_t scalarstackBytes;
    const size_t mixedstackBytes;
    RefMask mixedMask;

    const uint32_t maskSlots;

    BSQInvokeDecl(std::string name, BSQInvokeID ikey, std::string srcFile, SourceInfo sinfo, bool recursive, std::vector<BSQFunctionParameter> params, const BSQType* resultType, size_t scalarstackBytes, size_t mixedstackBytes, RefMask mixedMask, uint32_t maskSlots)
    : name(name), ikey(ikey), srcFile(srcFile), sinfo(sinfo), recursive(recursive), params(params), resultType(resultType), scalarstackBytes(scalarstackBytes), mixedstackBytes(mixedstackBytes), mixedMask(mixedMask), maskSlots(maskSlots)
    {;}

    virtual ~BSQInvokeDecl() {;}

    virtual bool isPrimitive() const = 0;

    static void jsonLoad(boost::json::value v);
};

class BSQInvokeBodyDecl : public BSQInvokeDecl 
{
public:
    const std::vector<InterpOp*> body;
    const uint32_t argmaskSize;

    const Argument resultArg;

    BSQInvokeBodyDecl(std::string name, BSQInvokeID ikey, std::string srcFile, SourceInfo sinfo, bool recursive, std::vector<BSQFunctionParameter> params, const BSQType* resultType, Argument resultArg, size_t scalarstackBytes, size_t mixedstackBytes, RefMask mixedMask, uint32_t maskSlots, std::vector<InterpOp*> body, uint32_t argmaskSize)
    : BSQInvokeDecl(name, ikey, srcFile, sinfo, recursive, params, resultType, scalarstackBytes, mixedstackBytes, mixedMask, maskSlots), body(body), argmaskSize(argmaskSize), resultArg(resultArg)
    {;}

    virtual ~BSQInvokeBodyDecl()
    {
        std::for_each(this->body.begin(), this->body.end(), [](InterpOp* op) {
            delete(op);
        });
    }

    virtual bool isPrimitive() const override
    {
        return false;
    }

    static BSQInvokeBodyDecl* jsonLoad(boost::json::value v);
};

class BSQPCode
{
public:
    const BSQInvokeID code;
    const std::vector<Argument> cargs;

    BSQPCode(BSQInvokeID code, std::vector<Argument> cargs): code(code), cargs(cargs) {;}
    ~BSQPCode() {;}
};

class BSQInvokePrimitiveDecl : public BSQInvokeDecl 
{
public:
    const BSQType* enclosingtype;
    const BSQPrimitiveImplTag implkey; 
    const std::string implkeyname;
    const std::map<std::string, std::pair<uint32_t, const BSQType*>> scalaroffsetMap;
    const std::map<std::string, std::pair<uint32_t, const BSQType*>> mixedoffsetMap;
    const std::map<std::string, const BSQType*> binds;
    const std::map<std::string, BSQPCode*> pcodes;

    BSQInvokePrimitiveDecl(std::string name, BSQInvokeID ikey, std::string srcFile, SourceInfo sinfo, bool recursive, std::vector<BSQFunctionParameter> params, const BSQType* resultType, size_t scalarstackBytes, size_t mixedstackBytes, RefMask mixedMask, uint32_t maskSlots, const BSQType* enclosingtype, BSQPrimitiveImplTag implkey, std::string implkeyname, std::map<std::string, std::pair<uint32_t, const BSQType*>> scalaroffsetMap, std::map<std::string, std::pair<uint32_t, const BSQType*>> mixedoffsetMap, std::map<std::string, const BSQType*> binds, std::map<std::string, BSQPCode*> pcodes)
    : BSQInvokeDecl(name, ikey, srcFile, sinfo, recursive, params, resultType, scalarstackBytes, mixedstackBytes, mixedMask, maskSlots), enclosingtype(enclosingtype), implkey(implkey), implkeyname(implkeyname), scalaroffsetMap(scalaroffsetMap), mixedoffsetMap(mixedoffsetMap), binds(binds), pcodes(pcodes)
    {;}

    virtual ~BSQInvokePrimitiveDecl() {;}

    virtual bool isPrimitive() const override
    {
        return true;
    }

    static BSQInvokePrimitiveDecl* jsonLoad(boost::json::value v);
};
