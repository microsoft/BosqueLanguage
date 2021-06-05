//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "bsqtype.h"
#include "bsqop.h"

class MIRConstantDecl 
{
public: 
    const BSQConstantID gkey;
    const uint64_t storageOffset;
    const BSQInvokeID valueInvoke;
    const BSQType* ctype;

    MIRConstantDecl(BSQConstantID gkey, uint64_t storageOffset, BSQInvokeID valueInvoke, BSQType* ctype): gkey(gkey), storageOffset(storageOffset), valueInvoke(valueInvoke), ctype(ctype) {;}
    ~MIRConstantDecl() {;}
};

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
    const Argument resultArg;

    const size_t scalarstackBytes;
    const size_t mixedstackBytes;
    RefMask mixedMask;

    const uint32_t maskSlots;

    BSQInvokeDecl(std::string name, BSQInvokeID ikey, std::string srcFile, SourceInfo sinfo, bool recursive, std::vector<BSQFunctionParameter> params, const BSQType* resultType, Argument resultArg, size_t scalarstackBytes, size_t mixedstackBytes, RefMask mixedMask, uint32_t maskSlots)
    : name(name), ikey(ikey), srcFile(srcFile), sinfo(sinfo), recursive(recursive), params(params), resultType(resultType), resultArg(resultArg), scalarstackBytes(scalarstackBytes), mixedstackBytes(mixedstackBytes), mixedMask(mixedMask), maskSlots(maskSlots)
    {;}

    virtual ~BSQInvokeDecl() {;}

    virtual bool isPrimitive() const = 0;
};

class BSQInvokeBodyDecl : public BSQInvokeDecl 
{
public:
    const std::vector<InterpOp*> body;
    const uint32_t argmaskSize;

    BSQInvokeBodyDecl(std::string name, BSQInvokeID ikey, std::string srcFile, SourceInfo sinfo, bool recursive, std::vector<BSQFunctionParameter> params, const BSQType* resultType, Argument resultArg, size_t scalarstackBytes, size_t mixedstackBytes, RefMask mixedMask, uint32_t maskSlots, std::vector<InterpOp*> body, uint32_t argmaskSize)
    : BSQInvokeDecl(name, ikey, srcFile, sinfo, recursive, params, resultType, resultArg, scalarstackBytes, mixedstackBytes, mixedMask, maskSlots), body(body), argmaskSize(argmaskSize)
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
};

class BSQPCode
{
public:
    const BSQInvokeID code;
    const std::vector<std::string> cargs;

    BSQPCode(BSQInvokeID code, std::vector<std::string> cargs): code(code), cargs(cargs) {;}
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
    const std::map<char, BSQTypeID> binds;
    const std::map<std::string, BSQPCode> pcodes;

    BSQInvokePrimitiveDecl(std::string name, BSQInvokeID ikey, std::string srcFile, SourceInfo sinfo, bool recursive, std::vector<BSQFunctionParameter> params, const BSQType* resultType, Argument resultArg, size_t scalarstackBytes, size_t mixedstackBytes, RefMask mixedMask, uint32_t maskSlots, const BSQType* enclosingtype, BSQPrimitiveImplTag implkey, std::string implkeyname,  std::map<std::string, std::pair<uint32_t, const BSQType*>> scalaroffsetMap, std::map<std::string, std::pair<uint32_t, const BSQType*>> mixedoffsetMap, std::map<char, BSQTypeID> binds, std::map<std::string, BSQPCode> pcodes)
    : BSQInvokeDecl(name, ikey, srcFile, sinfo, recursive, params, resultType, resultArg, scalarstackBytes, mixedstackBytes, mixedMask, maskSlots), enclosingtype(enclosingtype), implkey(implkey), implkeyname(implkeyname), scalaroffsetMap(scalaroffsetMap), mixedoffsetMap(mixedoffsetMap), binds(binds), pcodes(pcodes)
    {;}

    virtual ~BSQInvokePrimitiveDecl() {;}

    virtual bool isPrimitive() const override
    {
        return true;
    }
};
