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
    const std::string iname;
    const BSQInvokeID ikey;

    const std::string srcFile;
    const SourceInfo sinfo;
    
    const bool recursive;

    const std::vector<BSQFunctionParameter> params;
    const BSQType* resultType;

    const size_t scalarstackBytes;
    const uint32_t refstackSlots;
    const size_t mixedstackBytes;
    RefMask mixedMask;

    BSQInvokeDecl(std::string name, std::string iname, BSQInvokeID ikey, std::string srcFile, SourceInfo sinfo, bool recursive, std::vector<BSQFunctionParameter> params, BSQType* resultType, size_t scalarstackBytes, uint32_t refstackSlots, size_t mixedstackBytes, RefMask mixedMask)
    : name(name), iname(iname), ikey(ikey), srcFile(srcFile), sinfo(sinfo), recursive(recursive), params(params), resultType(resultType), scalarstackBytes(scalarstackBytes), refstackSlots(refstackSlots), mixedstackBytes(mixedstackBytes), mixedMask(mixedMask)
    {;}

    ~BSQInvokeDecl() {;}

    virtual bool isPrimitive() const = 0;
};

class BSQInvokeBodyDecl : public BSQInvokeDecl 
{
public:
    const std::vector<InterpOp*> body;
    const bool hasMask;

    BSQInvokeBodyDecl(std::string name, std::string iname, BSQInvokeID ikey, std::string srcFile, SourceInfo sinfo, bool recursive, std::vector<BSQFunctionParameter> params, BSQType* resultType, size_t scalarstackBytes, uint32_t refstackSlots, size_t mixedstackBytes, RefMask mixedMask, std::vector<InterpOp*> body, bool hasMask)
    : BSQInvokeDecl(name, iname, ikey, srcFile, sinfo, recursive, params, resultType, scalarstackBytes, refstackSlots, mixedstackBytes, mixedMask), body(body), hasMask(hasMask)
    {;}

    ~BSQInvokeBodyDecl()
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
    const BSQPrimitiveImplTag implkey; 
    const std::string implkeyname;
    const std::map<char, BSQTypeID> binds;
    const std::map<std::string, BSQPCode> pcodes;

    BSQInvokePrimitiveDecl(std::string name, std::string iname, BSQInvokeID ikey, std::string srcFile, SourceInfo sinfo, bool recursive, std::vector<BSQFunctionParameter> params, BSQType* resultType, size_t scalarstackBytes, uint32_t refstackSlots, size_t mixedstackBytes, RefMask mixedMask, BSQPrimitiveImplTag implkey, std::string implkeyname, std::map<char, BSQTypeID> binds, std::map<std::string, BSQPCode> pcodes)
    : BSQInvokeDecl(name, iname, ikey, srcFile, sinfo, recursive, params, resultType, scalarstackBytes, refstackSlots, mixedstackBytes, mixedMask), implkey(implkey), implkeyname(implkeyname), binds(binds), pcodes(pcodes)
    {;}

    ~BSQInvokePrimitiveDecl() {;}

    virtual bool isPrimitive() const override
    {
        return true;
    }
};
