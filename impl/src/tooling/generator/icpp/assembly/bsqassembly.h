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

    const uint32_t maskSlots;

    BSQInvokeDecl(std::string name, std::string iname, BSQInvokeID ikey, std::string srcFile, SourceInfo sinfo, bool recursive, std::vector<BSQFunctionParameter> params, BSQType* resultType, size_t scalarstackBytes, uint32_t refstackSlots, size_t mixedstackBytes, RefMask mixedMask, uint32_t maskSlots)
    : name(name), iname(iname), ikey(ikey), srcFile(srcFile), sinfo(sinfo), recursive(recursive), params(params), resultType(resultType), scalarstackBytes(scalarstackBytes), refstackSlots(refstackSlots), mixedstackBytes(mixedstackBytes), mixedMask(mixedMask), maskSlots(maskSlots)
    {;}

    ~BSQInvokeDecl() {;}

    virtual bool isPrimitive() const = 0;
};

class BSQInvokeBodyDecl : public BSQInvokeDecl 
{
public:
    const std::vector<InterpOp*> body;
    const uint32_t argmaskSize;

    BSQInvokeBodyDecl(std::string name, std::string iname, BSQInvokeID ikey, std::string srcFile, SourceInfo sinfo, bool recursive, std::vector<BSQFunctionParameter> params, BSQType* resultType, size_t scalarstackBytes, uint32_t refstackSlots, size_t mixedstackBytes, RefMask mixedMask, uint32_t maskSlots, std::vector<InterpOp*> body, uint32_t argmaskSize)
    : BSQInvokeDecl(name, iname, ikey, srcFile, sinfo, recursive, params, resultType, scalarstackBytes, refstackSlots, mixedstackBytes, mixedMask, maskSlots), body(body), argmaskSize(argmaskSize)
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
    : BSQInvokeDecl(name, iname, ikey, srcFile, sinfo, recursive, params, resultType, scalarstackBytes, refstackSlots, mixedstackBytes, mixedMask, 0), implkey(implkey), implkeyname(implkeyname), binds(binds), pcodes(pcodes)
    {;}

    ~BSQInvokePrimitiveDecl() {;}

    virtual bool isPrimitive() const override
    {
        return true;
    }
};
