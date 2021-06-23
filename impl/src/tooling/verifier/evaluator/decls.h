

#include <assert.h>

#include <cstdlib>
#include <cstdint>
#include <math.h>

#include <string>

#include <optional>
#include <vector>
#include <map>

#include <random>
typedef std::default_random_engine RandGenerator;

#include "z3++.h"

enum class TypeTag
{
    NoneTag = 0x0,
    BoolTag,
    NatTag,
    IntTag,
    BigNatTag,
    BigIntTag,
    RationalTag,
    FloatTag,
    DecimalTag,
    StringTag,
    StringOfTag,
    NumberOfTag,
    DataStringTag,
    ByteBufferTag,
    BufferTag,
    DataBufferTag,
    ISOTag,
    LogicalTag,
    UUIDTag,
    ContentHashTag
};

class ExtractionInfo
{
public:
    z3::model m;
    std::map<std::string, std::optional<z3::func_decl>> consfuncs;
};

class IType
{
public:
    const std::string name;

    IType(std::string name) : name(name) {;}
    virtual ~IType() {;}

    static IType* jparse(json j);

    virtual json fuzz(RandGenerator& rnd) const = 0;
    virtual json extract(ExtractionInfo* ex, z3::expr ctx) const = 0;

    virtual std::string consprint(json j) const = 0;
};

class NoneType : public IType
{
public:
    NoneType(std::string name) : IType(name) {;}
    virtual ~NoneType() {;}

    static NoneType* jparse(json j);

    virtual json fuzz(RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, z3::expr ctx) const override final;

    virtual std::string consprint(json j) const override final;
};

class BoolType : public IType
{
public:
    BoolType(std::string name) : IType(name) {;}
    virtual ~BoolType() {;}

    virtual json fuzz(RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, z3::expr ctx) const override final;

    virtual std::string consprint(json j) const override final;
};

class NatType : public IType
{
public:
    NatType(std::string name) : IType(name) {;}
    virtual ~NatType() {;}

    virtual json fuzz(RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, z3::expr ctx) const override final;

    virtual std::string consprint(json j) const override final;
};

class IntType : public IType
{

};

class BigNatType : public IType
{

};

class BigIntType : public IType
{

};

class RationalType : public IType
{

};

class FloatType : public IType
{

};

class DecimalType : public IType
{

};

class StringType : public IType
{

};

class StringOfType : public IType
{

};

class NumberOfType : public IType
{

};

class DataStringType : public IType
{

};

class ByteBufferType : public IType
{

};

class BufferType : public IType
{

};

class DataBufferType : public IType
{

};

class ISOType : public IType
{

};

class LogicalType : public IType
{

};

class UUIDType : public IType
{

};

class ContentHashType : public IType
{

};

class RecordType : public IType
{

};

class TupleType : public IType
{

};

class ListType : public IType
{

};

class InvokeSignature
{

};

////
// ------ Need to add in the signature thing
////
