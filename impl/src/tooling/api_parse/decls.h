

#include <assert.h>

#include <cstdlib>
#include <cstdint>
#include <math.h>
#include <ctime>
#include <chrono>
#include <cstdio>

#include <string>
#include <regex>

#include <optional>
#include <vector>
#include <stack>
#include <map>

#include <random>
typedef std::default_random_engine RandGenerator;

#include "json.hpp"
typedef nlohmann::json json;

class IType;
class InvokeSignature;
class APIModule;

enum class TypeTag
{
    NoneTag = 0x0,
    NothingTag,
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
    PrimitiveOfTag,
    DataStringTag,
    ByteBufferTag,
    BufferOfTag,
    DataBufferTag,
    ISOTag,
    LogicalTag,
    UUIDTag,
    ContentHashTag,
    TupleTag,
    RecordTag,
    SomethingTag,
    OkTag,
    ErrTag,
    ListTag,
    StackTag,
    QueueTag,
    SetTag,
    MapTag,
    EnumTag,
    EntityTag,
    UnionTag,
    ConceptTag
};

struct ApiJSON
{
    bool 
    typedef bool (*JSONParseFP)(const BSQType* btype, json, StorageLocationPtr);
};

class IType
{
public:
    const std::string name;

    IType(std::string name) : name(name) {;}
    virtual ~IType() {;}

    static IType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const = 0;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const = 0;
};

class IGroundedType : public IType
{
public:
    IGroundedType(std::string name): IType(name) {;}
    virtual ~IGroundedType() {;}
};

class NoneType : public IGroundedType
{
public:
    NoneType() : IGroundedType("NSCore::None") {;}
    virtual ~NoneType() {;}

    static NoneType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class NothingType : public IGroundedType
{
public:
    NothingType() : IGroundedType("NSCore::Nothing") {;}
    virtual ~NothingType() {;}

    static NothingType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class BoolType : public IGroundedType
{
public:
    BoolType() : IGroundedType("NSCore::Bool") {;}
    virtual ~BoolType() {;}

    static BoolType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class NatType : public IGroundedType
{
public:
    NatType() : IGroundedType("NSCore::Nat") {;}
    virtual ~NatType() {;}

    static NatType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class IntType : public IGroundedType
{
public:
    IntType() : IGroundedType("NSCore::Int") {;}
    virtual ~IntType() {;}

    static IntType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class BigNatType : public IGroundedType
{
public:
    BigNatType() : IGroundedType("NSCore::BigNat") {;}
    virtual ~BigNatType() {;}

    static BigNatType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class BigIntType : public IGroundedType
{
public:
    BigIntType() : IGroundedType("NSCore::BigInt") {;}
    virtual ~BigIntType() {;}

    static BigIntType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class RationalType : public IGroundedType
{
public:
    RationalType() : IGroundedType("NSCore::Rational") {;}
    virtual ~RationalType() {;}

    static RationalType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class FloatType : public IGroundedType
{
public:
    FloatType() : IGroundedType("NSCore::Float") {;}
    virtual ~FloatType() {;}

    static FloatType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class DecimalType : public IGroundedType
{
public:
    DecimalType() : IGroundedType("NSCore::Decimal") {;}
    virtual ~DecimalType() {;}

    static DecimalType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class StringType : public IGroundedType
{
public:
    StringType() : IGroundedType("NSCore::String") {;}
    virtual ~StringType() {;}

    static StringType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class PrimitiveOfType : public IGroundedType
{
public:
    const std::string oftype;
    const std::string usinginv; //may be sentinal "[NO CONSTRUCTOR]"

    PrimitiveOfType(std::string name, std::string oftype, std::string usinginv) : IGroundedType(name), oftype(oftype), usinginv(usinginv) {;}
    virtual ~PrimitiveOfType() {;}

    static PrimitiveOfType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class StringOfType : public IGroundedType
{
public:
    const std::string validator;

    StringOfType(std::string name, std::string validator) : IGroundedType(name), validator(validator) {;}
    virtual ~StringOfType() {;}

    static StringOfType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class DataStringType : public IGroundedType
{
public:
    const std::string oftype;

    DataStringType(std::string name, std::string oftype) : IGroundedType(name), oftype(oftype) {;}
    virtual ~DataStringType() {;}

    static DataStringType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class ByteBufferType : public IGroundedType
{
public:
    ByteBufferType() : IGroundedType("NSCore::ByteBuffer") {;}
    virtual ~ByteBufferType() {;}

    static ByteBufferType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class BufferOfType : public IGroundedType
{
public:
    BufferOfType(std::string name) : IGroundedType(name) {;}
    virtual ~BufferOfType() {;}

    static BufferOfType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class DataBufferType : public IGroundedType
{
public:
    DataBufferType(std::string name) : IGroundedType(name) {;}
    virtual ~DataBufferType() {;}

    static DataBufferType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class ISOTimeType : public IGroundedType
{
public:
    ISOTimeType() : IGroundedType("NSCore::ISOTime") {;}
    virtual ~ISOTimeType() {;}

    static ISOTimeType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class LogicalTimeType : public IGroundedType
{
public:
    LogicalTimeType() : IGroundedType("NSCore::LogicalTime") {;}
    virtual ~LogicalTimeType() {;}

    static LogicalTimeType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j,const z3::expr& ctx,  z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class UUIDType : public IGroundedType
{
public:
    UUIDType() : IGroundedType("NSCore::UUID") {;}
    virtual ~UUIDType() {;}

    static UUIDType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class ContentHashType : public IGroundedType
{
public:
    ContentHashType() : IGroundedType("NSCore::ContentHash") {;}
    virtual ~ContentHashType() {;}

    static ContentHashType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class TupleType : public IGroundedType
{
public:
    const std::vector<std::string> ttypes;

    TupleType(std::string name, std::vector<std::string> ttypes) : IGroundedType(name), ttypes(ttypes) {;}
    virtual ~TupleType() {;}

    static TupleType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class RecordType : public IGroundedType
{
public:
    const std::vector<std::string> props;
    const std::vector<std::string> ttypes;

    RecordType(std::string name, std::vector<std::string> props, std::vector<std::string> ttypes) : IGroundedType(name), props(props), ttypes(ttypes) {;}
    virtual ~RecordType() {;}

    static RecordType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class SomethingType : public IGroundedType
{
public:
    const std::string oftype;

    SomethingType(std::string name, std::string oftype) : IGroundedType(name), oftype(oftype) {;}
    virtual ~SomethingType() {;}

    static SomethingType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class OkType : public IGroundedType
{
public:
    const std::string oftype;

    OkType(std::string name, std::string oftype) : IGroundedType(name), oftype(oftype) {;}
    virtual ~OkType() {;}

    static OkType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class ErrType : public IGroundedType
{
public:
    const std::string oftype;

    ErrType(std::string name, std::string oftype) : IGroundedType(name), oftype(oftype) {;}
    virtual ~ErrType() {;}

    static ErrType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class ListType : public IGroundedType
{
public:
    const std::string oftype;

    ListType(std::string name, std::string oftype) : IGroundedType(name), oftype(oftype) {;}
    virtual ~ListType() {;}

    static ListType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class StackType : public IGroundedType
{
public:
    const std::string oftype;
    const std::string ultype;

    StackType(std::string name, std::string oftype, std::string ultype) : IGroundedType(name), oftype(oftype), ultype(ultype) {;}
    virtual ~StackType() {;}

    static StackType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};


class QueueType : public IGroundedType
{
public:
    const std::string oftype;
    const std::string ultype;

    QueueType(std::string name, std::string oftype, std::string ultype) : IGroundedType(name), oftype(oftype), ultype(ultype) {;}
    virtual ~QueueType() {;}

    static QueueType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class SetType : public IGroundedType
{
public:
    const std::string oftype;
    const std::string ultype;

    const std::string unqchkinv;
    const std::string unqconvinv;

    SetType(std::string name, std::string oftype, std::string ultype, std::string unqchkinv, std::string unqconvinv) : IGroundedType(name), oftype(oftype), ultype(ultype), unqchkinv(unqchkinv), unqconvinv(unqconvinv) {;}
    virtual ~SetType() {;}

    static SetType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class MapType : public IGroundedType
{
public:
    const std::string oftype;
    const std::string ultype;

    const std::string unqchkinv;

    MapType(std::string name, std::string oftype, std::string ultype, std::string unqchkinv) : IGroundedType(name), oftype(oftype), ultype(ultype), unqchkinv(unqchkinv) {;}
    virtual ~MapType() {;}

    static MapType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class EnumType : public IGroundedType
{
public:
    const std::string usinginv;
    const std::vector<std::pair<std::string, uint32_t>> enums;

    EnumType(std::string name, std::string usinginv, std::vector<std::pair<std::string, uint32_t>> enums) : IGroundedType(name), usinginv(usinginv), enums(enums) {;}
    virtual ~EnumType() {;}

    static EnumType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class EntityType : public IGroundedType
{
public:
    const std::vector<std::string> fields;
    const std::vector<std::string> ttypes;

    EntityType(std::string name, std::vector<std::string> fields, std::vector<std::string> ttypes) : IGroundedType(name), fields(fields), ttypes(ttypes) {;}
    virtual ~EntityType() {;}

    static EntityType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class UnionType : public IType
{
public:
    const std::vector<std::string> opts;

    UnionType(std::string name, std::vector<std::string> opts) : IType(name), opts(opts) {;}
    virtual ~UnionType() {;}

    static UnionType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class ConceptType : public IType
{
public:
    const std::vector<std::string> opts;

    ConceptType(std::string name, std::vector<std::string> opts) : IType(name), opts(opts) {;}
    virtual ~ConceptType() {;}

    static ConceptType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class InvokeSignature
{
public:
    const std::string name;
    const IType* restype;
    const std::vector<std::string> argnames;
    const std::vector<const IType*> argtypes;
    
    InvokeSignature(std::string name, const IType* restype, std::vector<std::string> argnames, std::vector<const IType*> argtypes): name(name), restype(restype), argnames(argnames), argtypes(argtypes) {;}

    static InvokeSignature* jparse(json j, const std::map<std::string, const IType*>& typemap);
};

class APIModule
{
public:
    const std::map<std::string, const IType*> typemap;
    const InvokeSignature* api;

    const size_t bv_width;
    const std::map<std::string, std::vector<std::pair<std::string, json>>> constants;

    APIModule(std::map<std::string, const IType*> typemap, InvokeSignature* api, size_t bv_width, std::map<std::string, std::vector<std::pair<std::string, json>>> constants)
    : typemap(typemap), api(api), bv_width(bv_width), constants(constants)
    {
        ;
    }

    ~APIModule()
    {
        for(auto iter = this->typemap.begin(); iter != this->typemap.end(); ++iter)
        {
            delete iter->second;
        }

        delete this->api;
    }

    static APIModule* jparse(json j);
};
