//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "common.h"

#include <random>
typedef std::default_random_engine RandGenerator;

class SMTParseJSON : public ApiManagerJSON<z3::expr, z3::solver>
{
private:
    std::vector<std::vector<uint8_t>> hashhash;

    RandGenerator rand;
    bool randEnabled;

    std::optional<uint64_t> intBinSearchUnsigned(z3::solver& s, const z3::expr& e, uint64_t min, uint64_t max, const std::vector<uint64_t>& topts);
    std::optional<int64_t> intBinSearchSigned(z3::solver& s, const z3::expr& e, int64_t min, int64_t max, const std::vector<int64_t>& topts);

    std::optional<std::string> expIntAsUInt(z3::solver& s, const z3::expr& e);
    std::optional<uint64_t> expIntAsUIntSmall(z3::solver& s, const z3::expr& e);
    std::optional<std::string> expIntAsInt(z3::solver& s, const z3::expr& e);
    std::optional<int64_t> expIntAsIntSmall(z3::solver& s, const z3::expr& e);

    std::optional<std::string> evalStringAsString(z3::solver& s, const z3::expr& e);
public:
    SMTParseJSON(): 
        ApiManagerJSON(), hashhash()
    {
        const char* SMT_SEED = std::getenv("SMT_RAND_SEED");
        
        //this->randEnabled = SMT_SEED != nullptr;
        //unsigned int vv = (randEnabled ? std::atoi(SMT_SEED) : 0);

        this->randEnabled = true;
        unsigned int vv = 0;

        this->rand.seed(vv);
    }

    static z3::expr generateInitialArgContext(z3::context& c, size_t i)
    {
        auto ii = c.int_val((uint64_t)0);
        auto ij = c.int_val((uint64_t)i);
        return z3::concat(ii.unit(), ij.unit());
    }

    static z3::expr generateInitialResultContext(z3::context& c)
    {
        auto ii = c.int_val((uint64_t)1);
        return ii.unit();
    }

    virtual ~SMTParseJSON() {;}

    virtual bool checkInvokeOk(const std::string& checkinvoke, z3::expr value, z3::solver& ctx) override final;

    virtual bool parseNoneImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseNothingImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseBoolImpl(const APIModule* apimodule, const IType* itype, bool b, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseNatImpl(const APIModule* apimodule, const IType* itype, uint64_t n, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseIntImpl(const APIModule* apimodule, const IType* itype, int64_t i, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseBigNatImpl(const APIModule* apimodule, const IType* itype, std::string n, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseBigIntImpl(const APIModule* apimodule, const IType* itype, std::string i, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseFloatImpl(const APIModule* apimodule, const IType* itype, std::string f, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseDecimalImpl(const APIModule* apimodule, const IType* itype, std::string d, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseRationalImpl(const APIModule* apimodule, const IType* itype, std::string n, uint64_t d, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseStringImpl(const APIModule* apimodule, const IType* itype, std::string s, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseByteBufferImpl(const APIModule* apimodule, const IType* itype, uint8_t compress, uint8_t format, std::vector<uint8_t>& data, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseDateTimeImpl(const APIModule* apimodule, const IType* itype, APIDateTime t, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseUTCDateTimeImpl(const APIModule* apimodule, const IType* itype, APIUTCDateTime t, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseCalendarDateImpl(const APIModule* apimodule, const IType* itype, APICalendarDate t, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseTickTimeImpl(const APIModule* apimodule, const IType* itype, uint64_t t, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseLogicalTimeImpl(const APIModule* apimodule, const IType* itype, uint64_t j, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseISOTimeStampImpl(const APIModule* apimodule, const IType* itype, APIISOTimeStamp t, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseUUID4Impl(const APIModule* apimodule, const IType* itype, std::vector<uint8_t> v, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseUUID7Impl(const APIModule* apimodule, const IType* itype, std::vector<uint8_t> v, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseSHAContentHashImpl(const APIModule* apimodule, const IType* itype, std::vector<uint8_t> v, z3::expr value, z3::solver& ctx) override final;
    virtual bool parseLatLongCoordinateImpl(const APIModule* apimodule, const IType* itype, float latitude, float longitude, z3::expr value, z3::solver& ctx) override final;
    
    virtual bool parseEnumImpl(const APIModule* apimodule, const IType* itype, uint64_t n, z3::expr value, z3::solver& ctx) override final;

    virtual void prepareParseTuple(const APIModule* apimodule, const IType* itype, z3::solver& ctx) override final;
    virtual z3::expr getValueForTupleIndex(const APIModule* apimodule, const IType* itype, z3::expr value, size_t i, z3::solver& ctx) override final;
    virtual void completeParseTuple(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;

    virtual void prepareParseRecord(const APIModule* apimodule, const IType* itype, z3::solver& ctx) override final;
    virtual z3::expr getValueForRecordProperty(const APIModule* apimodule, const IType* itype, z3::expr value, std::string pname, z3::solver& ctx) override final;
    virtual void completeParseRecord(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;

    virtual void prepareParseContainer(const APIModule* apimodule, const IType* itype, z3::expr value, size_t count, z3::solver& ctx) override final;
    virtual z3::expr getValueForContainerElementParse_T(const APIModule* apimodule, const IType* itype, z3::expr value, size_t i, z3::solver& ctx) override final;
    virtual std::pair<z3::expr, z3::expr> getValueForContainerElementParse_KV(const APIModule* apimodule, const IType* itype, z3::expr value, size_t i, z3::solver& ctx) override final;
    virtual void completeParseContainer(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;

    virtual void prepareParseEntity(const APIModule* apimodule, const IType* itype, z3::solver& ctx) override final;
    virtual void prepareParseEntityMask(const APIModule* apimodule, const IType* itype, z3::solver& ctx) override final;
    virtual z3::expr getValueForEntityField(const APIModule* apimodule, const IType* itype, z3::expr value, std::pair<std::string, std::string> fnamefkey, z3::solver& ctx) override final;
    virtual void completeParseEntity(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;

    virtual void setMaskFlag(const APIModule* apimodule, z3::expr flagloc, size_t i, bool flag, z3::solver& ctx) override final;

    virtual z3::expr parseUnionChoice(const APIModule* apimodule, const IType* itype, z3::expr value, size_t pick, const IType* picktype, z3::solver& ctx) override final;

    virtual std::optional<bool> extractBoolImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<uint64_t> extractNatImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<int64_t> extractIntImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<std::string> extractBigNatImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<std::string> extractBigIntImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<std::string> extractFloatImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<std::string> extractDecimalImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<std::pair<std::string, uint64_t>> extractRationalImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<std::string> extractStringImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<std::pair<std::vector<uint8_t>, std::pair<uint8_t, uint8_t>>> extractByteBufferImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<APIDateTime> extractDateTimeImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<APIUTCDateTime> extractUTCDateTimeImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<APICalendarDate> extractCalendarDateImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<uint64_t> extractTickTimeImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<uint64_t> extractLogicalTimeImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<APIISOTimeStamp> extractISOTimeStampImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<std::vector<uint8_t>> extractUUID4Impl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<std::vector<uint8_t>> extractUUID7Impl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<std::vector<uint8_t>> extractSHAContentHashImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<std::pair<float, float>> extractLatLongCoordinateImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;

    virtual std::optional<uint64_t> extractEnumImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;

    virtual z3::expr extractValueForTupleIndex(const APIModule* apimodule, const IType* itype, z3::expr value, size_t i, z3::solver& ctx) override final;
    virtual z3::expr extractValueForRecordProperty(const APIModule* apimodule, const IType* itype, z3::expr value, std::string pname, z3::solver& ctx) override final;
    virtual z3::expr extractValueForEntityField(const APIModule* apimodule, const IType* itype, z3::expr value, std::pair<std::string, std::string> fnamefkey, z3::solver& ctx) override final;

    virtual void prepareExtractContainer(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual std::optional<size_t> extractLengthForContainer(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx) override final;
    virtual z3::expr extractValueForContainer_T(const APIModule* apimodule, const IType* itype, z3::expr value, size_t i, z3::solver& ctx) override final;
    virtual std::pair<z3::expr, z3::expr> extractValueForContainer_KV(const APIModule* apimodule, const IType* itype, z3::expr value, size_t i, z3::solver& ctx) override final;
    virtual void completeExtractContainer(const APIModule* apimodule, const IType* itype, z3::solver& ctx) override final;

    virtual std::optional<size_t> extractUnionChoice(const APIModule* apimodule, const IType* itype, const std::vector<const IType*>& opttypes, z3::expr intoloc, z3::solver& ctx) override final;
    virtual z3::expr extractUnionValue(const APIModule* apimodule, const IType* itype, z3::expr value, size_t uchoice, z3::solver& ctx) override final;
};
