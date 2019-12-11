//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
#include "bsqruntime.h"

namespace BSQ
{
//%%STATIC_STRING_CREATE%%

//%%STATIC_INT_CREATE%%

const char* Runtime::propertyNames[] = {
    "Invalid",
//%%PROPERTY_NAMES
};

constexpr const char* s_nominaltypenames[] = {
    "[INVALID]",
//%%NOMINAL_TYPE_DISPLAY_NAMES
};

std::u32string Runtime::diagnostic_format(Value v)
{
    if(BSQ_IS_VALUE_NONE(v))
    {
        return std::u32string(U"none");
    }
    else if(BSQ_IS_VALUE_BOOL(v))
    {
        return BSQ_GET_VALUE_BOOL(v) ? std::u32string(U"true") : std::u32string(U"false");
    }
    else if(BSQ_IS_VALUE_INT(v))
    {
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return conv.from_bytes(std::to_string(BSQ_GET_VALUE_INT(v)));
    }
    else
    {
        const BSQRef* vv = BSQ_GET_VALUE_PTR(v, const BSQRef);
        if(dynamic_cast<const BSQString*>(vv) != nullptr)
        {
            auto sstr = dynamic_cast<const BSQString*>(vv);
            return std::u32string(U"\"") + std::u32string(sstr->sdata.cbegin(), sstr->sdata.cend()) + std::u32string(U"\"");
        }
        else if(dynamic_cast<const BSQStringOf*>(vv) != nullptr)
        {
            std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
            auto sof = dynamic_cast<const BSQStringOf*>(vv);

            return conv.from_bytes(s_nominaltypenames[(uint32_t)sof->oftype]) + std::u32string(U"'") + sof->sdata + std::u32string(U"'");
        }
        else if(dynamic_cast<const BSQPODBuffer*>(vv) != nullptr)
        {
            auto pbuf = dynamic_cast<const BSQPODBuffer*>(vv);
            std::u32string rvals(U"PODBuffer{");
            for (size_t i = 0; i < pbuf->sdata.size(); ++i)
            {
                if(i != 0)
                {
                    rvals += U", ";
                }

                rvals += pbuf->sdata[i];
            }
            rvals += U"}";

            return rvals;
        }
        else if(dynamic_cast<const BSQGUID*>(vv) != nullptr)
        {
            auto guid = dynamic_cast<const BSQGUID*>(vv);
            return std::u32string(U"GUID@") + std::u32string(guid->sdata.cbegin(), guid->sdata.cend());
        }
        else if(dynamic_cast<const BSQEnum*>(vv) != nullptr)
        {
            std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
            auto ev = dynamic_cast<const BSQEnum*>(vv);

            return conv.from_bytes(s_nominaltypenames[(uint32_t)ev->oftype]) + std::u32string(U"::") + conv.from_bytes(ev->ename);
        }
        else if(dynamic_cast<const BSQIdKey*>(vv) != nullptr)
        {
            std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
            auto idv = dynamic_cast<const BSQIdKey*>(vv);

            return conv.from_bytes(s_nominaltypenames[(uint32_t)idv->oftype]) + std::u32string(U"@") + Runtime::diagnostic_format(idv->sdata);
        }
        else if(dynamic_cast<const BSQTuple*>(vv) != nullptr)
        {
            auto tv = dynamic_cast<const BSQTuple*>(vv);
            std::u32string tvals(U"[");
            for(size_t i = 0; i < tv->entries.size(); ++i)
            {
                if(i != 0)
                {
                    tvals += U", ";
                }

                tvals += Runtime::diagnostic_format(tv->entries.at(i));
            }
            tvals += U"]";

            return tvals;
        }
        else if(dynamic_cast<const BSQRecord*>(vv) != nullptr)
        {
            std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;

            auto rv = dynamic_cast<const BSQRecord*>(vv);
            std::u32string rvals(U"{");
            for(size_t i = 0; i < rv->entries.size(); ++i)
            {
                if(i != 0)
                {
                    rvals += U", ";
                }

                rvals += conv.from_bytes(Runtime::propertyNames[(int32_t)rv->entries.at(i).first]) + U"=" + Runtime::diagnostic_format(rv->entries.at(i).second);
            }
            rvals += U"}";

            return rvals;
        }
        else
        {
            auto obj = dynamic_cast<const BSQObject*>(vv);
            if (dynamic_cast<const BSQList*>(obj) != nullptr)
            {
                std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
                auto list = dynamic_cast<const BSQList*>(obj);

                std::u32string ls(U"{");
                for (size_t i = 0; i < list->entries.size(); ++i)
                {
                    if (i != 0)
                    {
                        ls += U", ";
                    }

                    ls += Runtime::diagnostic_format(list->entries.at(i));
                }
                ls += U"}";

                return conv.from_bytes(s_nominaltypenames[(uint32_t) obj->ntype]) + ls;
            }
            else if (dynamic_cast<const BSQSet*>(obj) != nullptr)
            {
                std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
                auto set = dynamic_cast<const BSQSet*>(obj);

                std::u32string ss(U"{");
                bool first = true;
                for (auto iter = set->entries.cbegin(); iter != set->entries.cend(); ++iter)
                {
                    if (!first)
                    {
                        ss += U", ";
                    }
                    first = false;

                    ss += Runtime::diagnostic_format(iter->second);
                }
                ss += U"}";

                return conv.from_bytes(s_nominaltypenames[(uint32_t) obj->ntype]) + ss;
            }
            else if (dynamic_cast<const BSQMap*>(obj) != nullptr)
            {
                std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
                auto map = dynamic_cast<const BSQMap*>(vv);

                std::u32string ms(U"{");
                bool first = true;
                for (auto iter = map->entries.cbegin(); iter != map->entries.cend(); ++iter)
                {
                    if (!first)
                    {
                        ms += U", ";
                    }
                    first = false;

                    ms += Runtime::diagnostic_format(iter->second);
                }
                ms += U"}";

                return conv.from_bytes(s_nominaltypenames[(uint32_t) obj->ntype]) + ms;
            }
            else
            {
                std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;

                return conv.from_bytes(s_nominaltypenames[(uint32_t) obj->ntype]) + obj->display();
            }
        }
    }
}
} // namespace BSQ
