module BSQRuntime exposing (..)

type TypeTag = 
    TypeTag_Invalid
    --TYPE_TAG_DECLS--

ordinalOf : TypeTag -> Int
ordinalOf tt = 
    case tt of 
        --ORDINAL_TAG_DECLS--
        _ -> 
            -1

type AbstractTypeTag = 
    AbstractTypeTag_Invalid
    --ABSTRACT_TYPE_TAG_DECLS--

type TupleIndexTag = 
    TupleIndexTag_Invalid
    --INDEX_TAG_DECLS--

type RecordPropertyTag = 
    RecordPropertyTag_Invalid
    --TYPE_TAG_DECLS--

subtypeOf : TypeTag -> AbstractTypeTag -> Bool
subtypeOf tt oftype = 
    case (tt, oftype) of 
        --SUBTYPE_DECLS--
        _ -> 
            False

hasIndex : TypeTag -> TupleIndexTag -> Bool
hasIndex tt oftype = 
    case (tt, oftype) of 
        --TUPLE_HAS_INDEX_DECLS--
        _ -> 
            False

hasProperty : TypeTag -> RecordPropertyTag -> Bool
hasProperty tt oftype = 
    case (tt, oftype) of 
        --RECORD_HAS_PROPERTY_DECLS--
        _ -> 
            False

real_zero : Float
real_zero = 0.0

real_one : Float
real_one = 1.0

type alias BInt = 
    Int

type alias BNat = 
    Int

type alias BBigInt = 
    Int

type alias BBigNat = 
    Int

type alias BFloat = 
    Float

type alias BDecimal = 
    Float

type alias BRational = 
    Float

type alias BString = 
    String

type alias BTickTime = 
    Int

type alias BLogicalTime = 
    Int

type alias BUUID4 = 
    String

type alias BUUID7 = 
    String

type alias BSHAContentHash = 
    String

type alias BByteBuffer 
    = List Int

type alias BDateTime = 
    {
        year: Int,
        month: Int,
        day: Int,
        hour: Int,
        min: Int,
        tzdata: String
    }

type alias BUTCDateTime = 
    {
        year: Int,
        month: Int,
        day: Int,
        hour: Int,
        min: Int
    }

type alias BCalendarDate = 
    {
        year: Int,
        month: Int,
        day: Int
    }

type alias BRelativeTime = 
    {
        hour: Int,
        min: Int
    }

type alias BISOTimeStamp = 
    {
        year: Int,
        month: Int,
        day: Int,
        hour: Int,
        min: Int,
        sec: Int,
        millis: Int
    }

type alias BLatLongCoordinate = 
    {
        lat: Float,
        long: Float
    }


bInt_zero : BInt
bInt_zero = 
    0

bInt_one : BInt
bInt_one = 
    1

bNat_zero : BNat
bNat_zero = 
    0

bNat_one : BNat
bNat_one = 
    1

bBigInt_zero : BBigInt
bBigInt_zero = 
    0

bBigInt_one : BBigInt
bBigInt_one = 
    1

bBigNat_zero : BBigNat
bBigNat_zero = 
    0

bBigNat_one : BBigNat
bBigNat_one = 
    1

bFloat_zero : BFloat
bFloat_zero = 
    0.0

bFloat_one : BFloat
bFloat_one = 
    1.0

bDecimal_zero : BDecimal
bDecimal_zero = 
    0.0

bDecimal_one : BDecimal
bDecimal_one = 
    1.0

bRational_zero : BRational
bRational_zero = 
    0.0

bRational_one : BRational
bRational_one = 
    1.0

type alias BSQNone = Int

bsqnone_literal : BSQNone
bsqnone_literal = 
    0

type alias BSQNothing = Int

bsqnothing_literal : BSQNone
bsqnothing_literal = 
    0

bsqnone__less : BSQNone -> BSQNone -> Bool
bsqnone__less k1 k2 = 
    False

bool__less : Bool -> Bool -> Bool
bool__less k1 k2 = 
    (not k1) && k2

bint__less : BInt -> BInt -> Bool
bint__less k1 k2 = 
    k1 < k2

bnat__less : BNat -> BNat -> Bool
bnat__less k1 k2 = 
    k1 < k2

bbigint__less : BBigInt -> BBigInt -> Bool
bbigint__less k1 k2 = 
    k1 < k2

bbignat__less : BBigNat -> BBigNat -> Bool
bbignat__less k1 k2 = 
    k1 < k2

bstring__less : BString -> BString -> Bool
bstring__less k1 k2 = 
    k1 < k2

butcdatetime__less : BUTCDateTime -> BUTCDateTime -> Bool
butcdatetime__less k1 k2 = 
    if k1.year /= k2.year then
        k1.year < k2.year else
        if k1.month /= k2.month then 
            k1.month < k2.month else
            if k1.day /= k2.day then
                k1.day < k2.day else
                if k1.hour /= k2.hour then
                    k1.hour < k2.hour else
                    k1.min < k2.min

bcalendardate__less : BCalendarDate -> BCalendarDate -> Bool
bcalendardate__less k1 k2 = 
    if k1.year /= k2.year then
        k1.year < k2.year else
        if k1.month /= k2.month then 
            k1.month < k2.month else
            k1.day < k2.day

brelativetime__less : BRelativeTime -> BRelativeTime -> Bool
brelativetime__less k1 k2 = 
    if k1.hour /= k2.hour then
        k1.hour < k2.hour else
        k1.min < k2.min

bticktime__less : BTickTime -> BTickTime -> Bool
bticktime__less k1 k2 = 
    k1 < k2

blogicaltime__less : BLogicalTime -> BLogicalTime -> Bool
blogicaltime__less k1 k2 = 
    k1 < k2

bisotimestamp__less : BISOTimeStamp -> BISOTimeStamp -> Bool
bisotimestamp__less k1 k2 = 
    if k1.year /= k2.year then
        k1.year < k2.year else
        if k1.month /= k2.month then 
            k1.month < k2.month else
            if k1.day /= k2.day then
                k1.day < k2.day else
                if k1.hour /= k2.hour then
                    k1.hour < k2.hour else
                    if k1.min /= k2.min then
                    k1.min < k2.min else
                    if k1.sec /= k2.sec then
                        k1.sec < k2.sec else
                        k1.millis < k2.millis

buuid4__less : BUUID4 -> BUUID4 -> Bool
buuid4__less k1 k2 = 
    k1 < k2
    
buuid7__less : BUUID7 -> BUUID7 -> Bool
buuid7__less k1 k2 = 
    k1 < k2
    
bshacontenthashtime__less : BSHAContentHash -> BSHAContentHash -> Bool
bshacontenthashtime__less k1 k2 = 
    k1 < k2

