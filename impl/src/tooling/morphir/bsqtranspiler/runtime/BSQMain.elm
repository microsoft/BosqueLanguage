
module BSQMain exposing (..)

import Regex exposing(..)

type TypeTag = 
    TypeTag_Invalid
--TYPE_TAG_DECLS--

ordinalOf : TypeTag -> Int
ordinalOf tt = 
    case tt of 
--ORDINAL_TYPE_TAG_DECLS--
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
--PROPERTY_TAG_DECLS--

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

type alias BByteBuffer = 
    {
        format: Int,
        compress: Int,
        data: List Int
    }

bbytebuffer_cons : Int -> Int -> List Int -> BByteBuffer
bbytebuffer_cons f c d = 
    {format = f, compress = c, data = d}

type alias BDateTime = 
    {
        year: Int,
        month: Int,
        day: Int,
        hour: Int,
        min: Int,
        tzdata: String
    }

bdatetime_cons : Int -> Int -> Int -> Int -> Int -> String -> BDateTime
bdatetime_cons yy mm dd h m tz = 
    {year = yy, month = mm, day = dd, hour = h, min = m, tzdata = tz}

type alias BUTCDateTime = 
    {
        year: Int,
        month: Int,
        day: Int,
        hour: Int,
        min: Int
    }

butcdatetime_cons : Int -> Int -> Int -> Int -> Int -> BUTCDateTime
butcdatetime_cons yy mm dd h m = 
    {year = yy, month = mm, day = dd, hour = h, min = m}

type alias BCalendarDate = 
    {
        year: Int,
        month: Int,
        day: Int
    }

bcalendardate_cons : Int -> Int -> Int -> BCalendarDate
bcalendardate_cons yy mm dd = 
    {year = yy, month = mm, day = dd}

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

bisotimestamp_cons : Int -> Int -> Int -> Int -> Int -> Int -> Int -> BISOTimeStamp
bisotimestamp_cons yy mm dd h m s ms= 
    {year = yy, month = mm, day = dd, hour = h, min = m, sec = s, millis = ms}

type alias BLatLongCoordinate = 
    {
        lat: Float,
        long: Float
    }

blatlongcoordinate_cons : Float -> Float -> BLatLongCoordinate
blatlongcoordinate_cons latv longv = 
    {lat = latv, long = longv}

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

type alias BNone = Int

bsqnone_literal : BNone
bsqnone_literal = 
    0

type alias BNothing = Int

bsqnothing_literal : BNothing
bsqnothing_literal = 
    0

bsqnone_less : BNone -> BNone -> Bool
bsqnone_less _ _ = 
    False

--OF_TYPE_DECLS--

bool_less : Bool -> Bool -> Bool
bool_less k1 k2 = 
    (not k1) && k2

bint_less : BInt -> BInt -> Bool
bint_less k1 k2 = 
    k1 < k2

bnat_less : BNat -> BNat -> Bool
bnat_less k1 k2 = 
    k1 < k2

bbigint_less : BBigInt -> BBigInt -> Bool
bbigint_less k1 k2 = 
    k1 < k2

bbignat_less : BBigNat -> BBigNat -> Bool
bbignat_less k1 k2 = 
    k1 < k2

bstring_less : BString -> BString -> Bool
bstring_less k1 k2 = 
    k1 < k2

butcdatetime_less : BUTCDateTime -> BUTCDateTime -> Bool
butcdatetime_less k1 k2 = 
    if k1.year /= k2.year then
        k1.year < k2.year else
        if k1.month /= k2.month then 
            k1.month < k2.month else
            if k1.day /= k2.day then
                k1.day < k2.day else
                if k1.hour /= k2.hour then
                    k1.hour < k2.hour else
                    k1.min < k2.min

bcalendardate_less : BCalendarDate -> BCalendarDate -> Bool
bcalendardate_less k1 k2 = 
    if k1.year /= k2.year then
        k1.year < k2.year else
        if k1.month /= k2.month then 
            k1.month < k2.month else
            k1.day < k2.day

bticktime_less : BTickTime -> BTickTime -> Bool
bticktime_less k1 k2 = 
    k1 < k2

blogicaltime_less : BLogicalTime -> BLogicalTime -> Bool
blogicaltime_less k1 k2 = 
    k1 < k2

bisotimestamp_less : BISOTimeStamp -> BISOTimeStamp -> Bool
bisotimestamp_less k1 k2 = 
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

buuid4_less : BUUID4 -> BUUID4 -> Bool
buuid4_less k1 k2 = 
    k1 < k2
    
buuid7_less : BUUID7 -> BUUID7 -> Bool
buuid7_less k1 k2 = 
    k1 < k2
    
bshacontenthashtime_less : BSHAContentHash -> BSHAContentHash -> Bool
bshacontenthashtime_less k1 k2 = 
    k1 < k2

bsqbnone_default : BNone
bsqbnone_default = 
    0

bsqbnothing_default : BNothing
bsqbnothing_default = 
    0

bsqbool_default : Bool
bsqbool_default = 
    False

bsqbint_default : BInt 
bsqbint_default = 
    0

bsqbnat_default : BNat
bsqbnat_default = 
    0

bsqbbigint_default : BBigInt 
bsqbbigint_default = 
    0

bsqbbignat_default : BBigNat
bsqbbignat_default = 
    0

bsqbfloat_default : BFloat
bsqbfloat_default = 
    0.0

bsqbdecimal_default : BDecimal
bsqbdecimal_default = 
    0.0

bsqbrational_default : BRational
bsqbrational_default = 
    0.0

bsqbstring_default : BString
bsqbstring_default = 
    ""

bsqbticktime_default : BTickTime
bsqbticktime_default = 
    0

bsqblogicaltime_default : BLogicalTime
bsqblogicaltime_default = 
    0

bsqbuuid4_default : BUUID4
bsqbuuid4_default = 
    "0x0"

bsqbuuid7_default : BUUID7
bsqbuuid7_default = 
    "0x0"

bsqbshacontenthash_default : BSHAContentHash
bsqbshacontenthash_default = 
    "0x0"

bsqbbytebuffer_default : BByteBuffer
bsqbbytebuffer_default = 
    {format = 0, compress = 0, data = []}

bsqbdatetime_default : BDateTime
bsqbdatetime_default = 
    {
        year = 0,
        month = 0,
        day = 0,
        hour = 0,
        min = 0,
        tzdata = "UTC"
    }

bsqbutcdatetime_default : BUTCDateTime
bsqbutcdatetime_default =  
    {
        year = 0,
        month = 0,
        day = 0,
        hour = 0,
        min = 0
    }

bsqbcalendardate_default : BCalendarDate
bsqbcalendardate_default = 
    {
        year = 0,
        month = 0,
        day = 0
    }

bsqbisotimestamp_default : BISOTimeStamp
bsqbisotimestamp_default = 
    {
        year = 0,
        month = 0,
        day = 0,
        hour = 0,
        min = 0,
        sec = 0,
        millis = 0
    }

bsqblatlongcoordinate_default : BLatLongCoordinate
bsqblatlongcoordinate_default = 
    {
        lat = 0.0,
        long = 0.0
    }

type BKeyObject = 
    BKeyInvalid
    | BKeyNone_box
    | BKeyBool_box Bool
    | BKeyBInt_box BInt
    | BKeyBNat_box BNat
    | BKeyBBigInt_box BBigInt
    | BKeyBBigNat_box BBigNat
    | BKeyBString_box BString
    | BKeyBUTCDateTime_box BUTCDateTime
    | BKeyBCalendarDate_box BCalendarDate
    | BKeyBTickTime_box BTickTime
    | BKeyBLogicalTime_box BLogicalTime
    | BKeyBISOTimeStamp_box BISOTimeStamp
    | BKeyBUUID4_box BUUID4
    | BKeyBUUID7_box BUUID7
    | BKeyBSHAContentHash_box BSHAContentHash
--KEY_BOX_OPS--

unbox_BKeyBool : BKeyObject -> Bool
unbox_BKeyBool k =
    case k of 
        BKeyBool_box b -> 
            b
        _ -> 
            False

unbox_BKeyBInt : BKeyObject -> BInt
unbox_BKeyBInt k =
    case k of 
        BKeyBInt_box i -> 
            i
        _ -> 
            0

unbox_BKeyBNat : BKeyObject -> BNat
unbox_BKeyBNat k =
    case k of 
        BKeyBNat_box n -> 
            n
        _ -> 
            0

unbox_BKeyBBigInt : BKeyObject -> BBigInt
unbox_BKeyBBigInt k =
    case k of 
        BKeyBBigInt_box i -> 
            i
        _ -> 
            0

unbox_BKeyBBigNat : BKeyObject -> BBigNat
unbox_BKeyBBigNat k =
    case k of 
        BKeyBBigNat_box n -> 
            n
        _ -> 
            0

unbox_BKeyBString : BKeyObject -> BString
unbox_BKeyBString k =
    case k of 
        BKeyBString_box s -> 
            s
        _ -> 
            ""

unbox_BKeyBUTCDateTime : BKeyObject -> BUTCDateTime
unbox_BKeyBUTCDateTime k =
    case k of 
        BKeyBUTCDateTime_box t -> 
            t
        _ -> 
            bsqbutcdatetime_default


unbox_BKeyBCalendarDate : BKeyObject -> BCalendarDate
unbox_BKeyBCalendarDate k =
    case k of 
        BKeyBCalendarDate_box t -> 
            t
        _ -> 
            bsqbcalendardate_default

unbox_BKeyBTickTime : BKeyObject -> BTickTime
unbox_BKeyBTickTime k =
    case k of 
        BKeyBTickTime_box t -> 
            t
        _ -> 
            bsqbticktime_default

unbox_BKeyBLogicalTime : BKeyObject -> BLogicalTime
unbox_BKeyBLogicalTime k =
    case k of 
        BKeyBLogicalTime_box t -> 
            t
        _ -> 
            bsqblogicaltime_default

unbox_BKeyBISOTimeStamp : BKeyObject -> BISOTimeStamp
unbox_BKeyBISOTimeStamp k =
    case k of 
        BKeyBISOTimeStamp_box t -> 
            t
        _ -> 
            bsqbisotimestamp_default


unbox_BKeyBUUID4 : BKeyObject -> BUUID4
unbox_BKeyBUUID4 k =
    case k of 
        BKeyBUUID4_box u -> 
            u
        _ -> 
            bsqbuuid4_default

unbox_BKeyBUUID7 : BKeyObject -> BUUID7
unbox_BKeyBUUID7 k =
    case k of 
        BKeyBUUID7_box u -> 
            u
        _ -> 
            bsqbuuid7_default

unbox_BKeyBSHAContentHash : BKeyObject -> BSHAContentHash
unbox_BKeyBSHAContentHash k =
    case k of 
        BKeyBSHAContentHash_box h -> 
            h
        _ -> 
            bsqbshacontenthash_default

--KEY_UNBOX_OPS--

--KEY_DEFAULT_OPS--

type BKey = 
    BKey TypeTag BKeyObject

bkey_extract_value : BKey -> BKeyObject
bkey_extract_value k = 
    let (BKey _ obj) = k in obj

bkey_none : BKey
bkey_none = 
    BKey TypeTag_None BKeyNone_box

bsqbkey_default : BKey
bsqbkey_default = 
    bkey_none
        
bkey_less : BKey -> BKey -> Bool
bkey_less k1 k2 = 
    let (BKey tag1 obj1) = k1 in
    let (BKey tag2 obj2) = k2 in
    if tag1 /= tag2 then
        (ordinalOf tag1) < (ordinalOf tag2) else
        case obj1 of
            BKeyNone_box -> 
                False
            BKeyBool_box b1 -> 
                case obj2 of 
                    BKeyBool_box b2 -> 
                        bool_less b1 b2
                    _ -> 
                        False
            BKeyBInt_box i1 -> 
                case obj2 of 
                    BKeyBInt_box i2 -> 
                        bint_less i1 i2
                    _ -> 
                        False
            BKeyBNat_box n1 -> 
                case obj2 of 
                    BKeyBNat_box n2 -> 
                        bnat_less n1 n2
                    _ -> 
                        False
            BKeyBBigInt_box i1 -> 
                case obj2 of 
                    BKeyBBigInt_box i2 -> 
                        bbigint_less i1 i2
                    _ -> 
                        False
            BKeyBBigNat_box n1 -> 
                case obj2 of 
                    BKeyBBigNat_box n2 -> 
                        bbignat_less n1 n2
                    _ -> 
                        False
            BKeyBString_box s1 -> 
                case obj2 of 
                    BKeyBString_box s2 -> 
                        bstring_less s1 s2
                    _ -> 
                        False
            BKeyBUTCDateTime_box d1 -> 
                case obj2 of 
                    BKeyBUTCDateTime_box d2 -> 
                        butcdatetime_less d1 d2
                    _ -> 
                        False
            BKeyBCalendarDate_box d1 -> 
                case obj2 of 
                    BKeyBCalendarDate_box d2 -> 
                        bcalendardate_less d1 d2
                    _ -> 
                        False
            BKeyBTickTime_box t1 -> 
                case obj2 of 
                    BKeyBTickTime_box t2 -> 
                        bticktime_less t1 t2
                    _ -> 
                        False
            BKeyBLogicalTime_box t1 -> 
                case obj2 of 
                    BKeyBLogicalTime_box t2 -> 
                        blogicaltime_less t1 t2
                    _ -> 
                        False
            BKeyBISOTimeStamp_box t1 -> 
                case obj2 of 
                    BKeyBISOTimeStamp_box t2 -> 
                        bisotimestamp_less t1 t2
                    _ -> 
                        False
            BKeyBUUID4_box id1 -> 
                case obj2 of 
                    BKeyBUUID4_box id2 -> 
                        buuid4_less id1 id2
                    _ -> 
                        False
            BKeyBUUID7_box id1 -> 
                case obj2 of 
                    BKeyBUUID7_box id2 -> 
                        buuid7_less id1 id2
                    _ -> 
                        False
            BKeyBSHAContentHash_box h1 -> 
                case obj2 of 
                    BKeyBSHAContentHash_box h2 -> 
                        bshacontenthashtime_less h1 h2
                    _ -> 
                        False
            _ -> 
                False

--TUPLE_TYPE_DECLS--
--RECORD_TYPE_DECLS--
--TYPE_DECLS--

type BObject = 
    BObjectBNothing_box
    | BObjectBFloat_box BFloat
    | BObjectBDecimal_box BDecimal
    | BObjectBRational_box BRational
    | BObjectBByteBuffer_box BByteBuffer
    | BObjectBDateTime_box BDateTime
    | BObjectBLatLongCoordinate_box BLatLongCoordinate
    | BObjectRegex_box Regex.Regex
--TUPLE_TYPE_BOXING--
--RECORD_TYPE_BOXING--
--TYPE_BOXING--

unbox_BObjectBFloat : BObject -> BFloat
unbox_BObjectBFloat k =
    case k of 
        BObjectBFloat_box f -> 
            f
        _ -> 
            bsqbfloat_default

unbox_BObjectBDecimal : BObject -> BDecimal
unbox_BObjectBDecimal k =
    case k of 
        BObjectBDecimal_box d -> 
            d
        _ -> 
            bsqbdecimal_default

unbox_BObjectBRational : BObject -> BRational
unbox_BObjectBRational k =
    case k of 
        BObjectBRational_box f -> 
            f
        _ -> 
            bsqbrational_default

unbox_BObjectByteBuffer : BObject -> BByteBuffer
unbox_BObjectByteBuffer k =
    case k of 
        BObjectBByteBuffer_box b -> 
            b
        _ -> 
            bsqbbytebuffer_default

unbox_BObjectBDateTime : BObject -> BDateTime
unbox_BObjectBDateTime k =
    case k of 
        BObjectBDateTime_box t -> 
            t
        _ -> 
            bsqbdatetime_default

unbox_BObjectBLatLongCoordinate : BObject -> BLatLongCoordinate
unbox_BObjectBLatLongCoordinate k =
    case k of 
        BObjectBLatLongCoordinate_box t -> 
            t
        _ -> 
            bsqblatlongcoordinate_default

unbox_BObjectRegex : BObject -> Regex.Regex
unbox_BObjectRegex k =
    case k of 
        BObjectRegex_box f -> 
            f
        _ -> 
            Regex.never

--TERM_DEFAULT--

--TERM_UNBOX_OPS--

type BTerm = 
    BKeyObject BKey
    | BTermObject TypeTag BObject

bterm_none : BTerm
bterm_none = 
    BKeyObject bkey_none

bterm_nothing : BTerm
bterm_nothing = 
    BTermObject TypeTag_Nothing BObjectBNothing_box

bsqbterm_default : BTerm
bsqbterm_default = 
    bterm_nothing

getTypeTag_BKey : BKey -> TypeTag
getTypeTag_BKey t =
    let (BKey tag _) = t in tag

getTypeTag_BTerm : BTerm -> TypeTag
getTypeTag_BTerm t = 
    case t of 
        BKeyObject kk -> 
            getTypeTag_BKey kk
        BTermObject tag _ ->
            tag

getTermObj_BKey : BTerm -> BKey
getTermObj_BKey t =
    case t of 
        BKeyObject obj ->
            obj
        _ -> 
            bkey_none

getTermObj_BTerm : BTerm -> BObject
getTermObj_BTerm t = 
    case t of 
        BTermObject _ obj ->
            obj
        _ -> 
            BObjectBNothing_box

isBKeyNone : BKey -> Bool
isBKeyNone k = 
    getTypeTag_BKey k == TypeTag_None

isBTermNone : BTerm -> Bool
isBTermNone t = 
    getTypeTag_BTerm t == TypeTag_None

isBTermNothing : BTerm -> Bool
isBTermNothing t = 
    getTypeTag_BTerm t == TypeTag_Nothing

isBKeySome : BKey -> Bool
isBKeySome k = 
    getTypeTag_BKey k /= TypeTag_None

isBTermSome : BTerm -> Bool
isBTermSome t = 
    getTypeTag_BTerm t /= TypeTag_None

isBTermSomething : BTerm -> Bool
isBTermSomething t = 
    getTypeTag_BTerm t /= TypeTag_Nothing

type alias MapEntry k v = 
    {
        key: k,
        val: v
    }

result_is_success : (Result String a) -> Bool
result_is_success r = 
    case r of 
        Ok _ ->
            True
        _ -> 
            False

result_is_error : (Result String a) -> Bool
result_is_error r = 
    case r of 
        Err _ ->
            True
        _ -> 
            False

result_success_get_value : (Result String a) -> a -> a
result_success_get_value r d = 
    case r of 
        Ok v -> 
            v
        _ -> 
            d

result_error_get_value : (Result String a) -> String
result_error_get_value r = 
    case r of 
        Err e -> 
            e
        _ -> 
            "[NO ERROR INFO]"

list_head_w_default : (List a) -> a -> a
list_head_w_default l d =  
    case l of 
        [] ->
            d
        h :: _ ->
            h

type alias ReduceIdxInfo a =
    {
        index: Int,
        vv: a
    }

result_reduce : b -> (b -> a -> b) -> (List (Result String a)) -> (Result String b)
result_reduce acc f l = 
    case l of 
        [] ->
            Ok acc
        h :: t ->
            case h of 
                Err e -> 
                    Err e
                Ok v -> 
                    result_reduce (f acc v) f t

result_map_map : (List (Result String a)) -> (Result String (List a))
result_map_map l = 
    case l of 
        [] ->
            Ok []
        h :: t ->
            case h of 
                Err msg -> 
                    Err msg
                Ok v -> 
                    let tl = result_map_map t in
                    case tl of 
                        Err tlmsg -> 
                            Err tlmsg 
                        Ok tll ->
                            Ok (v :: tll)
            
--EPHEMERAL_DECLS--

--MASK_INFO--

--GLOBAL_DECLS--

--FUNCTION_DECLS--
