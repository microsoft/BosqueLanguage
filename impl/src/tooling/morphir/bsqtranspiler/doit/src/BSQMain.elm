
module BSQMain exposing (..)

import BSQRuntime exposing(..)

type BKeyObject = 
      BKeyNone_box
      | BKeyBool_box Bool
      | BKeyBInt_box BInt
      | BKeyBNat_box BNat
      | BKeyBBigint_box BBigInt
      | BKeyBBignat_box BBigNat
      | BKeyBString_box BString
      | BKeyBUTCdatetime_box BUTCDateTime
      | BKeyBCalendardate_box BCalendarDate
      | BKeyBRelativetime_box BRelativeTime
      | BKeyBTicktime_box BTickTime
      | BKeyBLogicaltime_box BLogicalTime
      | BKeyBISOTimeStamp_box BISOTimeStamp
      | BKeyBUUID4_box BUUID4
      | BKeyBUUID7_box BUUID7
      | BKeyBSHAContentHash_box BSHAContentHash
      --KEY_BOX_OPS--

type BKey = 
    BKey BSQRuntime.TypeTag BKeyObject


bkey__less : BKey -> BKey -> Bool
bkey__less k1 k2 = 
    let (BKey tag1 obj1) = k1 in
    let (BKey tag2 obj2) = k2 in
    if tag1 /= tag2 then
        (BSQRuntime.ordinalOf tag1) < (BSQRuntime.ordinalOf tag2) else
        case k1 of
            BKeyNone_box -> 
                False
            BKeyBool_box b1 -> 
                case k2 of 
                    BKeyBool_box b2 -> 
                        BSQRuntime.bool__less b1 b2
                    _ -> 
                        False
            BKeyBInt_box i1 -> 
                case k2 of 
                    BKeyBInt_box i2 -> 
                        BSQRuntime.bint__less i1 i2
                    _ -> 
                        False
            BKeyBNat_box n1 -> 
                case k2 of 
                    BKeyBNat_box n2 -> 
                        BSQRuntime.bnat__less n1 n2
                    _ -> 
                        False
            _ -> 
                False
            

    {-
  (let ((tt (BKey_oftype k1)) (ttv1 (TypeTag_OrdinalOf (BKey_type k1))) (ttv2 (TypeTag_OrdinalOf (BKey_type k2))))
    (ite (not (= ttv1 ttv2))
      (< ttv1 ttv2)
      (let ((vv1 (BKey_value k1)) (vv2 (BKey_value k2)))
        (ite (= tt TypeTag_None)
          false
          (ite (= tt TypeTag_Bool)
            (Bool@less (bsqkey_bool_value vv1) (bsqkey_bool_value vv2))
            (ite (= tt TypeTag_Int) 
              (BInt@less (bsqkey_int_value vv1) (bsqkey_int_value vv2))
              (ite (= tt TypeTag_Nat) 
                (BNat@less (bsqkey_nat_value vv1) (bsqkey_nat_value vv2))
                (ite (= tt TypeTag_BigInt)
                  (BBigInt@less (bsqkey_bigint_value vv1) (bsqkey_bigint_value vv2))
                  (ite (= tt TypeTag_BigNat)
                    (BBigNat@less (bsqkey_bignat_value vv1) (bsqkey_bignat_value vv2))
                    (ite (= tt TypeTag_String)
                      (BString@less (bsqkey_string_value vv1) (bsqkey_string_value vv2))
                      (ite (= tt TypeTag_UTCDateTime)
                        (BUTCDateTime@less (bsqkey_utcdatetime_value vv1) (bsqkey_utcdatetime_value vv2)) 
                        (ite (= tt TypeTag_CalendarDate)
                          (BCalendarDate@less (bsqkey_calendardate_value vv1) (bsqkey_calendardate_value vv2))
                          (ite (= tt TypeTag_RelativeTime)
                            (BRelativeTime@less (bsqkey_relativetime_value vv1) (bsqkey_relativetime_value vv2))
                            (ite (= tt TypeTag_TickTime)
                              (BTickTime@less (bsqkey_ticktime_value vv1) (bsqkey_ticktime_value vv2))
                              (ite (= tt TypeTag_LogicalTime)
                                (BLogicalTime@less (bsqkey_logicaltime_value vv1) (bsqkey_logicaltime_value vv2))
                                (ite (= tt TypeTag_ISOTimeStamp)
                                  (BISOTimeStamp@less (bsqkey_isotimestamp_value vv1) (bsqkey_isotimestamp_value vv2))
                                  (ite (= tt TypeTag_UUID4)
                                    (BUUID4@less (bsqkey_uuid4_value vv1) (bsqkey_uuid4_value vv2))
                                    (ite (= tt TypeTag_UUID7)
                                      (BUUID7@less (bsqkey_uuid7_value vv1) (bsqkey_uuid7_value vv2))
                                      (BSHAContentHash@less (bsqkey_shacontenthash_value vv1) (bsqkey_shacontenthash_value vv2))
                                    )
                                 -}
