;;-------------------------------------------------------------------------------------------------------
;; Copyright (C) Microsoft. All rights reserved.
;; Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;;-------------------------------------------------------------------------------------------------------

(set-logic ALL)

;;
;; Type Tags
;;

(declare-datatypes (
      (TypeTag 0)
    ) (
    ( 
      (TypeTag_$Invalid)
      ;;TYPE_TAG_DECLS;;
    )
))

(declare-fun TypeTag_OrdinalOf () Int)
(assert (= (TypeTag_OrdinalOf TypeTag_None) 0))
(assert (= (TypeTag_OrdinalOf TypeTag_Bool) 2))
(assert (= (TypeTag_OrdinalOf TypeTag_Nat) 3))
(assert (= (TypeTag_OrdinalOf TypeTag_Int) 4))
(assert (= (TypeTag_OrdinalOf TypeTag_BigNat) 5))
(assert (= (TypeTag_OrdinalOf TypeTag_BigInt) 6))
(assert (= (TypeTag_OrdinalOf TypeTag_String) 10))
(assert (= (TypeTag_OrdinalOf TypeTag_LogicalTime) 16))
(assert (= (TypeTag_OrdinalOf TypeTag_UUID) 17))
(assert (= (TypeTag_OrdinalOf TypeTag_ContentHash) 18))
;;ORDINAL_TAG_DECLS;;

(declare-datatypes (
      (AbstractTypeTag 0)
    ) (
    ( 
      (AbstractTypeTag_$Invalid)
      ;;ABSTRACT_TYPE_TAG_DECLS;;
    )
))

(declare-datatypes (
      (TupleIndexTag 0)
    ) (
    ( 
      (TupleIndexTag_$Invalid)
      ;;INDEX_TAG_DECLS;;
    )
))

(declare-datatypes (
      (RecordPropertyTag 0)
    ) (
    ( 
      (RecordPropertyTag_$Invalid)
      ;;RecordPropertyTag;;
    )
))

(declare-fun SubtypeOf@ (TypeTag AbstractTypeTag) Bool)
;;SUBTYPE_DECLS;;

(declare-fun HasIndex@ (TypeTag TupleIndexTag) Bool)
;;TUPLE_HAS_INDEX_DECLS;;

(declare-fun HasProperty@ (TypeTag RecordPropertyTag) Bool)
;;RECORD_HAS_PROPERTY_DECLS;;

(declare-fun TypeTagRank@ (TypeTag) Int)
;;KEY_TYPE_TAG_RANK;;

(declare-sort FloatValue)
(declare-const FloatValue@zero FloatValue)
(declare-const FloatValue@one FloatValue)

(declare-fun FloatValue@neg (FloatValue) FloatValue)
(declare-fun FloatValue@add (FloatValue FloatValue) FloatValue)
(declare-fun FloatValue@sub (FloatValue FloatValue) FloatValue)
(declare-fun FloatValue@mult (FloatValue FloatValue) FloatValue)
(declare-fun FloatValue@div (FloatValue FloatValue) FloatValue)

(declare-fun FloatValue@eq (FloatValue FloatValue) Bool)
(declare-fun FloatValue@neq (FloatValue FloatValue) Bool)
(declare-fun FloatValue@lt (FloatValue FloatValue) Bool)
(declare-fun FloatValue@gt (FloatValue FloatValue) Bool)
(declare-fun FloatValue@lteq (FloatValue FloatValue) Bool)
(declare-fun FloatValue@gteq (FloatValue FloatValue) Bool)

;;BINTEGRAL_TYPE_ALIAS;;
(define-sort BBigInt () Int)
(define-sort BBigNat () Int)
(define-sort BFloat () FloatValue)
(define-sort BDecimal () FloatValue)
(define-sort BRational () FloatValue)
;;BSTRING_TYPE_ALIAS;;
(define-sort BTickTime () Int)
(define-sort BLogicalTime () Int)
;;BUUID_TYPE_ALIAS;;
;;BHASHCODE_TYPE_ALIAS;;

;;TODO BHashable and Hash + HashInvert and axioms

(define-datatype BByteBuffer 
  (BByteBuffer@cons 
    (BByteBuffer@bytes (Seq (_ BitVec 8)))
    (BDateTimeRaw@format BNat)
    (BDateTimeRaw@compress BNat)
))

(declare-datatype BDateTimeRaw 
  (BDateTimeRaw@cons 
    (BDateTimeRaw@year BNat)
    (BDateTimeRaw@month BNat)
    (BDateTimeRaw@day BNat)
    (BDateTimeRaw@hour BNat)
    (BDateTimeRaw@min BNat) 
))

(declare-datatype BDateTime 
  (BDateTime@cons 
    (BDateTime@utctime BDateTimeRaw)
    (BDateTime@localtime BDateTimeRaw)
    (BDateTime@tzoffset BNat)
    (BDateTime@tzinfo BString)
))

;;BINT_CONSTANTS;;

(declare-sort NumericOps 0)
(declare-sort ListOps 0)

(declare-const BBigInt@zero BBigInt) (assert (= BBigInt@zero 0))
(declare-const BBigInt@one BBigInt) (assert (= BBigInt@one 1))

(declare-const BBigNat@zero BBigNat) (assert (= BBigNat@zero 0))
(declare-const BBigNat@one BBigNat) (assert (= BBigNat@one 1))

(declare-const BFloat@zero BFloat) (assert (= BFloat@zero FloatValue@zero))
(declare-const BFloat@one BFloat) (assert (= BFloat@one FloatValue@one))
(declare-const BFloat@pi BFloat)
(declare-const BFloat@e BFloat)

(declare-const BDecimal@zero BDecimal) (assert (= BDecimal@zero FloatValue@zero))
(declare-const BDecimal@one BDecimal) (assert (= BDecimal@one FloatValue@one))
(declare-const BDecimal@pi BDecimal)
(declare-const BDecimal@e BDecimal)

(declare-const BRational@zero BRational) (assert (= BRational@zero FloatValue@zero))
(declare-const BRational@one BRational) (assert (= BRational@one FloatValue@one))

(declare-fun BByteBuffer@expandstr ((BByteBuffer)) BString)

;;
;; Primitive datatypes 
;;
(declare-datatypes (
      (bsq_none 0)
      (bsq_nothing 0)
      ; Bool -> Bool
      ; Int -> BV
      ; Nat -> BV
      ; BigInt -> Int
      ; BigNat -> Int
      ; Float -> Real 
      ; Decimal -> Real
      ; Rational -> Real
      ; String -> String | (Seq (_ BitVec 64))
      ; ByteBuffer -> BByteBuffer
      ; DateTime -> BDateTime
      ; TickTime -> Int
      ; LogicalTime -> Int
      ; UUID -> BUUID
      ; ContentHash -> (_ BitVec X)
      (HavocSequence 0)
    ) (
      ( (bsq_none@literal) ) 
      ( (bsq_nothing@literal) )
      ( (HavocSequence@cons (HavocSequence@root Int) (HavocSequence@path (Seq BNat))) )
))

;;
;; KeyType Concept datatypes
;;
(declare-datatypes (
      (bsq_keyobject 0)
      (BKey 0)
    ) (
    (
      (bsqkey_none@literal)
      (bsqkey_bool@box (bsqkey_bool_value Bool))
      (bsqkey_int@box (bsqkey_int_value BInt))
      (bsqkey_nat@box (bsqkey_nat_value BNat))
      (bsqkey_bigint@box (bsqkey_bigint_value BBigInt))
      (bsqkey_bignat@box (bsqkey_bignat_value BBigNat))
      (bsqkey_string@box (bsqkey_string_value BString))
      (bsqkey_logicaltime@box (bsqkey_logicaltime_value BLogicalTime))
      (bsqkey_uuid@box (bsqkey_uuid_value BUUID))
      (bsqkey_contenthash@box (bsqkey_contenthash_value BHash))
    )
    ( (BKey@box (BKey_type TypeTag) (BKey_oftype TypeTag) (BKey_value bsq_keyobject)) )
))

(declare-const BKey@none BKey)
(assert (= BKey@none (BKey@box TypeTag_None TypeTag_None bsqkey_none@literal)))

(define-fun bsq_none@less ((k1 bsq_none) (k2 bsq_none)) Bool
  false
)

(define-fun Bool@less ((k1 Bool) (k2 Bool)) Bool
  (and (not k1) k2)
)

(define-fun BInt@less ((k1 BInt) (k2 BInt)) Bool
  (bvslt k1 k2)
)

(define-fun BNat@less ((k1 BNat) (k2 BNat)) Bool
  (bvult k1 k2)
)

(define-fun BBigInt@less ((k1 BBigInt) (k2 BBigInt)) Bool
  (< k1 k2)
)

(define-fun BBigNat@less ((k1 BBigNat) (k2 BBigNat)) Bool
  (< k1 k2)
)

(define-fun BString@less ((k1 BString) (k2 BString)) Bool
  (str.< k1 k2)
)

(define-fun BLogicalTime@less ((k1 BLogicalTime) (k2 BLogicalTime)) Bool
  (< k1 k2)
)

(define-fun BUUID@less ((k1 BUUID) (k2 BUUID)) Bool
  (bvult k1 k2)
)

(define-fun BContentHash@less ((k1 BContentHash) (k2 BContentHash)) Bool
  (bvult k1 k2)
)

(define-fun BKey@less ((k1 BKey) (k2 BKey)) Bool
  (let ((tt (BKey_oftype k1)) (ttv1 (TypeTag_OrdinalOf (BKey_type k1))) (ttv2 (TypeTag_OrdinalOf (BKey_type k2))))
    (ite (not (= ttv1 ttv2))
      (< ttv1 ttv2)
      (let ((vv1 (BKey_value k1)) (vv2 (BKey_value k2)))
        (ite (tt TypeTag_None)
          false
          (ite (= tt TypeTag_Bool)
            (Bool@less (bsqkey_bool_value vv1) (bsqkey_bool_value vv2))
            (ite (= tt TypeTag_Int) 
              (BInt@less (bsqkey_int_value k1) (bsqkey_int_value k2))
              (ite (= tt TypeTag_Nat) 
                (BNat@less (bsqkey_nat_value k1) (bsqkey_nat_value k2))
                (ite (= tt TypeTag_BigInt)
                  (BBigInt@less (bsqkey_bigint_value vv1) (bsqkey_bigint_value vv2))
                  (ite (= tt TypeTag_BigNat)
                    (BBigNat@less (bsqkey_bignat_value vv1) (bsqkey_bignat_value vv2))
                    (ite (= tt TypeTag_String)
                      (BString@less (bsqkey_string_value vv1) (bsqkey_string_value vv2))
                      (ite (= tt TypeTag_LogicalTime)
                        (BLogicalTime@less (bsqkey_logicaltime_value vv1) (bsqkey_logicaltime_value vv2))
                        (ite (= tt TypeTag_UUID)
                          (BUUID@less (bsqkey_uuid_value vv1) (bsqkey_uuid_value vv2))
                          (bsqkey_contenthash@less (bsqkey_contenthash_value vv1) (bsqkey_contenthash_value vv2))
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

;;
;; Any Concept datatypes
;;
(declare-datatypes (
    (bsq_regex 0)
    ;;TUPLE_DECLS;;
    ;;RECORD_DECLS;;
    ;;TYPE_DECLS;;
    (bsq_object 0)
    (BTerm 0)
    ) (
    ( (bsq_regex@cons (bsq_regex_value Int)) )
    ;;TUPLE_TYPE_CONSTRUCTORS;;
    ;;RECORD_TYPE_CONSTRUCTORS;;
    ;;TYPE_CONSTRUCTORS;;
    (
      (bsqobject_nothing@literal)
      (bsqobject_float@box (bsqobject_float_value BFloat))
      (bsqobject_decimal@box (bsqobject_decimal_value BDecimal))
      (bsqobject_rational@box (bsqobject_rational_value BRational))
      (bsqobject_bytebuffer@box (bsqobject_bytebuffer_value BByteBuffer))
      (bsqobject_datetime@box (bsqobject_datetime_value BDateTime))
      (bsqobject_ticktime@box (bsqobject_ticktime_value BTickTime))
      (bsqobject_regex@box (bsqobject_regex_value bsq_regex))
      ;;TUPLE_TYPE_BOXING;;
      ;;RECORD_TYPE_BOXING;;
      ;;TYPE_BOXING;;
    )
    ( 
      (BTerm@termbox (BTerm_termtype TypeTag) (BTerm_termvalue bsq_object))
      (BTerm@keybox (BTerm_keyvalue BKey)) 
    )
))

(declare-const BTerm@none BTerm)
(assert (= BTerm@none (BTerm@keybox BKey@none)))

(declare-const BTerm@nothing BTerm)
(assert (= BTerm@nothing (BTerm@termbox TypeTag_Nothing bsqobject_nothing@literal)))

;;
;;Define utility functions
;;
(define-fun GetTypeTag@BKey ((t BKey)) TypeTag
  (BKey_type t)
)

(define-fun GetTypeTag@BTerm ((t BTerm)) TypeTag
  (ite ((_ is BTerm@termbox) t) (BTerm_termtype t) (BKey_type (BTerm_keyvalue t)))
)

;;
;; Ephemeral datatypes
;;
(declare-datatypes (
    (elistnull 0)
    ;;EPHEMERAL_DECLS;;
    ) (
    ( (elistnull@cons) )
    ;;EPHEMERAL_CONSTRUCTORS;;
))

(declare-datatypes (
      (ErrorID 0)
    ) (
    ( 
      (ErrorID_AssumeCheck)
      (ErrorID_Target)
    )
))

(declare-datatypes (
      ;;RESULT_DECLS;;
      ;;MASK_DECLS;;
    ) (
    ;;RESULTS;;
    ;;MASKS;;
))

;;
;;Free constructors for entrypoint initialization
;;
(define-fun BNone@UFCons_API ((hs (Seq BNat))) bsq_none
  bsq_none@literal
)

(define-fun BNothing@UFCons_API ((hs (Seq BNat))) bsq_nothing
  bsq_nothing@literal
)

(declare-fun BBool@UFCons_API ((Seq BNat)) Bool)
(declare-fun BInt@UFCons_API ((Seq BNat)) BInt )
(declare-fun BNat@UFCons_API ((Seq BNat)) BNat)
(declare-fun BBigInt@UFCons_API ((Seq BNat)) BBigInt)
(declare-fun BBigNat@UFCons_API ((Seq BNat)) BBigNat)
(declare-fun BFloat@UFCons_API ((Seq BNat)) BFloat)
(declare-fun BDecimal@UFCons_API ((Seq BNat)) BDecimal)
(declare-fun BRational@UFCons_API ((Seq BNat)) BRational)
(declare-fun BString@UFCons_API ((Seq BNat)) BString)
(declare-fun BByteBuffer@UFCons_API ((Seq BNat)) BByteBuffer)
(declare-fun BDateTime@UFCons_API ((Seq BNat)) BDateTime)
(declare-fun BTickTime@UFCons_API ((Seq BNat)) BTickTime)
(declare-fun BLogicalTime@UFCons_API ((Seq BNat)) BLogicalTime)
(declare-fun BUUID@UFCons_API ((Seq BNat)) BUUID)
(declare-fun BContentHash@UFCons_API ((Seq BNat)) BHash)

(declare-fun ContainerSize@UFCons_API ((Seq BNat)) BNat)
(declare-fun EnumChoice@UFCons_API ((Seq BNat)) BNat)
(declare-fun UnionChoice@UFCons_API ((Seq BNat)) BNat)

;;GLOBAL_DECLS;;

;;UF_DECLS;;

;;FUNCTION_DECLS;;

;;GLOBAL_DEFINITIONS;;

;;ACTION;;
