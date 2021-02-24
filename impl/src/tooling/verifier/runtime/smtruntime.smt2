;;-------------------------------------------------------------------------------------------------------
;; Copyright (C) Microsoft. All rights reserved.
;; Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;;-------------------------------------------------------------------------------------------------------

(set-option :smt.mbqi true)

(set-option :timeout ;;TIMEOUT;;)

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

;;
;;UFloat kind + UF ops for strong refutation checks
;;
(declare-sort UFloat)

;;
;; Define sort aliases for Int/Nat/BigInt/BigNat/Float/Decimal/Rational/String representation options
;;
;;BINTEGRAL_TYPE_ALIAS;;
;;BFLOATPOINT_TYPE_ALIAS;;
;;STRING_TYPE_ALIAS;;

;;
;; Define uninterpreted functions for various kinds
;;
(declare-fun BFloatCons_UF (String) BFloat)
(declare-fun BFloatUnary_UF (String BFloat) BFloat)
(declare-fun BFloatBinary_UF (String BFloat BFloat) BFloat)

(declare-fun BDecimalCons_UF (String) BDecimal)
(declare-fun BDecimalUnary_UF (String BDecimal) BDecimal)
(declare-fun BDecimalBinary_UF (String BDecimal BDecimal) BDecimal)

(declare-fun BRationalCons_UF (String) BRational)
(declare-fun BRationalUnary_UF (String BRational) BRational)
(declare-fun BRationalBinary_UF (String BRational BRational) BRational)

;;
;; Define min/max/0 constants for Int/Nat/BigInt/BigNat/Float/Decimal/Rational/String representation options
;;
;;BINTEGRAL_CONSTANTS;;
;;BFLOATPOINT_CONSTANTS;;

;;Define the ISequence datatype and operators
(declare-sort ISequence)

(declare-fun ISequence@size (ISequence) BNat)
(declare-fun ISequence@get (ISequence BNat) BNat)

(define-fun ISequence@assertSorted ((s ISequence)) Bool
  (let ((len (ISequence@size s)))
    (forall ((i BNat) (j BNat))
      (=> (and (bvult i j) (bvult j len))
          (bvult (ISequence@get s i) (ISequence@get s j))))
  )
)

(define-fun ISequence@assertValuesRange ((s ISequence) (limit BNat)) Bool
  (let ((len (ISequence@size s)))
    (forall ((i BNat))
      (=> (bvult i len)
          (bvult (ISequence@get s i) limit)))
  )
)

(declare-const ISequence@empty ISequence)
(assert (= (ISequence@size ISequence@empty) BNat@zero))

;;
;; Primitive datatypes 
;;
(declare-datatypes (
      (bsq_none 0)
      ; Bool -> Bool
      ; Int -> BVX as BInt
      ; Nat -> BVX as BNat
      ; BigInt -> 2*BVX | Int as BBigInt
      ; BigNat -> 2*BVX | Int as BBigNat
      ; Float ->   Float | UFloat as BFloat
      ; Decimal -> Float | UFloat as BDecimal
      ; Rational -> Float | UFloat as BRational
      ; String -> String | (Seq (_ BitVec 64)) as BString
    ) (
    ( (bsq_none@literal) )
))

;;
;; KeyType Concept datatypes
;;
(declare-datatypes (
      ;;KEY_TUPLE_DECLS;;
      ;;KEY_RECORD_DECLS;;
      ;;KEY_TYPE_DECLS;;
      (bsq_keyobject 0)
      (BKey 0)
    ) (
    ;;KEY_TUPLE_TYPE_CONSTRUCTORS;;
    ;;KEY_RECORD_TYPE_CONSTRUCTORS;;
    ;;KEY_TYPE_CONSTRUCTORS;;
    (
      (bsqkey_none@literal) 
      (bsqkey_bool@box (bsqkey_bool_value Bool))
      (bsqkey_int@box (bsqkey_int_value BInt))
      (bsqkey_nat@box (bsqkey_nat_value BNat))
      (bsqkey_bigint@box (bsqkey_bigint_value BBigInt))
      (bsqkey_bignat@box (bsqkey_bignat_value BBigNat))
      (bsqkey_string@box (bsqkey_string_value BString))
      ;;KEY_TUPLE_TYPE_BOXING;;
      ;;KEY_RECORD_TYPE_BOXING;;
      ;;KEY_TYPE_BOXING;;
    )
    ( (BKey@box (BKey_type TypeTag) (BKey_value bsq_keyobject)) )
))

(declare-const BKey@none BKey)
(assert (= BKey@none (BKey@box TypeTag_None bsqkey_none@literal)))

(define-fun bsqkey_none@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  false
)

(define-fun bsqkey_bool@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  (and (not (bsqkey_bool_value k1)) (bsqkey_bool_value k2))
)

(define-fun bsqkey_int@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  (bvslt (bsqkey_int_value k1) (bsqkey_int_value k2))
)

(define-fun bsqkey_nat@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  (bvult (bsqkey_nat_value k1) (bsqkey_nat_value k2))
)

(define-fun bsqkey_bigint@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  (bvslt (bsqkey_bigint_value k1) (bsqkey_bigint_value k2))
)

(define-fun bsqkey_bignat@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  (bvult (bsqkey_bignat_value k1) (bsqkey_bignat_value k2))
)

(define-fun bsqkey_string@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  (str.< (bsqkey_string_value k1) (bsqkey_string_value k2))
)

;;
;; Any Concept datatypes
;;
(declare-datatypes (
    (bsq_regex 0)
    ;;TUPLE_DECLS;;
    ;;RECORD_DECLS;;
    ;;TYPE_COLLECTION_INTERNAL_INFO_DECLS;;
    ;;TYPE_DECLS;;
    (bsq_object 0)
    (BTerm 0)
    ) (
    ( (bsq_regex@cons (bsq_regex_value Int)) )
    ;;TUPLE_TYPE_CONSTRUCTORS;;
    ;;RECORD_TYPE_CONSTRUCTORS;;
    ;;TYPE_COLLECTION_INTERNAL_INFO_CONSTRUCTORS;;
    ;;TYPE_CONSTRUCTORS;;
    (
      (bsqobject_float@box (bsqobject_float_value BFloat))
      (bsqobject_decimal@box (bsqobject_decimal_value BDecimal))
      (bsqobject_rational@box (bsqobject_rational_value BRational))
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

;;
;;Define utility functions
;;
(define-fun GetTypeTag@BKey ((t BKey)) TypeTag
  (BKey_type t)
)

(define-fun GetTypeTag@BTerm ((t BTerm)) TypeTag
  (ite (is-BTerm@termbox t) (BTerm_termtype t) (BKey_type (BTerm_keyvalue t)))
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

(declare-datatypes () (
  (ErrorID
    ErrorID_AssumeCheck
    ErrorID_Target
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
(declare-fun BNone@UFCons_API ((Seq BNat)) bsq_none)
(declare-fun BBool@UFCons_API ((Seq BNat)) Bool)
(declare-fun BInt@UFCons_API ((Seq BNat)) BInt )
(declare-fun BNat@UFCons_API ((Seq BNat)) BNat)
(declare-fun BBigInt@UFCons_API ((Seq BNat)) BBigInt)
(declare-fun BBigNat@UFCons_API ((Seq BNat)) BBigNat)
(declare-fun BFloat@UFCons_API ((Seq BNat)) BFloat)
(declare-fun BDecimal@UFCons_API ((Seq BNat)) BDecimal)
(declare-fun BRational@UFCons_API ((Seq BNat)) BRational)
(declare-fun BString@UFCons_API ((Seq BNat)) BString)

(declare-fun ListSize@UFCons_API ((Seq BNat)) BNat)

;;GLOBAL_DECLS;;

;;UF_DECLS;;

;;FUNCTION_DECLS;;

;;GLOBAL_DEFINITIONS;;

;;ACTION;;
