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

;;BINTEGRAL_TYPE_ALIAS;;
(define-sort BBigInt () Int)
(define-sort BBigNat () Int)
(define-sort BFloat () Real)
(define-sort BDecimal () Real)
(define-sort BRational () Real)
(define-sort BStringPos () Int)
;;BSTRING_TYPE_ALIAS;;
(define-sort BByteBuffer () (Seq (_ BitVec 8)))
(define-sort BISOTime () Int)
(define-sort BLogicalTime () Int)
(define-sort BUUID () (_ BitVec 12)) ;;TODO we should experiment with this encoding -- int, bv128, constructor?
;;BHASHCODE_TYPE_ALIAS;;

;;TODO BHashable and Hash + HashInvert and axioms

;;BINT_CONSTANTS;;

(define-sort HavocSequence () (Seq BNat))

(declare-sort NumericOps 0)
(declare-sort ListFlatOps 0)
(declare-sort ListConcatOps 0)
(declare-sort ListOps 0)

(declare-const BBigInt@zero BBigInt) (assert (= BBigInt@zero 0))
(declare-const BBigInt@one BBigInt) (assert (= BBigInt@one 1))

(declare-const BBigNat@zero BBigNat) (assert (= BBigNat@zero 0))
(declare-const BBigNat@one BBigNat) (assert (= BBigNat@one 1))

(declare-const BFloat@zero BFloat) (assert (= BFloat@zero 0.0))
(declare-const BFloat@one BFloat) (assert (= BFloat@one 1.0))
(declare-const BFloat@pi BFloat) (assert (= BFloat@pi 3.141592653589793))
(declare-const BFloat@e BFloat) (assert (= BFloat@e 2.718281828459045))

(declare-const BDecimal@zero BDecimal) (assert (= BDecimal@zero 0.0))
(declare-const BDecimal@one BDecimal) (assert (= BDecimal@one 1.0))
(declare-const BDecimal@pi BDecimal) (assert (= BDecimal@pi 3.141592653589793))
(declare-const BDecimal@e BDecimal) (assert (= BDecimal@e 2.718281828459045))

(declare-const BRational@zero BRational) (assert (= BRational@zero 0.0))
(declare-const BRational@one BRational) (assert (= BRational@one 1.0))

(declare-fun BByteBuffer@expandstr ((BByteBuffer)) BString)

;;Define the ISequence datatype and operators
(declare-sort ISequence 0)

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

;;Define the JSequence datatype
(declare-datatype JSequencePair ((JSequencePair@cons (JSequencePair@a BNat) (JSequencePair@b BNat))))
(declare-sort JSequence 0)

(declare-fun JSequence@size (JSequence) BNat)
(declare-fun JSequence@get (JSequence BNat) JSequencePair)

(define-fun JSequence@assertSorted ((s JSequence)) Bool
  (let ((len (JSequence@size s)))
    (forall ((i BNat) (j BNat))
      (=> (and (bvult i j) (bvult j len))
          (or 
            (bvult (JSequencePair@a (JSequence@get s i)) (JSequencePair@a (JSequence@get s j)))
            (and (= (JSequencePair@a (JSequence@get s i)) (JSequencePair@a (JSequence@get s j))) (bvult (JSequencePair@b (JSequence@get s i)) (JSequencePair@b (JSequence@get s j))))
          )
      )
    )
  )
)

(define-fun JSequence@assertValuesRange ((s JSequence) (limita BNat) (limitb BNat)) Bool
  (let ((len (JSequence@size s)))
    (forall ((i BNat))
      (=> (bvult i len)
          (and (bvult (JSequencePair@a (JSequence@get s i)) limita) (bvult (JSequencePair@b (JSequence@get s i)) limitb))))
  )
)

(declare-const JSequence@empty JSequence)
(assert (= (JSequence@size JSequence@empty) BNat@zero))

;;Define the SSequence datatype
(declare-sort SSequence 0)

(declare-fun SSequence@size (SSequence) BNat)
(declare-fun SSequence@get (SSequence BNat) BNat)

(define-fun SSequence@assertValuesRange ((s SSequence) (limit BNat)) Bool
  (let ((len (SSequence@size s)))
    (forall ((i BNat))
      (=> (bvult i len)
          (bvult (SSequence@get s i) limit)))
  )
)

(declare-const SSequence@empty SSequence)
(assert (= (SSequence@size SSequence@empty) BNat@zero))

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
      ; StringPos -> Int
      ; String -> String | (Seq (_ BitVec 64))
      ; ByteBuffer -> (Seq (_ BitVec 8))
      ; ISOTime -> Int
      ; LogicalTime -> Int
      ; UUID -> ?? need to investigate
      ; ContentHash -> (_ BitVec X)
    ) (
      ( (bsq_none@literal) ) 
      ( (bsq_nothing@literal) ) 
))

;;
;; KeyType Concept datatypes
;;
(declare-datatypes (
      ;;KEY_TYPE_DECLS;;
      (bsq_keyobject 0)
      (BKey 0)
    ) (
    ;;KEY_TYPE_CONSTRUCTORS;;
    (
      (bsqkey_none@literal)
      (bsqkey_nothing@literal) 
      (bsqkey_bool@box (bsqkey_bool_value Bool))
      (bsqkey_int@box (bsqkey_int_value BInt))
      (bsqkey_nat@box (bsqkey_nat_value BNat))
      (bsqkey_bigint@box (bsqkey_bigint_value BBigInt))
      (bsqkey_bignat@box (bsqkey_bignat_value BBigNat))
      (bsqkey_string@box (bsqkey_string_value BString))
      (bsqkey_logicaltime@box (bsqkey_logicaltime_value BLogicalTime))
      (bsqkey_uuid@box (bsqkey_uuid_value BUUID))
      (bsqkey_contenthash@box (bsqkey_contenthash_value BHash))
      ;;KEY_TYPE_BOXING;;
    )
    ( (BKey@box (BKey_type TypeTag) (BKey_value bsq_keyobject)) )
))

(declare-const BKey@none BKey)
(assert (= BKey@none (BKey@box TypeTag_None bsqkey_none@literal)))

(declare-const BKey@nothing BKey)
(assert (= BKey@nothing (BKey@box TypeTag_Nothing bsqkey_nothing@literal)))

(define-fun bsqkey_none@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  false
)

(define-fun bsqkey_nothing@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
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
  (< (bsqkey_bigint_value k1) (bsqkey_bigint_value k2))
)

(define-fun bsqkey_bignat@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  (< (bsqkey_bignat_value k1) (bsqkey_bignat_value k2))
)

(define-fun bsqkey_string@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  (str.< (bsqkey_string_value k1) (bsqkey_string_value k2))
)

(define-fun bsqkey_logicaltime@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  (< (bsqkey_logicaltime_value k1) (bsqkey_logicaltime_value k2))
)

(define-fun bsqkey_uuid@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  (bvult (bsqkey_uuid_value k1) (bsqkey_uuid_value k2))
)

(define-fun bsqkey_contenthash@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  (bvult (bsqkey_contenthash_value k1) (bsqkey_contenthash_value k2))
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
      (bsqobject_stringpos@box (bsqobject_stringpos_value Int))
      (bsqobject_bytebuffer@box (bsqobject_bytebuffer_value BByteBuffer))
      (bsqobject_isotime@box (bsqobject_isotime_value Int))
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
(assert (= BTerm@nothing (BTerm@keybox BKey@nothing)))

;;TYPE_COLLECTION_EMPTY_DECLS;;

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
(declare-fun BISOTime@UFCons_API ((Seq BNat)) BISOTime)
(declare-fun BLogicalTime@UFCons_API ((Seq BNat)) BLogicalTime)
(declare-fun BUUID@UFCons_API ((Seq BNat)) BUUID)
(declare-fun BContentHash@UFCons_API ((Seq BNat)) BHash)

(declare-fun ListSize@UFCons_API ((Seq BNat)) BNat)
(declare-fun EnumChoice@UFCons_API ((Seq BNat)) BNat)
(declare-fun ConceptChoice@UFCons_API ((Seq BNat)) BNat)
(declare-fun UnionChoice@UFCons_API ((Seq BNat)) BNat)

;;GLOBAL_DECLS;;

;;UF_DECLS;;

;;FUNCTION_DECLS;;

;;GLOBAL_DEFINITIONS;;

;;ACTION;;
