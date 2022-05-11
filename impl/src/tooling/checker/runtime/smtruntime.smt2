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

(declare-fun TypeTag_OrdinalOf (TypeTag) Int)
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

(declare-const Real@zero Real)
(assert (= Real@zero 0.0))

(declare-const Real@one Real)
(assert (= Real@one 1.0))

(define-sort BInt () Int)
(define-sort BNat () Int)
(define-sort BBigInt () Int)
(define-sort BBigNat () Int)
(define-sort BFloat () Real)
(define-sort BDecimal () Real)
(define-sort BRational () Real)
;;BSTRING_TYPE_ALIAS;;
(define-sort BTickTime () Int)
(define-sort BLogicalTime () Int)
(define-sort BUUID () (Seq (_ BitVec 8)))
(define-sort BContentHash () (_ BitVec 16))

;;TODO BHashable and Hash + HashInvert and axioms

(declare-datatype BByteBuffer 
  (
    (BByteBuffer@cons (BByteBuffer@bytes (Seq (_ BitVec 8))) (BByteBuffer@format BNat) (BByteBuffer@compress BNat))
  )
)

(declare-datatype BDateTime 
  (
    (BDateTime@cons (BDateTime@year BNat) (BDateTime@month BNat) (BDateTime@day BNat) (BDateTime@hour BNat) (BDateTime@min BNat) (BDateTime@tzdata BString))
  )
)

(declare-const BInt@zero BInt) (assert (= BInt@zero 0))
(declare-const BInt@one BInt) (assert (= BInt@one 1))

(declare-const BNat@zero BNat) (assert (= BNat@zero 0))
(declare-const BNat@one BNat) (assert (= BNat@one 1))

(declare-const BBigInt@zero BBigInt) (assert (= BBigInt@zero 0))
(declare-const BBigInt@one BBigInt) (assert (= BBigInt@one 1))

(declare-const BBigNat@zero BBigNat) (assert (= BBigNat@zero 0))
(declare-const BBigNat@one BBigNat) (assert (= BBigNat@one 1))

(declare-const BFloat@zero BFloat) (assert (= BFloat@zero Real@zero))
(declare-const BFloat@one BFloat) (assert (= BFloat@one Real@one))

(declare-const BDecimal@zero BDecimal) (assert (= BDecimal@zero Real@zero))
(declare-const BDecimal@one BDecimal) (assert (= BDecimal@one Real@one))

(declare-const BRational@zero BRational) (assert (= BRational@zero Real@zero))
(declare-const BRational@one BRational) (assert (= BRational@one Real@one))

(define-sort HavocSequence () (Seq Int))

;;
;; Primitive datatypes 
;;
(declare-datatypes (
      (bsq_none 0)
      (bsq_nothing 0)
      ; Bool -> Bool
      ; Int -> Int
      ; Nat -> Int
      ; BigInt -> Int
      ; BigNat -> Int
      ; Float -> Real 
      ; Decimal -> Real
      ; Rational -> Real
      ; String -> String | (Seq (_ BitVec 8))
      ; ByteBuffer -> BByteBuffer
      ; DateTime -> BDateTime
      ; TickTime -> Int
      ; LogicalTime -> Int
      ; UUID -> BUUID
      ; ContentHash -> (_ BitVec 16)
    ) (
      ( (bsq_none@literal) ) 
      ( (bsq_nothing@literal) )
))

;;OF_TYPE_DECLS;;

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
      (bsqkey_contenthash@box (bsqkey_contenthash_value BContentHash))
      ;;KEY_BOX_OPS;;
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
  (< k1 k2)
)

(define-fun BNat@less ((k1 BNat) (k2 BNat)) Bool
  (< k1 k2)
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
  ;;TODO: fix this
  true
)

(define-fun BContentHash@less ((k1 BContentHash) (k2 BContentHash)) Bool
  (bvult k1 k2)
)

(define-fun BKey@less ((k1 BKey) (k2 BKey)) Bool
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
                      (ite (= tt TypeTag_LogicalTime)
                        (BLogicalTime@less (bsqkey_logicaltime_value vv1) (bsqkey_logicaltime_value vv2))
                        (ite (= tt TypeTag_UUID)
                          (BUUID@less (bsqkey_uuid_value vv1) (bsqkey_uuid_value vv2))
                          (BContentHash@less (bsqkey_contenthash_value vv1) (bsqkey_contenthash_value vv2))
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
(declare-fun BBool@UFCons_API (HavocSequence) Bool)
(declare-fun BInt@UFCons_API (HavocSequence) BInt)
(declare-fun BNat@UFCons_API (HavocSequence) BNat)
(declare-fun BBigInt@UFCons_API (HavocSequence) BBigInt)
(declare-fun BBigNat@UFCons_API (HavocSequence) BBigNat)
(declare-fun BFloat@UFCons_API (HavocSequence) BFloat)
(declare-fun BDecimal@UFCons_API (HavocSequence) BDecimal)
(declare-fun BRational@UFCons_API (HavocSequence) BRational)
(declare-fun BString@UFCons_API (HavocSequence) BString)
(declare-fun BByteBuffer@UFCons_API (HavocSequence) (Seq (_ BitVec 8)))
(declare-fun BDateYear@UFCons_API (HavocSequence) BNat)
(declare-fun BDateMonth@UFCons_API (HavocSequence) BNat)
(declare-fun BDateDay@UFCons_API (HavocSequence) BNat)
(declare-fun BDateHour@UFCons_API (HavocSequence) BNat)
(declare-fun BDateMinute@UFCons_API (HavocSequence) BNat)
(declare-fun BTickTime@UFCons_API (HavocSequence) BTickTime)
(declare-fun BLogicalTime@UFCons_API (HavocSequence) BLogicalTime)
(declare-fun BUUID@UFCons_API (HavocSequence) BUUID)
(declare-fun BContentHash@UFCons_API (HavocSequence) BContentHash)

(declare-fun ContainerSize@UFCons_API (HavocSequence) BNat)
(declare-fun UnionChoice@UFCons_API (HavocSequence) BNat)

(define-fun _@@cons_None_entrypoint ((ctx HavocSequence)) $Result_bsq_none
  ($Result_bsq_none@success bsq_none@literal)
)

(define-fun _@@cons_Nothing_entrypoint ((ctx HavocSequence)) $Result_bsq_nothing
  ($Result_bsq_nothing@success bsq_nothing@literal)
)

;;@BINTMIN, @BINTMAX, @SLENMAX, @BLENMAX
;;V_MIN_MAX;;

(define-fun _@@cons_Bool_entrypoint ((ctx HavocSequence)) $Result_Bool
  ($Result_Bool@success (BBool@UFCons_API ctx))
)

(define-fun _@@cons_Int_entrypoint ((ctx HavocSequence)) $Result_BInt
  (let ((iv (BInt@UFCons_API ctx)))
    (ite (and (<= @BINTMIN iv) (<= iv @BINTMAX))
      ($Result_BInt@success iv)
      ($Result_BInt@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_Nat_entrypoint ((ctx HavocSequence)) $Result_BNat
  (let ((iv (BNat@UFCons_API ctx)))
    (ite (and (<= 0 iv) (<= iv @BINTMAX))
      ($Result_BNat@success iv)
      ($Result_BNat@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_BigInt_entrypoint ((ctx HavocSequence)) $Result_BBigInt
  (let ((iv (BBigInt@UFCons_API ctx)))
    (ite (and (<= (+ @BINTMIN @BINTMIN) iv) (<= iv (+ @BINTMAX @BINTMAX)))
      ($Result_BBigInt@success iv)
      ($Result_BBigInt@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_BigNat_entrypoint ((ctx HavocSequence)) $Result_BBigNat
  (let ((iv (BBigNat@UFCons_API ctx)))
    (ite (and (<= 0 iv) (<= iv (+ @BINTMAX @BINTMAX)))
      ($Result_BBigNat@success iv)
      ($Result_BBigNat@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_Float_entrypoint ((ctx HavocSequence)) $Result_BFloat
  ($Result_BFloat@success (BFloat@UFCons_API ctx))
)

(define-fun _@@cons_Decimal_entrypoint ((ctx HavocSequence)) $Result_BDecimal
  ($Result_BDecimal@success (BDecimal@UFCons_API ctx))
)

(define-fun _@@cons_Rational_entrypoint ((ctx HavocSequence)) $Result_BRational
  ($Result_BRational@success (BRational@UFCons_API ctx))
)

(define-fun _@@cons_String_entrypoint ((ctx HavocSequence)) $Result_BString
  (let ((sv (BString@UFCons_API ctx)))
    (ite (<= (str.len sv) @SLENMAX)
      ($Result_BString@success sv)
      ($Result_BString@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_ByteBuffer_entrypoint ((ctx HavocSequence)) $Result_BByteBuffer
  (let ((compress (BNat@UFCons_API (seq.++ ctx (seq.unit 0)))) (format (BNat@UFCons_API (seq.++ ctx (seq.unit 1)))) (buff (BByteBuffer@UFCons_API (seq.++ ctx (seq.unit 2)))))
    (ite (and (< compress 2) (< format 4) (<= (seq.len buff) @BLENMAX))
      ($Result_BByteBuffer@success (BByteBuffer@cons buff compress format))
      ($Result_BByteBuffer@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_DateTime_entrypoint ((ctx HavocSequence)) $Result_BDateTime
  (let ((tctx (seq.++ ctx (seq.unit 0))))
    (let ((y (BDateYear@UFCons_API (seq.++ tctx (seq.unit 0)))) (m (BDateMonth@UFCons_API (seq.++ tctx (seq.unit 1)))) (d (BDateDay@UFCons_API (seq.++ tctx (seq.unit 2)))) (hh (BDateHour@UFCons_API (seq.++ tctx (seq.unit 3)))) (mm (BDateMinute@UFCons_API (seq.++ tctx (seq.unit 4)))) (tzo (BString@UFCons_API (seq.++ ctx (seq.unit 1)))))
      (ite (and (<= 0 y) (<= y 300) (<= 0 m) (<= m 11) (<= 1 d) (<= d 31) (<= 0 hh) (<= hh 23) (<= 0 mm) (<= mm 59) (or (= tzo "UTC") (= tzo "PST") (= tzo "MST") (= tzo "CEST")))
        ($Result_BDateTime@success (BDateTime@cons y m d hh mm tzo))
        ($Result_BDateTime@error ErrorID_AssumeCheck) 
      )
    )
  )
)

(define-fun _@@cons_TickTime_entrypoint ((ctx HavocSequence)) $Result_BTickTime
  (let ((tv (BTickTime@UFCons_API ctx)))
    (ite (and (<= 0 tv) (<= tv 1048576))
      ($Result_BTickTime@success tv)
      ($Result_BTickTime@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_LogicalTime_entrypoint ((ctx HavocSequence)) $Result_BLogicalTime
  (let ((lv (BLogicalTime@UFCons_API ctx)))
    (ite (and (<= 0 lv) (<= lv 64))
      ($Result_BLogicalTime@success lv)
      ($Result_BLogicalTime@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_UUID_entrypoint ((ctx HavocSequence)) $Result_BUUID
  (let ((uuv (BUUID@UFCons_API ctx)))
    (ite (= (seq.len uuv) 16)
      ($Result_BUUID@success uuv)
      ($Result_BUUID@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_ContentHash_entrypoint ((ctx HavocSequence)) $Result_BContentHash
  ($Result_BContentHash@success (BContentHash@UFCons_API ctx))
)

;;GLOBAL_DECLS;;

;;UF_DECLS;;

;;FUNCTION_DECLS;;

;;GLOBAL_DEFINITIONS;;

;;ACTION;;
