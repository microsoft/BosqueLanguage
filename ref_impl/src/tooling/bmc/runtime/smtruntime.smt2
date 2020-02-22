;;-------------------------------------------------------------------------------------------------------
;; Copyright (C) Microsoft. All rights reserved.
;; Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;;-------------------------------------------------------------------------------------------------------

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(set-option :timeout 10000)

(declare-datatypes (
      (bsq_safestring 0)
      (bsq_stringof 0)
      (bsq_guid 0)
      (bsq_datahash 0)
      (bsq_cryptohash 0)
      (bsq_logicaltime 0)
      (bsq_enum 0)
      (bsq_idkey 0)
      (bsq_idkey_logicaltime 0)
      (bsq_idkey_guid 0)
      (bsq_idkey_cryptohash 0)
      (BKeyValue 0)
    ) (
    ( (bsq_safestring@cons (bsq_safestring_type String) (bsq_safestring_value String)) )
    ( (bsq_stringof@cons (bsq_stringof_type String) (bsq_stringof_value String)) )
    ( (bsq_guid@cons (bsqy_guid_value String)) )
    ( (bsq_datahash@cons (bsq_datahash Int)) )
    ( (bsq_cryptohash@cons (bsq_cryptohash String)) )
    ( (bsq_logicaltime@cons (bsq_logicaltime_value Int)) )
    ( (bsq_enum@cons (bsq_enum_type String) (bsq_enum_value Int)) )
    ( (bsq_idkey@cons (bsq_idkey_type String) (bsq_idkey_value (Array String BKeyValue))) )
    ( (bsq_idkey_logicaltime@cons (bsq_idkey_logicaltime_type String) (bsq_idkey_logicaltime_value Int)) )
    ( (bsq_idkey_guid@cons (bsq_idkey_guid_type String) (bsq_idkey_guid_value String)) )
    ( (bsq_idkey_cryptohash@cons (bsq_idkey_cryptohash_type String) (bsq_idkey_cryptohash_value String)) )
    (
      (bsqkey_none) 
      (bsqkey_bool (bsqkey_bool_value Bool))
      (bsqkey_int (bsqkey_int_value Int))
      (bsqkey_string (bsqkey_string_value String))
      (bsqkey_safestring (bsqkey_safestring_value bsq_safestring))
      (bsqkey_stringof (bsqkey_stringof_value bsq_stringof))
      (bsqkey_guid (bsqkey_guid_value bsq_guid))
      (bsqkey_datahash (bsqkey_datahash bsq_datahash))
      (bsqkey_cryptohash (bsqkey_cryptohash bsq_cryptohash))
      (bsqkey_logicaltime (bsqkey_logicaltime_value bsq_logicaltime))
      (bsqkey_enum (bsqkey_enum_value bsq_enum))
      (bsqkey_idkey (bsqkey_idkey_value bsq_idkey))
      (bsqkey_idkey_logicaltime (bsqkey_idkey_logicaltime_value bsq_idkey_logicaltime))
      (bsqkey_idkey_guid (bsqkey_idkey_guid_value bsq_idkey_guid))
      (bsqkey_idkey_cryptohash (bsqkey_idkey_cryptohash_value bsq_idkey_cryptohash))
    )
))

(declare-datatypes ( 
    (bsq_buffer 0)
    (bsq_isotime 0)
    (bsq_regex 0)
    (bsq_tuple 0)
    (bsq_record 0)
    ;;NOMINAL_DECLS_FWD;;
    (bsq_object 0)
    (BTerm 0)
    ) (
    ( (bsq_buffer@cons (bsq_buffer_type String) (bsq_buffer_contents String)) )
    ( (bsq_isotime@cons (bsq_isotime_value Int)) )
    ( (bsq_regex@cons (bsq_regex_value String)) )
    ( (bsq_tuple@cons (bsqterm_tuple_flag Int) (bsq_tuple_entries (Array Int BTerm)))  )
    ( (bsq_record@cons (bsqterm_record_flag Int) (bsq_record_entries (Array String BTerm))) )
    ;;NOMINAL_CONSTRUCTORS;;
    (
      (bsq_object@empty)
    ;;NOMINAL_OBJECT_CONSTRUCTORS;;
    )
    (
      (bsqterm@clear)
      (bsqterm_key (bsqterm_key_value BKeyValue))
      (bsqterm_buffer (bsqterm_buffer_value bsq_buffer))
      (bsqterm_isotime (bsqterm_isotime_value bsq_isotime))
      (bsqterm_regex (bsqterm_regex_value bsq_regex))
      (bsqterm_tuple (bsqterm_tuple_value bsq_tuple)) 
      (bsqterm_record (bsqterm_record_value bsq_record))
      (bsqterm_object (bsqterm_object_type String) (bsqterm_object_value bsq_object))
    )
))

(declare-fun nominalDataKinds (String) Int)
;;NOMINAL_TYPE_TO_DATA_KIND_ASSERTS;;

(declare-const MIRNominalTypeEnum_None String)
(declare-const MIRNominalTypeEnum_Bool String)
(declare-const MIRNominalTypeEnum_Int String)
(declare-const MIRNominalTypeEnum_String String)
(declare-const MIRNominalTypeEnum_GUID String)
(declare-const MIRNominalTypeEnum_LogicalTime String)
(declare-const MIRNominalTypeEnum_DataHash String)
(declare-const MIRNominalTypeEnum_CryptoHash String)
(declare-const MIRNominalTypeEnum_ISOTime String)
(declare-const MIRNominalTypeEnum_Tuple String)
(declare-const MIRNominalTypeEnum_Regex String)
(declare-const MIRNominalTypeEnum_Record String)

;;SPECIAL_NAME_BLOCK_ASSERTS;;

(define-fun bsqkey_get_nominal_type ((keyv BKeyValue)) String
  (ite (= keyv bsqkey_none) MIRNominalTypeEnum_None
    (ite (is-bsqkey_bool keyv) MIRNominalTypeEnum_Bool
      (ite (is-bsqkey_int keyv) MIRNominalTypeEnum_Int
        (ite (is-bsqkey_string keyv) MIRNominalTypeEnum_String
          (ite (is-bsqkey_safestring keyv) (bsq_safestring_type (bsqkey_safestring_value keyv))
            (ite (is-bsqkey_stringof keyv) (bsq_stringof_type (bsqkey_stringof_value keyv))
              (ite (is-bsqkey_guid keyv) MIRNominalTypeEnum_GUID
                (ite (is-bsqkey_datahash keyv) MIRNominalTypeEnum_DataHash
                  (ite (is-bsqkey_cryptohash keyv) MIRNominalTypeEnum_CryptoHash
                    (ite (is-bsqkey_logicaltime keyv) MIRNominalTypeEnum_LogicalTime
                      (ite (is-bsqkey_enum keyv) (bsq_enum_type (bsqkey_enum_value keyv))
                        (ite (is-bsqkey_idkey keyv) (bsq_idkey_type (bsqkey_idkey_value keyv))
                          (ite (is-bsqkey_idkey_logicaltime keyv) (bsq_idkey_logicaltime_type (bsqkey_idkey_logicaltime_value keyv))
                            (ite (is-bsqkey_idkey_guid keyv) (bsq_idkey_guid_type (bsqkey_idkey_guid_value keyv))
                              (bsq_idkey_cryptohash_type (bsqkey_idkey_cryptohash_value keyv))
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
  )
)

(define-fun bsqterm_get_nominal_type ((term BTerm)) String
  (ite (is-bsqterm_key term) (bsqkey_get_nominal_type (bsqterm_key_value term))
    (ite (is-bsqterm_buffer term) (bsq_buffer_type (bsqterm_buffer_value term))
      (ite (is-bsqterm_isotime term) MIRNominalTypeEnum_ISOTime
        (ite (is-bsqterm_regex term) MIRNominalTypeEnum_Regex
          (ite (is-bsqterm_tuple term) MIRNominalTypeEnum_Tuple
            (ite (is-bsqterm_record term) MIRNominalTypeEnum_Record
              (bsqterm_object_type term)
            )
          )
        )
      )
    )
  )
)

(define-fun getDataKindFlag ((term BTerm)) Int
  (ite (= term bsqterm@clear) 3
    (ite (is-bsqterm_tuple term) (bsqterm_tuple_flag (bsqterm_tuple_value term))
      (ite (is-bsqterm_record term) (bsqterm_record_flag (bsqterm_record_value term))
        (nominalDataKinds (bsqterm_get_nominal_type term))
      )
    )
  )
)

(define-fun @fj ((f1 Int) (f2 Int)) Int
  (ite (and (= f1 3) (= f2 3)) 3
    (ite (or (= f1 0) (= f2 0)) 0
      1
    )
  )
)

;;EPHEMERAL_DECLS;;

(declare-const bsqterm_none BTerm)
(assert (= bsqterm_none (bsqterm_key bsqkey_none)))

(declare-const bsqtuple_array_empty (Array Int BTerm))
(assert (= bsqtuple_array_empty ((as const (Array Int BTerm)) bsqterm@clear)))

(declare-const bsqrecord_array_empty (Array String BTerm))
(assert (= bsqrecord_array_empty ((as const (Array String BTerm)) bsqterm@clear)))

;;EMPTY_CONTENT_ARRAY_DECLS;;

(declare-datatypes (
      (ErrorCode 0)
      ;;RESULTS_FWD;;
    ) (
    ( (result_error (error_id Int)) (result_bmc (bmc_id String)) )
    ;;RESULTS;;
))

;;current implementation is simple uninterpreted function -- want to implement these in core runtime with bounded checkable impl
(declare-fun stroi (String) Int)

;;current implementation is simple uninterpreted function -- maybe want to make these return a non-decidable error (or have bounded checkable impl)
(declare-fun mult_op (Int Int) Int) 
(declare-fun div_op (Int Int) Int)
(declare-fun mod_op (Int Int) Int)

(declare-const mirconceptsubtypearray_empty (Array String Bool))
(assert (= mirconceptsubtypearray_empty ((as const (Array String Bool)) false)))

;;CONCEPT_SUBTYPE_RELATION_DECLARE;;

;;SUBTYPE_DECLS;;

;;VFIELD_ACCESS;;

;;FUNCTION_DECLS;;

;;ARG_VALUES;;

;;INVOKE_ACTION;;

(check-sat)
;;GET_MODEL;;
