---- MODULE Operations ----

EXTENDS Integers

(* Granada operations *)

\* seed_nonce_revelation level nonce
\* endorsement_with_slot [endorsement shell protocol_data] slot
\* double_endorsement_evidence [endorsement shell protocol_data] [endorsement shell protocol_data] slot
\* double_baking_evidence block_header block_header
\* activate_account id activation_code
\* endorsement level
\* proposals source period (proposals : Protocol_hash list)
\* ballot source period (proposal : Protocol_hash) (ballot : Vote_repr.ballot)
\* failing_noop string

\* Manager operations
\* reveal pub_key
\* transaction amount ?parameters (entrypoint : string) (dest : Contract_repr.contract)
\* origination delegate ?script credit (preorigination : Contract_repr.t option)
\* delegation (pkh : Public_key_hash.t option)

OpHashes == Int
OpTypes == { "Endorsement", "Other" }
Operations == [ type : OpTypes, hash : OpHashes ]

OperationsWithHash(h) == [ type : OpTypes, hash : {h} ]

===========================
