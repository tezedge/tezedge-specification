---- MODULE Mempool ----

EXTENDS FiniteSets, Integers, Sequences

VARIABLES
    peers,
    outgoing,
    incoming,
    head,
    live_blocks,
    live_ops,
    known_valid,
    fetching,
    pending,
    mempool,
    banned,
    advertisement,
    applied,
    branch_delayed,
    branch_refused,
    refused

----

(*
The mempool manages a *validation state* based upon the current head chosen by the validation subsystem
- each time the mempool receives an operation
  - it tries to classify it on top of the current validation state
    - if the operation is applied successfully
      - the validation state is updated
      - the operation is classified as `Applied`
      - the operation is propagated to peers
    - else, the handling of the operation depends on its *classification* which is detailed below
      - given an operation, its classification may change if the head changes
      - when the validation subsystem switches its head
        - it notifies the mempool with the new `live_blocks` and `live_operations`, and
        - triggers a `flush` of the mempool
          - every classified operation which is *anchored* on a *live* block and which is not in the
            `live_operations` is set as `pending`, meaning they are waiting to be classified again
          - an exception is made for operations classified as `Branch_refused`
            - those operations are reclassified only if the old head is not the predecessor of the new head
*)

(* Operations *)
\* TODO

\* TODO classify operation on top of current validation state
\* do not want to advertise [refused] operations

\* TODO status
\* - fetching: hash known, operation not received
\* - pending: hash and operation known, not classified on top of [head]
\* - classified: hash and operation known, classification has been given
\* - banned: removed from all other fields and ignored when received in any form

\* TODO advertise [advertisement] + [mempool]

\* TODO prevalidator invariant: operation cannot be in more than one of [fetching], [pending], [in_mempool], and [banned]

========================
