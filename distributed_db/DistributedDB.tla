--------------------------- MODULE DistributedDB ---------------------------

EXTENDS Utils

CONSTANTS NumNodes,     \* number of nodes
          MaxQueueSize, \* bound on size of message queues
          NumChains,    \* initial number of chain ids
          N             \* bound on many things **to make model finite**

VARIABLES \* local information
          node_info,    \* record fields:
                        \* active   : [ Nodes -> SUBSET Chains ]
                        \* messages : [ Nodes -> [ Chains -> Seq(Messages) ] ]
                        \* branch   : [ Nodes -> [ Chains -> Branches ] ]
                        \* blocks   : [ Nodes -> [ Chains -> [ Branches -> Seq(Blocks) ] ] ] ]
          \* global view of network
          network_info  \* [ chains   : Chains
                        \* , branches : [ Chains -> Branches ]
                        \* , heights  : [ Chains -> [ Branches -> Nat ] ]
                        \* , blocks   : [ Chains -> [ Branches -> Seq(Blocks) ] ]
                        \* , protocol : Protocols
                        \* , active   : [ Chains -> SUBSET Nodes ]
                        \* , sent     : [ Chains -> [ Nodes -> Seq(Messages) ] ]
                        \* , recv     : [ Chains -> [ Nodes -> Seq(Messages) ] ] ]

vars == <<network_info, node_info>>

----------------------------------------------------------------------------

Nodes == 1..NumNodes

Chains == 1..NumChains

Branches == 0..N

Heights == 0..N

Protocols == 0..N

Headers ==
    [ height : Heights, chain : Chains, branch : Branches
    , protocol : Protocols, num_ops : 0..N ]

Operations == [ 0..N -> Pairs(Heights, 0..N) ]

Blocks == [ header : Headers, ops : Operations ]

----------------------------------------------------------------------------

(* Module-specific helper functions *)
\* check that [node]'s message queue on [chain] is not full
checkNodeQueue[node \in Nodes] ==
    [ chain \in Chains |-> Len(node_info.messages[chain][node]) < MaxQueueSize ]

\* check that there is space to send [node] a message on [chain]
checkNetQueue[chain \in Chains] ==
    [ node \in Nodes |-> Len(network_info.sent[chain][node]) < MaxQueueSize ]

RECURSIVE _update_msgs(_, _, _)
_update_msgs(msgs, msg, to_update) ==
    CASE to_update = {} -> msgs
    [] OTHER ->
         LET p == Pick(to_update)
             new == [ msgs EXCEPT ![p] = Append(@, msg) ]
         IN  _update_msgs(new, msg, to_update \ {p})

update_msgs(msgs, chain, msg) ==
    LET from == msg.from
        active == network_info.active[chain] \ {from}
        receivers ==
          { node \in active : checkNetQueue[chain][node] }
    IN  _update_msgs(msgs, msg, receivers)

(* check that queue is not full before appending the message *)
checkAppend(queue, msg) ==
    CASE Len(queue) < MaxQueueSize -> Append(queue, msg)
      [] OTHER -> queue

(* Blocks *)
Header(_height, _chain, _branch, _protocol, _num_ops) ==
    [ height |-> _height, chain |-> _chain, branch |-> _branch
    , protocol |-> _protocol, num_ops |-> _num_ops ]

Block(_header, _ops) == [ header |-> _header, ops |-> _ops ]

mkOps(_height, _num_ops) == [ x \in 1.._num_ops |-> <<_height, x>> ]

isNetwork(info) == DOMAIN info =
    { "active", "branches", "blocks", "chains", "protocol", "recv", "sent" }

isNode(info) == DOMAIN info = { "active", "branch", "blocks", "messages" }

\* If info = node_info, check that checkNodeQueue[node][chain] is satisified
\* If info = network_info, check that checkNetQueue[chain][node] is satisified
Recv(info, node, chain, msg) ==
    \* node_info
    CASE isNode(info)
        -> [ info EXCEPT !.messages =
               [ @ EXCEPT ![node] =
                   [ @ EXCEPT ![chain] = Append(@, msg) ] ] ]
    \* network_info
      [] isNetwork(info)
        -> [ info EXCEPT !.recv =
               [ @ EXCEPT ![chain] =
                   [ @ EXCEPT ![node] = <<msg>> \o @ ] ] ]

\* If info = network_info, must check that network_info.sent[chain][node] # <<>>
\* If info = node_info, must check that node_info.sent[node][chain] # <<>>
Consume(info, node, chain) ==
    \* network_info
    CASE isNetwork(info)
        -> [ info EXCEPT !.sent =
               [ @ EXCEPT ![chain] =
                   [ @ EXCEPT ![node] = Tail(@) ] ] ]
    \* node_info
      [] isNode(info) ->
           [ info EXCEPT !.messages =
               [ @ EXCEPT ![node] =
                   [ @ EXCEPT ![chain] = Tail(@) ] ] ]

\* Must check that checkNetQueue[chain][node] is satisfied
Sent(info, node, chain, msg) ==
    CASE isNetwork(info)
        -> [ info EXCEPT !.sent =
               [ @ EXCEPT ![chain] =
                   [ @ EXCEPT ![node] = Append(@, msg) ] ] ]

\* 
CheckSent(info, node, chain, msg) ==
    CASE isNetwork(info)
        -> [ info EXCEPT !.sent =
               [ @ EXCEPT ![chain] =
                   [ to \in Nodes |->
                       LET curr == @[to]
                       IN \* if active and has queue space, append msg
                         CASE to \in info.active[chain] \ {node}
                             -> checkAppend(curr, msg)
                          \* otherwise, do nothing
                           [] OTHER -> curr ] ] ]

----------------------------------------------------------------------------

(* Messages *)

(* Advertise messages *)
(*
 - Current_branch of Chain_id.t * Block_locator.t
 - Current_head of Chain_id.t * Block_header.t * Mempool.t
 - Block_header of Block_header.t
 - Operation of Operation.t
 - Protocol of Protocol.t
 - Operations_for_block of
      Block_hash.t * int * Operation.t list * Operation_list_list_hash.path
 - Checkpoint of Chain_id.t * Block_header.t
 - Protocol_branch of
      Chain_id.t * int (* proto_level: uint8 *) * Block_locator.t
 - Predecessor_header of Block_hash.t * int32 * Block_header.t
*)

Locators == { "locator" }       \* what is this?

Mempools == { "mempool" }       \* is this associated with a block or node?

AdParams ==
    [ chain : Chains,  locator : Locators ]
    \cup
    [ chain : Chains, header : Headers, mempool : Mempools ]
    \cup
    [ header : Headers ]
    \cup
    [ operation : Operations ]
    \cup
    [ protocol : Protocols ]
    \cup
    [ height : Heights, (*branch?,*) ops : NESeq_n(Operations, N)
    , ops_hash : NESeq_n(Heights, N) ]
    \cup
    [ chain : Chains, header : Headers ]
    \cup
    [ chain : Chains, (*int?,*) locator : Locators ]
    \cup
    [ height : Heights, (*int32?,*) header : Headers ]

AdMsgTypes ==
    { "Current_branch", "Current_head", "Block_header", "Operation"
    , "Protocol", "Operations_for_block", "Checkpoint", "Protocol_branch"
    , "Predecessor_header" }

AdMsgs == [ from : Nodes, type : AdMsgTypes, params : AdParams ]

(* Request messages *)
(*
 - Get_current_branch of Chain_id.t
 - Get_current_head of Chain_id.t
 - Get_checkpoint of Chain_id.t
 - Get_protocol_branch of Chain_id.t * int
 - Get_block_headers of Block_hash.t list
 - Get_operations of Operation_hash.t list
 - Get_protocols of Protocol_hash.t list
 - Get_operations_for_blocks of (Block_hash.t * int) list
 - Get_predecessor_header of Block_hash.t * int32
*)
ReqParams ==
    [ chain : Chains ]                                     \* current_branch, current_head, checkpoint
    \cup
    [ chain : Chains, branch : 1..N ]                      \* branch? for Get_protocol_branch
    \cup
    [ heights : NESeq_n(Heights, N) ]                      \* headers, operations, protocols
    \cup
    [ height_num_list : NESeq_n(Pairs(Heights, 1..N), N) ] \* num?
    \cup
    [ height : Heights, num : 1..N ]                       \* num?

OnlyChain == { "Get_current_branch", "Get_current_head", "Get_checkpoint" }

OnlyHeights == { "Get_block_headers", "Get_operations", "Get_protocols" }

ChainAndBranch == { "Get_protocol_branch" }

HeightNumList == { "Get_operations_for_blocks" }

HeightAndNum == { "Get_predecessor_header" }

ReqMsgTypes ==
    OnlyChain \cup OnlyHeights \cup ChainAndBranch \cup HeightNumList \cup HeightAndNum

ReqMsgs == [ from : Nodes, type : ReqMsgTypes, params : ReqParams ]

\* All messages
Messages == AdMsgs \cup ReqMsgs

\* Queues can have size at most MaxQueueSize
PossibleQueueStates == Seq_n(Messages, MaxQueueSize)

(* validates _type matches _params and creates the message *)
(* invalid type/param pairs will return a TLC error *)
Msg(_from, _type, _params) ==
    CASE \/ /\ _type \in OnlyChain
            /\ DOMAIN _params = { "chain" }
         \/ /\ _type \in OnlyHeights
            /\ DOMAIN _params = { "heights" }
         \/ /\ _type \in ChainAndBranch
            /\ DOMAIN _params = { "chain", "branch" }
         \/ /\ _type \in HeightNumList
            /\ DOMAIN _params = { "height_num_list" }
         \/ /\ _type \in HeightAndNum
            /\ DOMAIN _params = { "height", "num" }
         -> [ from |-> _from, type |-> _type, params |-> _params ]

----------------------------------------------------------------------------

(* Activate/Deactivate messages are not explicitly passed between nodes in this model *)

(* An inactive node becomes active on given chain *)
Activate(node, chain) ==
    /\ network_info' =
         [ network_info EXCEPT !.active = [ @ EXCEPT ![chain] = @ \cup {node} ] ]
    /\ node_info' =
         [ node_info EXCEPT !.active = [ @ EXCEPT ![node] = @ \cup {chain} ] ]

(* An active node becomes inactive on given chain *)
Deactivate(node, chain) ==
    /\ network_info' =
         [ network_info EXCEPT !.active = [ @ EXCEPT ![chain] = @ \ {node} ] ]
    /\ node_info' =
         [ node_info EXCEPT !.active = [ @ EXCEPT ![node] = @ \ {chain} ] ]

----------------------------------------------------------------------------

(* Request actions *)
(* Messages are sent to a queue where the receipient can receive the message *)

(* Request the current branch from one active peer *)
\* must check that [to] has room left in their queue
Get_current_branch_1(from, chain, to) ==
    LET msg == Msg(from, "Get_current_branch", [ chain |-> chain ])
    IN
      /\ network_info' = Sent(network_info, to, chain, msg)
      /\ UNCHANGED node_info

(* Request the current branch from all active peers *)
Get_current_branch_n(from, chain) ==
    LET msg == Msg(from, "Get_current_branch", [ chain |-> chain ])
    IN
      /\ network_info' = CheckSent(network_info, from, chain, msg)
      /\ UNCHANGED node_info

(* Request the current head from one active peer *)
Get_current_head_1(from, chain, to) ==
    LET msg == Msg(from, "Get_current_head", [ chain |-> chain ])
    IN
      /\ network_info' = Sent(network_info, to, chain, msg)
      /\ UNCHANGED node_info

(* Request the current head from all active peers *)
Get_current_head_n(from, chain) ==
    LET msg == Msg(from, "Get_current_head", [ chain |-> chain ])
    IN
      /\ network_info' = CheckSent(network_info, from, chain, msg)
      /\ UNCHANGED node_info

----------------------------------------------------------------------------

(* Advertise actions *)
(* Advertise messages are explicitly passed between nodes *)

\* TODO
\* These messages do not only serve as responses to requests
\* They are also broadcast to the active nodes of the chain?

----------------------------------------------------------------------------

(* Receiving messages *)
Receive_msg(node, chain) ==
    LET recv_q == network_info.sent[chain][node]
        in_q == node_info.messages[node][chain]
    IN
      /\ recv_q # <<>>                  \* there are messages for [node] to receive
      /\ checkNodeQueue[node][chain]    \* [node] has space for incoming messages
      /\ LET msg == Head(recv_q)
         IN
           \* [msg] is added to the end of [node]'s queue
           /\ node_info' =
                [ node_info EXCEPT !.messages =
                    [ @ EXCEPT ![node] = [ @ EXCEPT ![chain] = Append(@, msg) ] ] ]
           \* [msg] is removed from [node]'s sent and add to the beginning of recv
           /\ LET new == Consume(network_info, node, chain)
                  new_info == Recv(new, node, chain, msg)
              IN network_info' = new_info

----------------------------------------------------------------------------

(* Protocol upgrade *)
Protocol_upgrade ==
    /\ network_info.protocol < N
    /\ network_info' = [ network_info EXCEPT !.protocol = @ + 1 ]
    /\ UNCHANGED node_info

(* Block production *)
Produce_block(chain, branch, num_ops) ==
    LET proto == network_info.protocol                    \* current protocol
        height == network_info.heights[chain][branch] + 1 \* next block height
        ops == mkOps(height, num_ops)
        header == Header(height, chain, branch, proto, num_ops)
    IN
      /\ height <= N
      /\ network_info' =
           [ network_info EXCEPT
               !.blocks = [ c \in Chains |-> [ b \in network_info.branches[c] |->
                 CASE b = branch -> Append(@, Block(header, ops))
                   [] OTHER -> @ ] ] ]
      /\ UNCHANGED node_info

(* New branch *)
New_branch_for(chain) ==
    /\ network_info.branches[chain] < N
    /\ network_info' =
         [ network_info EXCEPT !.branches = [ @ EXCEPT ![chain] = @ + 1 ] ]
    /\ UNCHANGED node_info

----------------------------------------------------------------------------

\* TODO
(* A node that is inactive on a chain becomes active *)
Activation ==
    \E chain \in Chains :
        \E node \in Nodes \ network_info.active[chain] : Activate(node, chain)

(* A node that is active on a chain becomes inactive *)
Deactivation ==
    \E chain \in Chains :
        \E node \in network_info.active[chain] : Deactivate(node, chain)

(* Request current branch from an active peer who can receive a message *)
Get_current_branch_one ==
    \E from \in Nodes, chain \in Chains :
        \E to \in network_info.active[chain] \ {from} :
            /\ checkNetQueue[chain][to]
            /\ Get_current_branch_1(from, chain, to)

(* Request current branch from all active peers *)
Get_current_branch_all ==
    \E from \in Nodes :
        \E chain \in node_info.active[from] :
            /\ network_info.active[chain] \ {from} # {}
            /\ Get_current_branch_n(from, chain)

(* Request current head from an active peer *)
Get_current_head_one ==
    \E from \in Nodes :
        \E chain \in node_info.active[from] :
            \E to \in network_info.active[chain] \ {from} :
                /\ checkNetQueue[chain][to]
                /\ Get_current_head_1(from, chain, to)

(* Request current head from all active peers *)
Get_current_head_all ==
    \E from \in Nodes :
        \E chain \in node_info.active[from] :
            /\ network_info.active[chain] \ {from} # {}
            /\ Get_current_head_n(from, chain)

(* Receive a message *)
Receive ==
    \E chain \in Chains :
        \E node \in network_info.active[chain] : Receive_msg(node, chain)

----------------------------------------------------------------------------

(* A block is produced on an existing chain *)
Block_production ==
    \E chain \in 1..network_info.chains :
        \E branch \in 1..network_info.branches[chain], num_ops \in 0..N :
            Produce_block(chain, branch, num_ops)

----------------------------------------------------------------------------

(* Type invariant *)
TypeOK ==
    \* active nodes
    /\ \A node \in Nodes, chain \in Chains :
         node \in network_info.active[chain] <=> chain \in node_info.active[node]
    /\ network_info \in
         [ chains   : Chains
         , branches : [ Chains -> Branches ]
         , blocks   : [ Chains -> [ Branches -> Seq(Blocks) ] ]
         , protocol : Protocols
         , active   : [ Chains -> SUBSET Nodes ]
         , sent     : [ Chains -> [ Nodes -> Seq(Messages) ] ]
         , recv     : [ Chains -> [ Nodes -> Seq(Messages) ] ] ]
    /\ node_info \in
         [ active   : [ Nodes -> SUBSET Chains ]
         , messages : [ Nodes -> [ Chains -> Seq(Messages) ] ]
         , branches : [ Nodes -> [ Chains -> SUBSET Branches ] ]
         , blocks   : [ Nodes -> [ Chains -> [ Branches -> Seq(Blocks) ] ] ] ]

----------------------------------------------------------------------------

Init ==
    /\ network_info =
         [ chains   |-> 1
         , branches |-> [ c \in Chains |-> 0 ]
         , blocks   |-> [ c \in Chains |-> [ b \in Branches |-> <<>> ] ]
         , protocol |-> 0
         , active   |-> [ c \in Chains |-> {} ]
         , sent     |-> [ c \in Chains |-> [ n \in Nodes |-> <<>> ] ]
         , recv     |-> [ c \in Chains |-> [ n \in Nodes |-> <<>> ] ] ]
    /\ node_info =
         [ active   |-> [ n \in Nodes |-> {} ]
         , messages |-> [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
         , branches |-> [ n \in Nodes |-> [ c \in Chains |-> {} ] ]
         , blocks   |-> [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |-> <<>> ] ] ] ]

Next ==
    \/ Activation
    \/ Deactivation
    \/ Get_current_branch_one
    \/ Get_current_branch_all
    \/ Get_current_head_one
    \/ Get_current_head_all
    \/ Receive
    \/ Protocol_upgrade
    \* TODO finish

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------

(* Invariants *)
\* TODO

\* Once a message is sent, it is eventually received by the intended recipient
\* A [msg] to a [node] ends up in recv[chain][node] iff msg \in in_messages[chain][node]

=============================================================================
