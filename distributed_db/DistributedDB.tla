--------------------------- MODULE DistributedDB ---------------------------

EXTENDS Utils

CONSTANTS numNodes,     \* number of nodes
          numChains,    \* number of chains
          sizeBound     \* bound on many things **to make model finite**

VARIABLES \* local information
          node_info,    \* active   : [ Nodes -> SUBSET Chains ]
                        \* messages : [ Nodes -> [ Chains -> Seq(Messages) ] ]
                        \* branches : [ Nodes -> [ Chains -> Seq(Branches) ] ]
                        \* blocks   : [ Nodes -> [ Chains -> [ Branches -> Seq(Blocks) ] ] ] ]
          \* global view of network
          network_info  \* chains   : Chains
                        \* branch   : [ Chains -> Branches ]
                        \* height   : [ Chains -> [ Branches -> Heights ] ]
                        \* blocks   : [ Chains -> [ Branches -> Seq(Blocks) ] ]
                        \* protocol : Protocols
                        \* active   : [ Chains -> SUBSET Nodes ]
                        \* sent     : [ Chains -> [ Nodes -> SUBSET Messages ] ]
                        \* recv     : [ Chains -> [ Nodes -> Seq(Messages) ] ] ]

vars == <<network_info, node_info>>

----------------------------------------------------------------------------

Nodes == 1..numNodes

Chains == 1..numChains

Branches == 0..sizeBound

Heights == 0..sizeBound

Protocols == 0..sizeBound

Op_nums == 0..sizeBound

Headers ==
    [ height : Heights, chain : Chains, branch : Branches
    , protocol : Protocols, num_ops : Op_nums ]

Operations == [ Op_nums -> Pairs(Heights, 0..sizeBound) ]

Blocks == [ header : Headers, ops : Operations ]

----------------------------------------------------------------------------

(* Module-specific helper functions *)
\* check that [node]'s message queue on [chain] is not full
checkMessages[node \in Nodes] ==
    [ chain \in Chains |-> Len(node_info.messages[chain][node]) < sizeBound ]

\* check that there is space to send [node] a message on [chain]
checkSent[chain \in Chains] ==
    [ node \in Nodes |-> Cardinality(network_info.sent[chain][node]) < sizeBound ]

(* check that set is not full before including the message *)
checkUnion(set, msg) ==
    CASE Cardinality(set) < sizeBound -> set \cup {msg}
      [] OTHER -> set

(* Blocks *)
Header(height, chain, branch, protocol, num_ops) ==
    [ height |-> height, chain |-> chain, branch |-> branch
    , protocol |-> protocol, num_ops |-> num_ops ]

Block(header, ops) == [ header |-> header, ops |-> ops ]

mkOps(height, num_ops) == [ x \in 1..num_ops |-> <<height, x>> ]

isNetwork(info) == DOMAIN info =
    { "active", "branch", "blocks", "chains", "height", "protocol", "recv", "sent" }

isNode(info) == DOMAIN info = { "active", "branches", "blocks", "messages" }

\* If info = node_info, check that checkMessages[node][chain] is satisified
\* If info = network_info, check that checkSent[chain][node] is satisified
Recv(info, chain, node, msg) ==
    CASE isNode(info)    -> [ info EXCEPT !.messages[node][chain] = Append(@, msg) ]
      [] isNetwork(info) -> [ info EXCEPT !.recv[chain][node] = <<msg>> \o @ ]

\* If info = network_info, must check that network_info.sent[chain][node] # {}
\* If info = node_info, must check that node_info.messages[node][chain] # <<>>
Consume(info, chain, node, msg) ==
    CASE isNetwork(info) -> [ info EXCEPT !.sent[chain][node] = @ \ {msg} ]
      [] isNode(info)    -> [ info EXCEPT !.messages[node][chain] = Tail(@) ]

\* Must check that checkSent[chain][node] is satisfied
Sent(info, node, chain, msg) ==
    CASE isNetwork(info) -> [ info EXCEPT !.sent[chain][node] = @ \cup {msg} ]

\* Sends [msg] to all active nodes who can recieve it
SendToActive(info, from, chain, msg) ==
    CASE isNetwork(info) -> [ info EXCEPT !.sent[chain] =
      [ to \in Nodes |->
          LET curr == @[to]
          IN  \* if node is active and has sent space, add msg to sent
            CASE to \in info.active[chain] \ {from} -> checkUnion(curr, msg)
              \* else, do nothing
              [] OTHER -> curr ] ]

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
    [ height : Heights, (*branch?,*) ops : NESeq_n(Operations, sizeBound)
    , ops_hash : NESeq_n(Heights, sizeBound) ]
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
    [ chain : Chains, branch : 0..sizeBound ]              \* branch? for Get_protocol_branch
    \cup
    [ heights : NESeq_n(Heights, sizeBound) ]              \* headers, operations, protocols
    \cup
    [ height_num_list : NESeq_n(Pairs(Heights, 1..sizeBound), sizeBound) ] \* num?
    \cup
    [ height : Heights, num : 1..sizeBound ]                       \* num?

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
PossibleQueueStates == Seq_n(Messages, sizeBound)

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

(* Activate/Deactivate actions *)
(* These messages are not explicitly passed between nodes in this model *)

\* An inactive node becomes active on given chain
Activate(node, chain) ==
    /\ network_info' = [ network_info EXCEPT !.active[chain] = @ \cup {node} ]
    /\ node_info' = [ node_info EXCEPT !.active[node] = @ \cup {chain} ]

Activation ==
    \E chain \in Chains :
        \E node \in Nodes \ network_info.active[chain] : Activate(node, chain)

\* An active node becomes inactive on given chain
Deactivate(node, chain) ==
    /\ network_info' = [ network_info EXCEPT !.active[chain] = @ \ {node} ]
    /\ node_info' = [ node_info EXCEPT !.active[node] = @ \ {chain} ]

Deactivation ==
    \E chain \in Chains :
        \E node \in network_info.active[chain] : Deactivate(node, chain)

----------------------------------------------------------------------------

(* Request actions *)
(* Messages are sent to a set where the receipient can receive it later *)

\* Request the current branch from one active peer
\* must check that [to] has room left in their queue
Get_current_branch_1(from, chain, to) ==
    LET msg == Msg(from, "Get_current_branch", [ chain |-> chain ])
    IN
      /\ network_info' = Sent(network_info, to, chain, msg)
      /\ UNCHANGED node_info

\* Request current branch from an active peer who can receive a message
Get_current_branch_one ==
    \E from \in Nodes, chain \in Chains :
        \E to \in network_info.active[chain] \ {from} :
            /\ checkSent[chain][to]
            /\ Get_current_branch_1(from, chain, to)

\* Request the current branch from all active peers
\* The request is only sent to active nodes that have room in their sent sets
Get_current_branch_n(from, chain) ==
    LET msg == Msg(from, "Get_current_branch", [ chain |-> chain ])
    IN
      /\ network_info' = SendToActive(network_info, from, chain, msg)
      /\ UNCHANGED node_info

Get_current_branch_all ==
    \E from \in Nodes :
        \E chain \in node_info.active[from] :
            /\ network_info.active[chain] \ {from} # {}
            /\ Get_current_branch_n(from, chain)

\* Request the current head from one active peer
\* must check that 
Get_current_head_1(from, chain, to) ==
    LET msg == Msg(from, "Get_current_head", [ chain |-> chain ])
    IN
      /\ network_info' = Sent(network_info, to, chain, msg)
      /\ UNCHANGED node_info

Get_current_head_one ==
    \E from \in Nodes :
        \E chain \in node_info.active[from] :
            \E to \in network_info.active[chain] \ {from} :
                /\ checkSent[chain][to]
                /\ Get_current_head_1(from, chain, to)

(* Request the current head from all active peers *)
Get_current_head_n(from, chain) ==
    LET msg == Msg(from, "Get_current_head", [ chain |-> chain ])
    IN
      /\ network_info' = SendToActive(network_info, from, chain, msg)
      /\ UNCHANGED node_info

(* Request current head from all active peers *)
Get_current_head_all ==
    \E from \in Nodes :
        \E chain \in node_info.active[from] :
            /\ network_info.active[chain] \ {from} # {}
            /\ Get_current_head_n(from, chain)

----------------------------------------------------------------------------

(* Advertise actions *)
(* Advertise messages are explicitly passed between nodes *)

\* TODO
\* These messages do not only serve as responses to requests
\* They are also broadcast to the active nodes of the chain?

----------------------------------------------------------------------------

(* Receive action *)

\* An active [node] on [chain] receives a message
Receive_msg(node, chain) ==
    LET msgs == network_info.sent[chain][node]
        in_q == node_info.messages[node][chain]
        msg  == Pick(msgs)
    IN
      \* [msg] is added to the end of [node]'s queue
      /\ node_info' = [ node_info EXCEPT !.messages[node][chain] = Append(@, msg) ]
      \* [msg] is removed from [node]'s sent and added to the beginning of recv
      /\ LET new_net == Consume(network_info, chain, node, msg)
         IN network_info' = Recv(new_net, chain, node, msg)

\* If [node] has messages waiting on [chain] and room in their queue, they can receive a message
Receive ==
    \E chain \in Chains :
        \E node \in network_info.active[chain] :
            /\ network_info.sent[chain][node] # {} \* there are [chain] messages for [node] to receive
            /\ checkMessages[node][chain]          \* [node] has space for incoming [chain] messages
            /\ Receive_msg(node, chain)

----------------------------------------------------------------------------

(* Maintanence actions *)

\* Protocol upgrade
Protocol_upgrade ==
    /\ network_info.protocol < sizeBound
    /\ network_info' = [ network_info EXCEPT !.protocol = @ + 1 ]
    /\ UNCHANGED node_info

\* Block production
Produce_block(chain, branch, num_ops) ==
    LET proto  == network_info.protocol                  \* current protocol
        height == network_info.height[chain][branch] + 1 \* next block height on branch
        ops    == mkOps(height, num_ops)                 \* block operations
        header == Header(height, chain, branch, proto, num_ops)
    IN
      /\ network_info' =
           [ network_info EXCEPT !.blocks =
               [ c \in Chains |->
                   [ b \in Branches |->
                       LET blocks == network_info.blocks[c][b] IN
                       CASE b = branch -> <<Block(header, ops)>> \o blocks
                         [] OTHER -> blocks ] ] ]
      /\ UNCHANGED node_info

\* A block is produced on an existing branch of an existing chain
Block_production ==
    \E chain \in 1..network_info.chains :
        \E branch \in 0..network_info.branch[chain], num_ops \in Op_nums :
            /\ network_info.height[chain][branch] < sizeBound
            /\ Produce_block(chain, branch, num_ops)

\* Start a new branch on chain
New_branch_for(chain) ==
    /\ network_info' = [ network_info EXCEPT !.branch[chain] = @ + 1 ]
    /\ UNCHANGED node_info

\* Start a new branch on an existing chain
New_branch ==
    \E chain \in Chains :
        /\ network_info.branch[chain] < sizeBound
        /\ New_branch_for(chain)

----------------------------------------------------------------------------

(* Initial predicate *)
Init ==
    /\ network_info =
         [ chains   |-> 1
         , branch   |-> [ c \in Chains |-> 0 ]
         , blocks   |-> [ c \in Chains |-> [ b \in Branches |-> <<>> ] ]
         , protocol |-> 0
         , height   |-> [ c \in Chains |-> [ b \in Branches |-> -1 ] ]
         , active   |-> [ c \in Chains |-> {} ]
         , sent     |-> [ c \in Chains |-> [ n \in Nodes |-> {} ] ]
         , recv     |-> [ c \in Chains |-> [ n \in Nodes |-> <<>> ] ] ]
    /\ node_info =
         [ active   |-> [ n \in Nodes |-> {} ]
         , messages |-> [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
         , branches |-> [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
         , blocks   |-> [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |-> <<>> ] ] ] ]

(* Next actions *)
Next ==
    \/ Activation
    \/ Deactivation
    \/ Get_current_branch_one
    \/ Get_current_branch_all
    \/ Get_current_head_one
    \/ Get_current_head_all
    \/ Receive
    \/ Protocol_upgrade
    \/ Block_production
    \/ New_branch
    \* TODO finish

(* Fairness conditions *)
WFairness ==
    /\ WF_vars(Activation)
    /\ WF_vars(Deactivation)
    /\ WF_vars(Get_current_branch_one)
    /\ WF_vars(Get_current_branch_all)
    /\ WF_vars(Get_current_head_one)
    /\ WF_vars(Get_current_head_all)
    /\ WF_vars(Receive)
    /\ WF_vars(Protocol_upgrade)
    /\ WF_vars(Block_production)
    /\ WF_vars(New_branch)

(* Specification *)
Spec == Init /\ WFairness /\ [][Next]_vars

----------------------------------------------------------------------------

(* Invariants *)
\* TODO

\* Avoid silliness
TypeOK ==
    /\ network_info \in
         [ chains   : Chains
         , branch   : [ Chains -> Branches ]
         , blocks   : [ Chains -> [ Branches -> Seq(Blocks) ] ]
         , protocol : Protocols
         , height   : [ Chains -> [ Branches -> Heights \cup {-1} ] ]
         , active   : [ Chains -> SUBSET Nodes ]
         , sent     : [ Chains -> [ Nodes -> SUBSET Messages ] ]
         , recv     : [ Chains -> [ Nodes -> Seq(Messages) ] ] ]
    /\ node_info \in
         [ active   : [ Nodes -> SUBSET Chains ]
         , messages : [ Nodes -> [ Chains -> Seq(Messages) ] ]
         , branches : [ Nodes -> [ Chains -> Seq(Branches) ] ]
         , blocks   : [ Nodes -> [ Chains -> [ Branches -> Seq(Blocks) ] ] ] ]

\* network_info & node_info are in agreement
ActiveAgreement ==
    \A node \in Nodes, chain \in Chains :
        \* actives
        /\ node \in network_info.active[chain] <=> chain \in node_info.active[node]
        \* messages
        /\ ToSet(network_info.recv[chain][node]) = ToSet(node_info.messages[node][chain])
        \* branches
        /\ node_info.branches[node][chain] # <<>> =>
             Head(node_info.branches[node][chain]) <= network_info.branch[chain]
        \* blocks
        /\ \A branch \in ToSet(node_info.branches[node][chain]) :
               isSubSeq(node_info.blocks[node][chain][branch], network_info.blocks[chain][branch])

(* Properties *)

\* Once a message is sent, it is eventually received by the intended recipient
\* A [msg] sent to a [node] ends up in recv[chain][node]
SentMessagesAreReceived ==
    \A chain \in Chains :
        \A node \in network_info.active[chain] :
            \A msg \in Messages :
                msg \in network_info.sent[chain][node] ~>
                  /\ msg \in ToSet(network_info.recv[chain][node])
                  /\ msg \in ToSet(node_info.messages[node][chain])

=============================================================================
