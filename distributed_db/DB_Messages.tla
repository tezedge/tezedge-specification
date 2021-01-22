---------------------------- MODULE DB_Messages -----------------------------

CONSTANTS numChains, numNodes, sizeBound

VARIABLES network_info, node_info

LOCAL INSTANCE DB_Defs
LOCAL INSTANCE Utils

-----------------------------------------------------------------------------

\* There 2 types of messages:
\* - Full (advertise/request)
\* - Synchronization (expect/acknowledge/error)

-----------------------------------------------------------------------------

(***************************************)
(* Full messages (2 kinds):            *)
(* - Advertise messages                *)
(* - Request messages                  *)
(***************************************)

(* Advertise messages *)
(* Used to respond to specific requests and to broadcast messages to all active nodes on a chain *)

\* Advertise message parameters
AdParams ==
    [ branch : Branches ] \* Current_branch
    \cup
    [ branch : Branches, height : Heights ] \* Current_head
    \cup
    [ branch : Branches, height : Heights, header : Headers ] \* Block_header
    \cup
    [ branch : Branches, height : Heights, ops : Operations ] \* Operations

\* Advertise message types
AdMsgTypes == { "Block_header", "Current_branch", "Current_head", "Operations" }

\* Advertise messages
AdMsgs == [ from : Nodes, type : AdMsgTypes, params : AdParams ]


(* Request messages *)
(* Used to request specific info either from a single node or from all active nodes on a chain *)

\* Request message parameters
ReqParams ==
    [ chain : Chains ] \* Get_current_branch
    \cup
    [ branch : Branches ] \* Get_current_head
    \cup
    [ branch : Branches, height : Heights ] \* Get_block_header & Get_operations

\* Request message types
ReqMsgTypes == { "Get_block_header", "Get_current_branch", "Get_current_head", "Get_operations" }

\* Request messages
ReqMsgs == [ from : Nodes, type : ReqMsgTypes, params : ReqParams ]

\* A full message is either an advertise or request message
FullMsgs == AdMsgs \cup ReqMsgs

-----------------------------------------------------------------------------

(***************************************)
(* Synchronization messages (2 kinds): *)
(* - Expect messages                   *)
(* - Acknowledgment/error messages     *)
(***************************************)

(* Acknowledgment messages *)
(* Used to acknowlegde the receipt of a message from a node *)

\* Error message params
ErrorParams == [ branch : Branches, height : Heights ]

\* Error message types
ErrorMsgTypes == { "Err_block_header", "Err_operations" }

\* Error messages
ErrorMsgs == [ from : Nodes, type : ErrorMsgTypes, error : ErrorParams ]

\* Acknowledgment message types
AckMsgTypes == { "Ack_block_header", "Ack_current_branch", "Ack_current_head", "Ack_operations" }

\* Acknowledgment/error messages
AckMsgs == [ from : Nodes, type : AckMsgTypes ]

(* Expect messages *)
(* Used to register an expected response from a node *)

\* Expect message parameters
ExpectParams == ReqParams

\* Expect message types
ExpectMsgTypes == AdMsgTypes \cup AckMsgTypes

\* Expect messages
ExpectMsgs == [ from : Nodes, type : ExpectMsgTypes, expect : ExpectParams ]

\* A sync message is an ack, expect, or error message
SyncMsgs == AckMsgs \cup ExpectMsgs \cup ErrorMsgs

-----------------------------------------------------------------------------

(****************)
(* All messages *)
(****************)

Messages == FullMsgs \cup SyncMsgs

-----------------------------------------------------------------------------

\* full message predicate
isFullMsg(msg) == DOMAIN msg = { "from", "params", "type" }

\* advertise message predicate
isAdMsg(msg) == isFullMsg(msg) /\ msg.type \in AdMsgTypes

\* request message predicate
isReqMsg(msg) == isFullMsg(msg) /\ msg.type \in ReqMsgTypes

\* ack message predicate
isAckMsg(msg) == DOMAIN msg = { "from", "type" }

\* error message predicate
isErrorMsg(msg) == DOMAIN msg = { "error", "from", "type" }

\* expect message predicate
isExpectMsg(msg) == DOMAIN msg = { "expect", "from", "type" }

\* [msg] is a non-expect message
isNonExpectMsg(msg) ==
    \/ isAdMsg(msg)
    \/ isReqMsg(msg)
    \/ isAckMsg(msg)
    \/ isErrorMsg(msg)

\* Message "constructors"
\* validates [type] matches [params] and creates the message
\* invalid type/param pairs will return a TLC error
OnlyChain == { "Get_current_branch" }

OnlyBranch == { "Get_current_head", "Current_branch" }

BranchHeight == { "Get_block_header", "Get_operations", "Current_head" }

BranchHeightOps == { "Operations" }

BranchHeightHeader == { "Block_header" }

\* Full message "constructor"
Msg(from, type, params) ==
    CASE \/ /\ type \in OnlyChain
            /\ DOMAIN params = { "chain" }
         \/ /\ type \in OnlyBranch
            /\ DOMAIN params = { "branch" }
         \/ /\ type \in BranchHeight
            /\ DOMAIN params = { "branch", "height" }
         \/ /\ type \in BranchHeightOps
            /\ DOMAIN params = { "branch", "height", "ops" }
         \/ /\ type \in BranchHeightHeader
            /\ DOMAIN params = { "branch", "height", "header" } ->
         [ from |-> from, type |-> type, params |-> params ]

\* Synchronization message "constructors"
ExpectMsg(from, type, expect) ==
    CASE type \in ExpectMsgTypes -> [ from |-> from, type |-> type, expect |-> expect ]

AckMsg(from, type) ==
    CASE type \in AckMsgTypes -> [ from |-> from, type |-> type ]

ErrorMsg(from, type, error) ==
    CASE type \in ErrorMsgTypes -> [ from |-> from, type |-> type, error |-> error ]

-----------------------------------------------------------------------------

(****************)
(* Expectations *)
(****************)

\* convert advertise msg type to corresponding ack type
ack_type[ type \in AdMsgTypes ] ==
    CASE type = "Current_branch" -> "Ack_current_branch"
      [] type = "Current_head"   -> "Ack_current_head"
      [] type = "Block_header"   -> "Ack_block_header"
      [] type = "Operations"     -> "Ack_operations"

\* compute set of expected responses for [msg]
\* this set is either empty or contains a single expect message
\* a node can have any non-expect message to handle
expect_msg(to, msg) ==
    LET type   == msg.type
        params == msg.params
    IN CASE \* Request messages - advertise expected
            type = "Get_current_branch" -> {ExpectMsg(to, "Current_branch", [ chain |-> params.chain ])}
         [] type = "Get_current_head" -> {ExpectMsg(to, "Current_head", [ branch |-> params.branch ])}
         [] type = "Get_block_header" ->
              {ExpectMsg(to, "Block_header", [ branch |-> params.branch, height |-> params.height ])}
         [] type = "Get_operations" ->
              {ExpectMsg(to, "Operations", [ branch |-> params.branch, height |-> params.height ])}
            \* Advertise messages - ack expected
         [] type \in AdMsgTypes -> {AckMsg(to, ack_type[type])}
            \* Ack and Sys messages - nothing expected
         [] type \in AckMsgTypes -> {} \* no response expected from an ack message

\* from the type of an expected message, compute the original message type 
type_of_expect[ type \in ExpectMsgTypes ] ==
      \* advertise messages are expected as responses to request messages
    CASE type = "Current_branch" -> "Get_current_branch"
      [] type = "Current_head" -> "Get_current_head"
      [] type = "Block_header" -> "Get_block_header"
      [] type = "Operations" -> "Get_operations"
      \* acknowledgments are expected as responses to advertise messages
      [] type = "Ack_current_branch" -> "Current_branch"
      [] type = "Ack_current_head" -> "Current_head"
      [] type = "Ack_block_header" -> "Block_header"
      [] type = "Ack_operations" -> "Operations"

\* from an expected message, generate the original message to send again
msg_of_expect(exp) ==
    LET sender == exp.from
        params == exp.expect
        type   == exp.type
    IN Msg(sender, type_of_expect[type], params)

-----------------------------------------------------------------------------

(********************************)
(* Message-based action helpers *)
(********************************)

\* Send [msg] to [to] on [chain]
\* sent \in SUBSET Messages
Send(sent, msg) == checkAdd(sent, msg)

\* Register an expectation
\* expect \in SUBSET ExpectMsgs
Expect(expect, from, msg) == checkUnion(expect, expect_msg(from, msg))

\* Sends [msg] to all active nodes and [sys] on [chain]
\* sent \in [ SysNodes -> SUBSET Messages ]
Broadcast(sent, from, chain, msg) == checkAddToActive(sent, from, chain, msg)

\* Sends [msg] to all active nodes on [chain]
\* sent \in [ SysNodes -> SUBSET Messages ]
\* UNCHANGED network_info.sent[chain][sys] 
BroadcastNodes(sent, from, chain, msg) == checkAddToActiveNodes(sent, from, chain, msg)

\* Remove expected messages
ManageExpect(expect, from, type) ==
    LET exp_from == { exp \in expect : exp.from = from }
        exp_type == { exp \in exp_from : exp.type = type }
    IN expect \ exp_type

=============================================================================
