---------------------------- MODULE DB_Messages -----------------------------

CONSTANTS numChains, numNodes, sizeBound

VARIABLES network_info, node_info

LOCAL INSTANCE DB_Defs
LOCAL INSTANCE Utils

-----------------------------------------------------------------------------

\* There 3 types of messages:
\* - Full (advertise/request)
\* - Synchronization (expect/acknowledge)
\* - System

-----------------------------------------------------------------------------

(***************************************)
(* Full messages (2 kinds):            *)
(* - Advertise messages                *)
(* - Request messages                  *)
(***************************************)

(* Advertise messages *)
(* Used to respond to specific requests and to broadcast messages to all active nodes on a chain *)

\* - Current_branch
\* - Current_head
\* - Block_header
\* - Operations

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
AdMsgTypes == { "Current_branch", "Current_head", "Block_header", "Operations" }

\* Advertise messages
AdMsgs == [ from : Nodes, type : AdMsgTypes, params : AdParams ]


(* Request messages *)
(* Used to request specific info either from a single node or from all active nodes on a chain *)

\* - Get_current_branch
\* - Get_current_head
\* - Get_block_header
\* - Get_operations

\* Request message parameters
ReqParams ==
    [ chain : Chains ] \* Get_current_branch
    \cup
    [ branch : Branches ] \* Get_current_head
    \cup
    [ branch : Branches, height : Heights ] \* Get_block_header & Get_operations

\* Request message types
ReqMsgTypes == { "Get_current_branch", "Get_current_head", "Get_block_header", "Get_operations" }

\* Request messages
ReqMsgs == [ from : Nodes, type : ReqMsgTypes, params : ReqParams ]

\* A full message is either an advertise or request message
FullMsgs == AdMsgs \cup ReqMsgs

-----------------------------------------------------------------------------

(***************************************)
(* Synchronization messages (2 kinds): *)
(* - Expect messages                   *)
(* - Acknowledgement/error messages    *)
(***************************************)

(* Acknowledgement messages *)
(* Used to acknowlegde the receipt of a message from a node *)

\* Error message types
ErrorMsgTypes == { "Unkown_block" }

\* Error messages
ErrorMsgs == [ from : Nodes, type : ErrorMsgTypes ]

\* Acknowledgement message types
AckMsgTypes == { "Ack_current_branch", "Ack_current_head", "Ack_block_header", "Ack_operation" }

\* Acknowledgement/error messages
AckMsgs == [ from : Nodes, type : AckMsgTypes ] \cup ErrorMsgs

(* Expect messages *)
(* Used to register an expected response from a node *)

\* Expect message parameters
ExpectParams == ReqParams

\* Expect message types
ExpectMsgTypes == AdMsgTypes \cup AckMsgTypes \cup ErrorMsgTypes

\* Expect messages
ExpectMsgs == [ from : Nodes, type : ExpectMsgTypes, expect : ExpectParams ]

\* A sync message is either an ack or expect message
SyncMsgs == AckMsgs \cup ExpectMsgs

-----------------------------------------------------------------------------

(*******************)
(* System messages *)
(*******************)

NewBlock == { "New_block" }

NewBranch == { "New_branch" }

NewChain == { "New_chain" }

\* System message types
SysMsgTypes == NewBlock \cup NewBranch \cup NewChain

\* System message parameters
SysParams ==
    [ block : Blocks ] \* New_block
    \cup
    [ branch : Branches ] \* New_branch
    \cup
    [ chain : Chains ] \* New_chain

\* System messages
SysMsgs == [ type : SysMsgTypes, params : SysParams ]

-----------------------------------------------------------------------------

(****************)
(* All messages *)
(****************)

Messages == FullMsgs \cup ExpectMsgs \cup SysMsgs

-----------------------------------------------------------------------------

\* full message predicate
isFullMsg[ msg \in Messages ] == DOMAIN msg = { "from", "params", "type" }

\* ack message predicate
isAckMsg[ msg \in Messages ] == DOMAIN msg = { "from", "type" }

\* expect message predicate
isExpectMsg[ msg \in Messages ] == DOMAIN msg = { "expect", "from", "type" }

\* system message predicate
isSysMsg[ msg \in Messages ] == DOMAIN msg = { "params", "type" }

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

ErrorMsg(from, type) ==
    CASE type \in ErrorMsgTypes -> [ from |-> from, type |-> type ]

\* System message "constructor"
SysMsg(type, params) ==
    CASE \/ /\ type \in NewBlock
            /\ DOMAIN params = { "block" }
         \/ /\ type \in NewBranch
            /\ DOMAIN params = { "branch" }
         \/ /\ type \in NewChain
            /\ DOMAIN params = { "chain" } -> [ type |-> type, params |-> params ]

-----------------------------------------------------------------------------

(****************)
(* Expectations *)
(****************)

\* compute set of expected responses for [msg]
\* this set is either empty or contains a single expect message
expect_msg[ to \in Nodes, msg \in FullMsgs ] ==
    LET type   == msg.type
        params == msg.params
    IN
      CASE \* Request messages - advertise expected
           type = "Get_current_branch" -> {ExpectMsg(to, "Current_branch", [ chain |-> params.chain ])}
        [] type = "Get_current_head" ->
           {ExpectMsg(to, "Current_head", [ chain |-> params.chain, branch |-> params.branch ])}
        [] type = "Get_block_header" ->
           {ExpectMsg(to, "Block_header",
             [ chain |-> params.chain, branch |-> params.branch, height |-> params.height ])}
        [] type = "Get_operations" ->
           {ExpectMsg(to, "Operation",
             [ chain |-> params.chain, branch |-> params.branch, height |-> params.height, ops |-> params.ops ])}
           \* Advertise messages - ack expected
        [] type = "Current_branch" -> {AckMsg(to, "Ack_current_branch")}
        [] type = "Current_head"   -> {AckMsg(to, "Ack_current_head")}
        [] type = "Block_header"   -> {AckMsg(to, "Ack_block_header")}
        [] type = "Operations"     -> {AckMsg(to, "Ack_operations")}
           \* Acknowledgement messages
        [] type \in AckMsgTypes -> {} \* no response expected from an acknowledgement

-----------------------------------------------------------------------------

(* Network/Node info predicates *)
isNetwork(info) == DOMAIN info = { "active", "branch", "blocks", "chains", "height", "recv", "sent" }

isNode(info) == DOMAIN info = { "active", "branches", "blocks", "expect", "headers", "messages", "offchain" }

-----------------------------------------------------------------------------

(*************************)
(* Message-based actions *)
(*************************)

\* If info = network_info, check that checkRecv[chain][node] is satisified
\* If info = node_info, check that checkMessages[node][chain] is satisified
Recv(info, chain, node, msg) ==
    CASE isNetwork(info) -> [ info EXCEPT !.recv[chain][node] = checkCons(msg, @) ]
      [] isNode(info)    -> [ info EXCEPT !.messages[node][chain] = checkAppend(@, msg) ]

\* If info = node_info, must check that info.messages[node][chain] # <<>>
Consume(info, chain, node, msg) ==
    CASE isNetwork(info) -> [ info EXCEPT !.sent[chain][node] = @ \ {msg} ]
      [] isNode(info)    -> [ info EXCEPT !.messages[node][chain] = Tail(@),
                                          !.expect[node][chain] = @ \ expect_msg[node, msg] ]

\* must check that checkSent[chain][node] is satisfied
Send(to, chain, msg) == [ network_info EXCEPT !.sent[chain][to] = checkAdd(@, msg) ]

\* Register an expectation
Expect(from, chain, msg) == [ node_info EXCEPT !.expect[from][chain] = checkUnion(@, expect_msg[from, msg]) ]

\* Sends [msg] to all active nodes on [chain] who can recieve it
BroadcastToActive(from, chain, msg) ==
    [ network_info EXCEPT !.sent[chain] = [ to \in Nodes |->
        LET curr == @[to]
        IN  \* if node is active and has sent space, add msg to sent
          CASE to \in network_info.active[chain] \ {from} -> checkAdd(curr, msg)
            \* else, do nothing
            [] OTHER -> curr ] ]
            \* no expectations are registered for a broadcast because we don't know who will respond

=============================================================================
