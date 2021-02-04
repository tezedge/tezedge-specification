------------------------------- MODULE DB_TypeOK -------------------------------

EXTENDS Utils

CONSTANTS numNodes, numChains, sizeBound

VARIABLES node_info, network_info

(******************************)
(* Enumerable type invariants *)
(******************************)

LOCAL INSTANCE DB_Defs
LOCAL INSTANCE DB_Messages

--------------------------------------------------------------------------------

\* Avoid silliness
(***********************************************************************************)
(*  network_info \in                                                               *)
(*    [ active  : [ Chains -> SUBSET Nodes ]                                       *)
(*    , branch  : [ Chains -> Branches ]                                           *)
(*    , blocks  : [ Chains -> [ Branches -> BoundedSeq(Blocks) ] ]                 *)
(*    , chains  : Chains                                                           *)
(*    , height  : [ Chains -> [ Branches -> Heights \cup {-1} ] ]                  *)
(*    , sent    : [ Chains -> [ Nodes -> BoundedSubsets(Messages \ ExpectMsgs) ] ] *)
(*    , sysmsgs : [ Chains -> BoundedSubsets(Messages \ ExpectMsgs) ] ]            *)
(***********************************************************************************)

\* chains
NetworkChainsOK == network_info.chains \in Chains

\* active
NetworkActiveOK ==
    \A chain \in activeChains :
        /\ network_info.active[chain] \subseteq SysNodes
        /\ activeNodes[chain] \subseteq Nodes
        /\ sys \in network_info.active[chain]

\* branch
NetworkBranchesOK ==
    \A chain \in activeChains : network_info.branch[chain] \in Branches \cup {-1}

\* blocks
NetworkBlocksOK ==
    \A chain \in activeChains :
        \A branch \in activeBranches[chain] :
            LET blocks == network_info.blocks[chain][branch]
            IN /\ Len(blocks) <= sizeBound + 1 \* height of each branch <= sizeBound
               /\ Forall(blocks, isBlock)      \* all blocks are blocks

\* height
NetworkHeightsOK ==
    \A chain \in activeChains :
        \A branch \in activeBranches[chain] :
            network_info.height[chain][branch] \in Heights \cup {-1}

\* sent
NetworkSentOK ==
    \A chain \in activeChains :
        \A node \in activeNodes[chain] :
            LET sent == network_info.sent[chain][node]
            IN /\ Cardinality(sent) <= sizeBound            \* size of [sent] <= sizeBound
               /\ sent = { msg \in sent : isValidMsg(msg) } \* only valid messages are sent
\* sysmsgs
NetworkSysMsgsOK ==
    \A chain \in activeChains :
        LET sysmsgs == network_info.sysmsgs[chain]
            msgs    == ToSet(sysmsgs)
        IN /\ Len(sysmsgs) <= sizeBound                       \* size of [sysmsgs] <= sizeBound
           /\ msgs = { msg \in msgs : \/ isValidReqMsg(msg)   \* [sys] receives request messages
                                      \/ isValidAckMsg(msg) } \* [sys] receives ack message

\* check all fields of network_info
NetworkOK ==
    /\ NetworkChainsOK
    /\ NetworkActiveOK
    /\ NetworkBranchesOK
    /\ NetworkBlocksOK
    /\ NetworkHeightsOK
    /\ NetworkSentOK
    /\ NetworkSysMsgsOK

(**********************************************************************************)
(*  node_info \in                                                                 *)
(*    [ active   : [ Nodes -> SUBSET Chains ]                                     *)
(*    , blocks   : [ Nodes -> [ Chains -> [ Branches -> BoundedSeq(Blocks) ] ] ]  *)
(*    , branches : [ Nodes -> [ Chains -> BoundedSeq(Branches) ] ]                *)
(*    , expect   : [ Nodes -> [ Chains -> BoundedSubsets(ExpectMsgs) ] ]          *)
(*    , headers  : [ Nodes -> [ Chains -> BoundedSeq(Headers) ] ]                 *)
(*    , height   : [ Nodes -> [ Chains -> [ Branch -> Heights \cup {-1} ] ] ]     *)
(*    , messages : [ Nodes -> [ Chains -> BoundedSeq(Messages \ ExpectMsgs) ] ] ] *)
(**********************************************************************************)

\* active
NodeActiveOK ==
    \A node \in Nodes : node_info.active[node] \subseteq Chains

\* blocks
NodeBlocksOK ==
    \A chain \in activeChains :
        \A node \in activeNodes[chain], branch \in activeBranches[chain] :
            LET blocks == node_info.blocks[node][chain][branch]
            IN /\ Len(blocks) <= sizeBound \* height of each block <= sizeBound
               /\ Forall(blocks, isBlock)  \* all blocks are blocks

\* branches
NodeBranchesOK ==
    \A chain \in activeChains :
        \A node \in activeNodes[chain] :
            LET branches == node_info.branches[node][chain]
            IN /\ current_branch[node, chain] <= sizeBound \* branches <= sizeBound
               /\ checkBranches(branches, chain)           \* check that all branches are valid

\* expect
NodeExpectOK ==
    \A chain \in activeChains :
        \A node \in activeNodes[chain] :
            LET expect == node_info.expect[node][chain]
            IN /\ Cardinality(expect) <= sizeBound              \* bounded expect set
               /\ expect = { exp \in expect : isValidMsg(exp) } \* all expect messages valid
\* headers
NodeHeadersOK ==
    \A chain \in activeChains :
        \A node \in activeNodes[chain] :
            LET headers == node_info.headers[node][chain]
            IN /\ Len(headers) <= sizeBound \* bounded list of headers
               /\ Forall(headers, isHeader) \* all headers are headers
\* height
NodeHeightsOK ==
    \A chain \in activeChains :
        \A node \in activeNodes[chain] :
            \A branch \in branchSet[node, chain] :
                LET height == node_info.height[node][chain][branch]
                IN /\ height >= -1
                   /\ height <= network_info.height[chain][branch]

\* messages
NodeMessagesOK ==
    \A chain \in activeChains :
        \A node \in activeNodes[chain] :
            LET msgs == node_info.messages[node][chain]
            IN /\ Len(msgs) <= sizeBound   \* length of message queue <= sizeBound
               /\ Forall(msgs, isValidMsg) \* all messages are valid

\* check all fields of node_info
NodeOK ==
    /\ NodeActiveOK
    /\ NodeBlocksOK
    /\ NodeBranchesOK
    /\ NodeExpectOK
    /\ NodeHeadersOK
    /\ NodeHeightsOK
    /\ NodeMessagesOK

TypeOK ==
    /\ NetworkOK
    /\ NodeOK

================================================================================
