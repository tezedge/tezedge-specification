------------------------------- MODULE DB_TypeOK -------------------------------

EXTENDS Utils

CONSTANTS numNodes, numChains, sizeBound

VARIABLES node_active, node_blocks, node_branches, node_headers, node_height, node_incoming, node_sent,
          active, blocks, branch, chains, mailbox, height, sysmsgs

(******************************)
(* Enumerable type invariants *)
(******************************)

LOCAL INSTANCE DB_Defs
LOCAL INSTANCE DB_Messages

--------------------------------------------------------------------------------

\* Avoid silliness
(*********************************************************)
(* Network variables                                     *)
(* active  : Chains -> SUBSET Nodes                      *)
(* branch  : Chains -> Branches                          *)
(* blocks  : Chains -> Branches -> BoundedSeq(Blocks)    *)
(* chains  : Chains                                      *)
(* height  : Chains -> Branches -> Heights \cup {-1}     *)
(* mailbox : Chains -> Nodes -> BoundedSubsets(Messages) *)
(* sysmsgs : Chains -> BoundedSubsets(Messages)          *)
(*********************************************************)

\* active
ActiveOK ==
    \A chain \in Chains :
        /\ DOMAIN active = Chains
        /\ active[chain] \subseteq SysNodes
        /\ activeNodes[chain] \subseteq Nodes
        /\ inactiveNodes[chain] \subseteq Nodes
        /\ sys \in active[chain]

\* branch
BranchOK ==
    \A chain \in Chains :
        /\ DOMAIN branch = Chains
        /\ branch[chain] \in Branches \cup {-1}
        /\ chain \in activeChains => branch[chain] >= 0

\* blocks
BlocksOK ==
    \A chain \in Chains :
        \A b \in Branches :
            LET blks == blocks[chain][b]
            IN /\ DOMAIN blocks = Chains
               /\ DOMAIN blocks[chain] = Branches
               /\ Len(blks) <= sizeBound + 1                  \* height of each branch <= sizeBound
               /\ Forall(blks, isBlock)                       \* all blocks are valid
               /\ b \in activeBranches[chain] => blks /= <<>> \* active branches have blocks

\* chains
ChainsOK == chains \in Chains

\* height
HeightOK ==
    \A chain \in Chains :
        \A b \in Branches :
            /\ DOMAIN height = Chains
            /\ DOMAIN height[chain] = Branches
            /\ height[chain][b] \in Heights \cup {-1}
            /\ b \in activeBranches[chain] => height[chain][b] >= 0

\* mailbox
MailboxOK ==
    \A chain \in Chains :
        \A node \in SysNodes :
            LET mail == mailbox[chain][node]
                set  == ToSet(mail)
            IN /\ DOMAIN mailbox = Chains
               /\ DOMAIN mailbox[chain] = SysNodes
               /\ Len(mail) <= sizeBound                     \* bounded
               /\ set = { msg \in set : /\ msg.to = node
                                        /\ isValidMsg(msg) } \* only valid messages are sent

\* sysmsgs
SysMsgsOK ==
    \A chain \in Chains :
        LET smsgs == sysmsgs[chain]
            msgs  == ToSet(smsgs)
        IN /\ DOMAIN sysmsgs = Chains
           /\ Len(smsgs) <= sizeBound                            \* size of [sysmsgs] <= sizeBound
           /\ msgs = { msg \in msgs : /\ msg.to = sys
                                      /\ \/ isValidReqMsg(msg)   \* [sys] receives request messages
                                         \/ isValidAckMsg(msg) } \* [sys] receives ack message

\* check all fields of network_info
NetworkOK ==
    /\ ActiveOK
    /\ BranchOK
    /\ BlocksOK
    /\ ChainsOK
    /\ HeightOK
    /\ MailboxOK
    /\ SysMsgsOK

--------------------------------------------------------------------------------

(*********************************************************************)
(* Node variables                                                    *)
(* node_active   : Nodes -> SUBSET Chains                            *)
(* node_blocks   : Nodes -> Chains -> Branches -> BoundedSeq(Blocks) *)
(* node_branches : Nodes -> Chains -> BoundedSeq(Branches)           *)
(* node_headers  : Nodes -> Chains -> BoundedSeq(Headers)            *)
(* node_height   : Nodes -> Chains -> Branches -> Heights \cup {-1}  *)
(* node_incoming : Nodes -> Chains -> BoundedSeq(Messages)           *)
(* node_sent     : Nodes -> Chains -> BoundedSeq(Messages)           *)
(*********************************************************************)

\* node_active
NodeActiveOK ==
    \A node \in Nodes :
        /\ DOMAIN node_active = Nodes
        /\ node_active[node] \subseteq Chains

\* node_blocks
NodeBlocksOK ==
    \A chain \in Chains :
        \A node \in Nodes, b \in Branches :
            LET blks == node_blocks[node][chain][b]
            IN /\ DOMAIN node_blocks = Nodes
               /\ DOMAIN node_blocks[node] = Chains
               /\ DOMAIN node_blocks[node][chain] = Branches
               /\ Len(blks) <= sizeBound \* height of each block <= sizeBound
               /\ Forall(blks, isBlock)  \* all blocks are valid

\* node_branches
NodeBranchesOK ==
    \A chain \in Chains :
        \A node \in Nodes :
            LET branches == node_branches[node][chain]
            IN /\ DOMAIN node_branches = Nodes
               /\ DOMAIN node_branches[node] = Chains
               /\ current_branch[node, chain] <= sizeBound \* branches <= sizeBound
               /\ checkBranches(branches, chain)           \* check that all branches are valid

\* node_headers
NodeHeadersOK ==
    \A chain \in Chains :
        \A node \in Nodes :
            LET headers == node_headers[node][chain]
            IN /\ DOMAIN node_headers = Nodes
               /\ DOMAIN node_headers[node] = Chains
               /\ Len(headers) <= sizeBound \* bounded list of headers
               /\ Forall(headers, isHeader) \* all headers are valid headers

\* node_height
NodeHeightsOK ==
    \A chain \in Chains :
        \A node \in Nodes :
            \A b \in Branches :
                LET hgt == node_height[node][chain][b]
                IN /\ DOMAIN node_height = Nodes
                   /\ DOMAIN node_height[node] = Chains
                   /\ DOMAIN node_height[node][chain] = Branches
                   /\ hgt >= -1
                   /\ hgt <= height[chain][b] \* node heights do not exceed system heights

\* node_incoming
NodeIncomingOK ==
    \A chain \in Chains :
        \A node \in Nodes :
            LET msgs == node_incoming[node][chain]
                set  == ToSet(msgs)
            IN /\ DOMAIN node_incoming = Nodes
               /\ DOMAIN node_incoming[node] = Chains
               /\ Len(msgs) <= sizeBound   \* length of incoming queue <= sizeBound
               /\ Forall(msgs, isValidMsg) \* all incoming messages are valid
               /\ set = { msg \in set : msg.to = node }

\* node_sent
NodeSentOK ==
    \A chain \in Chains :
        \A node \in Nodes :
            LET sent == node_sent[node][chain]
                set  == ToSet(sent)
            IN /\ DOMAIN node_sent = Nodes
               /\ DOMAIN node_sent[node] = Chains 
               /\ Len(sent) <= sizeBound                     \* bounded
               /\ set = { msg \in set : /\ msg.from = node
                                        /\ isValidMsg(msg) } \* all sent messages are valid

\* check all fields of node_info
NodeOK ==
    /\ NodeActiveOK
    /\ NodeBlocksOK
    /\ NodeBranchesOK
    /\ NodeHeadersOK
    /\ NodeHeightsOK
    /\ NodeIncomingOK
    /\ NodeSentOK

--------------------------------------------------------------------------------

\* Type invariant
TypeOK ==
    /\ NetworkOK
    /\ NodeOK

================================================================================
