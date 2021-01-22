---------------------------- MODULE DB_Request -----------------------------

CONSTANTS numChains, numNodes, sizeBound

VARIABLES network_info, node_info

LOCAL INSTANCE DB_Defs
LOCAL INSTANCE DB_Messages
LOCAL INSTANCE Utils

----------------------------------------------------------------------------

(*******************)
(* Request actions *)
(*******************)

(* Messages are sent to a set where the receipient can receive or drop them later *)

(**********************)
(* Get_current_branch *)
(**********************)
\* [from] requests the current branch of [chain] from active peer [to]
Get_current_branch_1(from, chain, to) ==
    LET msg == Msg(from, "Get_current_branch", [ chain |-> chain ])
    IN /\ network_info' = [ network_info EXCEPT !.sent[chain][to] = Send(@, msg) ]     \* send [msg] to [to]
       /\ node_info' = [ node_info EXCEPT !.expect[from][chain] = Expect(@, to, msg) ] \* register expectation

\* A node requests the current branch on a chain from an active peer
Get_current_branch_one ==
    \E chain \in activeChains :
        \E from \in activeNodes[chain] :
            \E to \in activeSysNodes[chain] \ {from} :
                \* [from] doesn't know about an active branch on [chain]
                /\ branchSet[from, chain] # activeBranches[chain]
                \* [from] requests current branch of [chain] from [to]
                /\ Get_current_branch_1(from, chain, to)

\* [from] requests the current branch of [chain] from all active peers
\* Request message is sent to all active nodes on [chain] who can have a message sent to them
Get_current_branch_n(from, chain) ==
    LET msg == Msg(from, "Get_current_branch", [ chain |-> chain ])
    IN network_info' = [ network_info EXCEPT !.sent[chain] = Broadcast(@, from, chain, msg) ]

\* A node requests the current branch of some chain from all active peers on the chain
Get_current_branch_all ==
    \E chain \in activeChains :
        \E from \in activeNodes[chain] :
            \* [from] doesn't know about an active branch on [chain]
            /\ branchSet[from, chain] # activeBranches[chain]
            \* [from] requests current branches from all active nodes on [chain]
            /\ Get_current_branch_n(from, chain)
            /\ UNCHANGED node_info

(********************)
(* Get_current_head *)
(********************)
\* [from] requests the current head of [branch] from an active peer [to] on [chain]
Get_current_head_1(from, chain, branch, to) ==
    LET msg == Msg(from, "Get_current_head", [ branch |-> branch ])
    IN /\ network_info' = [ network_info EXCEPT !.sent[chain][to] = Send(@, msg) ]     \* send [msg] to [to]
       /\ node_info' = [ node_info EXCEPT !.expect[from][chain] = Expect(@, to, msg) ] \* register expectation

\* A node who knows about a branch on a chain requests the current head from one active peer
Get_current_head_one ==
    \E chain \in activeChains :
        \E from \in activeNodes[chain] :
            \E to \in activeSysNodes[chain] \ {from} :
                \E branch \in branchSet[from, chain] :
                    \* [from] has not seen evidence of a block on [branch]
                    /\ node_info.height[from][chain][branch] < currentHeight[chain, branch]
                    \* [from] requests current head of [branch] from [to]
                    /\ Get_current_head_1(from, chain, branch, to)

\* [from] requests the current head of [branch] from all active nodes on [chain]
Get_current_head_n(from, chain, branch) ==
    LET msg == Msg(from, "Get_current_head", [ branch |-> branch ])
    IN network_info' = [ network_info EXCEPT !.sent[chain] = Broadcast(@, from, chain, msg) ]

\* A node who knows about branches on a chain requests the current head from all active peers on that chain
Get_current_head_all ==
    \E chain \in activeChains :
        \E from \in activeNodes[chain] :
            \E branch \in branchSet[from, chain] :
               /\ node_info.height[from][chain][branch] < currentHeight[chain, branch]
               \* [from] requests current head of [branch] from all active nodes on [chain]
               /\ Get_current_head_n(from, chain, branch)
               /\ UNCHANGED node_info

(********************)
(* Get_block_header *)
(********************)
\* [from] requests the header of the block on [branch] at [height] from an active peer [to] on [chain]
Get_block_header_1(from, chain, branch, height, to) ==
    LET msg == Msg(from, "Get_block_header", [ branch |-> branch, height |-> height ])
    IN /\ network_info' = [ network_info EXCEPT !.sent[chain][to] = Send(@, msg) ]     \* send [msg] to [to]
       /\ node_info' = [ node_info EXCEPT !.expect[from][chain] = Expect(@, to, msg) ] \* register expectation

\* A node requests a block header on some branch at some height from an active peer on some chain
Get_block_header_one ==
    \E chain \in activeChains :
        \E from \in activeNodes[chain] :
            \E to \in activeNodes[chain] \ {from} :
                /\ checkSent[chain][to] \* a message can be sent to [to]
                /\ \E branch \in branchSet[from, chain] :
                       \* there are blocks which [from] has not seen
                       /\ currentHeights(chain, branch) \ heightSet[from, chain, branch] # {}
                       /\ LET h == min_set(currentHeights(chain, branch) \ heightSet[from, chain, branch])
                          IN \* [from] knows about a block at height [h] but has not gotten a header
                             /\ h <= node_info.height[from][chain][branch]
                             /\ Get_block_header_1(from, chain, branch, h, to) \* request header from [to]

\* [from] requests the header of the block on [branch] at [height] from all active peers on [chain]
Get_block_header_n(from, chain, branch, height) ==
    LET msg == Msg(from, "Get_block_header", [ branch |-> branch, height |-> height ])
    IN network_info' = [ network_info EXCEPT !.sent[chain] = Broadcast(@, from, chain, msg) ]
 
\* A node requests the header of the block on some branch at some height from all active peers on some chain
Get_block_header_all ==
    \E chain \in activeChains :
        \E from \in activeNodes[chain] :
            \E branch \in branchSet[from, chain] :
                \* there are blocks which [from] has not seen
                /\ currentHeights(chain, branch) \ heightSet[from, chain, branch] # {}
                /\ LET h == min_set(currentHeights(chain, branch) \ heightSet[from, chain, branch])
                   IN \* [from] knows about a block at height [h] but has not gotten a header
                      /\ h <= node_info.height[from][chain][branch]
                      /\ Get_block_header_n(from, chain, branch, h) \* request header from active
                      /\ UNCHANGED node_info

(******************)
(* Get_operations *)
(******************)
\* The requester must have the block's header before requesting its operations
\* [from] requests the operations of the block on [branch] at [height] on [chain] from active peer [to]
Get_operations_1(from, chain, branch, height, to) ==
    LET msg == Msg(from, "Get_operations", [ branch |-> branch, height |-> height ])
    IN /\ network_info' = [ network_info EXCEPT !.sent[chain][to] = Send(@, msg) ]     \* send [msg] to [to]
       /\ node_info' = [ node_info EXCEPT !.expect[from][chain] = Expect(@, to, msg) ] \* register expectation

\* A node requests the operations of a block on a chain from an active peer who can have a message sent to them
Get_operations_one ==
    \E chain \in activeChains :
        \E from \in activeNodes[chain] :
            \E to \in activeNodes[chain] \ {from} :
                LET headers == node_info.headers[from][chain]
                IN /\ headers # <<>>  \* [from] has a block's header and needs its operations
                   /\ LET branch == Head(headers).branch
                          height == Head(headers).height
                      IN Get_operations_1(from, chain, branch, height, to) \* send Get_operations request

\* [from] requests the operations of the block on [branch] at [height] from all active peers on [chain]
\* Request message is sent to all active nodes on [chain] who can have a message sent to them
Get_operations_n(from, chain, branch, height) ==
    LET msg == Msg(from, "Get_operations", [ branch |-> branch, height |-> height ])
    IN network_info' = [ network_info EXCEPT !.sent[chain] = Broadcast(@, from, chain, msg) ]

\* A node requests the operations of a block on a chain from all active peers who can have a message sent to them
Get_operations_all ==
    \E chain \in activeChains :
        \E from \in activeNodes[chain] :
            LET headers == node_info.headers[from][chain]
            IN /\ headers # <<>>  \* [from] has a block's header and needs its operations
               /\ LET branch == Head(headers).branch
                      height == Head(headers).height
                  IN /\ Get_operations_n(from, chain, branch, height)
                     /\ UNCHANGED node_info

=============================================================================
