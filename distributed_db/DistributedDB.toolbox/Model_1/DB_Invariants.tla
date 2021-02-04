----------------------------- MODULE DB_Invariants -----------------------------

EXTENDS Utils

CONSTANTS numNodes, numChains, sizeBound

VARIABLES node_info, network_info

LOCAL INSTANCE DB_Defs

(**************)
(* Properties *)
(**************)

\* Active nodes are eventually sent messages
ActiveNodesAreSentMessaages ==
    \A chain \in Chains :
        \A node \in Nodes :
            node \in activeNodes[chain] ~> network_info.sent[chain][node] /= <<>>

\* A sent message is eventually received by the intended recipient, as long as they remain active
\* A [msg] sent to a [node] eventually ends up in messages[node][chain]
SentMessagesAreReceivedByActives ==
    \A chain \in Chains :
        \A node \in Nodes :
            node \in activeNodes[chain] ~>
              LET sent == network_info.sent[chain][node]
              IN CASE sent = {} -> FALSE
                   [] OTHER ->
                        LET msg  == Pick(sent)
                            msgs == node_info.messages[node][chain]
                        IN msgs /= <<>> => msg = Head(msgs)

\* If a node remains active on [chain], then eventually they will learn about all [chain] branches
ActiveNodesEventuallyGetBranches ==
    \A chain \in Chains :
        \A node \in Nodes :
            node \in activeNodes[chain] ~>
                max_set(branchSet[node, chain]) = network_info.branch[chain]

\* If a node remains active on [chain], then eventually they will learn about all the blocks
\* on all the branches of [chain]
ActiveNodesEventuallySync ==
    \A chain \in Chains :
        \A node \in Nodes :
            node \in activeNodes[chain] ~>
                \A branch \in branchSet[node, chain] :
                    node_info.blocks[node][chain][branch] = network_info.blocks[chain][branch]

\* bootstrapping progress is made
\* active nodes are either synced with network or making progress towards that goal
\* TODO

--------------------------------------------------------------------------------

(**************)
(* Invariants *)
(**************)

\* network_info & node_info are in agreement
ActiveAgreement ==
    \A chain \in activeChains :
        \A node \in activeNodes[chain] :
            \* actives
            /\ chain \in node_info.active[node]
            \* branches
            /\ node_info.branches[node][chain] # <<>> =>
                 current_branch[node, chain] <= network_info.branch[chain]
            \* blocks
            /\ \A branch \in branchSet[node, chain] :
                   isSubSeq(node_info.blocks[node][chain][branch], network_info.blocks[chain][branch])
            \* height
            /\ \A branch \in branchSet[node, chain] :
                   node_info.height[node][chain][branch] <= currentHeight[chain, branch]

\* [chain] inactive nodes have empty [chain] messages
\* [chain] inactive nodes do not receive or handle [chain] messages
InactiveNodesDoNotHandleMessages ==
    \A chain \in activeChains :
        \A node \in inactiveNodes[chain] : 
            node_info.messages[node][chain] = <<>>

================================================================================
