----------------------------- MODULE DB_Invariants -----------------------------

CONSTANTS numNodes, numChains, sizeBound

VARIABLES node_active, node_blocks, node_branches, node_headers, node_height, node_incoming, node_sent,
          active, blocks, branch, chains, mailbox, height, sysmsgs

LOCAL INSTANCE DB_Defs
LOCAL INSTANCE DB_Messages

(**************)
(* Properties *)
(**************)

\* Active nodes are eventually sent messages
ActiveNodesAreSentMessages ==
    \A chain \in Chains :
        \A node \in Nodes :
            node \in activeNodes[chain] ~> mailbox[chain][node] /= <<>>

\* A sent message is eventually received by the intended recipient, as long as they remain active
\* A [msg] sent to a [node] eventually ends up in node_incoming[node][chain]
SentMessagesAreReceivedByActives ==
    \A chain \in Chains :
        \A node \in Nodes :
            node \in activeNodes[chain] ~>
              LET sent == mailbox[chain][node]
              IN /\ sent /= <<>>
                 /\ LET msg  == Head(sent)
                        msgs == node_incoming[node][chain]
                    IN /\ msgs /= <<>>
                       /\ msg \in ToSet(msgs)

\* TODO
\* Received messages are eventually handled by active nodes
ReceivedMessagesAreEventuallyHandled ==
    \A chain \in Chains :
        \A node \in Nodes :
            LET msgs == node_incoming[node][chain]
            IN /\ msgs /= <<>>
               /\ LET msg == Head(msgs)
                  IN CASE isValidReqMsg(msg) -> FALSE
                       [] isValidAdvMsg(msg) -> FALSE
                       [] isValidAckMsg(msg) -> FALSE
                       [] isValidErrMsg(msg) -> FALSE

\* bootstrapping progress is made
\* active nodes are either synced with network or making progress towards that goal

\* If a node remains active on [chain], then eventually they will learn about all [chain] branches
ActiveNodesEventuallyGetBranches ==
    \A chain \in Chains :
        \A node \in Nodes :
            node \in activeNodes[chain] ~>
                max_set(branchSet[node, chain]) = branch[chain]

\* If a node remains active on [chain], then eventually they will learn about all the blocks
\* on all the branches of [chain]
ActiveNodesEventuallySync ==
    \A chain \in Chains :
        \A node \in Nodes :
            node \in activeNodes[chain] ~>
                \A b \in branchSet[node, chain] :
                    node_blocks[node][chain][b] = blocks[chain][b]

--------------------------------------------------------------------------------

(**************)
(* Invariants *)
(**************)

\* network_info & node_info are in agreement
ActiveAgreement ==
    \A chain \in activeChains :
        \A node \in activeNodes[chain] :
            \* actives
            /\ chain \in node_active[node]
            \* branches
            /\ node_branches[node][chain] /= <<>> =>
                 current_branch[node, chain] <= branch[chain]
            \* blocks
            /\ \A b \in branchSet[node, chain] :
                   isSubSeq(node_blocks[node][chain][b], blocks[chain][b])
            \* height
            /\ \A b \in branchSet[node, chain] :
                   node_height[node][chain][b] <= height[chain][b]

================================================================================
