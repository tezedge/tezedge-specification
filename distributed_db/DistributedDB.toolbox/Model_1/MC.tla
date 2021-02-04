---- MODULE MC ----
EXTENDS DistributedDB, TLC

\* CONSTANT definitions @modelParameterConstants:0numChains
const_1612395535162881000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:1numNodes
const_1612395535162882000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2sizeBound
const_1612395535162883000 == 
3
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1612395535162884000 ==
DB_TypeOK!NetworkChainsOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1612395535162885000 ==
DB_TypeOK!NetworkActiveOK
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1612395535162886000 ==
DB_TypeOK!NetworkBranchesOK
----
\* INVARIANT definition @modelCorrectnessInvariants:3
inv_1612395535162887000 ==
DB_TypeOK!NetworkBlocksOK
----
\* INVARIANT definition @modelCorrectnessInvariants:4
inv_1612395535162888000 ==
DB_TypeOK!NetworkHeightsOK
----
\* INVARIANT definition @modelCorrectnessInvariants:5
inv_1612395535162889000 ==
DB_TypeOK!NetworkSentOK
----
\* INVARIANT definition @modelCorrectnessInvariants:6
inv_1612395535162890000 ==
DB_TypeOK!NetworkSysMsgsOK
----
\* INVARIANT definition @modelCorrectnessInvariants:7
inv_1612395535162891000 ==
DB_TypeOK!NodeActiveOK
----
\* INVARIANT definition @modelCorrectnessInvariants:8
inv_1612395535162892000 ==
DB_TypeOK!NodeBlocksOK
----
\* INVARIANT definition @modelCorrectnessInvariants:9
inv_1612395535162893000 ==
DB_TypeOK!NodeBranchesOK
----
\* INVARIANT definition @modelCorrectnessInvariants:10
inv_1612395535162894000 ==
DB_TypeOK!NodeExpectOK
----
\* INVARIANT definition @modelCorrectnessInvariants:11
inv_1612395535162895000 ==
DB_TypeOK!NodeHeadersOK
----
\* INVARIANT definition @modelCorrectnessInvariants:12
inv_1612395535162896000 ==
DB_TypeOK!NodeHeightsOK
----
\* INVARIANT definition @modelCorrectnessInvariants:13
inv_1612395535162897000 ==
DB_TypeOK!NodeMessagesOK
----
\* INVARIANT definition @modelCorrectnessInvariants:14
inv_1612395535162898000 ==
DB_Invariants!ActiveAgreement
----
\* INVARIANT definition @modelCorrectnessInvariants:15
inv_1612395535162899000 ==
DB_Invariants!InactiveNodesDoNotHandleMessages
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1612395535162900000 ==
DB_Invariants!SentMessagesAreReceivedByActives
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1612395535162901000 ==
DB_Invariants!ActiveNodesEventuallyGetBranches
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_1612395535162902000 ==
DB_Invariants!ActiveNodesEventuallySync
----
================================================================================
