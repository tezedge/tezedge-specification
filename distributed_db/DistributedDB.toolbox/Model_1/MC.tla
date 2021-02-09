---- MODULE MC ----
EXTENDS DistributedDB, TLC

\* CONSTANT definitions @modelParameterConstants:0sizeBound
const_1612903506446488000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1numChains
const_1612903506446489000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:2numNodes
const_1612903506446490000 == 
2
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1612903506446491000 ==
DB_TypeOK!ActiveOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1612903506446492000 ==
DB_TypeOK!BranchOK
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1612903506446493000 ==
DB_TypeOK!BlocksOK
----
\* INVARIANT definition @modelCorrectnessInvariants:3
inv_1612903506446494000 ==
DB_TypeOK!ChainsOK
----
\* INVARIANT definition @modelCorrectnessInvariants:4
inv_1612903506446495000 ==
DB_TypeOK!HeightOK
----
\* INVARIANT definition @modelCorrectnessInvariants:5
inv_1612903506446496000 ==
DB_TypeOK!MailboxOK
----
\* INVARIANT definition @modelCorrectnessInvariants:6
inv_1612903506446497000 ==
DB_TypeOK!SysMsgsOK
----
\* INVARIANT definition @modelCorrectnessInvariants:7
inv_1612903506446498000 ==
DB_TypeOK!NodeActiveOK
----
\* INVARIANT definition @modelCorrectnessInvariants:8
inv_1612903506446499000 ==
DB_TypeOK!NodeBlocksOK
----
\* INVARIANT definition @modelCorrectnessInvariants:9
inv_1612903506446500000 ==
DB_TypeOK!NodeBranchesOK
----
\* INVARIANT definition @modelCorrectnessInvariants:10
inv_1612903506446501000 ==
DB_TypeOK!NodeHeadersOK
----
\* INVARIANT definition @modelCorrectnessInvariants:11
inv_1612903506446502000 ==
DB_TypeOK!NodeHeightsOK
----
\* INVARIANT definition @modelCorrectnessInvariants:12
inv_1612903506446503000 ==
DB_TypeOK!NodeIncomingOK
----
\* INVARIANT definition @modelCorrectnessInvariants:13
inv_1612903506446504000 ==
DB_TypeOK!NodeSentOK
----
\* INVARIANT definition @modelCorrectnessInvariants:14
inv_1612903506446505000 ==
DB_Invariants!ActiveAgreement
----
================================================================================
