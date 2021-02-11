---- MODULE MC ----
EXTENDS DistributedDB, TLC

\* CONSTANT definitions @modelParameterConstants:0sizeBound
const_1612990546434164000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1numChains
const_1612990546434165000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:2numNodes
const_1612990546434166000 == 
2
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1612990546434167000 ==
DB_TypeOK!ActiveOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1612990546434168000 ==
DB_TypeOK!BranchOK
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1612990546434169000 ==
DB_TypeOK!BlocksOK
----
\* INVARIANT definition @modelCorrectnessInvariants:3
inv_1612990546434170000 ==
DB_TypeOK!ChainsOK
----
\* INVARIANT definition @modelCorrectnessInvariants:4
inv_1612990546434171000 ==
DB_TypeOK!HeightOK
----
\* INVARIANT definition @modelCorrectnessInvariants:5
inv_1612990546434172000 ==
DB_TypeOK!MailboxOK
----
\* INVARIANT definition @modelCorrectnessInvariants:6
inv_1612990546434173000 ==
DB_TypeOK!SysMsgsOK
----
\* INVARIANT definition @modelCorrectnessInvariants:7
inv_1612990546434174000 ==
DB_TypeOK!NodeActiveOK
----
\* INVARIANT definition @modelCorrectnessInvariants:8
inv_1612990546434175000 ==
DB_TypeOK!NodeBlocksOK
----
\* INVARIANT definition @modelCorrectnessInvariants:9
inv_1612990546434176000 ==
DB_TypeOK!NodeBranchesOK
----
\* INVARIANT definition @modelCorrectnessInvariants:10
inv_1612990546434177000 ==
DB_TypeOK!NodeHeadersOK
----
\* INVARIANT definition @modelCorrectnessInvariants:11
inv_1612990546434178000 ==
DB_TypeOK!NodeHeightsOK
----
\* INVARIANT definition @modelCorrectnessInvariants:12
inv_1612990546434179000 ==
DB_TypeOK!NodeIncomingOK
----
\* INVARIANT definition @modelCorrectnessInvariants:13
inv_1612990546434180000 ==
DB_TypeOK!NodeSentOK
----
\* INVARIANT definition @modelCorrectnessInvariants:14
inv_1612990546434181000 ==
DB_Invariants!ActiveAgreement
----
================================================================================
