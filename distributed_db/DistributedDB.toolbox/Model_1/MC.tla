---- MODULE MC ----
EXTENDS DistributedDB, TLC

\* CONSTANT definitions @modelParameterConstants:0sizeBound
const_1613429254548116000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:1numChains
const_1613429254548117000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:2numNodes
const_1613429254548118000 == 
2
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1613429254549119000 ==
DB_Invariants!ActiveAgreement
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1613429254549120000 ==
DB_TypeOK!TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1613429254549121000 ==
DB_Invariants!ActiveNodesEventuallySync
----
================================================================================
