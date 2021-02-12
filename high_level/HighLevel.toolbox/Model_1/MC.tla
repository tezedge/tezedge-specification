---- MODULE MC ----
EXTENDS HighLevel, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions ValidStates
const_16131573455652000 ==
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:0peerThreshold
const_16131573455653000 ==
2
----

\* CONSTANT definitions @modelParameterConstants:1connectionThreshold
const_16131573455654000 ==
2
----

\* CONSTANT definitions @modelParameterConstants:2NumNodes
const_16131573455655000 ==
3
----

\* CONSTANT definitions @modelParameterConstants:3NumJoins
const_16131573455656000 ==
2
----

\* CONSTANT definitions @modelParameterConstants:5sizeBound
const_16131573455657000 ==
2
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_16131573455658000 ==
TypeOK!TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_16131573455669000 ==
Properties!AllNodesHaveJoined
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_161315734556610000 ==
Properties!AllNodesHaveSameState
----
================================================================================
