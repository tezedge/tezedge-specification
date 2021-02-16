---- MODULE MC ----
EXTENDS HighLevel, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions ValidStates
const_16135110233152000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:0peerThreshold
const_16135110233153000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1connectionThreshold
const_16135110233154000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2NumNodes
const_16135110233155000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3NumJoins
const_16135110233156000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:5sizeBound
const_16135110233157000 == 
2
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_16135110233168000 ==
TypeOK!TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_16135110233169000 ==
Properties!AllNodesHaveJoined
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_161351102331610000 ==
Properties!AllNodesHaveSameState
----
================================================================================
