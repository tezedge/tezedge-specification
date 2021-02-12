---- MODULE MC ----
EXTENDS HighLevel, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions ValidStates
const_161316362831320000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:0peerThreshold
const_161316362831321000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1connectionThreshold
const_161316362831322000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2NumNodes
const_161316362831323000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3NumJoins
const_161316362831324000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:5sizeBound
const_161316362831325000 == 
2
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_161316362831326000 ==
TypeOK!TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_161316362831327000 ==
Properties!AllNodesHaveJoined
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_161316362831328000 ==
Properties!AllNodesHaveSameState
----
================================================================================
