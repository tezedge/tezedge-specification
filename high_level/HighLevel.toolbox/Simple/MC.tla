---- MODULE MC ----
EXTENDS HighLevel, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions ValidStates
const_161314311199411000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:0peerThreshold
const_161314311199412000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1connectionThreshold
const_161314311199413000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:2NumNodes
const_161314311199414000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3NumJoins
const_161314311199415000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:5sizeBound
const_161314311199416000 == 
1
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_161314311199417000 ==
TypeOK!TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_161314311199418000 ==
Properties!AllNodesHaveJoined
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_161314311199419000 ==
Properties!AllNodesHaveSameState
----
================================================================================
