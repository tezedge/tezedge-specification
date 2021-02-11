---- MODULE MC ----
EXTENDS HighLevel, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions ValidStates
const_16130128034852000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:0peerThreshold
const_16130128034853000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1connectionThreshold
const_16130128034854000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2NumNodes
const_16130128034855000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:3NumJoins
const_16130128034856000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:5sizeBound
const_16130128034857000 == 
4
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_16130128034868000 ==
TypeOK!TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_16130128034869000 ==
Properties!AllNodesHaveJoined
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_161301280348610000 ==
Properties!AllNodesHaveSameState
----
================================================================================
