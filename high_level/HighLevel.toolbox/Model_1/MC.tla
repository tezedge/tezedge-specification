---- MODULE MC ----
EXTENDS HighLevel, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions ValidStates
const_16135282433422000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:0peerThreshold
const_16135282433423000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1connectionThreshold
const_16135282433424000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2NumNodes
const_16135282433425000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3NumJoins
const_16135282433426000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:5sizeBound
const_16135282433427000 == 
2
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_16135282433428000 ==
TypeOK!TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_16135282433429000 ==
Properties!AllNodesHaveJoined
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_161352824334210000 ==
Properties!AllNodesHaveSameState
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_never_join ==
Properties!NeverJoin
----
================================================================================
