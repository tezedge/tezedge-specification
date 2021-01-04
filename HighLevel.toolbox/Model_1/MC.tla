---- MODULE MC ----
EXTENDS HighLevel, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions ValidStates
const_1609789021579127000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:0peerThreshold
const_1609789021579128000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1connectionThreshold
const_1609789021579129000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2queueBound
const_1609789021579130000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:3NumNodes
const_1609789021579131000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:4NumJoins
const_1609789021579132000 == 
2
----

=============================================================================
