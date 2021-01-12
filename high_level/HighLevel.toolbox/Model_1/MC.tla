---- MODULE MC ----
EXTENDS HighLevel, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions ValidStates
const_1609885088231169000 == 
{a, b}
----

\* SYMMETRY definition
symm_1609885088231170000 == 
Permutations(const_1609885088231169000)
----

\* CONSTANT definitions @modelParameterConstants:0peerThreshold
const_1609885088231171000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1connectionThreshold
const_1609885088231172000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2NumNodes
const_1609885088231173000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3NumJoins
const_1609885088231174000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:5sizeBound
const_1609885088231175000 == 
5
----

=============================================================================
