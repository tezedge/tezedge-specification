---- MODULE MC ----
EXTENDS HighLevel, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS a, b

\* MV CONSTANT definitions ValidStates
const_16141315634932000 == {a, b}

\* CONSTANT definitions @modelParameterConstants:0peerThreshold
const_16141315634933000 == 2

\* CONSTANT definitions @modelParameterConstants:1connectionThreshold
const_16141315634934000 == 2

\* CONSTANT definitions @modelParameterConstants:2NumNodes
const_16141315634935000 == 3

\* CONSTANT definitions @modelParameterConstants:3NumJoins
const_16141315634936000 == 2

\* CONSTANT definitions @modelParameterConstants:5sizeBound
const_16141315634937000 == 2

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_16141315634948000 == TypeOK!TypeOK

\* PROPERTY definition @modelCorrectnessProperties:0
prop_16141315634949000 == Properties!AllNodesHaveJoined

\* PROPERTY definition @modelCorrectnessProperties:1
prop_161413156349410000 == Properties!AllNodesHaveSameState

================================================================================
