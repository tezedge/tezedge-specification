---- MODULE ActionTraceChecker ----

(* Action trace checker spec *)

EXTENDS ActionTranslator, Parser

\* action trace reader variables
VARIABLES
    i,
    action

tvars == <<action, i>>

\* supply file path
ActionTrace == parse("./test/test3.test")

InitTrace ==
    /\ i = 1
    /\ action = ActionTrace[1]

ReadNextAction ==
    \* more actions to read and apply
    \/ /\ i < Len(ActionTrace)
       /\ i' = i + 1
       /\ action' = ActionTrace[i']
    \* we've applied the last action in the trace
    \/ /\ i = Len(ActionTrace)
       /\ i' = i + 1
       /\ action' = "Done"

NextTrace ==
    /\ ReadNextAction
    /\ ActionTranslator(action)

----

\* Compose spec and reader next actions
Compose(NextA, varsA, NextB, varsB) ==
    \/ NextA /\ NextB
    \/ UNCHANGED varsB /\ NextA
    \/ UNCHANGED varsA /\ NextB

ComposedNext == Compose(Next, vars, NextTrace, tvars)

ComposedSpec ==
    /\ Init
    /\ InitTrace
    /\ [][ComposedNext]_<<vars, tvars>>

\* this invariant will be:
\* - satisfied by an incorrect trace
\* - violated by a correct trace
Incorrect == i <= Len(ActionTrace)

\* this property will be:
\* - violated by an incorrect trace
\* - satisfied by a correct trace
Finished ==
    \/ ENABLED ComposedNext
    \/ action = "Done"

=======================================
