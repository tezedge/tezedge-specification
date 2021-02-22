---- MODULE MC ----

EXTENDS DB, TLC

\* CONSTANTS
num == 2

size == 1

\* Invariants & Properties
Consistency == Invariants!Agreement

Safety == TypeOK!TypeOK

Liveness == ActiveNodeEventuallySyncs

===================
