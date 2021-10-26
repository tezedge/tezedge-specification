---- MODULE Topology ----

EXTENDS FiniteSets, Naturals, Sequences, Utils

\* defined via refinement mapping upon instantiation
CONSTANTS
    NONE,
    Nodes,
    connections \* set of each node's connections

----

\* lte(NONE, _) = FALSE
\* lte(_, NONE) = TRUE
\* lte(x, y) = x <= y
lte(x, y) ==
    /\ x /= NONE
    /\ \/ y = NONE
       \/ x <= y

RECURSIVE _max_set(_, _)
_max_set(S, n) ==
    IF n = NONE \/ S = {} THEN n
    ELSE
        LET x == Pick(S) IN
        IF lte(x, n) THEN _max_set(S \ {x}, n)
        ELSE _max_set(S \ {x}, x)

Max(S) ==
    IF S = {} THEN NONE
    ELSE
        LET x == Pick(S) IN
        _max_set(S \ {x}, x)

\* Every node in S is directly connected to another node in S
Weakly_connected(S) == \A x \in S : \E y \in S : y \in connections[x]

\* x and y are connected by p : x = p[1] <-> ... <-> y = p[n]
connected_by_path(x, y, p) ==
    LET n == Len(p) IN
    /\ n > 1
    /\ x = p[1]
    /\ y = p[n]
    /\ \A i \in 1..(n - 1) : p[i] \in connections[p[i + 1]]

\* length of a minimal path connecting x to y, excluding x and y
RECURSIVE min_path_len(_, _, _, _)
min_path_len(x, y, S, n) ==
    CASE n = 2 /\ y \in connections[x] -> 1
      [] n > Cardinality(S) -> NONE
      [] OTHER ->
            IF \E p \in SeqOfLen(S, n) : connected_by_path(x, y, p) THEN n - 1
            ELSE min_path_len(x, y, S, n + 1)

Min_path_len(x, y) == min_path_len(x, y, Nodes, 2)

\* a minimal path connecting x to y
RECURSIVE min_path(_, _, _)
min_path(x, y, S) ==
    LET n == min_path_len(x, y, S, 2) IN
    CASE n = NONE -> <<>>
      [] n = 0 -> <<x, y>>
      [] OTHER ->
            LET inter == CHOOSE p \in SeqOfLen(S, n) : connected_by_path(x, y, Append(Cons(x, p), y)) IN
            Append(Cons(x, inter), y)

Min_path(x, y) ==
    IF y \in connections[x] THEN <<>>
    ELSE min_path(x, y, Nodes)

\* maximum length of the minimal paths originating from x
Max_path(x, S) ==
    LET min_paths == { Min_path_len(x, y) : y \in S } IN
    Max(min_paths)

\* longest minimal path connecting any two points of S
Max_path_len(S) == Max({ Max_path(x, S \ {x}) : x \in S })

\* subsets of S which have max path length <= n
Connected(n, S) == { ss \in SUBSET S : lte(Max_path_len(ss), n) }

=========================
