-------------------------------- MODULE DB_Init --------------------------------

EXTENDS Utils

CONSTANTS numNodes, numChains, sizeBound

VARIABLES node_info, network_info

LOCAL INSTANCE DB_Defs
LOCAL INSTANCE DB_Messages

--------------------------------------------------------------------------------

(**********************)
(* Initial predicates *)
(**********************)

\* usual
Init ==
    /\ network_info =
         [ active   |-> [ c \in Chains |-> {sys} ]
         , blocks   |-> [ c \in Chains |-> [ b \in Branches |-> <<>> ] ]
         , branch   |-> [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
         , chains   |-> 1
         , height   |-> [ c \in Chains |-> [ b \in Branches |-> -1 ] ]
         , sent     |-> [ c \in Chains |-> [ n \in SysNodes |-> {} ] ]
         , sysmsgs  |-> [ c \in Chains |-> <<>> ] ]
    /\ node_info =
         [ active   |-> [ n \in Nodes |-> {} ]
         , blocks   |-> [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |-> <<>> ] ] ]
         , branches |-> [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
         , expect   |-> [ n \in Nodes |-> [ c \in Chains |-> {} ] ]
         , headers  |-> [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
         , height   |-> [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |-> -1 ] ] ]
         , messages |-> [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ] ]

\* node 1 has branch 0, no blocks, no headers, no messages
Init_branch ==
    /\ network_info =
         [ active   |-> [ c \in Chains |-> IF c = 1 THEN {1, sys} ELSE {sys} ]
         , blocks   |-> [ c \in Chains |-> [ b \in Branches |-> <<>> ] ]
         , branch   |-> [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
         , chains   |-> 1
         , height   |-> [ c \in Chains |-> [ b \in Branches |->
             IF /\ c = 1
                /\ b = 0
             THEN 0
             ELSE -1 ] ]
         , sent     |-> [ c \in Chains |-> [ n \in SysNodes |-> {} ] ]
         , sysmsgs  |-> [ c \in Chains |-> <<>> ] ]
    /\ node_info =
         [ active   |-> [ n \in Nodes |-> IF n = 1 THEN {1} ELSE {} ]
         , blocks   |-> [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |-> <<>> ] ] ]
         , branches |-> [ n \in Nodes |-> [ c \in Chains |->
             IF /\ n = 1
                /\ c = 1
             THEN <<0>>
             ELSE <<>> ] ]
         , expect   |-> [ n \in Nodes |-> [ c \in Chains |-> {} ] ]
         , headers  |-> [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
         , height   |-> [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |-> -1 ] ] ]
         , messages |-> [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ] ]

\* [sys] has Get_block_header message
Init_height ==
    LET block == Block(Header(1, 0, 0, 0), mkOps(0, 0))
        msg   == Msg(1, "Get_block_header", [ branch |-> 0, height |-> 0 ])
        exp   == ExpectMsg(3, "Block_header", [ branch |-> 0, height |-> 0 ])
    IN /\ network_info =
            [ active   |-> [ c \in Chains |-> IF c = 1 THEN {1, sys} ELSE {sys} ]
            , blocks   |-> [ c \in Chains |-> [ b \in Branches |->
                IF /\ c = 1
                   /\ b = 0
                THEN <<block>>
                ELSE <<>> ] ]
            , branch   |-> [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
            , chains   |-> 1
            , height   |-> [ c \in Chains |-> [ b \in Branches |->
                IF /\ c = 1
                   /\ b = 0
                THEN 0
                ELSE -1 ] ]
            , sent     |-> [ c \in Chains |-> [ n \in SysNodes |-> {} ] ]
            , sysmsgs  |-> [ c \in Chains |-> IF c = 1 THEN <<msg>> ELSE <<>> ] ]
       /\ node_info =
            [ active   |-> [ n \in Nodes |-> IF n = 1 THEN {1} ELSE {} ]
            , blocks   |-> [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |-> <<>> ] ] ]
            , branches |-> [ n \in Nodes |-> [ c \in Chains |->
                IF /\ n = 1
                   /\ c = 1
                THEN <<0>>
                ELSE <<>> ] ]
            , expect   |-> [ n \in Nodes |-> [ c \in Chains |->
                IF /\ n = 1
                   /\ c = 1
                THEN {exp}
                ELSE {} ] ]
            , headers  |-> [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
            , height   |-> [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |->
                IF /\ n = 1
                   /\ c = 1
                   /\ b = 0
                THEN 0
                ELSE -1 ] ] ]
            , messages |-> [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ] ]

\* [sys] has Get_block_header message
Init_header ==
    LET header == Header(1, 0, 0, 0)
        block  == Block(header, mkOps(0, 0))
        msg    == Msg(1, "Get_operations", [ branch |-> 0, height |-> 0 ])
        exp    == ExpectMsg(3, "Operations", [ branch |-> 0, height |-> 0 ])
    IN /\ network_info =
            [ active   |-> [ c \in Chains |-> IF c = 1 THEN {1, sys} ELSE {sys} ]
            , blocks   |-> [ c \in Chains |-> [ b \in Branches |->
                IF /\ c = 1
                   /\ b = 0
                THEN <<block>>
                ELSE <<>> ] ]
            , branch   |-> [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
            , chains   |-> 1
            , height   |-> [ c \in Chains |-> [ b \in Branches |->
                IF /\ c = 1
                   /\ b = 0
                THEN 0
                ELSE -1 ] ]
            , sent     |-> [ c \in Chains |-> [ n \in SysNodes |-> {} ] ]
            , sysmsgs  |-> [ c \in Chains |-> IF c = 1 THEN <<msg>> ELSE <<>> ] ]
       /\ node_info =
            [ active   |-> [ n \in Nodes |-> IF n = 1 THEN {1} ELSE {} ]
            , blocks   |-> [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |-> <<>> ] ] ]
            , branches |-> [ n \in Nodes |-> [ c \in Chains |->
                IF /\ n = 1
                   /\ c = 1
                THEN <<0>>
                ELSE <<>> ] ]
            , expect   |-> [ n \in Nodes |-> [ c \in Chains |->
                IF /\ n = 1
                   /\ c = 1
                THEN {exp}
                ELSE {} ] ]
            , headers  |-> [ n \in Nodes |-> [ c \in Chains |->
                IF /\ n = 1
                   /\ c = 1
                THEN <<header>>
                ELSE <<>> ] ]
            , height   |-> [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |->
                IF /\ n = 1
                   /\ c = 1
                   /\ b = 0
                THEN 0
                ELSE -1 ] ] ]
            , messages |-> [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ] ]

\* node 1 has block, branch, height
Init_block ==
    LET header == Header(1, 0, 0, 0)
        block  == Block(header, mkOps(0, 0))
    IN /\ network_info =
            [ active   |-> [ c \in Chains |-> IF c = 1 THEN {1, sys} ELSE {sys} ]
            , blocks   |-> [ c \in Chains |-> [ b \in Branches |->
                IF /\ c = 1
                   /\ b = 0
                THEN <<block>>
                ELSE <<>> ] ]
            , branch   |-> [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
            , chains   |-> 1
            , height   |-> [ c \in Chains |-> [ b \in Branches |->
                IF /\ c = 1
                   /\ b = 0
                THEN 0
                ELSE -1 ] ]
            , sent     |-> [ c \in Chains |-> [ n \in SysNodes |-> {} ] ]
            , sysmsgs  |-> [ c \in Chains |-> <<>> ] ]
       /\ node_info =
            [ active   |-> [ n \in Nodes |-> IF n = 1 THEN {1} ELSE {} ]
            , blocks   |-> [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |->
                IF /\ n = 1
                   /\ c = 1
                   /\ b = 0
                THEN <<block>>
                ELSE <<>> ] ] ]
            , branches |-> [ n \in Nodes |-> [ c \in Chains |->
                IF /\ n = 1
                   /\ c = 1
                THEN <<0>>
                ELSE <<>> ] ]
            , expect   |-> [ n \in Nodes |-> [ c \in Chains |-> {} ] ]
            , headers  |-> [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
            , height   |-> [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |->
                IF /\ n = 1
                   /\ c = 1
                   /\ b = 0
                THEN 0
                ELSE -1 ] ] ]
            , messages |-> [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ] ]

\* node 1 has block, branch, height
Init_blocks ==
    LET header1 == Header(1, 0, 0, 0)
        block1  == Block(header1, mkOps(0, 0))
        header2 == Header(1, 0, 1, 0)
        block2  == Block(header2, mkOps(1, 2))
    IN /\ network_info =
            [ active   |-> [ c \in Chains |-> IF c = 1 THEN {1, sys} ELSE {sys} ]
            , blocks   |-> [ c \in Chains |-> [ b \in Branches |->
                IF /\ c = 1
                   /\ b = 0
                THEN <<block2, block1>>
                ELSE <<>> ] ]
            , branch   |-> [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
            , chains   |-> 1
            , height   |-> [ c \in Chains |-> [ b \in Branches |->
                IF /\ c = 1
                   /\ b = 0
                THEN 1
                ELSE -1 ] ]
            , sent     |-> [ c \in Chains |-> [ n \in SysNodes |-> {} ] ]
            , sysmsgs  |-> [ c \in Chains |-> <<>> ] ]
       /\ node_info =
            [ active   |-> [ n \in Nodes |-> IF n = 1 THEN {1} ELSE {} ]
            , blocks   |-> [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |->
                IF /\ n = 1
                   /\ c = 1
                   /\ b = 0
                THEN <<block1>>
                ELSE <<>> ] ] ]
            , branches |-> [ n \in Nodes |-> [ c \in Chains |->
                IF /\ n = 1
                   /\ c = 1
                THEN <<0>>
                ELSE <<>> ] ]
            , expect   |-> [ n \in Nodes |-> [ c \in Chains |-> {} ] ]
            , headers  |-> [ n \in Nodes |-> [ c \in Chains |->
                IF /\ n = 1
                   /\ c = 1
                THEN <<header2>>
                ELSE <<>> ] ]
            , height   |-> [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |->
                IF /\ n = 1
                   /\ c = 1
                   /\ b = 0
                THEN 1
                ELSE -1 ] ] ]
            , messages |-> [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ] ]

\* Initialization variants
Initialize(x) ==
    CASE x = 0 -> Init
      [] x = 1 -> Init_branch
      [] x = 2 -> Init_height
      [] x = 3 -> Init_header
      [] x = 4 -> Init_block
      [] x = 5 -> Init_blocks

================================================================================
