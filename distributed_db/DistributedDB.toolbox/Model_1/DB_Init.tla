-------------------------------- MODULE DB_Init --------------------------------

CONSTANTS numNodes, numChains, sizeBound

VARIABLES node_active, node_blocks, node_branches, node_headers, node_height, node_incoming, node_sent,
          active, blocks, branch, chains, mailbox, height, sysmsgs

(************************************************)
(* Module for defining different initial states *)
(************************************************)

LOCAL INSTANCE DB_Defs
LOCAL INSTANCE DB_Messages

--------------------------------------------------------------------------------

(**********************)
(* Initial predicates *)
(**********************)

mkBlock(c, b, h, n) == Block(Header(c, b, h), n)

\* usual
Init_empty ==
    /\ active  = [ c \in Chains |-> {sys} ]
    /\ blocks  = [ c \in Chains |-> [ b \in Branches |->
         IF c = 1 /\ b = 0
         THEN <<mkBlock(1, 0, 0, 0)>>
         ELSE <<>> ] ]
    /\ branch  = [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
    /\ chains  = 1
    /\ mailbox = [ c \in Chains |-> [ n \in SysNodes |-> <<>> ] ]
    /\ height  = [ c \in Chains |-> [ b \in Branches |->
         IF c = 1 /\ b = 0
         THEN 0
         ELSE -1 ] ]
    /\ sysmsgs = [ c \in Chains |-> <<>> ]
    /\ node_active   = [ n \in Nodes |-> {} ]
    /\ node_blocks   = [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |-> <<>> ] ] ]
    /\ node_branches = [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
    /\ node_headers  = [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
    /\ node_height   = [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |-> -1 ] ] ]
    /\ node_incoming = [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
    /\ node_sent     = [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]

\* node 1 has branch 0, no blocks, no headers, no messages
Init_branch ==
    /\ active  = [ c \in Chains |-> IF c = 1 THEN {1, sys} ELSE {sys} ]
    /\ blocks  = [ c \in Chains |-> [ b \in Branches |->
         IF c = 1 /\ b = 0
         THEN <<mkBlock(1, 0, 0, 0)>>
         ELSE <<>> ] ]
    /\ branch  = [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
    /\ chains  = 1
    /\ mailbox = [ c \in Chains |-> [ n \in SysNodes |-> <<>> ] ]
    /\ height  = [ c \in Chains |-> [ b \in Branches |->
         IF c = 1 /\ b = 0
         THEN 0
         ELSE -1 ] ]
    /\ mailbox = [ c \in Chains |-> [ n \in SysNodes |-> <<>> ] ]
    /\ sysmsgs = [ c \in Chains |-> <<>> ]
    /\ node_active   = [ n \in Nodes |-> IF n = 1 THEN {1} ELSE {} ]
    /\ node_blocks   = [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |-> <<>> ] ] ]
    /\ node_branches = [ n \in Nodes |-> [ c \in Chains |->
         IF /\ n = 1
            /\ c = 1
         THEN <<0>>
         ELSE <<>> ] ]
    /\ node_headers  = [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
    /\ node_height   = [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |-> -1 ] ] ]
    /\ node_incoming = [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
    /\ node_sent     = [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]

\* [sys] has Get_block_header message from node 1, chain 1, branch 0
Init_height ==
    LET msg == Msg(1, 0, "Get_block_header", [ branch |-> 0, height |-> 0 ])
    IN /\ active  = [ c \in Chains |-> IF c = 1 THEN {1, sys} ELSE {sys} ]
       /\ blocks  = [ c \in Chains |-> [ b \in Branches |->
            IF c = 1 /\ b = 0
            THEN <<mkBlock(1, 0, 0, 0)>>
            ELSE <<>> ] ]
       /\ branch  = [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
       /\ chains  = 1
       /\ mailbox = [ c \in Chains |-> [ n \in SysNodes |-> <<>> ] ]
       /\ height  = [ c \in Chains |-> [ b \in Branches |->
            IF c = 1 /\ b = 0
            THEN 0
            ELSE -1 ] ]
       /\ mailbox = [ c \in Chains |-> [ n \in SysNodes |-> <<>> ] ]
       /\ sysmsgs = [ c \in Chains |-> IF c = 1 THEN <<msg>> ELSE <<>> ]
       /\ node_active   = [ n \in Nodes |-> IF n = 1 THEN {1} ELSE {} ]
       /\ node_blocks   = [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |-> <<>> ] ] ]
       /\ node_branches = [ n \in Nodes |-> [ c \in Chains |->
            IF n = 1 /\ c = 1
            THEN <<0>>
            ELSE <<>> ] ]
       /\ node_headers  = [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
       /\ node_height   = [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |->
                IF n = 1 /\ c = 1 /\ b = 0
                THEN 0
                ELSE -1 ] ] ]
       /\ node_incoming = [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
       /\ node_sent     = [ n \in Nodes |-> [ c \in Chains |->
            IF n = 1 /\ c = 1
            THEN <<msg>>
            ELSE <<>> ] ]

\* node 1 has a header
\* [sys] has Get_operations message from node 1 on chain 1
Init_header ==
    LET hdr == Header(1, 0, 0)
        blk == Block(hdr, 0)
        msg == Msg(1, 0, "Get_operations", [ branch |-> 0, height |-> 0 ])
    IN /\ active  = [ c \in Chains |-> IF c = 1 THEN {1, sys} ELSE {sys} ]
       /\ blocks  = [ c \in Chains |-> [ b \in Branches |->
            IF c = 1 /\ b = 0
            THEN <<mkBlock(1, 0, 0, 0)>>
            ELSE <<>> ] ]
       /\ branch  = [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
       /\ chains  = 1
       /\ mailbox = [ c \in Chains |-> [ n \in SysNodes |-> <<>> ] ]
       /\ height  = [ c \in Chains |-> [ b \in Branches |->
            IF c = 1 /\ b = 0
            THEN 0
            ELSE -1 ] ]
       /\ mailbox = [ c \in Chains |-> [ n \in SysNodes |-> <<>> ] ]
       /\ sysmsgs = [ c \in Chains |-> IF c = 1 THEN <<msg>> ELSE <<>> ]
       /\ node_active   = [ n \in Nodes |-> IF n = 1 THEN {1} ELSE {} ]
       /\ node_blocks   = [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |-> <<>> ] ] ]
       /\ node_branches = [ n \in Nodes |-> [ c \in Chains |->
            IF n = 1 /\ c = 1
            THEN <<0>>
            ELSE <<>> ] ]
       /\ node_headers  = [ n \in Nodes |-> [ c \in Chains |->
            IF n = 1 /\ c = 1
            THEN <<hdr>>
            ELSE <<>> ] ]
       /\ node_height   = [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |->
            IF n = 1 /\ c = 1 /\ b = 0
            THEN 0
            ELSE -1 ] ] ]
       /\ node_incoming = [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
       /\ node_sent     = [ n \in Nodes |-> [ c \in Chains |->
            IF n = 1 /\ c = 1
            THEN <<msg>>
            ELSE <<>> ] ]

\* node 1 has block, branch, height
Init_block ==
    LET blk == mkBlock(1, 0, 0, 0)
    IN /\ active   = [ c \in Chains |-> IF c = 1 THEN {1, sys} ELSE {sys} ]
       /\ blocks   = [ c \in Chains |-> [ b \in Branches |->
            IF c = 1 /\ b = 0
            THEN <<blk>>
            ELSE <<>> ] ]
       /\ branch   = [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
       /\ chains   = 1
       /\ height   = [ c \in Chains |-> [ b \in Branches |->
            IF c = 1 /\ b = 0
            THEN 0
            ELSE -1 ] ]
       /\ mailbox  = [ c \in Chains |-> [ n \in SysNodes |-> <<>> ] ]
       /\ sysmsgs  = [ c \in Chains |-> <<>> ]
       /\ node_active   = [ n \in Nodes |-> IF n = 1 THEN {1} ELSE {} ]
       /\ node_blocks   = [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |->
            IF n = 1 /\ c = 1 /\ b = 0
            THEN <<blk>>
            ELSE <<>> ] ] ]
       /\ node_branches = [ n \in Nodes |-> [ c \in Chains |->
            IF n = 1 /\ c = 1
            THEN <<0>>
            ELSE <<>> ] ]
       /\ node_headers  = [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
       /\ node_height   = [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |->
            IF n = 1 /\ c = 1 /\ b = 0
            THEN 0
            ELSE -1 ] ] ]
       /\ node_incoming = [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
       /\ node_sent     = [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]

\* node 1 has block, branch, height
Init_block_header ==
    LET hdr1 == Header(1, 0, 0)
        blk1  == Block(hdr1, 0)
        hdr2 == Header(1, 0, 1)
        blk2  == Block(hdr2, 2)
    IN /\ active  = [ c \in Chains |-> IF c = 1 THEN {1, sys} ELSE {sys} ]
       /\ blocks  = [ c \in Chains |-> [ b \in Branches |->
            IF c = 1 /\ b = 0
            THEN <<blk2, blk1>>
            ELSE <<>> ] ]
       /\ branch  = [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
       /\ chains  = 1
       /\ height  = [ c \in Chains |-> [ b \in Branches |->
            IF c = 1 /\ b = 0
            THEN 1
            ELSE -1 ] ]
       /\ mailbox = [ c \in Chains |-> [ n \in SysNodes |-> <<>> ] ]
       /\ sysmsgs = [ c \in Chains |-> <<>> ]
       /\ node_active   = [ n \in Nodes |-> IF n = 1 THEN {1} ELSE {} ]
       /\ node_blocks   = [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |->
            IF n = 1 /\ c = 1 /\ b = 0
            THEN <<blk1>>
            ELSE <<>> ] ] ]
       /\ node_branches = [ n \in Nodes |-> [ c \in Chains |->
            IF n = 1 /\ c = 1
            THEN <<0>>
            ELSE <<>> ] ]
       /\ node_headers  = [ n \in Nodes |-> [ c \in Chains |->
            IF n = 1 /\ c = 1
            THEN <<hdr2>>
            ELSE <<>> ] ]
       /\ node_height   = [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |->
            IF n = 1 /\ c = 1 /\ b = 0
            THEN 1
            ELSE -1 ] ] ]
       /\ node_incoming = [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
       /\ node_sent     = [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]

\* node 1 has block, branch, height
Init_blocks ==
    LET blk1 == Block(Header(1, 0, 0), 0)
        blk2 == Block(Header(1, 0, 1), 2)
    IN /\ active  = [ c \in Chains |-> IF c = 1 THEN {1, sys} ELSE {sys} ]
       /\ blocks  = [ c \in Chains |-> [ b \in Branches |->
            IF c = 1 /\ b = 0
            THEN <<blk2, blk1>>
            ELSE <<>> ] ]
       /\ branch  = [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
       /\ chains  = 1
       /\ height  = [ c \in Chains |-> [ b \in Branches |->
            IF c = 1 /\ b = 0
            THEN 1
            ELSE -1 ] ]
       /\ mailbox = [ c \in Chains |-> [ n \in SysNodes |-> <<>> ] ]
       /\ sysmsgs = [ c \in Chains |-> <<>> ]
       /\ node_active   = [ n \in Nodes |-> IF n = 1 THEN {1} ELSE {} ]
       /\ node_blocks   = [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |->
            IF n = 1 /\ c = 1 /\ b = 0
            THEN <<blk1>>
            ELSE <<>> ] ] ]
       /\ node_branches = [ n \in Nodes |-> [ c \in Chains |->
            IF n = 1 /\ c = 1
            THEN <<0>>
            ELSE <<>> ] ]
       /\ node_headers  = [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
       /\ node_height   = [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |->
            IF n = 1 /\ c = 1 /\ b = 0
            THEN 1
            ELSE -1 ] ] ]
       /\ node_incoming = [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
       /\ node_sent     = [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]

Init_options == 0..6

\* Initialization variants
Initialize(x) ==
    CASE x = 1 -> Init_branch
      [] x = 2 -> Init_height
      [] x = 3 -> Init_header
      [] x = 4 -> Init_block
      [] x = 5 -> Init_block_header
      [] x = 6 -> Init_blocks
      [] OTHER -> Init_empty

================================================================================
