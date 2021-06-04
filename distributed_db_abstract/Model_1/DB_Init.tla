-------------------------------- MODULE DB_Init --------------------------------

(************************************************)
(* Module for defining different initial states *)
(************************************************)

EXTENDS DB_Defs

--------------------------------------------------------------------------------

(**********************)
(* Initial predicates *)
(**********************)

mkBlock(c, b, h, n) == Block(Header(c, b, h), n)

\* usual
Init_empty ==
    LET blk == mkBlock(1, 0, 0, 0) IN
    /\ blocks  = [ c \in Chains |-> [ b \in Branches |->
        IF c = 1 /\ b = 0 THEN <<blk>> ELSE <<>> ] ]
    /\ branch  = [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
    /\ chains  = 1
    /\ height  = [ c \in Chains |-> [ b \in Branches |-> IF c = 1 /\ b = 0 THEN 0 ELSE -1 ] ]
    /\ node_active   = {}
    /\ node_blocks   = [ c \in Chains |-> [ b \in Branches |-> <<>> ] ]
    /\ node_branches = [ c \in Chains |-> <<>> ]
    /\ node_headers  = [ c \in Chains |-> <<>> ]
    /\ node_height   = [ c \in Chains |-> [ b \in Branches |-> -1 ] ]

\* node has branch
Init_branch ==
    LET blk == mkBlock(1, 0, 0, 0) IN
    /\ blocks  = [ c \in Chains |-> [ b \in Branches |->
        IF c = 1 /\ b = 0 THEN <<blk>> ELSE <<>> ] ]
    /\ branch  = [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
    /\ chains  = 1
    /\ height  = [ c \in Chains |-> [ b \in Branches |-> IF c = 1 /\ b = 0 THEN 0 ELSE -1 ] ]
    /\ node_active   = {1}
    /\ node_blocks   = [ c \in Chains |-> [ b \in Branches |-> <<>> ] ]
    /\ node_branches = [ c \in Chains |-> IF c = 1 THEN <<0>> ELSE <<>> ]
    /\ node_headers  = [ c \in Chains |-> <<>> ]
    /\ node_height   = [ c \in Chains |-> [ b \in Branches |-> -1 ] ]

\* node has branch, height
Init_height ==
    LET blk == mkBlock(1, 0, 0, 0) IN
    /\ blocks  = [ c \in Chains |-> [ b \in Branches |->
        IF c = 1 /\ b = 0 THEN <<blk>> ELSE <<>> ] ]
    /\ branch  = [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
    /\ chains  = 1
    /\ height  = [ c \in Chains |-> [ b \in Branches |-> IF c = 1 /\ b = 0 THEN 0 ELSE -1 ] ]
    /\ node_active   = {1}
    /\ node_blocks   = [ c \in Chains |-> [ b \in Branches |-> <<>> ] ]
    /\ node_branches = [ c \in Chains |-> IF c = 1 THEN <<0>> ELSE <<>> ]
    /\ node_headers  = [ c \in Chains |-> <<>> ]
    /\ node_height   = [ c \in Chains |-> [ b \in Branches |-> IF c = 1 /\ b = 0 THEN 0 ELSE -1 ] ]

\* node has a branch, height, header
Init_header ==
    LET hdr == Header(1, 0, 0)
        blk == Block(hdr, 0)
    IN
    /\ blocks  = [ c \in Chains |-> [ b \in Branches |->
        IF c = 1 /\ b = 0 THEN <<blk>> ELSE <<>> ] ]
    /\ branch  = [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
    /\ chains  = 1
    /\ height  = [ c \in Chains |-> [ b \in Branches |-> IF c = 1 /\ b = 0 THEN 0 ELSE -1 ] ]
    /\ node_active   = {1}
    /\ node_blocks   = [ c \in Chains |-> [ b \in Branches |-> <<>> ] ]
    /\ node_branches = [ c \in Chains |-> IF c = 1 THEN <<0>> ELSE <<>> ]
    /\ node_headers  = [ c \in Chains |-> IF c = 1 THEN <<hdr>> ELSE <<>> ]
    /\ node_height   = [ c \in Chains |-> [ b \in Branches |-> IF c = 1 /\ b = 0 THEN 0 ELSE -1 ] ]

\* node 1 has branch, height, block
Init_block ==
    LET blk == mkBlock(1, 0, 0, 0) IN
    /\ blocks   = [ c \in Chains |-> [ b \in Branches |->
        IF c = 1 /\ b = 0 THEN <<blk>> ELSE <<>> ] ]
    /\ branch  = [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
    /\ chains  = 1
    /\ height  = [ c \in Chains |-> [ b \in Branches |-> IF c = 1 /\ b = 0 THEN 0 ELSE -1 ] ]
    /\ node_active   = {1}
    /\ node_blocks   = [ c \in Chains |-> [ b \in Branches |->
        IF c = 1 /\ b = 0 THEN <<blk>> ELSE <<>> ] ]
    /\ node_branches = [ c \in Chains |-> IF c = 1 THEN <<0>> ELSE <<>> ]
    /\ node_headers  = [ c \in Chains |-> <<>> ]
    /\ node_height   = [ c \in Chains |-> [ b \in Branches |-> IF c = 1 /\ b = 0 THEN 0 ELSE -1 ] ]

\* node has branch, height, header, block
Init_block_header ==
    LET hdr1 == Header(1, 0, 0)
        blk1  == Block(hdr1, 0)
        hdr2 == Header(1, 0, 1)
        blk2  == Block(hdr2, 1)
    IN
    /\ blocks  = [ c \in Chains |-> [ b \in Branches |->
        IF c = 1 /\ b = 0 THEN <<blk2, blk1>> ELSE <<>> ] ]
    /\ branch  = [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
    /\ chains  = 1
    /\ height  = [ c \in Chains |-> [ b \in Branches |-> IF c = 1 /\ b = 0 THEN 1 ELSE -1 ] ]
    /\ node_active   = {1}
    /\ node_blocks   = [ c \in Chains |-> [ b \in Branches |->
        IF c = 1 /\ b = 0 THEN <<blk1>> ELSE <<>> ] ]
    /\ node_branches = [ c \in Chains |-> IF c = 1 THEN <<0>> ELSE <<>> ]
    /\ node_headers  = [ c \in Chains |-> IF c = 1 THEN <<hdr2>> ELSE <<>> ]
    /\ node_height   = [ c \in Chains |-> [ b \in Branches |-> IF c = 1 /\ b = 0 THEN 1 ELSE -1 ] ]

\* node 1 has block, branch, height
Init_blocks ==
    LET blk1 == Block(Header(1, 0, 0), 0)
        blk2 == Block(Header(1, 0, 1), 1)
    IN
    /\ blocks  = [ c \in Chains |-> [ b \in Branches |->
        IF c = 1 /\ b = 0 THEN <<blk2, blk1>> ELSE <<>> ] ]
    /\ branch  = [ c \in Chains |-> IF c = 1 THEN 0 ELSE -1 ]
    /\ chains  = 1
    /\ height  = [ c \in Chains |-> [ b \in Branches |-> IF c = 1 /\ b = 0 THEN 1 ELSE -1 ] ]
    /\ node_active   = {1}
    /\ node_blocks   = [ c \in Chains |-> [ b \in Branches |->
        IF c = 1 /\ b = 0 THEN <<blk1>> ELSE <<>> ] ]
    /\ node_branches = [ c \in Chains |-> IF c = 1 THEN <<0>> ELSE <<>> ]
    /\ node_headers  = [ c \in Chains |-> <<>> ]
    /\ node_height   = [ c \in Chains |-> [ b \in Branches |-> IF c = 1 /\ b = 0 THEN 1 ELSE -1 ] ]

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
