# Emmy family specification

For more information about the Emmy family of consensus protocols, see [Emmy_protocol_details](./Emmy_family_details.md)

## Spec design

There are two phases for each `cycle`:
- `active` - occurs in every block slot of the cycle
- `cycle_admin` - only occurs in the last block slot of the cycle

Assume we are in block slot `bs` of cycle `c`:

In the `active` phase, bakers (roll ids) can bake blocks (represented by `<<roll, time>>`) according to the priority found in `BAKING_PRIORITY[c][bs]`. A baker's priority determines when they are eligible to bake a block wrt the time of the latest block they know of (which can be from baking or endorsing).

For each block slot in each cycle, `MAX_BAKE` baking slots are assigned. Once a block has been baked in block slot `bs`, the endorsers for the this block slot can start endorsing a block. Endorsers also add their endorsed block to their chain (the variable `delegate_blocks`). For each block slot in each cycle, `MAX_ENDORSE` endorsement slots are assigned. Any endorser in `ENDORSEMENT_RIGHTS[c][bs]` can endorse a block in this slot. Once the block delay has been met, bakers in the next slot can bake their blocks. `time` progresses during this phase.

In the last block slot of a cycle, after baking some blocks and a sufficient number of endorsers have endorsed a block, we can move to the `cycle_admin` phase.

In the `cycle_admin` phase, baking rewards and endorsements rewards are calculated and debited to the coresponding accounts and rolls are managed. `time` does not progress during this phase. Once the rewards have been paid and rolls managed, we increment the `cycle` and move to the `active` phase.
