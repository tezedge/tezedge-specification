# Consensus

## Spec design

There are three phases for each `block_slot` in each `cycle`:
- `bake`
- `endorse`
- `close`

Assume we are in block slot `bs` of cycle `c`:

In the `bake` phase, bakers (roll ids) can bake blocks (`<<roll, time>>`) according to the priority found in `BAKING_PRIORITY[c][bs]`. A baker's priority determines when they are eligible to bake a block wrt the time of their most recent block (which can be from baking or endorsing). For each block slot in each cycle, `MAX_BAKE` baking slots are assigned. Once a block has been baked in priority 0, we are free to move to the `endorse` phase. `time` progresses during this phase.

In the `endorse` phase, endorsers (roll ids) endorse a block in cycle `c`, block slot `bs`. Endorsers also add this block to their chain (`delegate_blocks`). For each block slot in each cycle, `MAX_ENDORSE` endorsement slots are assigned. Any endorser in `ENDORSEMENT_RIGHTS[c][bs]` can endorse a block in this slot. Once there are suff many endorsements (weighted) on a block, we are free to move to the `close` phase. `time` progresses during this phase.

In the `close` phase, baking rewards and endorsements rewards are calculated and debited to the cooresponding accounts, rolls are managed. `time` does not progress during this phase. Once the rewards have been paid and rolls managed, we increment the block slot and move to the `bake` phase.
