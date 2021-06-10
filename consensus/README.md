# Consensus

We'll start with an overview of Emmy, Emmy+, and Emmy★ and conclude with an overview of the design of the specification.

## Emmy

Introduced in the [Tezos whitepaper](https://tezos.com/whitepaper.pdf), Emmy is the original proof-of-stake protocol used in the Tezos network. Inspired by [Slasher](https://blog.ethereum.org/2014/01/15/slasher-a-punitive-proof-of-stake-algorithm/), [chain-of-activity](www.cs.technion.ac.il/~idddo/CoA.pdf), and proof-of-burn.

Each block is mined (*baked*) by a random stakeholder (the *baker*) and includes multiple signatures (*endorsements*) of the previous block provided by random stakeholders (the *endorsers*). Baking and endorsing both offer small rewards but also require making a one cycle security deposit to be forfeited in the event of a double baking or double endorsing.

The protocl unfolds in cycles of 2048 blocks. At the beginning of each cycle `c`, a random seed is derived from numbers chosen by bakers and committed to in the penultimate cycle `c - 2`, and revealed in the last `c - 1`. This seed determines the baking priorities and endorsing rights for the next cycle `c + 1`.

![](./seed_generation.png)

### Block delays

The protocol imposes minimum delays between blocks. In principle, each block can be baked by any stakeholder. However, for a given block, each stakeholder is subject to a random minimum delay. The stakeholder receiving the highest priority may bake the block one minute after the previous block. The stakeholder receiving the second highest priority may bake the block two minutes after the previous block, the third, three minutes, and so on.

This guarantees that a fork where only a small fraction of stakeholders contribute will exhibit a low rate of block creation.

### Random seed generation

Every block baked carries a hash commitment to a random number chosen by the baker. These numbers must be revealed in the next cycle under penalty of forfeiting the safety bond.

All the revealed numbers in a cycle are combined in a hash list and the seed is derived from the root using the `scrypt` key derivation function.

### Follow-the-coin procedure

A **roll** is a collection of 10000 ꜩ. There are thus about one million rolls in existence. A database maps every roll to its current owner.

Each address holds a certain set of specific rolls as well as some loose change. When we desire to spend a fraction of a full roll, the roll is broken and its serial number is sent in a LIFO queue of rolls. Every transaction is processed in a way that minimizes the number of broken rolls. Whenever an address holds enough coins to form a roll, a serial number is pulled from the queue and the roll is formed again.

The LIFO priority ensures that an attacker working on a secret fork cannot change the coins he holds by shuffling change between accounts.

### Baking blocks

The random seed is used to repeatedly select a roll. The first roll selected allows its stakeholder to bake a block after one minute, the second one after two minutes — and so on.

To avoid a potentially problematic situation were no stakeholder made a safety deposit to bake a particular block, after a 16 minutes delay, the block may be baked without a deposit.

Bonds are implicitly returned to their buyers immediately in any chain where they do not bake a block.

### Endorsing blocks

A chain’s *weight* could be defined to be the number of blocks. However, this would open the door to a form of *selfish mining*.

Instead, a signing (*endorsing*) scheme is used and the number of endorsements constitutes the weight of a chain. While a block is being baked, the random seed is used to randomly assign 16 endorsing rights to 16 rolls.

The stakeholders who received endorsing rights observe the blocks being baked and then submit endorsements of that blocks. Those endorsements are then included in the next block, by bakers attempting to secure their parent’s inclusion in the blockchain.

The endorsement reward received by endorsers is inversely proportional to the time interval between the block and its predecessor.

Endorsers thus have a strong incentive to endorse what they genuinely believe to be the best block produced at that point. They also have a strong incentive to agree on which block they will endorse as endorsement rewards are only paid if the block is ultimately included in the blockchain.

### Denunciations

In order to avoid double baking and double endorsing, a baker may include a *denunciation* in their block.

This denunciation takes the form of two signatures. The baker and block endorsers sign the height of the block, making the proof of malfeasance quite concise.

Once a party has been found guilty of double baking or double endorsing, the safety bond is forfeited.

## Emmy+

TODO

## Emmy★

TODO

## Spec design

There are two phases for each `cycle`:
- `active` - occurs in every block slot of the cycle
- `cycle_admin` - only occurs in the last block slot of the cycle

Assume we are in block slot `bs` of cycle `c`:

In the `active` phase, bakers (roll ids) can bake blocks (represented by `<<roll, time>>`) according to the priority found in `BAKING_PRIORITY[c][bs]`. A baker's priority determines when they are eligible to bake a block wrt the time of the latest block they know of (which can be from baking or endorsing).

For each block slot in each cycle, `MAX_BAKE` baking slots are assigned. Once a block has been baked in block slot `bs`, the endorsers for the this block slot can start endorsing a block. Endorsers also add their endorsed block to their chain (the variable `delegate_blocks`). For each block slot in each cycle, `MAX_ENDORSE` endorsement slots are assigned. Any endorser in `ENDORSEMENT_RIGHTS[c][bs]` can endorse a block in this slot. Once the block delay has been met, bakers in the next slot can bake their blocks. `time` progresses during this phase.

In the last block slot of a cycle, after baking some blocks and a sufficient number of endorsers have endorsed a block, we can move to the `cycle_admin` phase.

In the `cycle_admin` phase, baking rewards and endorsements rewards are calculated and debited to the coresponding accounts and rolls are managed. `time` does not progress during this phase. Once the rewards have been paid and rolls managed, we increment the `cycle` and move to the `active` phase.
