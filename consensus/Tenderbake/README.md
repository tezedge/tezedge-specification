# Tenderbake specification

For more information about Tenderbake and dynamic repeated consensus, see [Tenderbake](./Tenderbake.md)

For the TLA+ spec, see [Tenderbake spec](./Tenderbake.tla)

## Spec design

This specification follows the design of Tenderbake laid out in [Tendbake - A Solution to Dynamic Repeated Consenses for Blockchains](https://arxiv.org/abs/2001.11965). Liberal simplifications/abstractions are used to produce a tractable spec and will be explained below. As with all TLA+ specs, we specify the consensus protocol as an automaton (state machine).

### Possible actions of the state machine

The spec contains both *correct* and *faulty* processes. Correct processes follow the protocol while faulty processes behave arbitrarily. We describe the actions allowed by correct processes.

#### Propose

At the beginning of each round, a designated committee member, called the *proposer*, can propagate a new block to be preendorsed, then endorsed by the committee.

#### Preendorse

After a value has been proposed, the committee members signal their intention to "lock" on this value by boradcasting preendorsement messages.

#### Endorse

If a member sees a quorum of preendorsement messages for a value, they broadcast an endorsement message for that value. If a member sees a quorum of endorsement messages for a value, they consider this value to be correct and add the block to their local chain.

#### Observation

Observation actions are only enabled for noncommittee processes, . The committee depends on the level, not all processes will be part of each committee. These observers simply handle the network messages and adjust any corresponding local information.

#### Timeout

At any point in the execution of the state machine, it is possible for a correct process to timeout. When this occurs, the process pulls chains from all other processes.

### Simplifications/assumptions

- dynamic level comittees
  - committes depend only on the level
  - proposer depends on the round within the level
- `n >= 3f + 1` where `n` is the number of bakers (correct + faulty processes) and `f` is the number of faulty bakers (processes)
- all committee members have the ability to communicate with one another
- bakers do not maintain or exchange mempools
- chains are always pulled from all other processes (complete network topology)

## Run the code = verify the specification's properties

The spec's properties can be found [here](./Tenderbake.tla#L1006). To verify these properties using TLC,
1. Clone the repo
2. From the Tenderbake directory (/consensus/Tenderbake), do `tlc MC_safety.tla`
