# Tenderbake specification

For more information about Tenderbake and dynamic repeated consensus, see [Tenderbake](./Tenderbake.md)

For the TLA+ spec, see [Tenderbake spec](./Tenderbake.tla)

## Spec design

This specification follows the design of Tenderbake laid out in [Tendbake - A Solution to Dynamic Repeated Consenses for Blockchains](https://arxiv.org/abs/2001.11965). Liberal simplifications/abstractions are used to produce a tractable spec and will be explained below. As with all TLA+ specs, we specify the consensus protocol as a state machine.

The spec contains both *correct* and *faulty* processes. Correct processes follow the protocol while faulty processes behave arbitrarily.

### Simplifications/assumptions

- dynamic level comittees
  - committes depend only on the level
  - proposer depends on the round within the level
- `n >= 3f + 1` where `n` is the number of bakers (correct + faulty processes) and `f` is the number of faulty bakers (processes)
- all committee members have the ability to communicate with one another
- no mempool

## Run the code = verify the specification's properties

The spec's properties can be found [here](./Tanderbake.tla#L994). To verify these properties using TLC,
1. Clone the repo
2. From the Tenderbake directory, do `tlc MC_safety.tla`
