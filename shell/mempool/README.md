# Mempool specification

This is the formal specification for the Tezedge node's mempool. The main focus is to verify desirable liveness properties of endorsement propagation, specifcally that, in the absence of complete network failures, all nodes will eventually see each endorsement.

This directory contains two main TLA+ specifications: `Mempool` and `Mempool_global`. `Mempool` is a local spec; it only focuses on a single correct node and makes claims about only that node's behavior. `Mempool_global` is a global spec; it takes into consideration the entire network and the nodes' collective behavior. As always, the TLA+ specification models the protocol as a state machine.

## Mempool_global spec

This spec tracks all nodes in the network, i.e. a state is determined by the aggregation of all node variables. In this way we can verify global properties of the network behavior.

Each node participates in the propagation of operations on the P2P layer and keeps a local chain of blocks based on the messages they receive. Nodes aggregate and propagate operations via their *mempool*, a data structure consisting of an ordered collection of "known valid" operations and an unordered collection of "pending" operations.

Each node's shell has a prevalidator which classifies pending operations into one of four sets: `applied`, `branch_delayed`, `branch_refused`, and `refused`. Applied operations are those which have been applied. Branch delayed operations are those which are for a block in the future on the node's current branch. Branch refused operations are for a different branch than the node's current branch. Refused operations are not valid for any branch.

Nodes communicate via the typical P2P layer messages: `Current_head`, `Get_current_head`, etc.

### Mempool spec

This spec only tracks the local information of a single node, i.e. the state is determined by only this one node's variables. The purpose of this spec is to use it for trace checking the behavior from an actual Tezedge node. We do this to gain confidence about the conformance of our source code with the specification.

## Endorsement propagation

The `Mempool_global` spec satisfies several [liveness properties](./Mempool_global.tla#L465). The most important of which being `EndorsementPropagation`. This property says that all (valid) endorsement operations will eventually be included in a block in every node's local chain.

## Run the code = verify the spec's properties

To verify all the liveness properties of the spec using TLC,

1. Clone the repo
2. From the mempool directory (/shell/mempool), do `tlc MC_liveness.tla`
