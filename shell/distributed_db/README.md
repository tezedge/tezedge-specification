# Distributed DB Model

This is an effort to model the bootstrapping process on the Tezos blockchain. We use an asynchronous communication model which allows for messages to be dropped "during transit" and expected responses to sent messages to be registered. This specification follows the Tezos P2P and shell libraries as closely as possible with a few assumptions/simplifications.

## Assumptions/Simplifications

All models of sufficiently complex systems must make some assumptions and simplifications. This is a list of assumptions/simplifications used throughout this specification:

- no protocol upgrades (this can be added later)
- no checkpoints (this can also be added later)
- activation and deactivation messages are not explicitly passed between nodes
- no explicit connections for each chain/node (all active nodes on a chain can communicate with one another)
- nodes do not produce or validate blocks (all blocks are produced and validated by the "network")
- no competing blocks at a given height on a given branch of a given chain
- blocks are not endorsed
- all operations for a block are sent together when requested
- messages can be dropped (both on-chain and off-chain)
- no timeouts on header or operation requests

## Asynchronous communication model

The communication model we employ in the spec has a few important features. It is summarized as follows:

Each node on each chain has a *set* of messages that have been `sent` to them. These messages are either dropped or received by the intended recipient. If a message is dropped, the recipient has no knowledge that it was ever sent. If a message is received (they can be received in any order), it goes into a `messages` *queue* for the recipient to handle later. When handling a message that warrants a response or acknowledgment, the node will send the appropriate response or acknowledgment to the original sender. When a node sends another node a direct message on a chain (as opposed to broadcasting a message to all active nodes on the chain), the sender registers an expected response from the recipient in their `expect` *set*. This way if the message is dropped, the sender will know that they have not received the response they were expecting and can send their original message again.

We also allow for off-chain communication between the "system" and the nodes for adding new chains.

## Constants

There are *three* constants/parameters in this model:

- `numChains`: the maximum number of chains allowed

- `numNodes`: the number of nodes

Nodes are identified by an id from 1 to `numNodes`.

- `sizeBound`: a parameter used to constrain the sizes of sets and lengths of sequences

To simplify things and to keep the model finite, we have used a single parameter to bound the sizes of all sets and sequences in the model.

## Important sets

- The set of all nodes: `Nodes == 1..numNodes`

- The set of all chains: `Chains == 1..numChains`

- The set of all branches: `Branches == 0..sizeBound`

- The set of all block heights: `Heights == 0..sizeBound`

- The set of all numbers of block operations: `Op_nums == 0..sizeBound`

- `Headers`: the set of all block headers, i.e. records with the fields `chain`, `branch`, `height`, and `num_ops`

```
Headers == [ chain : Chains, branch : Branches, height : Heights, num_ops : Op_nums ]
```

- `Operations`: the set of all block operations, i.e. sequences of length 0, ..., `sizeBound` of pairs of a block height and operation numbers

```
Operations == UNION { [ 1..num_ops -> Pairs({h}, 1..num_ops) ] : h \in Heights, num_ops \in Op_nums }
```

This set looks more complicated than it actually is. As an example of an element it contains, it contains the empty sequence, `<<>>`. We see this by letting `num_ops` be 0; the set `1..0` in TLA+ is the empty set `{}` and the only sequence/function whose domain is `{}` is `<<>>`.

- `Blocks`: the set of all blocks, i.e. records with fields `header` and `ops`, where `header \in Headers` and `ops \in Operations`

```
Blocks == [ header : Headers, ops : Operations ]
```

- `Messages`: the set of all messages. There are *three* kinds of messages: `full`, `synchronization`, and `system`. See the `DB_Messages` module for more info.

## Variables

There are *two* variables in this model:

- `network_info` is a record with the following fields:

```
active : [ Chains -> SUBSET Nodes ]
blocks : [ Chains -> [ Branches -> Seq(Blocks) ] ]
branch : [ Chains -> Branches ]
chains : Chains
height : [ Chains -> [ Branches -> Heights \cup {-1} ] ]
sent   : [ Chains -> [ Nodes -> SUBSET Messages ] ]
```

The `network_info` variable is intended to capture a global view of the network, i.e. all chains, branches, blocks, messages, etc.

*Note*: The `SUBSET` operator takes a set `S` as input and returns the set of all subsets of `S`. The `Seq` operator takes a set `S` as input and returns the set of all sequences of elements from `S`.

The `active` field is a function from `Chains` to subsets of `Nodes`; `network_info.active[chain]` is the set of active nodes on `chain`.

The `blocks` field is a function from `Chains` to functions from `Branches` to sequences of `Blocks`; `network_info.blocks[chain][branch]` is the sequence of blocks on `branch` of `chain` in reverse chronological order.

The `branch` field is a function from `Chains` to `Branches`; `network_info.branch[chain]` is the current branch on `chain`.

The `chains` field is an element of `Chains`; `network_info.chains` is the number of active chains.

The `height` field is a function from `Chains` to functions from `Branches` to `Heights \cup {-1}`; `network_info.height[chain][branch]` is the current height of `branch` on `chain`. We `network_info.height[chain][branch] = -1` if an only if `branch` is not active on `chain`.

The `sent `field is a function from `Chains` to functions from `Nodes` to subsets of `Messages`; `network_info.sent[chain][node]` is the set of messages sent to `node` on `chain`.

- `node_info` is a record with the following fields:

```
active   : [ Nodes -> SUBSET Chains ]
blocks   : [ Nodes -> [ Chains -> [ Branches -> Seq(Blocks) ] ] ]
branches : [ Nodes -> [ Chains -> Seq(Branches) ] ]
expect   : [ Nodes -> [ Chains -> SUBSET Messages ] ]
headers  : [ Nodes -> [ Chains -> Seq(Headers) ] ]
messages : [ Nodes -> [ Chains -> Seq(Messages) ] ]
offchain : [ Nodes -> Seq(Messages) ]
```

The `node_info` variable is intended to capture a local view of the network, i.e. it only contains information known about the nodes.

The `active` field is a function from `Nodes` to subsets of `Chains`; `node_info.active[node]` is the set of chains on which `node` is active.

The `blocks` field is a function from `Nodes` to functions from `Chains` to functions from `Branches` to sequences of `Blocks`; `node_info.blocks[node][chain][branch]` is the sequence of blocks that `node` knows about on `branch` of `chain`.

The `branches` field is a function from `Nodes` to functions from `Chains` to sequences of `Branches`; `node_info.branches[node][chain]` is the sequence of branches on `chain` that `node` knows about, ordered from highest to lowest.

The `expect` field is a function from `Nodes` to functions from `Chains` to subsets of `Messages`; `node_info.expect[node][chain]` is the set of responses that `node` expects to messages they have sent to other active nodes on `chain`.

The `headers` field is a function from `Nodes` to functions from `Chains` to sequences of `Headers`; `node_info.headers[node][chain]` is the sequence of headers that `node` has received on `chain`, but has yet to receive the corresponding operations to form the block. They are reverse lexicographically ordered by branch, then height, i.e. higher branches and higher heights come first.

The `messages` field is a function from `Nodes` to functions from `Chains` to sequences of `Messages`; `node_info.messages[node][chain]` is the queue of messages that `node` has received on `chain`. They will be handled in a FIFO fashion.

The `offchain` field is a function from `Nodes` to sequences of `Messages`; `node_info.offchain[node]` is the queue of messages that `node` has received off-chain. Nodes do not communicate off-chain. Currently, only `New_chain` system messages are sent here.

## Specification

A TLA+ specification determines the possible initial states and the evolution of a model, i.e. it determines all possible behaviors that can be exhibited in a model. Typically, a TLA+ specification is defined by an *initial predicate* and a collection of *next actions*, like this:

```
Spec == Init /\ [][Next]_<<network_info, node_info>>
```

where `Init` is the initial predicate and `Next` is the collection of next actions. This formula means that a model satisfying `Spec` must have an initial state satisfying `Init` and all actions (state transitions) are either from the collection `Next` or they do not change the variables `network_info` and `node_info`. These actions which don't change the variables are called *stuttering steps* and they are required for modularity and compositionality of models.

### Initial predicate

The *initial predicate* defines the initial state(s) of the model; it constrains the values of the variables in an initial state. It is defined as follows:

```
Init ==
    /\ network_info =
         [ active   |-> [ c \in Chains |-> {} ]
         , blocks   |-> [ c \in Chains |-> [ b \in Branches |-> <<>> ] ]
         , branch   |-> [ c \in Chains |-> 0 ]
         , chains   |-> 1
         , height   |-> [ c \in Chains |-> [ b \in Branches |-> -1 ] ]
         , recv     |-> [ c \in Chains |-> [ n \in Nodes |-> <<>> ] ]
         , sent     |-> [ c \in Chains |-> [ n \in Nodes |-> {} ] ] ]
    /\ node_info =
         [ active   |-> [ n \in Nodes |-> {} ]
         , blocks   |-> [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |-> <<>> ] ] ]
         , branches |-> [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
         , expect   |-> [ n \in Nodes |-> [ c \in Chains |-> {} ] ]
         , headers  |-> [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |-> {} ] ] ]
         , messages |-> [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
         , offchain |-> [ n \in Nodes |-> <<>> ] ]
```

Initially, our model variables have these values. Our initial predicate defines a unique initial state.

For example, the `active` field of `network_info` is initially a function/sequence whose domain is the set `Chains` and each value of the function is the empty set, i.e. `network_info.active[1] = {}`, ..., `network_info.active[numChains] = {}`. This is interpreted as: initially, each chain has *no* active nodes.

Theoretically, we can start the model from any valid state and let the evolution be governed by the `Next` actions.

Pragmatically, we want to be able to enumerate the initial states and that's really simple if our initial predicate defines a unique initial state.

### Next actions

There are *six* kinds of `Next` actions in this specification.

#### Activation actions

These actions allow nodes to become active and inactive on a chain. They are defined in the `DB_Activation` module.

- `Activation`: an inactive node becomes active on a chain
- `Deactivation`: an active node becomes inactive on a chain

#### Advertise actions

These actions allow a node to broadcast their current branch on a chain and their current head on a branch. They are defined and explained in the `DB_Advertise` module.

- `Advertise_branch`: a node advertises their current branch
- `Advertise_head`: a node advertises their current head (height)

#### Handle actions

These actions allow nodes to react to messages they have received. They are defined in the `DB_Handle` module.

- `Handle_offchain_msg`: a node reacts to an offchain message
- `Handle_onchain_msg`: a node reacts to a message from another node
- `Send_again`: a node sends a message again because they have not gotten a response to the original message

#### Maintenance actions

These actions allow chains, branches, and blocks to be added to the network. They are defined in the `DB_Maintenance` module.

- `Block_production`: a new block is produced and broadcast to active nodes
- `New_branch`: a new branch is created and broadcast to active nodes
- `New_chain`: a new chain is created and broadcast to nodes offchain

#### Receive actions

These actions allow nodes to receive or drop messages sent to them; they are needed because of the communication model. They are defined in the `DB_Receive` module.

- `Receive`: a message is received, i.e. added to the queue of messages the node can react to
- `Drop`: a message sent to a node is dropped and the node is none the wiser
- `Drop_offchain`: a message sent to a node offchain is dropped

#### Request actions

These actions allow nodes to send messages requesting specific information from another node. They are defined in the `DB_Request` module.

- `Get_current_branch_one`: a node requests the current branch from another active node
- `Get_current_branch_all`: a node requests the current branch from all other active nodes
- `Get_current_head_one`: a node requests the current head from another active node
- `Get_current_head_all`: a node requests the current head from all other active nodes
- `Get_block_header_one`: a node requests a block header from another active node
- `Get_block_header_all`: a node requests a block header from all other active nodes
- `Get_operations_one`: a node requests a block's operations from another active node
- `Get_operations_all`: a node requests a block's operations from all other active nodes
