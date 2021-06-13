# Handshaking

## Assumptions/Simplifications

- no communication with DNS
- there are good nodes and bad nodes
  - good nodes follow the protocol
  - bad nodes behave arbitrarily
- metadata is not exchanged
- every node can communicate with every other node (arbitrary network topologies can be enforced easily)
- good nodes try to make connections whenever they can
- good nodes can only be `nack` a `conn_msg` if they have >= `MIN` connections

## Communication model

There are *three* message types sent by good nodes

- `conn_req`
- `ack`
- `nack`

The order in which good nodes send messages is enforced by the enabling conditions for the corresponding actions

Additionally, bad nodes can send `bad` messages and any messages in any order

## Specification attributes

### Constants

- `NODES` - the set of node (ids) in the network
- `GOOD_NODES` - set of nodes which follow the protocol, bad nodes can act arbitrarily
- `MIN` - minimum number of connections
- `MAX` - maximum number of connections

### Variables

- `blacklist` - tuple of each node's blacklisted peers
- `connections` - tuple of each node's accepted connections
- `handshaking` - tuple of each node's in-progress handshake
- `messages` - tuple of each node's incoming messages
- `received_conn_msg` - tuple of each node's peers who have sent a conn_msg

### Actions

#### `SendConnectionMessage`

A good node `g` sends another node `n` a `conn_msg`, `g`'s `conn_attempts` with `n` increment, and `g` is now handshaking with `n`.

Enabling conditions:

- `g` and `n` are distinct
- `g` has fewer than `MAX` connections
- `g` has not exceeded the maximum number of connection attempts
- `g` has not blacklisted `n`
- `g` is not already connected to `n`
- `g` is not already handshaking `n`
- `g` has not received a `conn_msg` from `n` (if `g` has, they will do `HandleConnectionMessage` instead)
- `g` does not currently have a nack from `n`

#### `HandleConnectionMessage`

TODO

Enabling conditions:

#### `Ack`

TODO

Enabling conditions:

#### `HandleAck`

TODO

Enabling conditions:

#### `Nack`

TODO

Enabling conditions:

#### `HandleNack`

TODO

Enabling conditions:

#### `HandleBad`

TODO

Enabling conditions:

#### `HandleBadAckNack`

TODO

Enabling conditions:

#### `Timeout_handshaking(n)`

TODO

Enabling conditions:

#### `Timeout_connection(n)`

TODO

Enabling conditions:

## Invariants/Safety

#### `TypeOK`

TODO

#### `NoSelfInteractions`

TODO

#### `GoodNodesDoNotExceedMaxConnections`

TODO

#### `GoodNodesDoNotHandshakeTheirConnections`

TODO

#### `GoodNodesOnlyReceiveConnectionMessagesWhenHandshaking`

TODO

## Properties/Liveness

#### `GoodNodesAlwaysRespondToConnectionMessagesWithAckOrNack`

TODO

#### `IfPossibleGoodNodesWillEventuallyExceedMinConnections`

TODO

#### `ConnectionsBetweenGoodNodesAreEventuallyBidirectionalOrClosed`

TODO

## State machine

TODO

![](./state_machine.dot.svg)
