# Handshaking (blacklist_timeouts)

This is the second iteration of the handshaking specification. Please see the [attributes](./README.md#specification-attributes) section for spec details.

[Handshaking.tla](./Handshaking.tla) has all of the features of the previous iteration except it swaps the notion of boundedly many timeouts and connection attempts for blacklisting (banning) a peer upon timeout.

## Verifying the specification's properties

### Safety

To verify the spec's safety properties for a model with 1 bad node and 2 good nodes, one can invoke TLC via

```
$ tlc MC_safety.tla deadlock -worker 4096
```

The expected output can be found in [`MC_safety.out`](./MC_safety.out).

Note: in general, TLC produces a large number of explicit states which are stored on disk. Thus, we prefer to use TLC on a remote server or instead, use Apalache. Verification of large models using TLC is generally infeasible.

Alternatively, to verify the safety properties for larger models (e.g. 5 bad nodes and 5 good nodes), one can verify that the conjunction of all safety properties, `IndInv`, consitutes an inductive invariant by using Apalache. To do this, go to the [`apalache`](./apalache) directory and choose any of the supplied configurations. Within your directory of choice (e.g. [`5good_5bad`](./apalache/5good_5bad)), use the command

```
$ apalache check --init=Init --inv=IndInv --length=0 MC_safety_5good_5bad.tla 
```

to verify that the initial state, `Init`, satisfies the property `IndInv` (i.e. `--init=Init --inv=IndInv --length=0`). Then, to verify that for any state satisfying the property, any successor state (admissible under the specified next-state relation) must also satisfy the property, we do

```
$ apalache check --init=IndInv --inv=IndInv --length=1 MC_safety_5good_5bad.tla 
```

This will check that for any state satisfying the property (i.e. `--init=IndInv`), the successor state also satisfies the property (i.e. `--inv=IndInv --length=1`). Likewise, the expected output can be found in [`MC_safety_5good_5bad.out`](./apalache/5good_5bad/MC_safety_5good_5bad.out).

Once we have verified both of these claims, by the *principle of induction*, we have verified that `IndInv` is satisfied in all states of the model.

### Liveness

[`MC_liveness.cfg`](./MC_liveness.cfg) is the configuration used to verify all liveness properties and [`MC_liveness.tla`](./MC_liveness.tla) is the corresponding model file. The easiest way to verify the liveness properties is to run TLC on `MC_liveness.tla` by doing

```
tlc MC_liveness.tla -deadlock -workers 4096
```

See [`MC_liveness.out`](./MC_liveness.out) for expected output.

## Specification attributes

### Assumptions/Simplifications

- no communication with DNS
- there are good nodes and bad nodes
  - good nodes follow the protocol
  - bad nodes behave arbitrarily
- every node can communicate with every other node (arbitrary network topologies can be enforced easily)
- good nodes try to make connections whenever they can
- good nodes can only `nack` a `conn` message if they have >= `MIN` connections
- peers are not exchanged with `nack` messages
- no disconnection messages

### Communication model

There are *four* message types sent by good nodes:

- `conn`
- `meta`
- `ack`
- `nack`

The order in which good nodes send messages is enforced by the enabling conditions for the corresponding actions.

Additionally, bad nodes can send `bad` messages and any messages in any order. For this reason, and to reduce the size of the state space, messages sent to bad nodes are not kept in a message queue.

### Constants

- `BAD_NODES` - the set of byzantine node (ids) in the network
- `GOOD_NODES` - set of nodes which follow the protocol, bad nodes can act arbitrarily
- `MIN` - minimum number of connections
- `MAX` - maximum number of connections

### Variables

- `blacklist` - tuple of each node's blacklisted peers
- `connections` - tuple of each node's accepted connections
- `messages` - tuple of each node's incoming messages
- `recv_ack` - tuple of each node's peers who have sent an `ack` message
- `recv_conn` - tuple of each node's peers who have sent a `conn` message
- `recv_meta` - tuple of each node's peers who have sent a `meta` message
- `sent_ack` - tuple of each node's peers to whom they have sent an `ack` message
- `sent_conn` - tuple of each node's peers to whom they have sent a `conn` message
- `sent_meta` - tuple of each node's peers to whom they have sent a `meta` message
- `in_progress` - tuple of each node's peers with whom they are currently exchanging handshaking messages

## nack_peers

The final iteration can be found in [`nack_peers`](./nack_peers).
