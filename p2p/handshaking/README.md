# Handshaking

This directory contains a few iterations of the handshaking spec. The final iteration can be found in [`./blacklist_timeouts/nack_peers`](./blacklist_timeouts/nack_peers).

*Handshaking* is the mechanism through which nodes establish a secure communication channel with each other.

[Handshaking.tla](./Handshaking.tla) is the first iteration of the handshaking spec. It features a bounded amount of connection attempts and timeouts between any two nodes. After this limit is reached, those actions are disabled.

## Specification assumptions/simplifications

- no communication with DNS
- metadata is not exchanged
- every node can communicate with every other node (arbitrary network topologies can be simulated easily)
- connections only close when `nack`ed, i.e. no disconnects
- nodes try to make connections whenever they can
- `conn_msg` can only be `nack`ed if both nodes have >= `MIN` connections or receiving node has >= `MAX`
- nodes can only timeout and attempt to connect to another node a bounded number of times

## Verifying the specification's properties

### Safety

`MC_safety.cfg` is the configuration used to verify all safety properties and `MC_safety.tla` is the corresponding model file. The easiest way to verify the safety properties is to run TLC on `MC_safety.tla` by doing

```
tlc MC_safety.tla -deadlock -workers <N>
```

where `<N>` is the number of workers used when computations can be parallelized. The `-deadlock` flag disables deadlock checking, we use this option because our desired states are technically deadlocked (all actions are disabled) states. See `MC_safety.out` for expected output.

### Liveness

`MC_liveness.cfg` is the configuration used to verify all liveness properties and `MC_liveness.tla` is the corresponding model file. The easiest way to verify the liveness properties is to run TLC on `MC_liveness.tla` by doing

```
tlc MC_liveness.tla -deadlock -workers 4096
```

See `MC_liveness.out` for expected output.

## [blacklist_timeouts](./blacklist_timeouts)

In the next iterations of the spec, we made the decision to take a very conservative approach to handling timeouts: any time a node `n` timeouts while communicating with another node `m`, `n` blacklists `m`. Blacklisting here, is equivalent to banning because once a node is blacklisted, there is no further communication between the two nodes.
