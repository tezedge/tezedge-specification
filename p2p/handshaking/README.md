# Handshaking

This directory contains a few iterations of the handshaking spec. The final iteration can be found in `./blacklist_timeouts/nack_peers`

[Handshaking.tla](./Handshaking.tla) is the first iteration of the handshaking spec. It features a bounded amount of connection attempts and timeouts between any two nodes. After this limit is reached, those actions are disabled.

## Verifying the specification's properties

### Safety

`MC_safety.cfg` is the configuration used to verify all safety properties and `MC_safety.tla` is the corresponding model file. The easiest way to verify the safety properties is to run TLC on `MC_safety.tla` by doing

```
tlc MC_safety.tla -deadlock -workers <N>
```

where `<N>` is the number of workers used when computations can be parallelized. See `MC_safety.out` for expected output.

### Liveness

`MC_liveness.cfg` is the configuration used to verify all liveness properties and `MC_liveness.tla` is the corresponding model file. The easiest way to verify the liveness properties is to run TLC on `MC_liveness.tla` by doing

```
tlc MC_liveness.tla -deadlock -workers 4096
```

See `MC_liveness.out` for expected output.

## blacklist_timeouts

In the next iterations of the spec, we made the decision to take a very conservative approach to handling timeouts: any time a node `n` timeouts while communicating with another node `m`, `n` blacklists `m`. Blacklisting here, is equivalent to banning because once a node is blacklisted, there is no further communication between the two nodes.
