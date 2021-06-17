# Handshaking (nack_peers)

[Handshaking_nack_peers.tla](./Handshaking_nack_peers.tla) is the final iteration of the handshaking spec. This specification contains all of the features of the previous iteration, [`blacklist_timeouts`](../), with the addition of communication with the DNS (i.e. not all nodes can communicate with one another), disconnect messages, and the inclusion of a set of peers in `nack` messages.

## Specification assumptions/simplifications

- there are good nodes and bad nodes
  - good nodes follow the protocol
  - bad nodes behave arbitrarily
- every node can communicate with every other node (arbitrary network topologies can be enforced easily)
- good nodes try to make connections whenever they can
- good nodes can only `nack` a `conn` message if they have >= `MIN` connections
- since disconnections are allowed, nodes may repeatedly connect and disconnect from one another
  - stronger fairness conditions are enforced to satisfy liveness properties

## Verifying the specification's properties

### Safety

To verify the spec's safety properties for a model with 1 bad node and 2 good nodes, one can invoke TLC via

```
$ tlc MC_safety.tla deadlock -worker 4096
```

The expected output can be found in [`MC_safety.out`](./MC_safety.out).

Alternatively, to verify the safety properties for larger models (e.g. 1 bad node and 4 good nodes), one can verify that the conjunction of all safety properties, `IndInv`, consitutes an inductive invariant by using Apalache. To do this, go to the [`apalache`](./apalache) directory and choose any of the supplied configurations. Within your directory of choice (e.g. [`4good_1bad`](./apalache/4good_1bad)), use the command

```
$ apalache check --init=Init --inv=IndInv --length=0 MC_safety_4good_1bad.tla 
```

to verify that the initial state, [`Init`](./Handshaking_nack_peers.tla#L348), satisfies the property [`IndInv`](./Handshaking_nack_peers.tla#L455) (i.e. `--init=Init --inv=IndInv --length=0`). Then, to verify that for any state satisfying the property, any successor state must also satisfy the property, we do

```
$ apalache check --init=IndInv --inv=IndInv --length=1 MC_safety_4good_ bad.tla 
```

This will check that for any state satisfying the property (i.e. `--init=IndInv`), the successor state also satisfies the property (i.e. `--inv=IndInv --length=1`). Likewise, the expected output can be found in [`MC_safety_4good_1bad.out`](./apalache/4good_1bad/MC_safety_4good_1bad.out).

Once we have verified both of these claims, by the *principle of induction*, we have verified that `IndInv` is satisfied in all states of the model.

### Liveness

Apalache does not have the capability to check liveness properties yet, so we use TLC for this task. Consequently, we can only reasonably verify liveness for small models. Thus, [`MC_liveness.tla`](./MC_liveness.tla) is a model file with 1 bad node and 2 good nodes and [`MC_liveness.cfg`](./MC_liveness.cfg) is the corresponding model configuration.

To verify the liveness properties for this model, from this directory, we execute the command

```
tlc MC_liveness.tla -workers 4096 -deadlock
```

The expected output can be found in [`MC_liveness.out`](./MC_liveness.out).

The main issue we encounter while verifying liveness for larger models is an exhaustion of disk space. One can experiment with passing the `-gzip` flag to `tlc` to improve this situation. We have not pushed this methodology to its logical conclusion yet.
