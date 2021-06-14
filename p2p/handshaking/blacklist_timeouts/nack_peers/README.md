# Handshaking (nack_peers)

This is the final iteration of the handshaking spec. This specification contains all of the features of the previous iteration, `blacklist_timeouts`, with the addition of disconnect messages and the inclusion of a set of peers in `nack` messages.

## Verifying the specification's properties

### Safety

To verify the spec's safety properties for a model with 1 bad node and 2 good nodes, one can invoke TLC via

```
$ tlc MC_safety.tla deadlock -worker 4096
```

The expected output can be found in `MC_safety.out`.

Alternatively, to verify the safety properties for larger models (e.g. 1 bad node and 4 good nodes), one can verify that the conjunction of all safety properties, `IndInv`, consitutes an inductive invariant by using Apalache. To do this, go to the `apalache` directory and choose any of the supplied configurations. Within your directory of choice (e.g. `4good_1bad`), use the command

```
$ apalache check --init=Init --inv=IndInv --length=0 MC_safety_4good_1bad.tla 
```

to verify that the initial state, `Init`, satisfies the property `IndInv` (i.e. `--init=Init --inv=IndInv --length=0`). Then, to verify that for any state satisfying the property, any successor state must also satisfy the property, we do

```
$ apalache check --init=IndInv --inv=IndInv --length=1 MC_safety_4good_ bad.tla 
```

This will check that for any state satisfying the property (i.e. `--init=IndInv`), the successor state also satisfies the property (i.e. `--inv=IndInv --length=1`). Likewise, the expected output can be found in `MC_4good_1bad.out`.

Once we have verified both of these claims, by the *principle of induction*, we have verified that `IndInv` is satisfied in all states of the model.

### Liveness

Apalache does not have the capability to check liveness properties yet, so we use TLC for this task. Consequently, we can only reasonably verify liveness for small models. Thus, `MC-liveness.tla` is a model file with 1 bad node and 2 good nodes and `MC_liveness.cfg` is the corresponding model configuration.

To verify the liveness properties for this model, from this directory, we execute the command

```
tlc MC_liveness.tla -workers 4096 -deadlock
```

The expected output can be found in `MC_liveness.out`.

The main issue we encounter while verifying liveness for larger models is an exhaustion of disk space. One can experiment with passing the `-gzip` flag to `tlc` to improve this situation. We have not pushed this methodology to its logical conclusion yet.
