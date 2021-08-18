# Handshaking

*Handshaking* is the mechanism by which nodes establish encrypted communication channels with one another (similar to TLS handshake). This is a particularly important protocol to formally verify because of the attack surface created by communicating with new and unknown peers.

Several assumptions/simplifictions are made in the spec and detailed [here](./README.md#specification-assumptions/simplifications)

## Running the code = verifying the specification's properties

There are two classes of properties which we are interested in verifying: *safety* and *liveness*. Roughly, safety properties say that nothing bad can happen and liveness properties say that something good must eventually happen.

In order to verify any properties of the spec, we must instantiate each parameter with a concrete value, this is called a *model* of the spec. Then, we must direct TLC as to which specification and model to use and which properties to check so it can properly orchestrate the verification process. This done by supplying a configuration file (this is done under the hood since we give the model and config files the same name).

It is common practice to create seperate models and configuration files for checking safety and liveness properties.

### Safety

To verify the spec's safety properties for a model with 1 bad node and 2 good nodes, one can invoke TLC via

```
$ tlc MC_safety.tla -deadlock -worker 4096
```

where `-deadlock` is an option telling TLC to not consider deadlock states as an error (in our spec, we are actually hoping to reach a deadlock state) and `-workers 4096` directs TLC to use up to `4096` threads to parallelize any tasks.

`MC_safety.tla` is the model file which declares the concrete values for all spec parameters. `MC_safety.cfg` is the corresponding configuration file which instantiates the parameters with the declared concrete values and tells TLC which properties (*INVARIANTS*) to check. The property names in the config file correspond to declarations in the spec (Handshaking.tla).

If no errors are found, then TLC has verified that all the invariants supplied in the config file are satisfied. The expected output can be found in [`MC_safety.out`](./MC_safety.out).

#### Checking safety with Apalache

Alternatively, to verify the safety properties for larger models (e.g. 1 bad node and 4 good nodes), one can verify that the conjunction of all safety properties, [`IndInv`](./apalache/4good_1bad/Handshaking.tla#L485) , consitutes an inductive invariant by using Apalache. To do this, go to the [`apalache`](./apalache) directory and choose any of the supplied configurations. Within your directory of choice (e.g. [`4good_1bad`](./apalache/4good_1bad)), we first use the command

```
$ apalache check --init=Init --inv=IndInv --length=0 MC_safety_4good_1bad.tla 
```

to verify that the initial state, [`Init`](./apalache/4good_1bad/Handshaking.tla#L392-L403), satisfies the property `IndInv` (i.e. `--init=Init --inv=IndInv --length=0`). Then, to verify that for any state satisfying the property, any successor state must also satisfy the property, we do

```
$ apalache check --init=IndInv --inv=IndInv --length=1 MC_safety_4good_ bad.tla 
```

This will check that for any state satisfying the property (i.e. `--init=IndInv`), the successor state also satisfies the property (i.e. `--inv=IndInv --length=1`). Likewise, the expected output can be found in [`MC_safety_4good_1bad.out`](./apalache/4good_1bad/MC_safety_4good_1bad.out).

Again, success is simply an absence of errors. Once we have verified both of these claims, by the *principle of induction*, we have verified that `IndInv` is satisfied in all states of the model.

### Liveness

Apalache does not have the capability to check liveness properties yet, so we use TLC for this task. Consequently, we can only reasonably verify liveness for small models. Thus, [`MC_liveness.tla`](./MC_liveness.tla) is a model file with 1 bad node and 2 good nodes and [`MC_liveness.cfg`](./MC_liveness.cfg) is the corresponding model configuration.

To verify the liveness properties for this model (i.e. the *PROPERTIES* in the config), from this directory, we execute the command

```
tlc MC_liveness.tla -deadlock -workers 4096
```

The expected output can be found in [`MC_liveness.out`](./MC_liveness.out).

The main issue we encounter while verifying liveness for larger models is an exhaustion of disk space. One can experiment with passing the `-gzip` flag to `tlc` to improve this situation, but this makes model checking take even longer. We have not pushed this methodology to its logical conclusion yet.

## Specification assumptions/simplifications

- nodes communicate with DNS for peers
- there are good nodes and bad nodes
  - good nodes follow the protocol
  - bad nodes behave arbitrarily
- every node can communicate with every other node (arbitrary network topologies can be enforced easily)
- good nodes try to make connections whenever they can
- good nodes can only `nack` a `conn` message if they have >= `MIN` connections
- disconnects are blacklisted
