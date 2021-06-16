# tezedge-specification

This project contains various formal specifications and models for different aspects of the Tezedge node's p2p overlay network, shell, and consensus.

In the security-critical realm of blockchains, it is not enough to simply test our software. Since these systems contain sensitive financial information and business logic, we believe that it is absolutely necessary to formally verify the code we write.

Part of the formal verification process focuses on the design we intend to implement in our code. This is the realm of formal specification and model checking. TLA+, our formal specification language of choice, is well-known, widely used, and particularly well-suited to reasoning about concurrent and distributed algorithms.

Formal specification and model checking give us assurance and verification that our algorithms have the intended properties and no undesirable behavior. Formal specification is, of course, not a replacement for testing, but a necessary companion and counterpart. TLA+ gives one the ability to exhaustively check all possible behaviors of a system.

## The tools we use

### TLA+

[TLA+](https://lamport.azurewebsites.net/tla/tla.html) is our chosen specification language. It enables one to encode the specification of a state machine, as well as its safety and liveness properties, in the language of [temporal logic of actions](https://lamport.azurewebsites.net/pubs/lamport-actions.pdf). TLA+ comes with an explicit state model checker, [TLC](https://github.com/tlaplus/tlaplus), which exhaustively checks all behaviors of the specified state machine, verifies its properties, and provides counterexamples to violated properties.

The latest release of the TLA+ toolbox can be found [here](https://github.com/tlaplus/tlaplus/releases/tag/v1.7.1).

### Apalache

[Apalache](https://github.com/informalsystems/apalache) is a symbolic model checker for TLA+; Apalache translates TLA+ into the logic supported by SMT solvers such as Z3.

We use Apalache extensively in this project to typecheck specifications and verify inductive (safety) invariants (see [Apalache docs](https://apalache.informal.systems/docs/apalache/index.html)). The easiest way to get and run Apalache is with [docker](https://apalache.informal.systems/docs/apalache/installation/docker.html):

1. Pull the `unstable` image (one may use the `latest` image, but `unstable` provides more features)

```
$ docker pull apalache/mc:unstable
```

2. Set an alias for the `unstable` image (if you're using Linux or macOS)

```
$ alias apalache='docker run --rm -v $(pwd):/var/apalache apalache/mc:unstable'
```

3. Verify that the setup works

```
$ apalache version
```

Note that this command will generate a `detailed.log` file in the directory in which it is run.

Specific instructions to verify inductive invariants are provided in the corresponding spec's directory.

### TLA+ command line tool

The default way to write TLA+ specs and run the model checker (TLC) is through the (graphical) toolbox. However, for the ease of running TLC on a remote server, one may be interested in also getting the TLA+ command line tool [tla-bin](https://github.com/pmer/tla-bin).

### TLA+ VSCode extension

For those who prefer to work in VSCode, there is the extension [vscode-tlaplus](https://github.com/alygin/vscode-tlaplus) which is well-maintained and highly recommended.

## Project navigation

There are three main objects of focus for our specifications, corresponding to the three layers in Tezos: `p2p`, `shell`, and `consensus`

### p2p

This project contains specifications and models related to the p2p overlay network:

- hanshaking
- I/O resource management

### shell

This project contains specifications and models related to the shell:

- bootstrapping
- distributed_db

### consensus

This project contains specifications and models related to consensus:

- Emmy/Emmy+/Emmy★
- Tenderbake

### utils

This project contains TLA+ functions and operators used extensively in the other projects
