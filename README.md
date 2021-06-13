# tezedge-specification

Various specifications and models for different aspects of the Tezedge node's p2p overlay network, shell, and consensus.

## Tools

### Apalache

[Apalache](https://github.com/informalsystems/apalache) is used extensively in this project to typecheck specifications and verify inductive (safety) invariants (see [Apalache docs](https://apalache.informal.systems/docs/apalache/index.html)). The easiest way to get and run Apalache is through [docker](https://apalache.informal.systems/docs/apalache/installation/docker.html):

Pull the `unstable` image:

```
docker pull apalache/mc:unstable
```

Set an alias for the `unstable` image (if you're using Linux or macOS):

```
$ alias apalache='docker run --rm -v $(pwd):/var/apalache apalache/mc:unstable'
```

Specific instructions to verify inductive invariants are provided in the corresponding spec's directory.

### TLA+ command line tool

[tla-bin](https://github.com/pmer/tla-bin)

### TLA+ VSCode extension

[vscode-tlaplus](https://github.com/alygin/vscode-tlaplus)

## Project navigation

There are three main objects of focus for our specifications corresponding to the three layers in Tezos: `p2p`, `shell`, and `consensus`

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
