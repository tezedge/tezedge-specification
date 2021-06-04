# model-p2p

Various specifications and models for different aspects of the Tezos p2p overlay network and shell.

## counter

This project contains a specification and models of the counter used for I/O resource management (see [Moving_average](https://gitlab.com/Isaac-DeFrain/tezos/-/blob/master/src/lib_stdlib_unix/moving_average.ml))

## distributed_db

This project contains a specification and models of the shell's distributed database (see [Distributed_db](https://gitlab.com/tezos/tezos/-/blob/master/src/lib_shell/distributed_db.ml)). Please see this project's readme for more information.

## handshaking

This project contains a specification and models of the handshaking protocol (see [P2p_socket](https://gitlab.com/tezos/tezos/-/blob/master/src/lib_p2p/p2p_socket.ml)).

## high_level

This project contains a high-level specification and models of the handshaking and bootstrapping processes.

## scheduler

This project contains a specification and models for the fair I/O scheduler (see [P2p_io_scheduler](https://gitlab.com/Isaac-DeFrain/tezos/-/blob/master/src/lib_p2p/p2p_io_scheduler.ml))

## scheduler_rw

This project contains a specification and models for a simple read (or write) scheduler (see [P2p_io_scheduler](https://gitlab.com/Isaac-DeFrain/tezos/-/blob/master/src/lib_p2p/p2p_io_scheduler.ml)). This specification is instantiated in the scheduler specification.

## utils

This project contains TLA+ functions and operators used extensively in the other projects.
