# model-p2p

Various models for different aspects of the Tezos p2p overlay network.

## counter

This project contains a model of the counter used for I/O resource management (see [Moving_average](https://gitlab.com/Isaac-DeFrain/tezos/-/blob/master/src/lib_stdlib_unix/moving_average.ml))

## distributed_db

This is where the bulk of current work is happening. Please see this project's readme for more information.

## high_level

This project contains a high-level model of the handshaking and bootstrapping processes.

## scheduler

This project contains a model for the fair I/O scheduler (see [P2p_io_scheduler](https://gitlab.com/Isaac-DeFrain/tezos/-/blob/master/src/lib_p2p/p2p_io_scheduler.ml))

## scheduler_rw

This project contains a model for a simple read (or write) scheduler. This model is instantiated in the scheduler project.

## utils

This project simply contains TLA+ functions and operators used extensively in the other projects.
