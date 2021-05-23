# bootstrapping

The main specification is in [`Bootstrap_pipeline.tla`](./Bootstrap_pipeline.tla)

## Assumptions/Simplifications

- all messages are for the same `chain_id`
- all headers are for the same `proto_level`
- no `timestamp`s
- only three message types:
  - `Get_current_branch`/`Current_branch`
  - `Get_block_headers`/`Block_header`
  - `Get_operations`/`Operation`
  - i.e. no `Current_head` or mempool
- bootstrapping nodes have the ability to request a specific history sample, by levels
- bootstrapping nodes only communicate with established nodes
- node's are blacklisted when we timeout while communicating with them
- lengths of all chains are bounded by `MAX_LEVEL`
- number of operations per block is bounded by `MAX_OPS`

## Bootstrapping node phases

## Block structure

```
block = {
  header : Headers,
  ops    : Seq(Operations)
}
```

### Header structure

```
header = {
  level       : Levels,
  predecessor : BlockHashes,
  context     : Hashes,
  fitness     : 0..Max_fitness,
  ops_hash    : Hashes
}
```

### Operations structure

```
ops = {
  block_hash : BlockHashes,
  op         : 0..MAX_OPS
}
```

## Constants

- `BAD_NODES` - byzantine nodes
- `GOOD_NODES` - nodes who follow the protocol
- `BAD_BOOTSTRAPPING` - byzantine bootstrapping nodes
- `GOOD_BOOTSTRAPPING` - bootstrapping nodes who follow the protocol
- `MIN_PEERS` - minimum number of peers
- `MAX_PEERS` - maximum number of peers
- `MAX_LEVEL` - maximum level of a block
- `MAX_OPS` - maximum number of operations per block
- `CURRENT_HEAD` - each good node's current head
- `BLOCKS` - each good node's blocks
- `VALIDATOR` - Blocks -> { "known_valid", "known_invalid", "unknown" }
- `SAMPLES` - GOOD_NODES * Bootstrapping_nodes -> Seq_n(Levels)
- `HASH_BLOCK_MAP` - BlockHashes -> Headers

## Variables

### Message and blacklist variables

- `b_blacklist` - each good bootstrapping node's set of blacklisted peers
- `b_messages` - each good bootstrapping node's set of messages
- `n_blacklist` - each good node's set of blacklisted peers
- `n_messages` - each good node's set of messages

### History variables

#### Bootstrapping

- `sent_get_branch` - each good bootstrapping node's set of peers to whom they have sent a Get_current_branch message
- `sent_get_headers` - each good bootstrapping node's function from peers to whom they have sent a Get_block_headers message to the requested headers
- `sent_get_ops` - each good bootstrapping node's function from peers to whom they have sent a Get_operations message to the requested operations
- `recv_branch` - each good bootstrapping node's set of peers from whom they have received a Current_branch message
- `recv_header` - each good bootstrapping node's function from peers from whom they have received a Block_header message to set of headers received
- `recv_ops` - each good bootstrapping node's function from peers from whom they have received a Operation message to set of operations received

#### Node

- `sent_branch` - each good node's set of peers to whom they have sent a Current_branch message
- `sent_headers` - each good node's function from peers to whom they have sent a Block_header message to the set of headers sent
- `sent_ops` - each good node's function from peers to whom they have sent a Operation message to the set of operations sent
- `recv_get_branch` - each good node's set of peers from whom they have received a Get_current_branch message
- `recv_get_headers` - each good node's set of peers from whom they have received a Get_block_headers message
- `recv_get_ops` - each good node's set of peers from whom they have received a Get_operations message

### Bootstrapping variables

- `phase` - each good bootstrapping node's phase
- `connections` - each good and bad bootstrapping node's set of connections
- `current_head` - each good bootstrapping node's current head
- `fittest_head` - each good bootstrapping node's peers' current heads
- `validated_blocks` - each good bootstrapping node's function from level to validated block at that level
- `level_to_validate` - each good bootstrapping node's lowest common level of fetched headers and operations
- `header_pipe` - each good bootstrapping node's queue of fetched headers
- `operation_pipe` - each good bootstrapping node's queue of fetched operations

### Node variables

- `servicing_headers` - each good node's function from peers from whom they have received a Get_block_headers message to the headers they requested
- `servicing_ops` - each good node's function from peers from whom they have received a Get_operations message to the operations they requested

## Actions

TODO
