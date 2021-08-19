# Bootstrapping (plain English) specification

> Note: this bootstrapping algorithm is safe under the assumption that less than 1/3 of peers are byzantine.

## Overview

This specification will describe the bootstrapping algorithm performed by a single node (referred to as "the node") via a *finite state automaton*. The states completely govern the behavior of the node at any given time, which messages they send, whether they are processing received messages, etc. There are several variables which contribute to the node's state. One very important variable being `phase` which we'll describe by the high-level activity of the node while in that phase:

1. `Search`
  - the node searches for the longest common prefix (*major branch*) by sending `Get_current_branch` and `Get_block_headers` messages to all (non-blacklisted) peers
  - the focus during this phase is on getting the latest block headers that peers know about to expedite the process of finding the major branch, the major branch coincides with the highest level common block (this is the head of the major branch)
  - at the end of this phase, the node will have knowledge of the major branch via possession of block hashes and headers, specifically the head of this branch, and have a set of core peers to request remaining data from
2. `Validation`
  - the node downloads all (remaining) headers via `Get_block_headers`and operations via `Get_operations` for the blocks in the major branch from a set of core peers
  - the node prevalidates received data by cross-checking header and operation hashes
  - the focus during this phase is on getting the earliest missing headers and operations (i.e. those closest to the node's current head) so that the node can concurrently apply these blocks while it requests the later data
  - at the end of this phase, the node will have downloaded all block headers and operations for the major branch
3. `Application`
  - enqueuing headers and operations and applying blocks
  - the node does not send or handle messages while in this phase
  - at the end of this phase, the node will have applied all blocks in the major branch to their chain

Essentially, a bootstrapping node will start from a snapshot (or from the genesis block) and begin in the `Search` state. Presumably, the node's current knowledge of the state is incomplete (this is why we are bootstrapping after all) so, this state, they send their peers `Get_current_branch` messages. Once responses (*locators*) are received, if the supplied block hashes are known to the node, nothing really needs to happen. If the supplied block hashes are unknown to the node, the node will compare with block hashes it has received from other peers and/or request the associated headers by sending `Get_block_headers` messages.

Once a branch is found to be shared by a quorum of peers (the notion of quorum can be 2/3, for example), the node will proceed to the `Validation` state, in which, they request all associated headers (`Get_block_headers`) and operations (`Get_operations`) for this branch. If no validation issues arise, the node will eventually acquire the requested headers and operations.

Once a contiguous batch of headers and operations can be applied to the node's current state (this quantity is a parameter which can be tuned), the node transitions to the `Application` state. The headers and operations are enqueued and the resulting blocks are applied to the node's state sequentially. If the node has more headers and operations to get/apply, the node transitions back to the `Validation` state. Otherwise, the node returns to the `Search` state, requesting its peers' current branches to see if progress has been made.

## In depth

The node's state is determined by the values of the node's local variables, `phase` being just one of them. The node maintains the following variables:

| Variable | Description |
|----------|-------------|
| `blacklist` | set of the node's blacklisted peers |
| `messages` | set of messages sent to the node (not yet received) |
| `phase` | high-level state of the node |
| `connections` | set of the node's peers/connections |
| `core_peers` | set of the node's peers who share the major branch |
| `peer_score` | the score of each of the node's peers |
| `current_head` | the node's current fittest header with majority support |
| `fittest_head` | function from peers to the fittest head's header the node has received from this peer |
| `header_pipe` | the node's queue of fetched headers |
| `operation_pipe` | the node's queue of fetched operations, batched per block |
| `validated_blocks` | function from level to the node's validated block at that level |
| `prevalidated_hds` | set of prevalidated headers |
| `prevalidated_ops` | set of prevalidated operations |
| `sent_get_branch` | set of peers to whom the node has sent a `Get_current_branch` message |
| `sent_get_headers` | function from peers to whom the node has sent a `Get_block_headers` message to the requested header hashes |
| `sent_get_ops` | function from peers to whom the node has sent a `Get_operations` message to the hash of the corresponding block |
| `recv_branch` | set of peers from whom the node has received a `Current_branch` message |
| `recv_header` | function from peers from whom the node has received a `Block_header` message to the set of (hash, header) pairs received |
| `recv_ops` | function from peers from whom the node has received a `Operation` message to set of operations received |

Note: All communications happen between the node and its *non-blacklisted* peers.

### Peer scores

*Peer scores* function as a metric of a peer's reliability w.r.t.
  - timeliness, and
  - data integrity

Each message the node sends has an accompanying timer (the allotted time should be tuned). If the node does not receive a valid/expected response within the given time, then the peer's score will be reduced by a specified amount `decr_amt` (this value will need to be tuned). On the other hand, if the node receives the response (once) within the allotted time, then the peer's score will be increased by a specified amount `incr_amt` (if possible, the score cannot exceed a maximum value `max_score`).

Regarding data integrity, if a peer sends data the node didn't request, the node blacklists the peer and temporarily stops communicating with them (again a timer is set, after this time elapses the peer can be removed from the blacklist set). If the peer, however, sends data requested by the node multiple times, either in the allotted time or not, the node will decrease that peer's score accordingly for each duplicate message.

We will use the following actions to adjust peer scores:

```
incr_score(peer) == peer_score' = [ peer_score EXCEPT ![peer] = min(@ + incr_amt, max_score) ]
decr_score(peer) == peer_score' = [ peer_score EXCEPT ![peer] = max(@ - decr_amt, 0) ]
```

Peer scores are used as a communication heuristic. During the `Validation` phase, specifically, the node will preferentially communicate with peers with the highest scores, allocating resources proportional to their relative scores. When the node is disconnected from a peer, any data the node requested from that peer will be requested from peers with the highest peer scores. If a peer's score goes to 0, the node immediately blacklists that peer.

Now we describe some useful data structures (in OCaml syntax).

### Blocks

Blocks are records with two fields:

```ocaml
type block = {
  header : header;
  ops : operation list
}
```

We have the `block` constructor function: `block(header, ops) = { header; ops }`.

Headers are records with five fields:

```ocaml
type header = {
  level : int;
  predecessor : block_hash;
  ops_hash : operation_hash list;
  fitness : int;
  context : context_hash
}
```

Operations are records with two fields:

```ocaml
type operation = {
  block_hash : block_hash;
  op : raw_operation
}
```

### Phases

We will describe the different phases and how the node's variables evolve over time. Essentially, one can think that we have an ADT to describe the phases:

```ocaml
type phase =
  | Search
  | Validation of int
  | Application
```

The `Validation` phase keeps track of the target level so the node knows when to transition to the `Application` phase.

### `Search`

> The node's goal in this phase is to find a branch (prefix) which is common among a quorum of their peers, i.e. the major branch.

The node starts the bootstrapping process in the `Search` phase with the `connections` they have obtained from handshaking or some other interaction with peers (e.g. via `Nack` or `Swap` messages). If bootstrapping from a snapshot, the node will have some corresponding latest block, this is the node's initial `current_head`. Explicitly, we assume this head is contained in the chains of a quorum of peers (any reasonable definition of *snapshot* should conform to this requirement). Otherwise, the genesis block serves this purpose.

Initially, the `core_peers` set is empty since the node does not know which peers have the correct data and each peer `n` has `peer_score[n] = max_score`.

As mentioned above, the node's goal in this phase is to find the major branch. Thus, the node will *focus on downloading the latest headers* from their peers, starting with the predecessor of each peer's current head and the latest hashes they provide in the locators.

#### Requesting current branches

To start getting a view of their peers' states, the node will issue a `Get_current_branch` request to each peer. This can be done all at once or one-by-one in any order. From the perspective of the node, only the `sent_get_branch` variable is mutated in this step

```
sent_get_branch' = sent_get_branch \cup ps
```

where `ps` is the set of peers to whom the node sends the request. This simply says that we add the node ids of the recipients to the set `sent_get_branch`.

#### Handling current branches

After some `Get_current_branch` messages have been sent, the node will start to receive `Current_branch` messages in response. `Current_branch` messages contain a *block locator* (a pair consisting of a block header (presumably, the current head of the sender) and a pseudorandom list of block hashes in sequential order (the seed for the randomness is generated from the ids of the sender and receiver)). The list of block hashes in a locator serves as a pseudorandom sample of the sender's chain which the receiver can use as a reference for request block headers and as a sanity check.

If the node requested a current branch from the sender `n`, then upon receiving the message `msg = Current_branch (hd, hist)` in the allotted time, the node makes the following adjustments to its variables:

```
incr_score(n)
messages' = messages \ {msg}
fittest_head' = [ fittest_head EXCEPT ![bn][n] =
    CASE curr_hd.level < @.level -> @
      [] curr_hd.level > @.level -> curr_hd
      [] curr_hd.fitness < @.fitness -> @
      [] curr_hd.fitness < @.fitness -> curr_hd ]
recv_header'  = [ recv_header  EXCEPT ![n] = @ \cup {hd} ]
recv_branch'  = [ recv_branch  EXCEPT ![n] = @ \cup ToSet(hist) ]
```

where `hd` is the block header and `hist` is the list of block hashes included in the locator. This says that the node changes `fittest_head[n]` to `hd` if `hd` is at a higher level or at the same level and the fitness of `hd` is strictly greater than the fitness of the header currently held in `fittest_head[n]` (if this is the first header received from `n` then the node includes it automatically). The node also removes `msg` from its set of `messages`, includes `hd` in `recv_header[n]`, and includes all hashes in `hist` in `recv_branch[n]`. Of course, if the node did not request this data from `n`, then `n` will be blacklisted. Also, if this is a duplicate response, the node decreases `n`'s score.

#### Requesting block headers

Once the node has received some current heads and block hash samples from peers, before they request any block headers, the node checks if it can determine the major branch. For example, if the node hasn't received messages from a quorum of peers, then there's no way they can make this determination yet. Also, if the node receives the same current head from a quorum of peers, for example, then they can immediately detect the major branch. In general, this decision is more subtle and will require the node to request some headers from their peers first.

As another example, if the node has received the same block hash or header from a quorum of peers, then the latest common head must lie above this block. An observation like this can guide the node's requests. So before arbitrarily making requests, the node should survey the data it has and decide if a better strategy can be employed.

If a decision about the major branch cannot be made yet, then the node requests the latest headers from their peers by sending `Get_block_headers bhs` messages to the peers from which they have received block hashes and who are not blacklisted (`bhs` is a set of block hashes). The node can request any block headers from any peer, but to minimize the amount of unfulfilled requests at first, the node requests headers that their peers should certainly have, e.g. the node requests the headers corresponding to the block hashes received from the peer. The node makes the following adjustments to its variables:

```
sent_get_headers' = [ sent_get_headers EXCEPT ![n] = @ \cup bhs ]
```

If the node can decide the major branch, then they transition to the `Validation` phase.

```
phase' = Validation l
```

where `l` is the level of the target head.

As long as peers respond to the node's block header requests, eventually the node will find a major branch and transition to the `Validation` phase.

#### Handling block headers

After sending some requests for block headers, the node will start to get `msg = Block_header bh` messages where `bh` is a block header. Any block header received from a peer `n` should correspond to a requested block hash. Prior to adjusting any variables, the node checks that `hash(bh) \in sent_get_headers[n]` and `bh` is not known to be invalid. If this check fails, the node blacklists `n`. If the check succeeds, the node then checks if `(hash(hd), hd) \in recv_header[n]`. If so or if the timer has expired for this request, the node does `decr_score(n)`. If not and the timer has not expired, the node makes the following adjustments to its variables:

```
incr_score(n)
messages' = messages \ {msg}
recv_header' = [ recv_header EXCEPT ![n] = @ \cup {(hash(hd), hd)} ]
recv_branch' = [ recv_branch EXCEPT ![n] = @ \cup {hash(hd)} ]
```

This says that the node has received the message, adds the pair `(hash(hd), hd)` to the set `recv_header[n]`, adds the hash of this block to `recv_branch[n]`, and increases `peer_score[n]`.

Once the node has discovered the major branch, necessarily a quorum of peers have knowledge of this branch's blocks. The node adds these peers to the set of `core_peers`.

Note: if locators also included the levels corresponding to their hashes and there was a mechanism to request only block hashes at specific levels, we could optimize this searching algorithm further by allowing the node to only handle block hashes instead of headers and expedite the discovery of of the major branch.

### `Validation`

> The node's goal in this phase is to download contiguous batches of the corresponding headers and operations for the blocks in the major branch.

We can run validation and application in parallel, contiguous batches (how many blocks should be included in each batch is a parameter that will need to be tuned). Thus, the focus of the node during this phase is to download the earliest blocks in the major branch that are not yet in its chain.

Once a major branch is found, the node requests the headers and operations for the blocks in this branch from its `core_peers`, starting with the earliest ones above its `current_head`. Since each member of `core_peers` presumably has all the blocks the node needs, the node can randomly choose core peers and request any of the headers or operations still needed. Of course, prioritizing the core peers with the highest scores. The most obvious place to start requesting data is from the earliest block hashes the particular core peer provided in the locator included in their `Current_branch` message.

#### Requesting block headers

Now that the major branch has been discovered, the node knows exactly which headers and operations (hashes) need to be downloaded and the peers that can serve those data reliably. The node will focus on these peers and attempt to only download each header and operation once. Of course, if the node times out while waiting for a response, then the node will adjust this peer's score accordingly and have to request this data again or from another peer (depending on the relative scores and what has already been requested). If the peer provides data that is invalid or was not requested, then the peer is blacklisted.

In the successful case, the node adjusts its variables as above.

#### Handling block headers

As the node receives headers for the blocks in the major branch, they will adjust their variables as above.

Once a `header` and the corresponding operations have been downloaded, the node can check that the operations are correct by verifying that the list of their hashes is equal to `header.ops_hash`. If this is the case, the node will move the header and the corresponding operations to their respective prevalidated sets:

```
prevalidated_hds' = prevalidated_hds \cup {header}
prevalidated_ops' = prevalidated_ops \cup {ops}
```

where `ops` is the list of operations for the block with header `header`.

Once the node has downloaded the earliest, contiguous batch of headers and operations in this branch and prevalidated them, they temporarily transition to the `Application` phase.

#### Requesting operations

As the node discovers the block hashes included in the major branch, they can immediately request the corresponding operations for that block by sending a `Get_operations bh` message to one of their peers (`bh` is the corresponding block hash). The node makes the following adjustments to its variables:

```
sent_get_ops' = [ sent_get_ops EXCEPT ![n] = @ \cup {bh} ]
```

where `n` is the id of the peer the request is sent to.

#### Handling operations

As before, when the node receives an operation response `msg = Operation op`, if this data was requested, then the node makes the following adjustments to its variables:

```
messages' = messages \ {msg}
recv_operation' = recv_operation[n] \cup {op}
```

i.e. the node receives `msg` and adds the `op` to the set of received operations from the sender.

Once all operations for a block have been received along with the header, the node attempts the to validate this data. If any inconsistencies are found, the node blacklists the peer who sent this data and requests it from another peer. Otherwise, the node moves these data to their respective prevalidated sets.

Once the node has downloaded the earliest batch of headers and operations for the blocks in this branch and prevalidated them, they can spawn an `Application` process. (There isn't a need to distinguish this process as a separate phase since application can be done in parallel with validation.)

### `Application`

> The node's goal in this phase is to apply a batch of blocks it has downloaded from its core peers to its local chain.

#### Enqueuing prevalidated headers and operations

In this process, the node has prevalidated a batch of headers and operations in the major branch which can be applied to their chain. The node will move all the headers and collections of operations to their respective pipes (queues) starting with the lowest level and proceeding to the highest level. While there are still elements in the prevalidated sets, the node adjusts its variables as follows:

```
prevalidated_hds' = prevalidated_hds \ {hd}
prevalidated_ops' = prevalidated_ops \ {ops}
header_pipe'      = push(hd, header_pipe)
operation_pipe'   = push(ops, operation_pipe)
```

where `hd` is the lowest level header left in `prevalidated_hds` and `ops` is the corresponding operation list.

#### Applying blocks

Once the batch of headers and operations has been validated and enqueued into their respective pipes (i.e. when `prevalidated_hds = {}` and `prevalidated_ops = {}`), the node can form each block and apply it to its local chain.

```
LET hd  == pop(header_pipe)    \* mutates header_pipe
    ops == pop(operation_pipe) \* mutates operation_pipe
IN
validated_blocks' = [ validated_blocks EXCEPT ![hd.level] = block(hd, ops) ]
```

In general, the node will spawn the `Application` process several times. Each time, applying all blocks in the batch in order.

Once all blocks have been applied to the node's local context up to the validation level, they are synced with the major branch. In terms of safety, this is the best we can hope to do.
