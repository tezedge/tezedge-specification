# Bootstrapping algorithm

## Overview

The general idea for the bootstrapping algorithm is as follows:
- query every peer's current branch
- attempt to find a short sequence, call it a *segment*, of blocks which are supported by a quorum of peers with which to extend the node's chain
  - the segment starts at the block above the node's current head and ends at the latest, earliest peer block (see notes for step 3)
  - first, get all the headers in this sequence
  - then, get the operations only for the blocks with a quorum of support
- continue extending the node's chain by short segments until our current head has a timestamp within the threshold to be considered `Synced`
- the only caveat is that the node's header retention strategy may have to change once we've gotten within 8 cycles of our peer's current heads to hedge against reorgs

### General remarks

This algorithm is not optimized. We may be sending more (or less) messages than is actually necessary. The current focus is safety and correctness. Once this is achieved, we can shift our focus to performance. I don't claim to have even made all "obvious" optimizations in this doc.

All messages sent by the node should have a timer associated with them in order to have a clearly defined notion of when the node has not received a response. Not receiving a response, unfortunately, cannot always be penalized (see [more notes](./bootstrapping_algorithm.md#handling-timeouts)). However, receiving a valid response to a request should always increase the peer's score, if not already at the max value (here, valid simply means the response has the correct type and if we requested a header or operation, it has the expected hash, it isn't a duplicate, etc).

*Quorum* always means > 2/3 of the node's current peers

### Initial conditions

The node begins the bootstrapping process with:
- a current head (block), either genesis or a block provided by a snapshot
- a set of connections/peers
- an `Unsynced` synchronization status
- all peers with maximum `peer_score`
- all peers having the genesis block as their current head
- a global `earliest_hashes` variable instantiated by an empty set
- a global `pending_headers` variable instantiated by an empty map
- a global `pending_operations` variable instantiated by an empty map

The `earliest_hashes` variable is used as a kind of temporary target to meet before applying blocks. This variable has a type like:

```rust
pub type Hashes = HashSet<BlockHashes>
```

The `pending_headers` and `pending_operations` variables are used to temporarily aggregate (the short segments mentioned above) headers and corresponding operations, respectively.

`pending_headers` has a type like:

```rust
pub type PendingHeaders = HashMap<BlockLevel, HashSet<HeaderData>>
```

where

```rust
pub struct HeaderData {
  header : Header,
  hash : BlockHash,
  supporters : HashSet<PeerId>
}
```

and `pending_operations` has a type like:

```rust
pub type PendingOperations = HashMap<Level, HashSet<Vec<Operation>>>
```

(these types are *not* meant to be taken literally, just to give an idea)

### Steps

1. Request `GetCurrentBranch` from each peer
  - if the peer has already advertised its current branch, we don't need to request it
2. For each received `CurrentBranchMessage` (see [notes](./bootstrapping_algorithm.md#notes-on-algorithm-steps)):
  - determine the *earliest* (lowest level) hash above the node's current head and add this hash to a global, mutable set `earliest_hashes`
  - validate all hashes that correspond to a block with level at or below the node's current head's level
    - disconnect from each peer which does not pass this validation step (their branch deviates from what the node takes as a given)
  - adjust the peer's current head if the supplied header has a higher level or fitness
    - this is all the node does when handling `CurrentHeadMessage`s while `Unsynced`
3. Request all headers corresponding to the hashes in `earliest_hashes` from each responsive peer by sending a `GetBlockHeaders` message
  - as the node receives more and more `CurrentBranchMessage`s, the collection of `earliest_hashes` grows
    - the node just uses whatever value it reads from `earliest_hashes` to make the list of headers it requests from each peer, initially
    - the node keeps track of which hashes have been requested from each peer and as we receive more earliest hashes, we make the corresponding block header requests from all peers whom we have not requested it
      - when new hashes are added to `earliest_hashes`, the node requests all these headers from the sender and the not-yet-requested ones from all other peers
    - ultimately, the node should request all received headers from each peer (well, not quite, see notes)
4. For each received `BlockHeaderMessage`:
  - check hash of received header was actually requested from this peer
    - if the header wasn't requested, then we should penalize the peer
  - add header data to `pending_headers` and update
    - this requires calculating implied support for any known (i.e. pending) ancestors and support from children (see [notes](./bootstrapping_algorithm.md#notes-on-algorithm-steps))
  - check if any headers have a quorum of support
    - if not, the node continues requesting and handling block headers
    - else, prune the `pending_headers`
      - for each level, if there is a header with a quorum of support, remove the rest at that level
        - if there is a quorum of support for a header, then all ancestors also have a quorum of support
      - any peer supporting a header other than the one with quorum support at any level should be penalized
  - if it's not the case that all remaining headers in `pending_headers` have quorum support, then the node continues requesting and handling headers as before
    - effectively, the node goes back to step 3
    - else, continue to step 5
5. The node requests all operations for each block with a header in `pending_headers` from any peer it still has a connection with
  - start with the operations for the earliest block and move to the latest, adding the operations to `pending_operations` upon receipt
  - once the node has all operations for the earliest block, they apply it
  - update current head accordingly
  - repeat for all remaining pending blocks
6. After applying all blocks in the segment, clear the `earliest_hashes`, `pending_headers`, and `pending_operations` variables
  - populate `earliest_hashes` with each peer's next earliest hash, if any exist
  - go back to requesting headers (step 3)

#### Notes on algorithm steps

1. These requests are made concurrently, order is irrelevant as long as the node makes a request to all peers
  - the node only needs to check if they already have a `CurrentBranchMessage` from the peer before sending a request
  - all messages carry a `chain_id` parameter, this spec assumes all messages are for the same `chain_id`
2. All `CurrentBranchMessage`s can be handled concurrently
  - the individual steps in 2. are performed sequentially for a given message/peer
  - [`CurrentBranchMessage`](https://github.com/tezedge/tezedge/blob/master/tezos/messages/src/p2p/encoding/current_branch.rs)s have two fields: `chain_id` and `current_branch`
    - `current_branch` has two fields: `current_head` and `history`
      - `current_head` is the header of the sender's current head
      - `history` is a vector of `BlockHash`es which are determined by `Step`s
        - these `Step`s are deterministically generated from a `Seed` which depends only on the `CryptoBoxPublicKeyHash`es of the sender and receiver
          - [Seed](https://github.com/tezedge/tezedge/blob/master/crypto/src/seeded_step.rs#L15)
          - [Step](https://github.com/tezedge/tezedge/blob/master/crypto/src/seeded_step.rs#L35-L89)
          - [CryptoBoxPublicKeyHash](https://github.com/tezedge/tezedge/blob/master/crypto/src/hash.rs#L176)
        - the `Step`s basically tell us the "distance" between blocks in the `history`
        - starting from the supplied head's level, we can successively subtract the `Step` values from this number to produce the levels of each of the hashes in the `history`
```rust
// for example
// since we want to reconstruct the levels of the hashes sent to us, we generate the seed the same way the peer did
// current_head refers to the header provided by the peer in the CurrentBranchMessage
// hist_len is the length of the history vector
fn reconstruct_history_levels(node_id: &CryptoBoxPublicKeyHash, peer_id: &CryptoBoxPublicKeyHash, current_head: &BlockHeader, hist_len: i32) -> Vec<Level> {
    // peer is the sender, node is the receiver
    let seed = Seed::new(peer_id, node_id);
    let mut step = Step::init(&seed, current_head.message_hash()?.try_into()?.as_ref()); // we want a ref to the hash of current_head
    let mut l = current_head.level;
    let mut ls: Vec<Level> = Vec::new();
    let mut i: i32 = 0;
    // compute a vector of all the levels corresponding to the hashes in history
    while (i < hist_len) {
        step.next();
        ls.push(l - step);
        l -= step;
        i += 1;
    }
    ls
}
```
  - whether `earliest_hashes` is implemented as a set or list without duplicates is irrelevant
  - obviously, we will need to have a locking mechanism for `earliest_hashes` since it will be read and written to by several threads
  - the node disregards the mempool portion of `CurrentHeadMessage`s while `Unsynced`
3. The order in which the node requests block headers from the responsive peers (those who have sent a `CurrentBranchMessage`) is not important as long as the node eventually sees a quorum of support for some of the requested block headers
  - these initial requests can be made concurrently
  - upon handling a `CurrentBranchMessage`, the node can immediately add the earliest hash from that peer to `earliest_hashes`
  - the later requests can also be made concurrently
    - it probably makes the most sense to have one worker per peer/connection which runs every so often, checks for new earliest hashes, and makes the corresponding requests
    - the frequency at which this worker performs these tasks should be proportional to the peer's score
  - we only need to request all earliest hashes from each peer if we don't have sufficient support for a single branch prior to this point
    - the goal here is to find a quorum of peers supporting one segment
      - the segment being from the block above the node's current head to the latest, earliest block
      - it is probably confusing to read a phase like "latest, earliest block"... all we mean here, is the latest (highest level) out of the earliest blocks
4. The node can handle `BlockHeaderMessage`s concurrently
  - a penalty can either be a decrease to the peer's score or {grey, black}listing them
  - updating support for a header:
    - `pending_headers` is really a directed acyclic graph and in general, it is not connected
    - [daggy](https://github.com/mitchmindtree/daggy) may be useful in implementing this
      - it's not necessarily connected because headers can arrive in any order
      - edges are directed from higher-level (child) to lower-level (parent) headers
      - edges only exist between a parent and a child
    - for example, if a peer `p` sends the node a header `hd`, they support this header explicitly
      - if `hd` has already been included in `pending_headers`, we add `p` to the set of supporters
      - else, we add `hd` to `pending_headers` with `p` as the only supporter
      - now update the support for all headers in `pending_headers`:
        - starting at the tip (header with no child) of each branch, traverse the branch down to the base (header with no parent)
        - the supporters of the tip is unchanged
        - for each non-tip header in the branch, add the child's supporters to its set of of supporters
  - at the moment, headers can only be requested by `GetBlockHeadersMessage`
    - once Octez supports `GetPredecessorHeaderMessage`s, the header acquisition process can be sped up
      - this will enable us to request blocks based on level instead of hashes
5. The operation requests should be spread out among as many reliable peers as possible to parallelize the task
  - we do not need redundancy here since we've already established consensus on the headers in the segment and we can check hashes to verify the operations

## More notes and questions

### Requesting blocks headers

Is it worse to request too many or too few?

The above algorithm says to request all of the `earliest_hashes` for each peer. This may lead to getting a lot of duplicate responses from different peers.

The other obvious way to go with this is to only request the `earliest_hash` that the peer provided. This may lead to not getting enough responses and require us to make several requests after waiting for and processes responses.

### Handling disconnects

- we want to stay within a specified range of connections, between `min` and `max`
- we may need to implement a mutable `reconnection_counter` and choose a threshold `t`
  - when disconnected from a peer unexpectedly,  and if less than threshold, attempt to reconnect again
    - increment the counter: `reconnection_counter += 1`
    - if `reconnection_threshold < t` then attempt to connect with the peer again
    - else blacklist or ban peer
  - `reconnection_counter` should take a very long time to reset, on the order of a day or week (not sure what timescale makes the most sense)
- we may also need to set a threshold `tt` (dependent on `max`, e.g. `tt ~ 0.1 * max`) such that when the number of our connections becomes less than `max - tt`, the node prioritizes establishing connections over requesting header and operation data
  - we should first try to connect with peers we already know, but have been disconnected from
  - then we should try to request peers from our highest scoring peers via `SwapRequest`

### Handling timeouts

Each message has an associated timer:
- No response to `GetCurrentBranchMessage`
  - decrease `peer_score`
  - if `peer_score > 0` then request again
  - else disconnect from this peer
- We can't penalize a peer for not responding to header or operation requests in the same way
  - Octez node doesn't respond when a peer requests a block or operation hash it doesn't know about
    - [implementation](https://gitlab.com/tezos/tezos/-/blob/master/src/lib_shell/p2p_reader.ml#L250-262)
    - I'm not convinced this is a good thing...
  - we may need to use a request counter for each requested hash for each peer instead
    - each time we send a `GetBlockHeadersMessage` or `GetOperationsMessage` to a peer, we increment the counters for each requested hash
      - if we don't receive response in the allotted time, increment the counter(s) and request hash(es) again
      - if we receive a response to one of these hashes, we can remove it from the collection
      - once the counter gets to a certain threshold, we can move the corresponding hash to a collection of "do not ask" hashes we no longer request from this peer
      - ask another high-scoring peer for the hash and repeat this process until a peer responds or the hash is moved to a quorum of peers' "do not ask" collections
        - it may make sense to penalize the peer who gave us this hash at this point
  - unexpected responses are still penalized
  - expected responses still increase the peer's score

### Reorgs

In the case of a reorg, we want to minimize the number of blocks which the node needs to download from peers at that time. There are at least two strategies we can employ to deal with reorgs:

1. the node keeps all blocks (headers + operations) from the latest 8 cycles (or whatever the correct number is) in a cached structure similar to `pending_headers`
  - with this strategy, in the event of a reorg, once the node discovers the new main branch, they can apply the corresponding blocks starting from the correct context
  - the trade-offs being:
    - pro: we don't have to apply *all* blocks we receive and maintain several active branches; we only apply the necessary blocks
    - con: once we learn about a reorg, there will be a delay while we apply the necessary blocks to our context before we are caught up
2. the node not only keeps all blocks from the last 8 cycles, but also applies them as they're accumulated and manages several separate branches
  - with this strategy, in the event of a reorg, once the node discovers the new main branch, they can immediately switch to that branch
  - the trade-offs being:
    - pro: we can immediately switch to the new min branch with no delay
    - con: we may end up applying many unnecessary blocks during the course of maintaining the branches

#### Questions

How many blocks/cycles do we realistically need to keep as a hedge against reorgs?

Can we leverage a similar quorum support idea here as well?
- we may be able to set a threshold of support needed to maintain a branch
- for example, if we've seen blocks at all levels from, say, 70% of our peers and there is only, say, 10% support for a particular branch, is it safe to stop maintaining that branch?
