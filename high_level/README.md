# High Level Handshaking and Bootstrapping Model

## Assumptions/Simplifications
- handshaking goes off without a hitch
- no notion of different chains or protocols
- no blocks/ops
- no fairness in message passing, i.e. no scheduling/load balancing
- once peers are obtained, they do not change
- once nodes have a secure connection, they keep it forever
- once a joining node has sufficiently many secure connections, they do not gain or lose any
- bootstrapping nodes only request state from one established node at a time

## Handshaking process
This is process is intentionally straightforward in this model. All messages are passed atomically and can't be dropped.

## Bootstrapping process
Once a joining node has connected to sufficiently many peers (established nodes), they can begin bootstrapping. Once in the bootstrapping phase, a joining node can request the current state from any of their connections (established nodes). Joining nodes only communicate with established nodes and established nodes only communicate with joining nodes.

### Messages passed
- joining nodes send `Get_current_state`, `Ack_current_state` messages
- joining nodes expect `Current_state` messages in response to their `Get_current_state` messages

- established nodes send `Current_state` messages to joining nodes, either in response to a specific request (pull) or as an advertisement (push)
- established nodes expect `Ack_current_state` messages in response to their non-advertisement `Current_state` messages

## Each node has 2 sets and a queue for message passing
- `sent`: set of messages sent to the given node (size is bounded)
- `expect`: set of expected responses to sent messages (size is bounded)
- `recv`: queue of messages the node has received (size is bounded)

When a message is sent by a node, the expected response is stored in their expect set. When a node receives a message, they check their expect set for the corresponding entry to delete.
