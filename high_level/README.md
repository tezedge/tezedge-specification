# High Level Handshaking and Bootstrapping Model

## Assumptions/Simplifications

- no notion of different chains or protocols
- no blocks/headers/operations, just abstract states
- no explicit scheduling for message passing
- once peers are obtained, they do not change
- fixed set of nodes, i.e. nodes do not activate/deactivate
- once nodes have a secure connection, they keep it forever
- once a joining node has sufficiently many secure connections, they do not gain or lose any
- bootstrapping nodes only request state from one established node at a time
- no advertisement of states

## Requesting Peers

Joining nodes request peers atomically. They get a set of peers all at once.

## Handshaking process

Secure connections between joining nodes and established nodes are made one by one.

## Bootstrapping process

Once a joining node has connected to sufficiently many peers (established nodes), they can begin bootstrapping. Once in the bootstrapping phase, a joining node requests the current state from any of their connections (established nodes). Joining nodes only communicate with established nodes and established nodes only communicate with joining nodes.

### Messages

- joining nodes only send `Get_current_state` and `Ack_current_state` messages to established nodes
- established nodes only send `Current_state` messages in response to a `Get_current_state` message from a joining node

Each node has 3 queues for message passing:

- `mailbox`: queue of messages sent to the given node
- `sent`: queue of messages sent by the given node
- `recv`: queue of messages the node has received (these messages are "consumed" and responded to accordingly by the `Handle` action)

The lengths of these queues are all bounded by the constant `sizeBound`.
