# Tenderbake

Tenderbake is an instance of a general solution to the *dynamic repeated consensus* problem for blockchains. The system model is taken to be partially synchronous with byzantine failures.

In this environment, committees responsible for deciding values at different levels can change, hence *dynamic*, and we want to be able to continue choosing committee members and coming to consensus on a value at each level, hence *repeated consensus*.

The committee for a given level is chosen based only on the value decided at the previous level. COmmittee members are called *bakers*.

## Quourm certificates

In a setting with byzantine failures, when we speak of quorums, we will always mean a *byzantine quorum*, i.e. if a committee has `n` members, of which `f` are faulty, and `n >= 3f + 1`, then `2f + 1` members constitute a quorum. In this way, any two quorums necessarily share at least one correct baker.

A *preendorsement quorum certificate* (QC) is a set of legitimate committee members who have preendorsed the same *value* to be added on top of the same *block*, in the same *round*, at the same *level*.

An *endorsement quorum certificate* (QC) is a set of legitimate committee members who have endorsed the same *value* to be added on top of the same *block*, in the same *round*, at the same *level*.

In the spec, we represent QCs as a 5-tuple: `<<level, round, predecessor hash, value, set of committee members>>`

## Rounds

In general, there are arbitrarily many rounds at each level with increasing durations to facilitate message delivery and ultimately, decision making. In the asynchronous period before GST, there is no guarantee on message delivery or transmission delays. Once we are past the GST, it is assumed that we have loosely synchronized clocks and not too delayed message transmissions. Then we will be able to decide a value within `f + 2` rounds.

Each round has one proposer who is the only process which can propose a value in that round's `PROPOSE` phase.

## Phases

Each round consists of *three* phases:

- `PROPOSE` phase
  - a value is proposed by the round's designated proposer
  - `Propose` messages are broadcast to active committee members, including self
  - non-proposing bakers wait for a proposal message

- `PREENDORSE` phase
  - if a baker is not locked on a value or is locked on a value from a previous round, they preendorse the current (valid) proposal
  - `Preendorse` messages are broadcast to committee members, including self, to signal this intention
  - if a baker is locked on a value at a higher round or locked and the proposal is newly generated (`eR = 0` and `pQC = {}`), they do not preendorse the proposal
  - `Preendorsements` messages containing the corresponding preendorsement quorum certificate are broadcast to the committee members

- `ENDORSE`
  - if a baker has a preendorsement quorum for a value `v`, they endorse `v`
  - `Endorse` messages are broadcast to committee members along with the pQC justifying the endorsement
  - if a baker has an endorsement quorum for value `v`, they decide `v`

## Messages

There is a message type and corresponding payload for each phase. The message types and corresponding payloads are:

| Type | Payload |
|------|---------|
| Propose         | 4-tuple of endorsement quorum certificate, endorsable value, endorsable round, and preendorsement quorum certificate |
| Preendorse      | value |
| Preendorsements | preendorsement quorum certificate |
| Endorse         | endorsed value |
