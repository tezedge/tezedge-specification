---- MODULE ActionTranslator ----

EXTENDS Bootstrap

PeersDnsLookupInitAction(data) == UNCHANGED vars
PeersDnsLookupErrorAction(data) == UNCHANGED vars
PeersDnsLookupSuccessAction(data) == UNCHANGED vars
PeersDnsLookupCleanupAction(data) == UNCHANGED vars
PeersAddIncomingPeerAction(data) == UNCHANGED vars
PeersAddMultiAction(data) == UNCHANGED vars
PeersRemoveAction(data) == UNCHANGED vars
PeerConnectionIncomingAcceptAction(data) == UNCHANGED vars
PeerConnectionIncomingAcceptErrorAction(data) == UNCHANGED vars
PeerConnectionIncomingAcceptSuccessAction(data) == UNCHANGED vars
PeerConnectionIncomingSuccessAction(data) == UNCHANGED vars
PeerConnectionOutgoingRandomInitAction(data) == UNCHANGED vars
PeerConnectionOutgoingInitAction(data) == UNCHANGED vars
PeerConnectionOutgoingPendingAction(data) == UNCHANGED vars
PeerConnectionOutgoingErrorAction(data) == UNCHANGED vars
PeerConnectionOutgoingSuccessAction(data) == UNCHANGED vars
PeerDisconnectAction(data) == UNCHANGED vars
PeerDisconnectedAction(data) == UNCHANGED vars
P2pServerEventAction(data) == UNCHANGED vars
P2pPeerEventAction(data) == UNCHANGED vars
WakeupEventAction(data) == UNCHANGED vars
PeerTryWriteAction(data) == UNCHANGED vars
PeerTryReadAction(data) == UNCHANGED vars
PeerChunkReadInitAction(data) == UNCHANGED vars
PeerChunkReadPartAction(data) == UNCHANGED vars
PeerChunkReadDecryptAction(data) == UNCHANGED vars
PeerChunkReadReadyAction(data) == UNCHANGED vars
PeerChunkReadErrorAction(data) == UNCHANGED vars
PeerChunkWriteSetContentAction(data) == UNCHANGED vars
PeerChunkWriteEncryptContentAction(data) == UNCHANGED vars
PeerChunkWriteCreateChunkAction(data) == UNCHANGED vars
PeerChunkWritePartAction(data) == UNCHANGED vars
PeerChunkWriteReadyAction(data) == UNCHANGED vars
PeerChunkWriteErrorAction(data) == UNCHANGED vars
PeerBinaryMessageReadInitAction(data) == UNCHANGED vars
PeerBinaryMessageReadChunkReadyAction(data) == UNCHANGED vars
PeerBinaryMessageReadSizeReadyAction(data) == UNCHANGED vars
PeerBinaryMessageReadReadyAction(data) == UNCHANGED vars
PeerBinaryMessageReadErrorAction(data) == UNCHANGED vars
PeerBinaryMessageWriteSetContentAction(data) == UNCHANGED vars
PeerBinaryMessageWriteNextChunkAction(data) == UNCHANGED vars
PeerBinaryMessageWriteReadyAction(data) == UNCHANGED vars
PeerBinaryMessageWriteErrorAction(data) == UNCHANGED vars
PeerHandshakingInitAction(data) == UNCHANGED vars
PeerHandshakingConnectionMessageInitAction(data) == UNCHANGED vars
PeerHandshakingConnectionMessageEncodeAction(data) == UNCHANGED vars
PeerHandshakingConnectionMessageWriteAction(data) == UNCHANGED vars
PeerHandshakingConnectionMessageReadAction(data) == UNCHANGED vars
PeerHandshakingConnectionMessageDecodeAction(data) == UNCHANGED vars
PeerHandshakingEncryptionInitAction(data) == UNCHANGED vars
PeerHandshakingMetadataMessageInitAction(data) == UNCHANGED vars
PeerHandshakingMetadataMessageEncodeAction(data) == UNCHANGED vars
PeerHandshakingMetadataMessageWriteAction(data) == UNCHANGED vars
PeerHandshakingMetadataMessageReadAction(data) == UNCHANGED vars
PeerHandshakingMetadataMessageDecodeAction(data) == UNCHANGED vars
PeerHandshakingAckMessageInitAction(data) == UNCHANGED vars
PeerHandshakingAckMessageEncodeAction(data) == UNCHANGED vars
PeerHandshakingAckMessageWriteAction(data) == UNCHANGED vars
PeerHandshakingAckMessageReadAction(data) == UNCHANGED vars
PeerHandshakingAckMessageDecodeAction(data) == UNCHANGED vars
PeerHandshakingErrorAction(data) == UNCHANGED vars
PeerHandshakingFinishAction(data) == UNCHANGED vars
StorageBlockHeadersPutAction(data) == UNCHANGED vars
StorageBlockHeaderPutNextInitAction(data) == UNCHANGED vars
StorageBlockHeaderPutNextPendingAction(data) == UNCHANGED vars
StorageStateSnapshotCreateAction(data) == UNCHANGED vars
StorageRequestCreateAction(data) == UNCHANGED vars
StorageRequestInitAction(data) == UNCHANGED vars
StorageRequestPendingAction(data) == UNCHANGED vars
StorageRequestErrorAction(data) == UNCHANGED vars
StorageRequestSuccessAction(data) == UNCHANGED vars
StorageRequestFinishAction(data) == UNCHANGED vars

ActionTranslator(input) ==
    LET act  == input[1]
        data == input[2]
    IN
    CASE act = "PeersDnsLookupInit" -> PeersDnsLookupInitAction(data)
      [] act = "PeersDnsLookupError" -> PeersDnsLookupErrorAction(data)
      [] act = "PeersDnsLookupSuccess" -> PeersDnsLookupSuccessAction(data)
      [] act = "PeersDnsLookupCleanup" -> PeersDnsLookupCleanupAction(data)
      [] act = "PeersAddIncomingPeer" -> PeersAddIncomingPeerAction(data)
      [] act = "PeersAddMulti" -> PeersAddMultiAction(data)
      [] act = "PeersRemove" -> PeersRemoveAction(data)
      [] act = "PeerConnectionIncomingAccept" -> PeerConnectionIncomingAcceptAction(data)
      [] act = "PeerConnectionIncomingAcceptError" -> PeerConnectionIncomingAcceptErrorAction(data)
      [] act = "PeerConnectionIncomingAcceptSuccess" -> PeerConnectionIncomingAcceptSuccessAction(data)
      [] act = "PeerConnectionIncomingSuccess" -> PeerConnectionIncomingSuccessAction(data)
      [] act = "PeerConnectionOutgoingRandomInit" -> PeerConnectionOutgoingRandomInitAction(data)
      [] act = "PeerConnectionOutgoingInit" -> PeerConnectionOutgoingInitAction(data)
      [] act = "PeerConnectionOutgoingPending" -> PeerConnectionOutgoingPendingAction(data)
      [] act = "PeerConnectionOutgoingError" -> PeerConnectionOutgoingErrorAction(data)
      [] act = "PeerConnectionOutgoingSuccess" -> PeerConnectionOutgoingSuccessAction(data)
      [] act = "PeerDisconnect" -> PeerDisconnectAction(data)
      [] act = "PeerDisconnected" -> PeerDisconnectedAction(data)
      [] act = "P2pServerEvent" -> P2pServerEventAction(data)
      [] act = "P2pPeerEvent" -> P2pPeerEventAction(data)
      [] act = "WakeupEvent" -> WakeupEventAction(data)
      [] act = "PeerTryWrite" -> PeerTryWriteAction(data)
      [] act = "PeerTryRead" -> PeerTryReadAction(data)
      [] act = "PeerChunkReadInit" -> PeerChunkReadInitAction(data)
      [] act = "PeerChunkReadPart" -> PeerChunkReadPartAction(data)
      [] act = "PeerChunkReadDecrypt" -> PeerChunkReadDecryptAction(data)
      [] act = "PeerChunkReadReady" -> PeerChunkReadReadyAction(data)
      [] act = "PeerChunkReadError" -> PeerChunkReadErrorAction(data)
      [] act = "PeerChunkWriteSetContent" -> PeerChunkWriteSetContentAction(data)
      [] act = "PeerChunkWriteEncryptContent" -> PeerChunkWriteEncryptContentAction(data)
      [] act = "PeerChunkWriteCreateChunk" -> PeerChunkWriteCreateChunkAction(data)
      [] act = "PeerChunkWritePart" -> PeerChunkWritePartAction(data)
      [] act = "PeerChunkWriteReady" -> PeerChunkWriteReadyAction(data)
      [] act = "PeerChunkWriteError" -> PeerChunkWriteErrorAction(data)
      [] act = "PeerBinaryMessageReadInit" -> PeerBinaryMessageReadInitAction(data)
      [] act = "PeerBinaryMessageReadChunkReady" -> PeerBinaryMessageReadChunkReadyAction(data)
      [] act = "PeerBinaryMessageReadSizeReady" -> PeerBinaryMessageReadSizeReadyAction(data)
      [] act = "PeerBinaryMessageReadReady" -> PeerBinaryMessageReadReadyAction(data)
      [] act = "PeerBinaryMessageReadError" -> PeerBinaryMessageReadErrorAction(data)
      [] act = "PeerBinaryMessageWriteSetContent" -> PeerBinaryMessageWriteSetContentAction(data)
      [] act = "PeerBinaryMessageWriteNextChunk" -> PeerBinaryMessageWriteNextChunkAction(data)
      [] act = "PeerBinaryMessageWriteReady" -> PeerBinaryMessageWriteReadyAction(data)
      [] act = "PeerBinaryMessageWriteError" -> PeerBinaryMessageWriteErrorAction(data)
      [] act = "PeerHandshakingInit" -> PeerHandshakingInitAction(data)
      [] act = "PeerHandshakingConnectionMessageInit" -> PeerHandshakingConnectionMessageInitAction(data)
      [] act = "PeerHandshakingConnectionMessageEncode" -> PeerHandshakingConnectionMessageEncodeAction(data)
      [] act = "PeerHandshakingConnectionMessageWrite" -> PeerHandshakingConnectionMessageWriteAction(data)
      [] act = "PeerHandshakingConnectionMessageRead" -> PeerHandshakingConnectionMessageReadAction(data)
      [] act = "PeerHandshakingConnectionMessageDecode" -> PeerHandshakingConnectionMessageDecodeAction(data)
      [] act = "PeerHandshakingEncryptionInit" -> PeerHandshakingEncryptionInitAction(data)
      [] act = "PeerHandshakingMetadataMessageInit" -> PeerHandshakingMetadataMessageInitAction(data)
      [] act = "PeerHandshakingMetadataMessageEncode" -> PeerHandshakingMetadataMessageEncodeAction(data)
      [] act = "PeerHandshakingMetadataMessageWrite" -> PeerHandshakingMetadataMessageWriteAction(data)
      [] act = "PeerHandshakingMetadataMessageRead" -> PeerHandshakingMetadataMessageReadAction(data)
      [] act = "PeerHandshakingMetadataMessageDecode" -> PeerHandshakingMetadataMessageDecodeAction(data)
      [] act = "PeerHandshakingAckMessageInit" -> PeerHandshakingAckMessageInitAction(data)
      [] act = "PeerHandshakingAckMessageEncode" -> PeerHandshakingAckMessageEncodeAction(data)
      [] act = "PeerHandshakingAckMessageWrite" -> PeerHandshakingAckMessageWriteAction(data)
      [] act = "PeerHandshakingAckMessageRead" -> PeerHandshakingAckMessageReadAction(data)
      [] act = "PeerHandshakingAckMessageDecode" -> PeerHandshakingAckMessageDecodeAction(data)
      [] act = "PeerHandshakingError" -> PeerHandshakingErrorAction(data)
      [] act = "PeerHandshakingFinish" -> PeerHandshakingFinishAction(data)
      [] act = "StorageBlockHeadersPut" -> StorageBlockHeadersPutAction(data)
      [] act = "StorageBlockHeaderPutNextInit" -> StorageBlockHeaderPutNextInitAction(data)
      [] act = "StorageBlockHeaderPutNextPending" -> StorageBlockHeaderPutNextPendingAction(data)
      [] act = "StorageStateSnapshotCreate" -> StorageStateSnapshotCreateAction(data)
      [] act = "StorageRequestCreate" -> StorageRequestCreateAction(data)
      [] act = "StorageRequestInit" -> StorageRequestInitAction(data)
      [] act = "StorageRequestPending" -> StorageRequestPendingAction(data)
      [] act = "StorageRequestError" -> StorageRequestErrorAction(data)
      [] act = "StorageRequestSuccess" -> StorageRequestSuccessAction(data)
      [] act = "StorageRequestFinish" -> StorageRequestFinishAction(data)

====
