import tlc2.value.impl.*;
import util.UniqueString;

import java.io.*;
import java.util.*;

// import nodeActions.*;

/**
 * Parser class
 */
public class Parser {
  public static Value parse(final StringValue absolutePath) throws IOException {
    BufferedReader br = new BufferedReader(new FileReader(absolutePath.val.toString()));
    List<Value> values = new ArrayList<>();
    try {
      String line = br.readLine();
      while (line != null) {
        // split string on seperator
        String[] lnarr = line.split("> ");
        // [vals] will hold the tuple of values for each state
        List<Value> vals = new ArrayList<>();
        if (!NodeActions.allActions().contains(lnarr[0])) {
          throw new IllegalArgumentException(lnarr[0].concat(" is not a node action"));
        }
        if (lnarr.length == 1) {
          // Only an action name was read, no params
          vals.add(new StringValue(lnarr[0]));
          vals.add(dispatchDataParser(lnarr[0], new String[0]));
        } else {
          // Parameters were read
          vals.add(new StringValue(lnarr[0]));
          vals.add(dispatchDataParser(lnarr[0], lnarr[1].split(", ")));
        }
        values.add(new TupleValue(vals.toArray(new Value[0])));
        line = br.readLine();
      }
    } finally {
      br.close();
    }
    return new TupleValue(values.toArray(new Value[0]));
  }

  /**
   * Dispatch action data parser
   */
  private static Value dispatchDataParser(String action, String[] data) {
    List<Value> vals = new ArrayList<>();
    if (NodeActions.dnsActions().contains(action)) {
      vals = parseDnsData(action, data);
    } else if (NodeActions.peersActions().contains(action)) {
      vals = parsePeersData(action, data);
    } else if (NodeActions.peerIncomingActions().contains(action)) {
      vals = parsePeerIncomingData(action, data);
    } else if (NodeActions.peerOutgoingActions().contains(action)) {
      vals = parsePeerOutgoingData(action, data);
    } else if (NodeActions.peerDisconnectionActions().contains(action)) {
      vals = parseDisconnectionData(action, data);
    } else if (NodeActions.eventActions().contains(action)) {
      vals = parseEventData(action, data);
    } else if (NodeActions.readWriteActions().contains(action)) {
      vals = parseReadWriteData(action, data);
    } else if (NodeActions.connectionActions().contains(action)) {
      vals = parseConnectionData(action, data);
    } else if (NodeActions.storageActions().contains(action)) {
      vals = parseStorageData(action, data);
    }
    return new TupleValue(vals.toArray(new Value[0]));
  }

  /**
   * Dns data parsers
   */
  private static List<Value> parseDnsData(String action, String[] data) {
    List<Value> vals = new ArrayList<>();
    if (action.equals(NodeActions.PeersDnsLookupInit)) {
      if (data.length != 2) {
        throw new IllegalArgumentException("PeerDnsLookupInit should have two values: address and Port");
      }
      vals.add(new StringValue(data[0]));
      vals.add(parsePort(data[1]));
    } else if (action.equals(NodeActions.PeersDnsLookupError)) {
      if (data.length != 1) {
        throw new IllegalArgumentException("PeerDnsLookupError should have one value: DnsLookupError");
      }
      vals.add(parseDnsError(data[0]));
    } else if (action.equals(NodeActions.PeersDnsLookupSuccess)) {
      vals.add(parseAddresses(data));
    } else if (action.equals(NodeActions.PeersDnsLookupCleanup)) {
      if (data.length != 0) {
        throw new IllegalArgumentException("PeerDnsLookupCleanup should have no values");
      }
    }
    return vals;
  }

  private static Value parsePort(String port) {
    return parseIntValue(port);
  }

  private static Value parseDnsError(String err) {
    return new StringValue("DnsError: ".concat(err));
  }

  private static Value parseAddress(String addr) {
    // assume Ipv6 addresses are written: _:_:_:_:_:_:_:_:port
    String[] arr = addr.split(":");
    if (arr.length != 9) {
      throw new IllegalArgumentException("Ipv6 socket address should have: 16 byte ip address and port");
    }
    UniqueString[] fields = new UniqueString[] {
      UniqueString.uniqueStringOf("ip"),
      UniqueString.uniqueStringOf("port")
    };
    Value[] values = new Value[2];
    values[1] = parseIntValue(arr[8]);
    List<Value> ip_vals = new ArrayList<>();
    for (int i = 0; i < 8; i++) {
      ip_vals.add(parseIntValue(arr[i]));
    }
    values[0] = new TupleValue(ip_vals.toArray(new Value[0]));
    return new RecordValue(fields, values, true);
  }

  private static Value parseAddresses(String[] addrs) {
    Value[] vals = new Value[addrs.length];
    for (int i = 0; i < addrs.length; i++) {
      vals[i] = parseAddress(addrs[i]);
    }
    return new TupleValue(vals);
  }

  /**
   * Peers data parsers
   */
  private static List<Value> parsePeersData(String action, String[] data) {
    List<Value> vals = new ArrayList<>();
    if (action.equals(NodeActions.PeersAddIncomingPeer)) {
      if (data.length != 2) {
        throw new IllegalArgumentException("PeersAddIncomingPeer should have two values: PeerToken and SocketAddr");
      }
      vals.add(parseToken(data[0]));
      vals.add(parseAddress(data[1]));
    } else if (action.equals(NodeActions.PeersAddMulti)) {
      vals.add(parseAddresses(data));
    } else if (action.equals(NodeActions.PeersRemove)) {
      if (data.length != 1) {
        throw new IllegalArgumentException("PeersRemove should have one value: SocketAddr");
      }
      vals.add(parseAddress(data[0]));
    }
    return vals;
  }

  // parse peer token
  private static Value parseToken(String token) {
    return new StringValue("PeerToken: ".concat(token));
  }

  /**
   * Peer incoming data parsers
   */
  private static List<Value> parsePeerIncomingData(String action, String[] data) {
    List<Value> vals = new ArrayList<>();
    if (action.equals(NodeActions.PeerConnectionIncomingAccept)) {
      if (data.length != 0) {
        throw new IllegalArgumentException("PeerConnectionIncomingAccept should have no values");
      }
    } else if (action.equals(NodeActions.PeerConnectionIncomingAcceptSuccess)) {
      if (data.length != 2) {
        throw new IllegalArgumentException("PeerConnectionIncomingAcceptSuccess should have two values: PeerToken and SocketAddr");
      }
      vals.add(parseToken(data[0]));
      vals.add(parseAddress(data[1]));
    } else if (action.equals(NodeActions.PeerConnectionIncomingAcceptError)) {
      if (data.length != 1) {
        throw new IllegalArgumentException("PeerConnectionIncomingAcceptError should have one value: PeerConnectionIncomingAcceptError");
      }
      vals.add(parseIoError(data[0]));
    }
    return vals;
  }

  /**
   * Peer outgoing data parsers
   */
  private static List<Value> parsePeerOutgoingData(String action, String[] data) {
    List<Value> vals = new ArrayList<>();
    if (action.equals(NodeActions.PeerConnectionOutgoingRandomInit)) {
      if (data.length != 0) {
        throw new IllegalArgumentException("PeerConnectionOutgoingRandomInit should have no values");
      }
    } else if (action.equals(NodeActions.PeerConnectionOutgoingInit)) {
      if (data.length != 1) {
        throw new IllegalArgumentException("PeerConnectionOutgoingInit should have one value: SocketAddr");
      }
      vals.add(parseAddress(data[0]));
    } else if (action.equals(NodeActions.PeerConnectionOutgoingPending)) {
      if (data.length != 2) {
        throw new IllegalArgumentException("PeerConnectionOutgoingPending should have two values: SocketAddr and PeerToken");
      }
      vals.add(parseAddress(data[0]));
      vals.add(parseToken(data[1]));
    } else if (action.equals(NodeActions.PeerConnectionOutgoingError)) {
      if (data.length != 2) {
        throw new IllegalArgumentException("PeerConnectionOutgoingError should have two values: SocketAddr and IOErrorKind");
      }
      vals.add(parseAddress(data[0]));
      vals.add(parseIoError(data[1]));
    } else if (action.equals(NodeActions.PeerConnectionOutgoingSuccess)) {
      if (data.length != 2) {
        throw new IllegalArgumentException("PeerConnectionOutgoingSuccess should have one values: SocketAddr");
      }
      vals.add(parseAddress(data[0]));
    }
    return vals;
  }

  private static Value parseIoError(String error) {
    return new StringValue("IOError: ".concat(error));
  }

  /**
   * Peer disconnection data parsers
   */
  private static List<Value> parseDisconnectionData(String action, String[] data) {
    List<Value> vals = new ArrayList<>();
    if (action.equals(NodeActions.PeerDisconnect)) {
      if (data.length != 1) {
        throw new IllegalArgumentException("PeerDisconnect should have one value: SocketAddr");
      }
      vals.add(parseAddress(data[0]));
    } else if (action.equals(NodeActions.PeerDisconnected)) {
      if (data.length != 1) {
        throw new IllegalArgumentException("PeerDisconnected should have one value: SocketAddr");
      }
      vals.add(parseAddress(data[0]));
    }
    return vals;
  }

  /**
   * Event data parsers
   */
  private static List<Value> parseEventData(String action, String[] data) {
    List<Value> vals = new ArrayList<>();
    if (action.equals(NodeActions.P2pServerEvent)) {
      if (data.length != 0) {
        throw new IllegalArgumentException("P2pServerEvent should have no values");
      }
    } else if (action.equals(NodeActions.P2pPeerEvent)) {
      if (data.length != 5) {
        throw new IllegalArgumentException("P2pPeerEvent should have five values: PeerToken, SocketAddr, is_readable, is_writable, and is_closed");
      }
      vals.add(parseToken(data[0]));
      vals.add(parseAddress(data[1]));
      vals.add(new BoolValue(Boolean.parseBoolean(data[2])));
      vals.add(new BoolValue(Boolean.parseBoolean(data[3])));
      vals.add(new BoolValue(Boolean.parseBoolean(data[4])));
    } else if (action.equals(NodeActions.WakeupEvent)) {
      if (data.length != 0) {
        throw new IllegalArgumentException("WakeupEvent should have no values");
      }
    }
    return vals;
  }

  // include P2pPeerUnknownEvent?

  /**
   * Read/write data parsers
   */
  private static List<Value> parseReadWriteData(String action, String[] data) {
    List<Value> vals = new ArrayList<>();
    if (action.equals(NodeActions.PeerTryWrite)) {
      if (data.length != 1) {
        throw new IllegalArgumentException("PeerTryWrite should have one value: SocketAddr");
      }
      vals.add(parseAddress(data[0]));
    } else if (action.equals(NodeActions.PeerTryRead)) {
      if (data.length != 1) {
        throw new IllegalArgumentException("PeerTryRead should have one value: SocketAddr");
      }
      vals.add(parseAddress(data[0]));
    }
    return vals;
  }

  /**
   * Connection data parsers
   */
  private static List<Value> parseConnectionData(String action, String[] data) {
    List<Value> vals = new ArrayList<>();
    if (action.equals(NodeActions.PeerHandshakingInit)) {
      if (data.length != 1) {
        throw new IllegalArgumentException("PeerHandshakingInit should have one value: SocketAddr");
      }
      vals.add(parseAddress(data[0]));
    } else if (action.equals(NodeActions.PeerConnectionMessageWriteInit)) {
      // if (data.length != 2) {
      //   throw new IllegalArgumentException("PeerConnectionMessageWriteInit should have two values: SocketAddr and BinaryChunk");
      // }
      vals.add(parseAddress(data[0]));
      vals.add(parseBinaryChunk(tail(data)));
    } else if (action.equals(NodeActions.PeerConnectionMessagePartWritten)) {
      if (data.length != 2) {
        throw new IllegalArgumentException("PeerConnectionMessagePartWritten should have two values: SocketAddr and bytes_written");
      }
      vals.add(parseAddress(data[0]));
      vals.add(parseIntValue(data[1]));
    } else if (action.equals(NodeActions.PeerConnectionMessageWriteError)) {
      if (data.length != 2) {
        throw new IllegalArgumentException("PeerConnectionMessageWriteError should have two values: SocketAddr and IOErrorKind");
      }
      vals.add(parseAddress(data[0]));
      vals.add(parseIoError(data[1]));
    } else if (action.equals(NodeActions.PeerConnectionMessageWriteSuccess)) {
      if (data.length != 1) {
        throw new IllegalArgumentException("PeerConnectionMessageWriteSuccess should have one value: SocketAddr");
      } 
      vals.add(parseAddress(data[0]));
    } else if (action.equals(NodeActions.PeerConnectionMessageReadInit)) {
      if (data.length != 1) {
        throw new IllegalArgumentException("PeerConnectionMessageReadInit should have one value: SocketAddr");
      } 
      vals.add(parseAddress(data[0]));
    } else if (action.equals(NodeActions.PeerConnectionMessagePartRead)) {
      vals.add(parseAddress(data[0]));
      vals.add(parseBytes(tail(data)));
    } else if (action.equals(NodeActions.PeerConnectionMessageReadError)) {
      if (data.length != 2) {
        throw new IllegalArgumentException("PeerConnectionMessageReadError should have two values: SocketAddr and IOErrorKind");
      }
      vals.add(parseAddress(data[0]));
      vals.add(parseIoError(data[1]));
    } else if (action.equals(NodeActions.PeerConnectionMessageReadSuccess)) {
      if (data.length != 4) {
        throw new IllegalArgumentException("PeerConnectionMessageReadSuccess should have four values: SocketAddr, Port, compatible_version, and PublicKey");
      }
      vals.add(parseAddress(data[0]));
      vals.add(parsePort(data[1]));
      vals.add(parseVersion(data[2]));
      // if (true) {
      //   throw new IllegalArgumentException(vals.toString());
      // }
      vals.add(parsePubKey(data[3]));
    }
    return vals;
  }

  private static Value parseBinaryChunk(String[] chunk) {
    // BinaryChunk: Vec<u8>
    Value[] vals = new Value[chunk.length];
    for (int i = 0; i < chunk.length; i++) {
      vals[i] = parseIntValue(chunk[i]);
    }
    return new TupleValue(vals);
  }

  private static Value parseBytes(String[] bytes) {
    Value[] vals = new Value[bytes.length];
    for (int i = 0; i < bytes.length; i++) {
      vals[i] = parseIntValue(bytes[i]);
    }
    return new TupleValue(vals);
  }

  private static Value parseVersion(String version) {
    // [ chain : String, ddb : u16, p2p : u16 ]
    UniqueString[] fields = new UniqueString[] {
      UniqueString.uniqueStringOf("chain"),
      UniqueString.uniqueStringOf("ddb"),
      UniqueString.uniqueStringOf("p2p")
    };
    String[] vals = version.split("\\.");
    if (vals.length != 3) {
      throw new IllegalArgumentException("Version should have three values: chain, ddb, and p2p");
    }
    Value[] values = new Value[] {
      new StringValue(vals[0]),
      parseIntValue(vals[1]),
      parseIntValue(vals[2])
    };
    return new RecordValue(fields, values, true);
  }

  private static Value parsePubKey(String pubKey) {
    // TODO
    return new StringValue(pubKey);
  }

  /**
   * Storage data parsers
   */
  private static List<Value> parseStorageData(String action, String[] data) {
    List<Value> vals = new ArrayList<>();
    if (action.equals(NodeActions.StorageBlockHeadersPut)) {
      vals = parseBlockHeaders(data);
    } else if (action.equals(NodeActions.StorageBlockHeaderPutNextInit)) {
      if (data.length != 0) {
        throw new IllegalArgumentException("StorageBlockHeaderPutNextInit should have no values");
      }
    } else if (action.equals(NodeActions.StorageBlockHeaderPutNextPending)) {
      if (data.length != 1) {
        throw new IllegalArgumentException("StorageBlockHeaderPutNextPending should have one value: RequestId");
      }
      vals = parseRequestId(data[0]);
    } else if (action.equals(NodeActions.StorageStateSnapshotCreate)) {
      if (data.length != 0) {
        throw new IllegalArgumentException("StorageStateSnapshotCreate should have no values");
      }
    } else if (action.equals(NodeActions.StorageRequestCreate)) {
      if (data.length != 1) {
        throw new IllegalArgumentException("StorageRequestCreate should have one value: payload");
      }
      vals.add(parsePayload(data[0]));
    } else if (action.equals(NodeActions.StorageRequestInit)) {
      if (data.length != 1) {
        throw new IllegalArgumentException("StorageRequestInit should have one value: RequestId");
      }
      vals = parseRequestId(data[0]);
    } else if (action.equals(NodeActions.StorageRequestPending)) {
      if (data.length != 1) {
        throw new IllegalArgumentException("StorageRequestPending should have one value: RequestId");
      }
      vals = parseRequestId(data[0]);
    } else if (action.equals(NodeActions.StorageRequestError)) {
      if (data.length != 2) {
        throw new IllegalArgumentException("StorageRequestError should have two values: RequestId and StorageResponseError");
      }
      vals.add(parseAddress(data[0]));
      vals.add(parseStorageError(data[1]));
    } else if (action.equals(NodeActions.StorageRequestSuccess)) {
      if (data.length != 2) {
        throw new IllegalArgumentException("StorageRequestSuccess should have two values: RequestId and StorageResponseSuccess");
      }
      vals.add(parseAddress(data[0]));
      vals.add(parseStorageSuccess(data[1]));
    } else if (action.equals(NodeActions.StorageRequestFinish)) {
      if (data.length != 1) {
        throw new IllegalArgumentException("StorageRequestFinish should have one value: RequestId");
      }
      vals = parseRequestId(data[0]);
    }
    return vals;
  }

  private static List<Value> parseBlockHeaders(String[] headers) {
    Value[] vals = new Value[headers.length];
    for (int i = 0; i < headers.length; i++) {
      vals[i] = parseBlockHeader(headers[i]);
    }
    return Arrays.asList(vals);
  }

  private static Value parseBlockHeader(String header) {
    // TODO
    return new StringValue("BlockHeader");
  }

  private static List<Value> parseRequestId(String id) {
    // assumes id has the form locator:counter
    String[] arr = id.split(":");
    if (arr.length != 2) {
      throw new IllegalArgumentException("RequestId should have two values: locator and counter");
    }
    Value[] vals = new Value[arr.length];
    vals[0] = parseIntValue(arr[0]);
    vals[1] = parseIntValue(arr[1]);
    return Arrays.asList(vals);
  }

  private static Value parsePayload(String payload) {
    // TODO
    return new StringValue("Payload");
  }

  private static Value parseStorageError(String error) {
    // TODO
    return new StringValue("StorageResponseError");
  }

  private static Value parseStorageSuccess(String success) {
    // TODO
    return new StringValue("StorageResponseSuccess");
  }

  // array tail
  private static <T> T[] tail(T[] array) {
    int len = array.length;
    if (len == 0) {
      throw new IllegalArgumentException("Empty array has no tail");
    }
    return Arrays.copyOfRange(array, 1, len);
  }

  // parse an IntValue
  private static Value parseIntValue(String value) {
    return IntValue.gen(Integer.parseInt(value));
  }
}

/**
 * Node actions class
 */
class NodeActions {
  /**
   * Dns actions
   */
  public static final String PeersDnsLookupInit = new String("PeersDnsLookupInit");
  public static final String PeersDnsLookupError = new String("PeersDnsLookupError");
  public static final String PeersDnsLookupSuccess = new String("PeersDnsLookupSuccess");
  public static final String PeersDnsLookupCleanup = new String("PeersDnsLookupCleanup");

  public static Set<String> dnsActions() {
    Set<String> acts = new HashSet<String>();
    acts.add(PeersDnsLookupInit);
    acts.add(PeersDnsLookupError);
    acts.add(PeersDnsLookupSuccess);
    acts.add(PeersDnsLookupCleanup);
    return acts;
  }

  /**
   * Peers actions
   */
  public static final String PeersAddIncomingPeer = new String("PeersAddIncomingPeer");
  public static final String PeersAddMulti = new String("PeersAddMulti");
  public static final String PeersRemove = new String("PeersRemove");

  public static Set<String> peersActions() {
    Set<String> acts = new HashSet<String>();
    acts.add(PeersAddIncomingPeer);
    acts.add(PeersAddMulti);
    acts.add(PeersRemove);
    return acts;
  }

  /**
   * Peer incoming actions
   */
  public static final String PeerConnectionIncomingAccept = new String("PeerConnectionIncomingAccept");
  public static final String PeerConnectionIncomingAcceptError = new String("PeerConnectionIncomingAcceptError");
  public static final String PeerConnectionIncomingAcceptSuccess = new String("PeerConnectionIncomingAcceptSuccess");
  public static final String PeerConnectionIncomingSuccess = new String("PeerConnectionIncomingSuccess");

  public static Set<String> peerIncomingActions() {
    Set<String> acts = new HashSet<String>();
    acts.add(PeerConnectionIncomingAccept);
    acts.add(PeerConnectionIncomingAcceptError);
    acts.add(PeerConnectionIncomingAcceptSuccess);
    acts.add(PeerConnectionIncomingSuccess);
    return acts;
  }

  /**
   * Peer outgoing actions
   */
  public static final String PeerConnectionOutgoingRandomInit = new String("PeerConnectionOutgoingRandomInit");
  public static final String PeerConnectionOutgoingInit = new String("PeerConnectionOutgoingInit");
  public static final String PeerConnectionOutgoingPending = new String("PeerConnectionOutgoingPending");
  public static final String PeerConnectionOutgoingError = new String("PeerConnectionOutgoingError");
  public static final String PeerConnectionOutgoingSuccess = new String("PeerConnectionOutgoingSuccess");

  public static Set<String> peerOutgoingActions() {
    Set<String> acts = new HashSet<String>();
    acts.add(PeerConnectionOutgoingRandomInit);
    acts.add(PeerConnectionOutgoingInit);
    acts.add(PeerConnectionOutgoingPending);
    acts.add(PeerConnectionOutgoingError);
    acts.add(PeerConnectionOutgoingSuccess);
    return acts;
  }

  /**
   * Peer disconnection actions
   */
  public static final String PeerDisconnect = new String("PeerDisconnect");
  public static final String PeerDisconnected = new String("PeerDisconnected");

  public static Set<String> peerDisconnectionActions() {
    Set<String> acts = new HashSet<String>();
    acts.add(PeerDisconnect);
    acts.add(PeerDisconnected);
    return acts;
  }

  /**
   * Event actions
   */
  public static final String P2pServerEvent = new String("P2pServerEvent");
  public static final String P2pPeerEvent = new String("P2pPeerEvent");
  public static final String WakeupEvent = new String("WakeupEvent");

  public static Set<String> eventActions() {
    Set<String> acts = new HashSet<String>();
    acts.add(P2pServerEvent);
    acts.add(P2pPeerEvent);
    acts.add(WakeupEvent);
    return acts;
  }

  /**
   * Read/write actions
   */
  public static final String PeerTryWrite = new String("PeerTryWrite");
  public static final String PeerTryRead = new String("PeerTryRead");

  public static Set<String> readWriteActions() {
    Set<String> acts = new HashSet<String>();
    acts.add(PeerTryWrite);
    acts.add(PeerTryRead);
    return acts;
  }

  /**
   * Connection actions
   */
  public static final String PeerHandshakingInit = new String("PeerHandshakingInit");
  public static final String PeerConnectionMessageWriteInit = new String("PeerConnectionMessageWriteInit");
  public static final String PeerConnectionMessagePartWritten = new String("PeerConnectionMessagePartWritten");
  public static final String PeerConnectionMessageWriteError = new String("PeerConnectionMessageWriteError");
  public static final String PeerConnectionMessageWriteSuccess = new String("PeerConnectionMessageWriteSuccess");
  public static final String PeerConnectionMessageReadInit = new String("PeerConnectionMessageReadInit");
  public static final String PeerConnectionMessagePartRead = new String("PeerConnectionMessagePartRead");
  public static final String PeerConnectionMessageReadError = new String("PeerConnectionMessageReadError");
  public static final String PeerConnectionMessageReadSuccess = new String("PeerConnectionMessageReadSuccess");

  public static Set<String> connectionActions() {
    Set<String> acts = new HashSet<String>();
    acts.add(PeerHandshakingInit);
    acts.add(PeerConnectionMessageWriteInit);
    acts.add(PeerConnectionMessagePartWritten);
    acts.add(PeerConnectionMessageWriteError);
    acts.add(PeerConnectionMessageWriteSuccess);
    acts.add(PeerConnectionMessageReadInit);
    acts.add(PeerConnectionMessagePartRead);
    acts.add(PeerConnectionMessageReadError);
    acts.add(PeerConnectionMessageReadSuccess);
    return acts;
  }

  /**
   * Storage actions
   */
  public static final String StorageBlockHeadersPut = new String("StorageBlockHeadersPut");
  public static final String StorageBlockHeaderPutNextInit = new String("StorageBlockHeaderPutNextInit");
  public static final String StorageBlockHeaderPutNextPending = new String("StorageBlockHeaderPutNextPending");
  public static final String StorageStateSnapshotCreate = new String("StorageStateSnapshotCreate");
  public static final String StorageRequestCreate = new String("StorageRequestCreate");
  public static final String StorageRequestInit = new String("StorageRequestInit");
  public static final String StorageRequestPending = new String("StorageRequestPending");
  public static final String StorageRequestError = new String("StorageRequestError");
  public static final String StorageRequestSuccess = new String("StorageRequestSuccess");
  public static final String StorageRequestFinish = new String("StorageRequestFinish");

  public static Set<String> storageActions() {
    Set<String> acts = new HashSet<String>();
    acts.add(StorageBlockHeadersPut);
    acts.add(StorageBlockHeaderPutNextInit);
    acts.add(StorageBlockHeaderPutNextPending);
    acts.add(StorageStateSnapshotCreate);
    acts.add(StorageRequestCreate);
    acts.add(StorageRequestInit);
    acts.add(StorageRequestPending);
    acts.add(StorageRequestError);
    acts.add(StorageRequestSuccess);
    acts.add(StorageRequestFinish);
    return acts;
  }

   /**
    * All node actions
    */
  public static Set<String> allActions() {
    Set<String> acts = new HashSet<String>();
    acts.addAll(dnsActions());
    acts.addAll(peersActions());
    acts.addAll(peerIncomingActions());
    acts.addAll(peerOutgoingActions());
    acts.addAll(peerDisconnectionActions());
    acts.addAll(eventActions());
    acts.addAll(readWriteActions());
    acts.addAll(connectionActions());
    acts.addAll(storageActions());
    return acts;
  }
}
