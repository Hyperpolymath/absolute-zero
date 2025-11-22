# NOP Protocol Specification for Computer Network Operations

## Protocol Identifier
- **Name**: NOPRO (No-Operation Protocol)
- **Version**: 1.0
- **Purpose**: Standardized CNO framework for zero-effect network operations
- **Classification**: Experimental esoteric network protocol

## Abstract

The NOP Protocol (NOPRO) defines a standardized approach to Computer Network Operations
that traverse the network stack while intentionally producing no application-level effect.
This protocol is designed for research, testing, and understanding the inherent costs and
side effects of "doing nothing" over a network.

## 1. Protocol Overview

### 1.1 Design Philosophy

NOPRO embodies the principle of "maximum overhead, minimum effect":
- **Overhead**: Full network stack traversal required
- **Effect**: Zero application state change
- **Observable**: All operations leave forensic traces
- **Measurable**: Every operation consumes quantifiable resources

### 1.2 Use Cases

1. **Network Infrastructure Testing**
   - Latency measurement without data payload
   - Path MTU discovery
   - Firewall rule validation

2. **CNO Research**
   - Covert channel characterization
   - Timing attack primitives
   - Resource exhaustion analysis

3. **Forensic Analysis**
   - Minimal packet footprint analysis
   - Network monitoring system testing
   - Intrusion detection signature development

4. **Educational Purposes**
   - Demonstrating network overhead
   - Protocol stack understanding
   - Security awareness training

## 2. Protocol Layers and Operations

### 2.1 Application Layer Specification

#### 2.1.1 NOP Command Set

```
NOPRO defines the following application-level commands:

1. NULL-QUERY
   - Send: Empty application payload
   - Expect: Acknowledgment with empty payload
   - Effect: None

2. ECHO-VOID
   - Send: Request to echo nothing
   - Expect: Response containing nothing
   - Effect: None

3. PING-NULL
   - Send: Timing probe with null payload
   - Expect: Timing response with null payload
   - Effect: RTT measurement only

4. SYNC-NOTHING
   - Send: Synchronization request
   - Expect: Synchronization acknowledgment
   - Effect: Clock synchronization, no data transfer

5. STATUS-IDLE
   - Send: Status query
   - Expect: "Idle/No operation" response
   - Effect: State confirmation only
```

#### 2.1.2 Message Format

```
+------------------+------------------+------------------+
|   Message Type   |   Sequence Num   |    Timestamp     |
|     (1 byte)     |     (4 bytes)    |    (8 bytes)     |
+------------------+------------------+------------------+
|   Reserved (all zeros)              |    Checksum      |
|          (19 bytes)                 |    (4 bytes)     |
+-------------------------------------+------------------+

Total: 36 bytes of overhead to communicate nothing
```

**Field Descriptions:**
- **Message Type**: 0x00 = NULL-QUERY, 0x01 = ECHO-VOID, etc.
- **Sequence Number**: Monotonically increasing packet counter
- **Timestamp**: Nanoseconds since epoch (for timing channels)
- **Reserved**: Must be zero (but creates covert channel opportunity)
- **Checksum**: CRC32 of entire message

### 2.2 Transport Layer Specification

#### 2.2.1 TCP-Based NOPRO

**Connection Establishment:**
```
Client → Server: SYN (seq=X)
Server → Client: SYN-ACK (seq=Y, ack=X+1)
Client → Server: ACK (seq=X+1, ack=Y+1)

[Connection established, no data transmitted]

Client → Server: FIN (seq=X+1)
Server → Client: ACK (seq=Y+1, ack=X+2)
Server → Client: FIN (seq=Y+1)
Client → Server: ACK (seq=X+2, ack=Y+2)

Result: 7 packets, ~420 bytes overhead, 0 bytes application data
```

**State Machine:**
```
CLOSED → SYN_SENT → ESTABLISHED → FIN_WAIT_1 → FIN_WAIT_2 → TIME_WAIT → CLOSED

Total connection lifetime: ~60 seconds (TIME_WAIT)
NAT table entry lifetime: ~120 seconds
Firewall state entry: Created and destroyed
```

#### 2.2.2 UDP-Based NOPRO

**Datagram Exchange:**
```
Client → Server: UDP (36-byte NOPRO message)
Server → Client: UDP (36-byte NOPRO response)

Result: 2 packets, ~164 bytes total overhead
No connection state, but NAT/firewall entries created
```

**Advantages:**
- Lower overhead than TCP
- No connection establishment delay
- Immediate NAT binding creation

**Disadvantages:**
- No delivery guarantee (even for nothing)
- No flow control
- Easier to filter/drop

### 2.3 Network Layer Specification

#### 2.3.1 IPv4 NOPRO

```
IP Header (20 bytes minimum):
- Version: 4
- IHL: 5 (no options)
- DSCP: 0 (default)
- ECN: 0 (non-ECN-capable)
- Total Length: 20 (header) + 8 (UDP) + 36 (payload) = 64 bytes
- Identification: Unique per packet (covert channel)
- Flags: DF (Don't Fragment) set
- Fragment Offset: 0
- TTL: 64 (default, but variable for reconnaissance)
- Protocol: 17 (UDP) or 6 (TCP)
- Header Checksum: Calculated
- Source IP: Sender address
- Destination IP: Receiver address
```

#### 2.3.2 IPv6 NOPRO

```
IPv6 Header (40 bytes, no extension headers):
- Version: 6
- Traffic Class: 0
- Flow Label: 0 (or covert channel)
- Payload Length: 44 (UDP + payload)
- Next Header: 17 (UDP) or 6 (TCP)
- Hop Limit: 64
- Source Address: 128-bit IPv6 address
- Destination Address: 128-bit IPv6 address

Note: IPv6 has 20 extra bytes of overhead vs IPv4
```

### 2.4 Link Layer Specification

```
Ethernet II Frame:
+------------------+------------------+------------------+
| Dest MAC (6 B)   | Src MAC (6 B)    | EtherType (2 B)  |
+------------------+------------------+------------------+
|                 Payload (46-1500 bytes)                |
+--------------------------------------------------------+
|                   FCS (4 bytes)                        |
+--------------------------------------------------------+

For NOPRO:
- EtherType: 0x0800 (IPv4) or 0x86DD (IPv6)
- Payload: IP packet (64+ bytes)
- Padding: If payload < 46 bytes (not applicable for NOPRO)
```

## 3. Network Stack Traversal Analysis

### 3.1 Outbound Path (Sender)

```
Application:    NOPRO library generates message
                  ↓ (syscall overhead: ~1 μs)
Transport:      UDP/TCP header added, checksum calculated
                  ↓ (routing lookup: ~100 ns)
Network:        IP header added, routing decision made
                  ↓ (ARP lookup: 0-100 ms if not cached)
Link:           Ethernet frame constructed, FCS calculated
                  ↓ (DMA transfer: ~1 μs)
Physical:       NIC transmits electrical/optical signals
                  ↓ (propagation: ~5 μs per km)
```

### 3.2 Network Path (Intermediate Devices)

```
Each router/switch processes the packet:

Physical:       Signal reception and clock recovery
                  ↓
Link:           Frame validation, FCS check
                  ↓ (MAC lookup: ~10 ns in TCAM)
Network:        IP header parsing, TTL decrement
                  ↓ (routing lookup: ~100 ns)
Link:           New frame construction for next hop
                  ↓
Physical:       Signal retransmission

Per-hop latency: ~1-10 μs (LAN) or 1-10 ms (WAN)
```

### 3.3 Inbound Path (Receiver)

```
Physical:       Signal reception
                  ↓
Link:           Frame validation, destination MAC check
                  ↓
Network:        IP checksum validation, destination check
                  ↓
Transport:      Port demultiplexing, checksum validation
                  ↓ (context switch: ~1 μs)
Application:    NOPRO library processes message
                  ↓
Result:         Nothing happens (by design)
```

## 4. Resource Consumption Metrics

### 4.1 Bandwidth Consumption

#### TCP-Based NOPRO Session
```
Handshake:      3 packets × 66 bytes = 198 bytes
Data:           0 bytes
Teardown:       4 packets × 66 bytes = 264 bytes
Total:          462 bytes

Bandwidth rate (1 session/sec): 3,696 bps
Bandwidth rate (1000 sessions/sec): 3.7 Mbps
```

#### UDP-Based NOPRO Exchange
```
Request:        1 packet × 78 bytes = 78 bytes
Response:       1 packet × 78 bytes = 78 bytes
Total:          156 bytes

Bandwidth rate (1 exchange/sec): 1,248 bps
Bandwidth rate (1000 exchanges/sec): 1.2 Mbps
```

### 4.2 State Table Consumption

```
NAT Device:
- Entry size: ~64 bytes (IP/port mapping + metadata)
- Timeout: 60s (UDP) or 7200s (TCP established)
- Max entries: Typically 65,536-1,048,576

NOPRO attack potential:
- 10,000 sessions/sec = 640 KB/sec NAT table growth
- Can exhaust typical NAT table in ~100 seconds
```

```
Stateful Firewall:
- Entry size: ~128 bytes (connection tracking + counters)
- Timeout: Similar to NAT
- Max entries: Typically 100,000-10,000,000

Connection tracking overhead:
- Hashtable lookup: O(1) average, O(n) worst case
- Memory allocation for new entries
- Timer management for timeouts
```

### 4.3 Energy Consumption Per Operation

```
Component              Energy per NOPRO Packet
-------------------------------------------------
NIC (sender)           1.0 μJ
NIC (receiver)         1.0 μJ
Switch (per hop)       0.1 μJ
Router (per hop)       0.5 μJ
Firewall (stateful)    2.0 μJ
NAT device             1.5 μJ

Typical path (client → NAT → firewall → 3 routers → server):
= 1.0 + 1.5 + 2.0 + (3 × 0.5) + 1.0 = 7.0 μJ per NOPRO packet

1 million NOPRO packets = 7 J
1 billion NOPRO packets = 7 kJ = 1.67 kcal
```

## 5. Timing Channels and Covert Communication

### 5.1 Timing-Based Covert Channels

#### Inter-Packet Delay Encoding
```
Binary encoding via packet timing:
- '0' bit: Send packet after 100 ms delay
- '1' bit: Send packet after 200 ms delay

Message "HI" (01001000 01001001):
Timing sequence: 200,100,200,200,100,200,200,200,200,100,200,200,100,200,200,100 ms

Bandwidth: ~10 bps (with overhead)
Covertness: High (appears as irregular application behavior)
Detection: Requires precise timing analysis
```

#### Rate Modulation
```
Packets per second encoding:
- Baseline: 10 packets/sec
- '0' bit: 10 packets/sec (baseline)
- '1' bit: 20 packets/sec (doubled rate)

Bandwidth: 1 bps (averaged over 1-second windows)
Covertness: Very high (appears as load variation)
Detection: Requires long-term statistical analysis
```

### 5.2 Storage-Based Covert Channels

#### IP Identification Field
```
16-bit IP ID field can encode data:
- Normally increments sequentially
- Can embed 2 bytes per packet

Message encoding:
IP ID = 0x4841 → "HA"
IP ID = 0x434B → "CK"

Bandwidth: 16 bps (at 1 packet/sec)
Covertness: Medium (anomalous ID values detectable)
Detection: Statistical analysis of ID sequence
```

#### TCP Sequence Number LSBs
```
Use least significant bits of TCP sequence number:
- Normal: Random 32-bit initial sequence number
- Covert: Encode data in lower 8 bits

Example:
ISN = 0xXXXXXX48 → 'H' (0x48)
ISN = 0xXXXXXX41 → 'A' (0x41)

Bandwidth: 8 bps per connection (one-time during handshake)
Covertness: High (small deviation from random)
Detection: Requires analysis of ISN distribution
```

#### Reserved Field Modulation
```
NOPRO message has 19 reserved bytes:
- Specification requires all zeros
- Covert use: Embed 152 bits per message

Bandwidth: 152 bps (at 1 message/sec)
Covertness: Low (violates protocol specification)
Detection: Trivial (check for non-zero reserved fields)
```

### 5.3 Hybrid Covert Channels

```
Combining timing and storage:
- Use IP ID for primary data channel (16 bps)
- Use inter-packet timing for clock synchronization
- Use UDP source port for sequence numbering

Effective bandwidth: ~20 bps
Robustness: High (multiple redundant channels)
Covertness: Medium-high (requires multiple detection methods)
```

## 6. NAT and Firewall State Analysis

### 6.1 NAT Binding Creation

#### Outbound UDP NOPRO
```
Internal state: 192.168.1.100:54321 → 203.0.113.5:8000
NAT translation: 192.168.1.100:54321 → 198.51.100.1:54321

NAT table entry:
{
  internal_ip: 192.168.1.100,
  internal_port: 54321,
  external_ip: 198.51.100.1,
  external_port: 54321,
  destination_ip: 203.0.113.5,
  destination_port: 8000,
  protocol: UDP,
  timeout: 60 seconds,
  created: timestamp,
  last_activity: timestamp,
  byte_count: 78,
  packet_count: 1
}

Memory: 64 bytes
Lifetime: 60 seconds (refreshed on each packet)
```

#### Outbound TCP NOPRO
```
Three-way handshake creates persistent binding:

NAT table entry (ESTABLISHED state):
{
  ... (similar to UDP)
  protocol: TCP,
  tcp_state: ESTABLISHED,
  timeout: 7200 seconds (2 hours),
  ...
}

Memory: 64 bytes
Lifetime: Up to 2 hours after last activity
```

### 6.2 Firewall State Machine

#### Stateful Packet Filter
```
Outbound NOPRO packet:

1. New connection check: No existing state → Create NEW entry
2. Rule evaluation:
   - Source: Internal network (trusted)
   - Destination: External network
   - Action: ACCEPT (default outbound policy)

3. State entry created:
{
  src_ip: 192.168.1.100,
  src_port: 54321,
  dst_ip: 203.0.113.5,
  dst_port: 8000,
  protocol: UDP,
  state: NEW → ESTABLISHED (after return packet),
  timeout: 60 seconds,
  byte_count: 78,
  packet_count: 1,
  action: ACCEPT
}

Inbound return packet:
- State lookup: ESTABLISHED → Skip rule evaluation
- Action: ACCEPT (stateful return traffic)
- Update counters and timeout
```

#### Deep Packet Inspection (DPI)
```
Additional processing for NOPRO packets:

1. Protocol identification:
   - Port-based: UDP port 8000 (custom)
   - Signature-based: NOPRO message header pattern

2. Payload inspection:
   - Extract message type field
   - Validate checksum
   - Check for anomalies in reserved fields

3. Metadata extraction:
   - Sequence number tracking
   - Timestamp analysis
   - Covert channel detection

DPI overhead:
- CPU: ~10-100 μs per packet (depending on rules)
- Memory: Additional 128-256 bytes per flow
- Latency: +1-10 ms (inline inspection)
```

### 6.3 State Exhaustion Attacks

#### NAT Table Flooding
```python
# Pseudo-code for NAT exhaustion via NOPRO

for source_port in range(1024, 65536):
    send_nopro_udp(
        src_ip="192.168.1.100",
        src_port=source_port,
        dst_ip="203.0.113.5",
        dst_port=8000
    )
    # Each packet creates unique NAT entry
    # 64,512 entries × 64 bytes = 4 MB

# Result: NAT table full, legitimate traffic blocked
# Duration: ~1 second at 100k packets/sec
```

#### Firewall Connection Tracking Exhaustion
```python
# Pseudo-code for firewall state exhaustion

for dst_ip in range(203.0.113.1, 203.0.113.255):
    for dst_port in range(1, 65536):
        send_nopro_tcp_syn(
            src_ip="192.168.1.100",
            dst_ip=f"203.0.113.{dst_ip}",
            dst_port=dst_port
        )
        # Each SYN creates state entry
        # 254 IPs × 65,535 ports = 16.6M potential entries

# Result: Firewall CPU exhausted, state table full
# Side effect: Legitimate connections dropped
```

## 7. Energy and Environmental Impact

### 7.1 Per-Packet Energy Budget

```
Energy consumption per NOPRO UDP packet (156 bytes on wire):

Sender NIC:
- DMA read from RAM: 156 bytes × 10 nJ/byte = 1.56 μJ
- Packet processing: 1000 cycles × 0.5 nJ/cycle = 0.50 μJ
- Signal transmission: 1248 bits × 100 nJ/bit = 124.80 μJ
- Total sender: ~127 μJ

Network path (5 hops average):
- Switch (Layer 2): 0.1 μJ per hop × 5 = 0.5 μJ
- Router (Layer 3): 0.5 μJ per hop × 5 = 2.5 μJ
- Total network: ~3 μJ

Receiver NIC:
- Signal reception: ~50 μJ
- DMA write to RAM: 1.56 μJ
- Interrupt processing: 0.50 μJ
- Total receiver: ~52 μJ

Grand total: 127 + 3 + 52 = 182 μJ per NOPRO packet
```

### 7.2 Aggregate Energy Consumption

```
Scenario: Enterprise network with 10,000 clients

NOPRO traffic patterns:
- Each client: 1 NOPRO exchange per minute (heartbeat)
- Rate: 10,000 × 2 packets/min = 333 packets/sec
- Daily packets: 10,000 × 2 × 60 × 24 = 28.8 million

Daily energy:
- Direct: 28.8M × 182 μJ = 5.24 MJ = 1.46 kWh
- Cooling (1.5× PUE): 2.19 kWh
- Total: 3.65 kWh/day

Annual energy:
- Direct + cooling: 3.65 × 365 = 1,332 kWh/year
- CO2 emissions: ~660 kg CO2e (US grid average)
- Cost: ~$130/year (at $0.10/kWh)

For transmitting nothing.
```

### 7.3 Internet-Scale Impact

```
Hypothetical: 1% of internet traffic is NOPRO-like (keepalives, heartbeats, null polls)

Current internet traffic: ~5,000 exabytes/year
NOPRO-equivalent: 50 exabytes/year
Average packet size: 100 bytes

Packets per year: 50 EB / 100 B = 500 quadrillion packets

Energy consumption:
- Per packet: 182 μJ
- Total: 500 × 10^15 × 182 × 10^-6 J = 91 × 10^12 J = 91 TJ
- With cooling: 91 × 1.5 = 136.5 TJ

Equivalent:
- 37,500 MWh of electricity
- 18,750 tons of CO2 emissions
- Energy to power ~3,500 US homes for a year

All to accomplish nothing at the application layer.
```

## 8. Forensic Implications

### 8.1 Evidence Left by NOPRO Traffic

#### Network Packet Captures
```
tcpdump/Wireshark will record:
- Full packet headers and payload
- Precise timestamps (microsecond or nanosecond)
- Interface metadata
- PCAP file on disk (persistent evidence)

A single NOPRO exchange creates:
- Packet metadata: ~200 bytes per packet in PCAP
- Full packet: ~156 bytes on wire
- Total PCAP size: ~356 bytes per exchange

1 million NOPRO exchanges = 356 MB PCAP file
```

#### Flow Records (NetFlow/IPFIX)
```
Flow record for NOPRO session:

{
  src_ip: "192.168.1.100",
  dst_ip: "203.0.113.5",
  src_port: 54321,
  dst_port: 8000,
  protocol: 17 (UDP),
  start_time: "2025-11-22T10:30:00.000Z",
  end_time: "2025-11-22T10:30:00.100Z",
  packets: 2,
  bytes: 156,
  tcp_flags: null,
  tos: 0
}

Size: ~100 bytes per flow
Retention: Typically 30-90 days
Aggregation: May combine multiple NOPRO exchanges
```

#### Firewall and IDS Logs
```
Firewall log entry:

Nov 22 10:30:00 fw01 kernel: [UFW ALLOW] IN= OUT=eth0 SRC=192.168.1.100 \
DST=203.0.113.5 LEN=64 TOS=0x00 PREC=0x00 TTL=64 ID=12345 PROTO=UDP \
SPT=54321 DPT=8000 LEN=44

IDS alert (if NOPRO signature exists):

[**] [1:1000001:1] NOPRO Protocol Detected [**]
[Priority: 3] {UDP} 192.168.1.100:54321 -> 203.0.113.5:8000

Size: ~200 bytes per log entry
Retention: Typically 1 year
Searchable: By IP, port, protocol, signature
```

### 8.2 Correlation and Attribution

#### Traffic Pattern Analysis
```
NOPRO sessions may reveal:

1. Temporal patterns:
   - Regular intervals (automated scripts)
   - Business hours vs. off-hours
   - Correlation with other events

2. Spatial patterns:
   - Source IP geolocation
   - Destination IP reputation
   - ASN and network ownership

3. Behavioral patterns:
   - Port selection (random vs. sequential)
   - Payload variations (covert channels)
   - Response times (system fingerprinting)
```

#### Multi-Source Correlation
```
Combining evidence from:
- Firewall logs (connection timing)
- DNS queries (preceding NOPRO traffic)
- ARP cache (local network activity)
- DHCP logs (IP-to-MAC-to-device mapping)
- Application logs (triggering events)

Result: Attribution of NOPRO traffic to specific user/device/application
```

### 8.3 Anti-Forensic Considerations

#### Limitations of "Doing Nothing"
```
Even NOPRO traffic cannot avoid:
- Mandatory metadata (IP addresses, ports)
- Timing information (packet timestamps)
- Size information (packet length)
- Path information (TTL, routing)

"I sent nothing" is not a valid defense when:
- Packet captures show NOPRO packets
- Logs show network connections
- Firewall state tables show entries
- Flow records show traffic
```

#### Plausible Deniability Challenges
```
Prosecutor: "You sent 10,000 NOPRO packets to this IP address."
Defense: "But I transmitted no data!"
Prosecutor: "You transmitted 1.56 MB of network traffic with no purpose."

The act of sending NOPRO is itself evidence of intent.
The overhead is not deniable.
The timing is not deniable.
The destination is not deniable.
```

## 9. Security Considerations

### 9.1 NOPRO as an Attack Vector

1. **Reconnaissance**
   - Port scanning with minimal footprint
   - Firewall rule inference
   - Network topology mapping

2. **Resource Exhaustion**
   - NAT table flooding
   - Firewall state exhaustion
   - Bandwidth consumption
   - Log storage depletion

3. **Covert Communication**
   - Timing channels
   - Storage channels in headers
   - Traffic pattern encoding

4. **Distraction and Misdirection**
   - Flood with NOPRO while conducting real attack
   - Overwhelm analysts with low-priority alerts
   - Mask malicious traffic in NOPRO noise

### 9.2 Defensive Measures

#### Rate Limiting
```
Firewall rule:
iptables -A INPUT -p udp --dport 8000 -m limit --limit 10/sec -j ACCEPT
iptables -A INPUT -p udp --dport 8000 -j DROP

Limits NOPRO to 10 packets/sec, drops excess
```

#### Anomaly Detection
```
Baseline normal behavior:
- Typical NOPRO rate: 1 packet/min per client
- Typical clients: 100

Anomaly thresholds:
- Rate: >10 packets/sec from single source
- Volume: >1000 total packets/hour
- Pattern: Regular interval <1 sec (likely automated)

Action: Alert, rate-limit, or block
```

#### Deep Packet Inspection
```
DPI rule for NOPRO:
if (udp.dport == 8000 and payload[0] in [0x00, 0x01, 0x02, 0x03, 0x04]):
    if (payload[13:32] != b'\x00' * 19):  # Reserved field not zero
        alert("NOPRO reserved field anomaly")
        drop()
```

### 9.3 Recommendations

1. **For Network Administrators**
   - Monitor NOPRO-like traffic patterns
   - Set rate limits on ephemeral port usage
   - Implement connection tracking limits
   - Use anomaly detection for null-payload traffic

2. **For Security Analysts**
   - Correlate NOPRO with other suspicious activity
   - Analyze timing patterns for covert channels
   - Investigate high-volume low-payload flows
   - Check for reserved field manipulation

3. **For Developers**
   - Avoid creating NOPRO-like protocols
   - Use proper heartbeat/keepalive mechanisms
   - Minimize null-payload transmissions
   - Document legitimate null-effect operations

## 10. Conclusion

The NOP Protocol demonstrates a fundamental paradox in computer networking:
**You cannot send "nothing" without sending something.**

Every NOPRO operation:
- Consumes bandwidth (minimum 156 bytes UDP, 462 bytes TCP)
- Occupies state tables (NAT, firewall, connection tracking)
- Expends energy (hundreds of microjoules per packet)
- Leaves forensic evidence (logs, flow records, packet captures)
- Creates timing channels (microsecond-precision timestamps)

NOPRO serves as a framework for understanding the unavoidable overhead and side effects
of network communication. In Computer Network Operations, there is no true "no-operation."
The only way to accomplish nothing is to not communicate at all - the network equivalent
of "Absolute Zero."

## Appendix A: NOPRO Implementation Reference

### A.1 Port Assignments
- **UDP**: 8000 (unregistered, for experimental use)
- **TCP**: 8000 (same)

### A.2 Message Type Codes
- `0x00`: NULL-QUERY
- `0x01`: ECHO-VOID
- `0x02`: PING-NULL
- `0x03`: SYNC-NOTHING
- `0x04`: STATUS-IDLE
- `0x05-0xFF`: Reserved for future use

### A.3 Error Codes
- `0x00`: Success (nothing happened)
- `0x01`: Failure (something happened - protocol violation)
- `0x02`: Invalid message type
- `0x03`: Checksum mismatch
- `0x04`: Reserved field not zero

### A.4 Default Timeouts
- UDP NAT binding: 60 seconds
- TCP established: 7200 seconds
- Response timeout: 5 seconds

## Appendix B: References

1. TCP/IP Illustrated, Volume 1: The Protocols (Stevens, 2011)
2. Computer Networks: A Systems Approach (Peterson & Davie, 2021)
3. Firewalls and Internet Security (Cheswick & Bellovin, 2003)
4. The Art of Network Architecture (White & Donohue, 2014)
5. Covert Channels in the TCP/IP Protocol Suite (Rowland, 1997)

---

**Document Version**: 1.0
**Last Updated**: 2025-11-22
**Status**: Experimental Specification
**Classification**: Public / Educational Use
