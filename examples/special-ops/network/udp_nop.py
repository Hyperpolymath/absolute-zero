#!/usr/bin/env python3
"""
UDP NOP - UDP Packet Sent But With No Effect

This script demonstrates a UDP datagram that traverses the entire network stack,
creates NAT/firewall state, consumes bandwidth and energy, leaves forensic traces,
yet produces zero meaningful application-level effect.

Unlike TCP, UDP has no connection establishment overhead, but still:
- Sends minimum 2 packets (request + response)
- Consumes ~156 bytes of bandwidth (minimum)
- Creates NAT and firewall state entries
- Occupies ephemeral ports temporarily
- Consumes CPU cycles and memory
- Leaves forensic evidence in logs
- Expends measurable energy

This demonstrates that even the "lightweight" protocol cannot avoid overhead
when attempting to accomplish nothing.
"""

import socket
import time
import sys
import struct
import hashlib
from datetime import datetime

# ANSI color codes for output
class Colors:
    HEADER = '\033[95m'
    BLUE = '\033[94m'
    CYAN = '\033[96m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'


def print_header(text):
    """Print formatted header"""
    print(f"\n{Colors.HEADER}{Colors.BOLD}{'='*70}{Colors.ENDC}")
    print(f"{Colors.HEADER}{Colors.BOLD}{text:^70}{Colors.ENDC}")
    print(f"{Colors.HEADER}{Colors.BOLD}{'='*70}{Colors.ENDC}\n")


def print_info(label, value):
    """Print formatted info line"""
    print(f"{Colors.CYAN}{label:.<40}{Colors.ENDC} {Colors.GREEN}{value}{Colors.ENDC}")


def print_packet(direction, packet_type, details=""):
    """Print packet transmission details"""
    arrow = "→" if direction == "out" else "←"
    color = Colors.BLUE if direction == "out" else Colors.YELLOW
    timestamp = datetime.now().strftime("%H:%M:%S.%f")[:-3]
    print(f"{color}[{timestamp}] {arrow} {packet_type:15} {details}{Colors.ENDC}")


def print_layer(layer_name, description):
    """Print network stack layer processing"""
    print(f"{Colors.CYAN}  [{layer_name}]{Colors.ENDC} {description}")


class NoproMessage:
    """
    NOPRO protocol message structure

    Format:
    - Message type (1 byte): 0x00 = NULL-QUERY, 0x01 = ECHO-VOID
    - Sequence number (4 bytes): Packet counter
    - Timestamp (8 bytes): Nanoseconds since epoch
    - Reserved (19 bytes): Must be zero
    - Checksum (4 bytes): CRC32 of entire message

    Total: 36 bytes of overhead to communicate nothing
    """

    MESSAGE_TYPES = {
        0x00: "NULL-QUERY",
        0x01: "ECHO-VOID",
        0x02: "PING-NULL",
        0x03: "SYNC-NOTHING",
        0x04: "STATUS-IDLE"
    }

    def __init__(self, msg_type=0x00, seq_num=0):
        self.msg_type = msg_type
        self.seq_num = seq_num
        self.timestamp = time.time_ns()
        self.reserved = b'\x00' * 19

    def pack(self):
        """Serialize message to bytes"""
        # Pack without checksum first
        msg = struct.pack('!BIQ19s',
                         self.msg_type,
                         self.seq_num,
                         self.timestamp,
                         self.reserved)

        # Calculate checksum
        checksum = self.calculate_checksum(msg)

        # Add checksum
        return msg + struct.pack('!I', checksum)

    @staticmethod
    def unpack(data):
        """Deserialize message from bytes"""
        if len(data) != 36:
            raise ValueError(f"Invalid message size: {len(data)} (expected 36)")

        msg_type, seq_num, timestamp, reserved, checksum = struct.unpack('!BIQ19sI', data)

        # Verify checksum
        msg_without_checksum = data[:32]
        expected_checksum = NoproMessage.calculate_checksum(msg_without_checksum)
        if checksum != expected_checksum:
            raise ValueError(f"Checksum mismatch: {checksum:08x} != {expected_checksum:08x}")

        msg = NoproMessage(msg_type, seq_num)
        msg.timestamp = timestamp
        return msg

    @staticmethod
    def calculate_checksum(data):
        """Calculate CRC32 checksum"""
        import zlib
        return zlib.crc32(data) & 0xffffffff

    def __str__(self):
        msg_type_name = self.MESSAGE_TYPES.get(self.msg_type, f"UNKNOWN({self.msg_type:02x})")
        ts = self.timestamp / 1e9
        return (f"NOPRO[type={msg_type_name}, seq={self.seq_num}, "
                f"time={ts:.9f}]")


def calculate_overhead():
    """Calculate and display network overhead for UDP NOP"""
    print_header("UDP NOP Network Overhead Calculation")

    # Ethernet frame overhead
    ethernet_header = 14
    fcs = 4
    preamble_sfd = 8
    ifg = 12

    # IP header (minimum, no options)
    ip_header = 20

    # UDP header
    udp_header = 8

    # NOPRO message
    nopro_payload = 36

    # Calculate per-packet overhead
    packet_overhead = ethernet_header + ip_header + udp_header + fcs
    wire_overhead = packet_overhead + preamble_sfd + ifg
    total_packet_size = wire_overhead + nopro_payload

    print_info("Ethernet header", f"{ethernet_header} bytes")
    print_info("IP header (no options)", f"{ip_header} bytes")
    print_info("UDP header", f"{udp_header} bytes")
    print_info("Frame Check Sequence", f"{fcs} bytes")
    print_info("Headers total", f"{packet_overhead} bytes")
    print()
    print_info("NOPRO message payload", f"{nopro_payload} bytes")
    print_info("Application data", f"{Colors.RED}0 bytes{Colors.ENDC}")
    print()
    print_info("Preamble + SFD", f"{preamble_sfd} bytes")
    print_info("Inter-frame gap", f"{ifg} bytes")
    print_info("Total on-wire per packet", f"{total_packet_size} bytes")
    print()

    # Request + Response
    request_overhead = total_packet_size
    response_overhead = total_packet_size
    total_overhead = request_overhead + response_overhead

    print_info("Request packet", f"{request_overhead} bytes")
    print_info("Response packet", f"{response_overhead} bytes")
    print_info("Total exchange overhead", f"{total_overhead} bytes")
    print()
    print_info("Overhead:data ratio", f"{Colors.RED}∞:0 (infinite overhead){Colors.ENDC}")
    print()

    # Compare to TCP
    tcp_overhead = 462  # From tcp_nop.py
    udp_savings = tcp_overhead - total_overhead
    udp_percentage = (total_overhead / tcp_overhead) * 100

    print_info("TCP NOP overhead", f"{tcp_overhead} bytes")
    print_info("UDP NOP overhead", f"{total_overhead} bytes")
    print_info("Savings vs TCP", f"{udp_savings} bytes ({100-udp_percentage:.1f}% reduction)")
    print()
    print(f"{Colors.YELLOW}UDP is more efficient at doing nothing!{Colors.ENDC}")
    print(f"{Colors.CYAN}But still cannot achieve true 'no operation'.{Colors.ENDC}")


def demonstrate_udp_simplicity():
    """Demonstrate UDP's lack of state machine"""
    print_header("UDP 'Stateless' Protocol (Sort Of)")

    print(f"{Colors.BOLD}No Connection State Machine:{Colors.ENDC}\n")
    print("Unlike TCP, UDP has no connection states:")
    print(f"{Colors.GREEN}✓ No SYN/SYN-ACK/ACK handshake{Colors.ENDC}")
    print(f"{Colors.GREEN}✓ No ESTABLISHED state{Colors.ENDC}")
    print(f"{Colors.GREEN}✓ No FIN/ACK termination{Colors.ENDC}")
    print(f"{Colors.GREEN}✓ No TIME_WAIT period{Colors.ENDC}")

    print(f"\n{Colors.BOLD}BUT... State Still Exists:{Colors.ENDC}\n")
    print(f"{Colors.RED}✗ NAT still creates translation table entries{Colors.ENDC}")
    print(f"{Colors.RED}✗ Firewall still tracks 'sessions'{Colors.ENDC}")
    print(f"{Colors.RED}✗ Socket still occupies ephemeral port{Colors.ENDC}")
    print(f"{Colors.RED}✗ OS still allocates socket buffers{Colors.ENDC}")

    print(f"\n{Colors.BOLD}UDP Packet Flow:{Colors.ENDC}\n")
    print("1. Client sends UDP datagram")
    print("   - Ephemeral port allocated")
    print("   - NAT entry created")
    print("   - Firewall allows outbound")
    print()
    print("2. Server receives UDP datagram")
    print("   - No acknowledgment required")
    print("   - Process or discard")
    print()
    print("3. Server sends UDP response")
    print("   - Firewall allows return traffic (stateful)")
    print("   - NAT translates destination")
    print()
    print("4. Client receives response")
    print("   - No acknowledgment sent")
    print("   - Transaction complete")
    print()
    print(f"{Colors.YELLOW}Total packets: 2 (vs 7 for TCP){Colors.ENDC}")


def demonstrate_stack_traversal():
    """Demonstrate network stack traversal for UDP"""
    print_header("Network Stack Traversal (UDP)")

    print(f"{Colors.BOLD}OUTBOUND PATH (Sender):{Colors.ENDC}")
    print_layer("Application", "sendto() system call with NOPRO message")
    print_layer("Transport", "UDP header added, checksum calculated, no state")
    print_layer("Network", "IP header added, routing lookup, TTL=64")
    print_layer("Link", "ARP resolution (if needed), Ethernet frame constructed")
    print_layer("Physical", "Packet serialized to electrical/optical signals")

    print(f"\n{Colors.BOLD}NETWORK PATH (Each Router/Switch):{Colors.ENDC}")
    print_layer("Physical", "Signal reception and clock recovery")
    print_layer("Link", "Frame validation, FCS check, MAC lookup")
    print_layer("Network", "IP header parsing, TTL decrement, routing decision")
    print_layer("Link", "New frame constructed for next hop")
    print_layer("Physical", "Signal retransmission")
    print(f"{Colors.CYAN}  Note: Same as TCP - protocol-agnostic{Colors.ENDC}")

    print(f"\n{Colors.BOLD}INBOUND PATH (Receiver):{Colors.ENDC}")
    print_layer("Physical", "Signal reception")
    print_layer("Link", "Frame validation, destination MAC check")
    print_layer("Network", "IP checksum validation, destination IP check")
    print_layer("Transport", "UDP checksum validation, port demultiplexing")
    print_layer("Application", "recvfrom() receives NOPRO message, does nothing")


def demonstrate_nat_firewall_state():
    """Demonstrate NAT and firewall state for UDP"""
    print_header("NAT and Firewall State (UDP)")

    print(f"{Colors.BOLD}NAT Translation Table Entry:{Colors.ENDC}\n")
    nat_entry = {
        "internal_ip": "192.168.1.100",
        "internal_port": "54321",
        "external_ip": "198.51.100.1",
        "external_port": "54321",
        "destination_ip": "203.0.113.5",
        "destination_port": "8000",
        "protocol": "UDP",
        "timeout": "60 seconds (idle timeout)",
        "created": datetime.now().isoformat(),
        "last_packet": datetime.now().isoformat(),
        "bytes_transferred": "78 (request + response)",
        "packets": "2"
    }

    for key, value in nat_entry.items():
        print_info(key, value)

    print(f"\n{Colors.YELLOW}Note: NAT entry destroyed after 60s of inactivity{Colors.ENDC}")
    print(f"{Colors.YELLOW}Sending more packets refreshes the timeout{Colors.ENDC}")

    print(f"\n{Colors.BOLD}Firewall State Table Entry:{Colors.ENDC}\n")
    fw_entry = {
        "flow_id": "0x12345678",
        "state": "NEW → (IMPLIED ESTABLISHED)",
        "rule_matched": "Allow outbound UDP",
        "return_traffic": "Allowed (stateful firewall)",
        "timeout": "60 seconds",
        "bytes": "78 (headers + payload)",
        "action": "ACCEPT"
    }

    for key, value in fw_entry.items():
        print_info(key, value)

    print(f"\n{Colors.BOLD}UDP 'Stateless' Myth:{Colors.ENDC}\n")
    print(f"{Colors.CYAN}While UDP itself is stateless, middle boxes are not:{Colors.ENDC}")
    print(f"- NAT creates 5-tuple mapping (src IP/port, dst IP/port, protocol)")
    print(f"- Firewall tracks UDP 'sessions' for return traffic")
    print(f"- Both consume memory and CPU")
    print(f"- Both create forensic evidence")


def demonstrate_timing_channels():
    """Demonstrate timing channel opportunities in UDP"""
    print_header("Timing Channels and Covert Communication (UDP)")

    print(f"{Colors.BOLD}Timing-Based Covert Channels:{Colors.ENDC}\n")

    print(f"{Colors.YELLOW}1. Inter-packet delay encoding:{Colors.ENDC}")
    print("   - '0' bit: Send packet after 100ms delay")
    print("   - '1' bit: Send packet after 200ms delay")
    print("   - Bandwidth: ~10 bps")
    print("   - Detection: Requires timing analysis")

    print(f"\n{Colors.YELLOW}2. Packet rate modulation:{Colors.ENDC}")
    print("   - Baseline: 10 packets/sec")
    print("   - '0' bit: 10 packets/sec")
    print("   - '1' bit: 20 packets/sec")
    print("   - Bandwidth: 1 bps (averaged)")
    print("   - Detection: Statistical analysis")

    print(f"\n{Colors.BOLD}Storage-Based Covert Channels:{Colors.ENDC}\n")

    print(f"{Colors.YELLOW}3. IP ID field:{Colors.ENDC}")
    print("   - 16-bit identification field in IP header")
    print("   - Can encode 2 bytes per packet")
    print("   - Bandwidth: 16 bps @ 1 packet/sec")
    print("   - Detection: IP ID sequence analysis")

    print(f"\n{Colors.YELLOW}4. UDP source port:{Colors.ENDC}")
    print("   - Source port can encode data")
    print("   - Range: 1024-65535 (ephemeral range)")
    print("   - Encoding: Port number encodes message")
    print("   - Bandwidth: ~16 bps per packet")
    print("   - Detection: Port selection pattern analysis")

    print(f"\n{Colors.YELLOW}5. NOPRO reserved field:{Colors.ENDC}")
    print("   - 19 bytes of 'reserved' space")
    print("   - Specification says must be zero")
    print("   - Covert use: Embed 152 bits")
    print("   - Bandwidth: 152 bps @ 1 packet/sec")
    print("   - Detection: Trivial (non-zero reserved)")

    print(f"\n{Colors.BOLD}UDP Advantages for Covert Channels:{Colors.ENDC}\n")
    print(f"{Colors.GREEN}✓ No connection setup (less conspicuous){Colors.ENDC}")
    print(f"{Colors.GREEN}✓ Can change source port each packet{Colors.ENDC}")
    print(f"{Colors.GREEN}✓ No sequence numbers to correlate{Colors.ENDC}")
    print(f"{Colors.GREEN}✓ Faster transmission (no ACKs){Colors.ENDC}")


def demonstrate_energy_cost():
    """Calculate and display energy cost of UDP NOP"""
    print_header("Energy Cost of UDP NOP")

    # Energy per packet (microjoules)
    nic_tx = 127.0
    nic_rx = 52.0
    network_hop = 0.6
    hops = 5

    packets_sent = 1
    packets_received = 1
    total_packets = 2

    energy_tx = packets_sent * nic_tx
    energy_rx = packets_received * nic_rx
    energy_network = total_packets * network_hop * hops
    total_energy = energy_tx + energy_rx + energy_network

    print_info("Energy per TX packet (NIC)", f"{nic_tx} μJ")
    print_info("Energy per RX packet (NIC)", f"{nic_rx} μJ")
    print_info("Energy per hop per packet", f"{network_hop} μJ")
    print_info("Average network hops", f"{hops}")
    print()
    print_info("Packets sent", f"{packets_sent}")
    print_info("Packets received", f"{packets_received}")
    print_info("Total packets", f"{total_packets}")
    print()
    print_info("Transmission energy", f"{energy_tx:.1f} μJ")
    print_info("Reception energy", f"{energy_rx:.1f} μJ")
    print_info("Network routing energy", f"{energy_network:.1f} μJ")
    print_info("Total energy per UDP NOP", f"{total_energy:.1f} μJ")
    print()

    # Compare to TCP
    tcp_energy = 670.0  # From tcp_nop.py
    udp_savings = tcp_energy - total_energy
    udp_percentage = (total_energy / tcp_energy) * 100

    print_info("TCP NOP energy", f"{tcp_energy:.1f} μJ")
    print_info("UDP NOP energy", f"{total_energy:.1f} μJ")
    print_info("Energy savings vs TCP", f"{udp_savings:.1f} μJ ({100-udp_percentage:.1f}% reduction)")
    print()

    # Scale up
    million = 1_000_000
    billion = 1_000_000_000

    energy_million = total_energy * million / 1_000_000  # Convert to Joules
    energy_billion = total_energy * billion / 1_000_000

    print_info("Energy for 1M UDP NOPs", f"{energy_million:.2f} J")
    print_info("Energy for 1B UDP NOPs", f"{energy_billion:.2f} kJ")
    print()

    # Environmental context
    print_info("Equivalent (1B packets)", f"Heat {energy_billion/4184:.2f}g water by 1°C")


def udp_nop_client(host='127.0.0.1', port=8000, msg_type=0x00, seq_num=0,
                   timeout=2.0, verbose=True):
    """
    Send a UDP NOP packet and wait for response.

    Args:
        host: Target host
        port: Target port
        msg_type: NOPRO message type
        seq_num: Sequence number
        timeout: Response timeout in seconds
        verbose: Print detailed output

    Returns:
        dict: Operation statistics
    """
    if verbose:
        print_header(f"UDP NOP Client → {host}:{port}")

    stats = {
        'start_time': time.time(),
        'end_time': None,
        'request_sent': False,
        'response_received': False,
        'rtt': None,
        'error': None
    }

    sock = None
    try:
        # Create UDP socket
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.settimeout(timeout)

        if verbose:
            print_info("Socket created", f"fd={sock.fileno()}, type=DGRAM")
            print_info("Local address", f"{sock.getsockname()}")
            print()

        # Create NOPRO message
        msg = NoproMessage(msg_type, seq_num)

        if verbose:
            print_info("Message created", str(msg))
            print_info("Message size", f"{len(msg.pack())} bytes")
            print_info("Application data", f"{Colors.RED}0 bytes{Colors.ENDC}")
            print()

        # Send packet
        packet_data = msg.pack()

        if verbose:
            print(f"{Colors.BOLD}Sending UDP datagram...{Colors.ENDC}\n")
            print_packet("out", "UDP", f"{len(packet_data)} bytes, ephemeral port allocated")

        send_time = time.time()
        sock.sendto(packet_data, (host, port))
        stats['request_sent'] = True
        stats['send_time'] = send_time

        if verbose:
            print_info("Packet sent", f"{len(packet_data)} bytes")
            print_info("Local address", f"{sock.getsockname()}")
            print()

        # Wait for response
        if verbose:
            print(f"{Colors.BOLD}Waiting for response (timeout={timeout}s)...{Colors.ENDC}\n")

        try:
            data, server_addr = sock.recvfrom(1024)
            receive_time = time.time()
            stats['response_received'] = True
            stats['receive_time'] = receive_time
            stats['rtt'] = receive_time - send_time

            if verbose:
                print_packet("in", "UDP", f"{len(data)} bytes from {server_addr}")
                print()

            # Parse response
            response_msg = NoproMessage.unpack(data)

            if verbose:
                print_info("Response received", str(response_msg))
                print_info("Round-trip time", f"{stats['rtt']*1000:.3f} ms")
                print_info("Response valid", f"{Colors.GREEN}Yes{Colors.ENDC}")
                print_info("Application effect", f"{Colors.RED}None{Colors.ENDC}")
                print()

        except socket.timeout:
            stats['error'] = "Timeout waiting for response"
            if verbose:
                print(f"{Colors.RED}Timeout: No response received{Colors.ENDC}")
                print(f"{Colors.YELLOW}The packet was still sent and consumed resources.{Colors.ENDC}")

    except Exception as e:
        stats['error'] = str(e)
        if verbose:
            print(f"{Colors.RED}Error: {e}{Colors.ENDC}")
    finally:
        if sock:
            sock.close()
        stats['end_time'] = time.time()
        stats['total_time'] = stats['end_time'] - stats['start_time']

    return stats


def udp_nop_server(host='127.0.0.1', port=8000, verbose=True):
    """
    Run a UDP NOP server: receive packets, send response, do nothing.

    Args:
        host: Bind address
        port: Bind port
        verbose: Print detailed output
    """
    if verbose:
        print_header(f"UDP NOP Server @ {host}:{port}")

    sock = None
    try:
        # Create UDP socket
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.bind((host, port))

        if verbose:
            print_info("Server listening", f"{host}:{port}")
            print_info("Protocol", "UDP (connectionless)")
            print_info("Waiting for packets", "Press Ctrl+C to stop")
            print()

        packet_count = 0
        while True:
            if verbose and packet_count == 0:
                print(f"{Colors.BOLD}Waiting for UDP datagrams...{Colors.ENDC}\n")

            # Receive packet
            data, client_addr = sock.recvfrom(1024)
            receive_time = time.time()
            packet_count += 1

            if verbose:
                print_packet("in", "UDP", f"{len(data)} bytes from {client_addr}")

            # Parse NOPRO message
            try:
                msg = NoproMessage.unpack(data)

                if verbose:
                    print_info("Message received", str(msg))
                    print_info("Client address", f"{client_addr}")
                    print()

                # Create response (same type, same sequence number)
                response = NoproMessage(msg.msg_type, msg.seq_num)
                response_data = response.pack()

                # Send response
                if verbose:
                    print_packet("out", "UDP", f"{len(response_data)} bytes to {client_addr}")

                sock.sendto(response_data, client_addr)

                if verbose:
                    print_info("Response sent", str(response))
                    print_info("Application effect", f"{Colors.RED}None{Colors.ENDC}")
                    print()
                    print(f"{Colors.BOLD}{'='*70}{Colors.ENDC}\n")

            except ValueError as e:
                if verbose:
                    print(f"{Colors.RED}Invalid NOPRO message: {e}{Colors.ENDC}")
                    print(f"{Colors.YELLOW}Ignoring packet...{Colors.ENDC}\n")

    except KeyboardInterrupt:
        if verbose:
            print(f"\n{Colors.YELLOW}Server shutting down...{Colors.ENDC}")
            print_info("Total packets processed", f"{packet_count}")
    except Exception as e:
        print(f"{Colors.RED}Server error: {e}{Colors.ENDC}")
    finally:
        if sock:
            sock.close()
            if verbose:
                print_info("Server socket closed", "")


def main():
    """Main function"""
    if len(sys.argv) > 1 and sys.argv[1] == 'server':
        # Run as server
        host = sys.argv[2] if len(sys.argv) > 2 else '127.0.0.1'
        port = int(sys.argv[3]) if len(sys.argv) > 3 else 8000
        udp_nop_server(host, port)
    else:
        # Run demonstrations and client
        calculate_overhead()
        demonstrate_udp_simplicity()
        demonstrate_stack_traversal()
        demonstrate_nat_firewall_state()
        demonstrate_timing_channels()
        demonstrate_energy_cost()

        # Try to send packet
        print_header("Attempting UDP NOP Exchange")
        print(f"{Colors.YELLOW}Note: This will timeout if no server is running.{Colors.ENDC}")
        print(f"{Colors.YELLOW}Run '{sys.argv[0]} server' in another terminal to start a server.{Colors.ENDC}")
        print()

        stats = udp_nop_client(verbose=True)

        print_header("Operation Statistics")
        print_info("Total duration", f"{stats['total_time']*1000:.3f} ms")
        print_info("Request sent", f"{stats['request_sent']}")
        print_info("Response received", f"{stats['response_received']}")
        if stats.get('rtt'):
            print_info("Round-trip time", f"{stats['rtt']*1000:.3f} ms")
        if stats.get('error'):
            print_info("Error", f"{Colors.RED}{stats['error']}{Colors.ENDC}")
        print()

        print_header("Conclusion")
        print(f"{Colors.BOLD}UDP NOP Summary:{Colors.ENDC}\n")
        print(f"- Minimum {Colors.YELLOW}2 packets{Colors.ENDC} transmitted (vs 7 for TCP)")
        print(f"- Minimum {Colors.YELLOW}156 bytes{Colors.ENDC} consumed on wire (vs 462 for TCP)")
        print(f"- Application data transferred: {Colors.RED}{Colors.BOLD}0 bytes{Colors.ENDC}")
        print(f"- NAT and firewall entries: {Colors.YELLOW}Created{Colors.ENDC}")
        print(f"- Energy consumed: {Colors.YELLOW}~185 μJ{Colors.ENDC} (vs 670 for TCP)")
        print(f"- Forensic evidence: {Colors.YELLOW}Logged in multiple systems{Colors.ENDC}")
        print()
        print(f"{Colors.GREEN}UDP is more efficient than TCP at doing nothing.{Colors.ENDC}")
        print(f"{Colors.CYAN}But you still cannot 'do nothing' over UDP.{Colors.ENDC}")
        print(f"{Colors.CYAN}Even the lightweight protocol has unavoidable overhead.{Colors.ENDC}")


if __name__ == '__main__':
    main()
