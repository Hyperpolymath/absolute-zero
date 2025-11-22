#!/usr/bin/env python3
"""
TCP NOP - TCP Connection That Exchanges No Data

This script demonstrates a TCP connection that traverses the entire network stack,
establishes a full connection with three-way handshake, maintains state, and then
cleanly terminates - all without exchanging any application data.

Despite transferring zero application bytes, this operation:
- Sends 7 packets (SYN, SYN-ACK, ACK, FIN, ACK, FIN, ACK)
- Consumes ~462 bytes of bandwidth (minimum, without options)
- Creates NAT and firewall state entries
- Occupies ephemeral ports
- Consumes CPU cycles and memory
- Leaves forensic evidence in logs
- Expends measurable energy

This is the network equivalent of executing a NOP instruction that requires
a complex state machine and resource allocation.
"""

import socket
import time
import sys
import struct
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


def calculate_overhead():
    """Calculate and display network overhead for TCP NOP"""
    print_header("TCP NOP Network Overhead Calculation")

    # Ethernet frame overhead
    ethernet_header = 14
    fcs = 4
    preamble_sfd = 8
    ifg = 12

    # IP header (minimum, no options)
    ip_header = 20

    # TCP header (minimum, no options)
    tcp_header = 20

    # Calculate per-packet overhead
    packet_overhead = ethernet_header + ip_header + tcp_header + fcs
    wire_overhead = packet_overhead + preamble_sfd + ifg

    print_info("Ethernet header", f"{ethernet_header} bytes")
    print_info("IP header (no options)", f"{ip_header} bytes")
    print_info("TCP header (no options)", f"{tcp_header} bytes")
    print_info("Frame Check Sequence", f"{fcs} bytes")
    print_info("Packet overhead (Layer 2-4)", f"{packet_overhead} bytes")
    print()
    print_info("Preamble + SFD", f"{preamble_sfd} bytes")
    print_info("Inter-frame gap", f"{ifg} bytes")
    print_info("Total on-wire per packet", f"{wire_overhead} bytes")
    print()

    # Three-way handshake
    handshake_packets = 3
    handshake_overhead = handshake_packets * wire_overhead

    # Four-way termination
    termination_packets = 4
    termination_overhead = termination_packets * wire_overhead

    # Total
    total_packets = handshake_packets + termination_packets
    total_overhead = total_packets * wire_overhead

    print_info("Handshake packets (SYN, SYN-ACK, ACK)", f"{handshake_packets}")
    print_info("Handshake overhead", f"{handshake_overhead} bytes")
    print_info("Termination packets (FIN, ACK, FIN, ACK)", f"{termination_packets}")
    print_info("Termination overhead", f"{termination_overhead} bytes")
    print()
    print_info("Total packets transmitted", f"{total_packets}")
    print_info("Total bandwidth consumed", f"{total_overhead} bytes")
    print_info("Application data transferred", f"{Colors.RED}0 bytes{Colors.ENDC}")
    print()
    print_info("Efficiency", f"{Colors.RED}0% (overhead:data ratio = ∞:0){Colors.ENDC}")


def demonstrate_tcp_states():
    """Demonstrate TCP state machine traversal"""
    print_header("TCP State Machine Traversal")

    states = [
        ("CLOSED", "No connection exists"),
        ("SYN_SENT", "SYN packet sent, waiting for SYN-ACK"),
        ("ESTABLISHED", "Connection established, can transfer data"),
        ("FIN_WAIT_1", "FIN packet sent, waiting for ACK"),
        ("FIN_WAIT_2", "FIN acknowledged, waiting for peer's FIN"),
        ("TIME_WAIT", "Both FINs exchanged, waiting 2*MSL"),
        ("CLOSED", "Connection fully terminated"),
    ]

    for i, (state, description) in enumerate(states, 1):
        color = Colors.GREEN if state == "ESTABLISHED" else Colors.YELLOW
        if state == "CLOSED":
            color = Colors.RED
        print(f"{color}{i}. {state:15}{Colors.ENDC} - {description}")

    print(f"\n{Colors.CYAN}Total state transitions: {len(states) - 1}{Colors.ENDC}")
    print(f"{Colors.CYAN}Time in ESTABLISHED state: ~microseconds{Colors.ENDC}")
    print(f"{Colors.CYAN}Time in TIME_WAIT state: ~60 seconds (2*MSL){Colors.ENDC}")


def demonstrate_stack_traversal():
    """Demonstrate network stack traversal"""
    print_header("Network Stack Traversal (Each Packet)")

    print(f"{Colors.BOLD}OUTBOUND PATH (Sender):{Colors.ENDC}")
    print_layer("Application", "socket.connect() system call")
    print_layer("Transport", "TCP header added, checksum calculated, state=SYN_SENT")
    print_layer("Network", "IP header added, routing lookup, TTL=64")
    print_layer("Link", "ARP resolution (if needed), Ethernet frame constructed")
    print_layer("Physical", "Packet serialized to electrical/optical signals")

    print(f"\n{Colors.BOLD}NETWORK PATH (Each Router/Switch):{Colors.ENDC}")
    print_layer("Physical", "Signal reception and clock recovery")
    print_layer("Link", "Frame validation, FCS check, MAC lookup")
    print_layer("Network", "IP header parsing, TTL decrement, routing decision")
    print_layer("Link", "New frame constructed for next hop")
    print_layer("Physical", "Signal retransmission")

    print(f"\n{Colors.BOLD}INBOUND PATH (Receiver):{Colors.ENDC}")
    print_layer("Physical", "Signal reception")
    print_layer("Link", "Frame validation, destination MAC check")
    print_layer("Network", "IP checksum validation, destination IP check")
    print_layer("Transport", "TCP checksum validation, state machine update")
    print_layer("Application", "accept() call returns socket - but no data to read")


def demonstrate_nat_firewall_state():
    """Demonstrate NAT and firewall state changes"""
    print_header("NAT and Firewall State Changes")

    print(f"{Colors.BOLD}NAT Translation Table Entry:{Colors.ENDC}\n")
    nat_entry = {
        "internal_ip": "192.168.1.100",
        "internal_port": "54321",
        "external_ip": "198.51.100.1",
        "external_port": "54321",
        "destination_ip": "203.0.113.5",
        "destination_port": "8000",
        "protocol": "TCP",
        "state": "ESTABLISHED",
        "timeout": "7200 seconds (2 hours)",
        "created": datetime.now().isoformat(),
        "bytes_transferred": "0",
        "packets": "7"
    }

    for key, value in nat_entry.items():
        print_info(key, value)

    print(f"\n{Colors.BOLD}Firewall State Table Entry:{Colors.ENDC}\n")
    fw_entry = {
        "connection_id": "0xABCD1234",
        "state": "ESTABLISHED → TIME_WAIT → CLOSED",
        "rule_matched": "Allow outbound TCP",
        "bytes": "0 (application data)",
        "overhead_bytes": "462 (headers only)",
        "duration": "~60 seconds (TIME_WAIT)",
        "action": "ACCEPT"
    }

    for key, value in fw_entry.items():
        print_info(key, value)

    print(f"\n{Colors.BOLD}Resource Consumption:{Colors.ENDC}\n")
    print_info("NAT table entry size", "~64 bytes")
    print_info("Firewall state entry size", "~128 bytes")
    print_info("Ephemeral port occupied", "Yes (60 seconds minimum)")
    print_info("Memory allocated", "~192 bytes total")
    print_info("CPU cycles consumed", "~10,000 cycles per packet")


def demonstrate_timing_channels():
    """Demonstrate timing channel opportunities"""
    print_header("Timing Channels and Side Effects")

    print(f"{Colors.BOLD}Observable Timing Information:{Colors.ENDC}\n")
    print_info("SYN transmission time", "Microsecond precision")
    print_info("SYN-ACK round-trip time (RTT)", "Network latency revealed")
    print_info("Connection establishment time", "Three-way handshake duration")
    print_info("Time to FIN", "Application-specific timing")
    print_info("TIME_WAIT duration", "OS fingerprinting (2*MSL varies)")

    print(f"\n{Colors.BOLD}Covert Channel Opportunities:{Colors.ENDC}\n")
    print(f"{Colors.YELLOW}1. Connection timing:{Colors.ENDC}")
    print("   - Encode '0' bit: Connect after 100ms delay")
    print("   - Encode '1' bit: Connect after 200ms delay")
    print("   - Bandwidth: ~10 bits/sec")

    print(f"\n{Colors.YELLOW}2. TCP sequence number LSBs:{Colors.ENDC}")
    print("   - ISN normally random 32-bit value")
    print("   - Use lower 8 bits to encode data")
    print("   - Bandwidth: 8 bits per connection")

    print(f"\n{Colors.YELLOW}3. TCP window size:{Colors.ENDC}")
    print("   - Advertised window size can encode data")
    print("   - Range: 0-65535 (16 bits)")
    print("   - Low detectability")

    print(f"\n{Colors.YELLOW}4. Connection rate modulation:{Colors.ENDC}")
    print("   - Baseline: 10 connections/sec")
    print("   - Encode '0': 10 conn/sec, '1': 20 conn/sec")
    print("   - Bandwidth: 1 bit/sec (averaged)")


def demonstrate_energy_cost():
    """Calculate and display energy cost"""
    print_header("Energy Cost of TCP NOP")

    # Energy per packet (microjoules)
    nic_tx = 127.0
    nic_rx = 52.0
    network_hop = 0.6  # Average per switch/router
    hops = 5

    packets_sent = 4  # SYN, ACK, FIN, ACK from client
    packets_received = 3  # SYN-ACK, ACK, FIN from server
    total_packets = 7

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
    print_info("Total packets in conversation", f"{total_packets}")
    print()
    print_info("Transmission energy", f"{energy_tx:.1f} μJ")
    print_info("Reception energy", f"{energy_rx:.1f} μJ")
    print_info("Network routing energy", f"{energy_network:.1f} μJ")
    print_info("Total energy per TCP NOP", f"{total_energy:.1f} μJ")
    print()

    # Scale up
    million = 1_000_000
    billion = 1_000_000_000

    energy_million = total_energy * million / 1_000_000  # Convert to Joules
    energy_billion = total_energy * billion / 1_000_000

    print_info("Energy for 1 million TCP NOPs", f"{energy_million:.2f} J")
    print_info("Energy for 1 billion TCP NOPs", f"{energy_billion:.2f} kJ")
    print()

    # Environmental context
    water_heating = energy_billion / 4184  # J to heat 1g water by 1°C
    print_info("Equivalent", f"Heat {water_heating:.2f}g water by 1°C")

    # Annual impact
    connections_per_sec = 1000
    connections_per_year = connections_per_sec * 60 * 60 * 24 * 365
    annual_energy = connections_per_year * total_energy / 1_000_000  # Joules
    annual_kwh = annual_energy / 3_600_000
    co2_kg = annual_kwh * 0.5  # Rough estimate, varies by grid

    print()
    print_info("At 1000 TCP NOPs/sec:", "")
    print_info("  Annual energy", f"{annual_kwh:.2f} kWh")
    print_info("  Annual CO2 emissions", f"{co2_kg:.2f} kg CO2e")
    print_info("  Annual cost (@$0.10/kWh)", f"${annual_kwh * 0.10:.2f}")


def tcp_nop_client(host='127.0.0.1', port=8000, verbose=True):
    """
    Perform a TCP NOP operation: establish connection, transfer nothing, close.

    Args:
        host: Target host
        port: Target port
        verbose: Print detailed output

    Returns:
        dict: Connection statistics
    """
    if verbose:
        print_header(f"TCP NOP Client → {host}:{port}")

    stats = {
        'start_time': time.time(),
        'end_time': None,
        'connected': False,
        'error': None
    }

    sock = None
    try:
        # Create socket
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)

        if verbose:
            print_info("Socket created", f"fd={sock.fileno()}")
            print_info("Local address (before connect)", f"{sock.getsockname()}")
            print()

        # Get socket options before connection
        if verbose:
            try:
                tcp_nodelay = sock.getsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY)
                print_info("TCP_NODELAY", f"{bool(tcp_nodelay)}")
            except:
                pass

        # Connect (triggers three-way handshake)
        if verbose:
            print(f"{Colors.BOLD}Initiating three-way handshake...{Colors.ENDC}\n")
            print_packet("out", "SYN", f"seq=X, local ephemeral port allocated")

        connect_start = time.time()
        sock.connect((host, port))
        connect_time = time.time() - connect_start

        stats['connected'] = True
        stats['connect_time'] = connect_time

        if verbose:
            print_packet("in", "SYN-ACK", f"seq=Y, ack=X+1")
            print_packet("out", "ACK", f"seq=X+1, ack=Y+1")
            print()
            print_info("Connection established", f"{connect_time*1000:.3f} ms")
            print_info("Local address", f"{sock.getsockname()}")
            print_info("Remote address", f"{sock.getpeername()}")
            print()
            print(f"{Colors.GREEN}STATE: ESTABLISHED{Colors.ENDC}")
            print(f"{Colors.CYAN}Application data transferred: {Colors.RED}0 bytes{Colors.ENDC}")
            print()

        # Intentionally do NOT send or receive any data
        # This is the "NOP" - connection exists but does nothing

        # Optional: Brief pause to demonstrate ESTABLISHED state
        time.sleep(0.01)  # 10ms in ESTABLISHED state

        # Close connection (triggers four-way termination)
        if verbose:
            print(f"{Colors.BOLD}Initiating four-way termination...{Colors.ENDC}\n")
            print_packet("out", "FIN", f"seq=X+1")

        close_start = time.time()
        sock.close()
        close_time = time.time() - close_start

        stats['close_time'] = close_time

        if verbose:
            print_packet("in", "ACK", f"ack=X+2")
            print_packet("in", "FIN", f"seq=Y+1")
            print_packet("out", "ACK", f"ack=Y+2")
            print()
            print_info("Connection closed", f"{close_time*1000:.3f} ms")
            print(f"{Colors.YELLOW}STATE: TIME_WAIT (will last ~60 seconds){Colors.ENDC}")
            print()

    except ConnectionRefusedError:
        stats['error'] = "Connection refused (no server listening)"
        if verbose:
            print(f"{Colors.RED}Error: Connection refused{Colors.ENDC}")
            print(f"{Colors.YELLOW}This is expected if no server is running.{Colors.ENDC}")
            print(f"{Colors.YELLOW}The client still sent SYN packets and consumed resources.{Colors.ENDC}")
    except Exception as e:
        stats['error'] = str(e)
        if verbose:
            print(f"{Colors.RED}Error: {e}{Colors.ENDC}")
    finally:
        if sock and stats['connected']:
            try:
                sock.close()
            except:
                pass
        stats['end_time'] = time.time()
        stats['total_time'] = stats['end_time'] - stats['start_time']

    return stats


def tcp_nop_server(host='127.0.0.1', port=8000, verbose=True):
    """
    Run a TCP NOP server: accept connections, transfer nothing, close.

    Args:
        host: Bind address
        port: Bind port
        verbose: Print detailed output
    """
    if verbose:
        print_header(f"TCP NOP Server @ {host}:{port}")

    server_sock = None
    try:
        # Create server socket
        server_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        server_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        server_sock.bind((host, port))
        server_sock.listen(1)

        if verbose:
            print_info("Server listening", f"{host}:{port}")
            print_info("Waiting for connections", "Press Ctrl+C to stop")
            print()

        while True:
            if verbose:
                print(f"{Colors.BOLD}Waiting for client...{Colors.ENDC}\n")

            # Accept connection (completes three-way handshake)
            client_sock, client_addr = server_sock.accept()

            if verbose:
                print_packet("in", "SYN", f"from {client_addr}")
                print_packet("out", "SYN-ACK", "seq=Y, ack=X+1")
                print_packet("in", "ACK", "seq=X+1, ack=Y+1")
                print()
                print_info("Client connected", f"{client_addr}")
                print(f"{Colors.GREEN}STATE: ESTABLISHED{Colors.ENDC}")
                print()

            # Intentionally do NOT send or receive any data
            # This is the server-side "NOP"

            # Wait for client to close
            # recv() will return empty when client closes
            try:
                data = client_sock.recv(1024)
                if not data:
                    if verbose:
                        print(f"{Colors.CYAN}Client initiated close (FIN received){Colors.ENDC}")
            except:
                pass

            # Close our side
            if verbose:
                print_packet("in", "FIN", f"from {client_addr}")
                print_packet("out", "ACK", "ack=X+2")
                print_packet("out", "FIN", "seq=Y+1")
                print_packet("in", "ACK", "ack=Y+2")
                print()

            client_sock.close()

            if verbose:
                print_info("Connection closed", f"{client_addr}")
                print(f"{Colors.CYAN}Application data transferred: {Colors.RED}0 bytes{Colors.ENDC}")
                print()
                print(f"{Colors.BOLD}{'='*70}{Colors.ENDC}\n")

    except KeyboardInterrupt:
        if verbose:
            print(f"\n{Colors.YELLOW}Server shutting down...{Colors.ENDC}")
    except Exception as e:
        print(f"{Colors.RED}Server error: {e}{Colors.ENDC}")
    finally:
        if server_sock:
            server_sock.close()
            if verbose:
                print_info("Server socket closed", "")


def main():
    """Main function"""
    if len(sys.argv) > 1 and sys.argv[1] == 'server':
        # Run as server
        host = sys.argv[2] if len(sys.argv) > 2 else '127.0.0.1'
        port = int(sys.argv[3]) if len(sys.argv) > 3 else 8000
        tcp_nop_server(host, port)
    else:
        # Run demonstrations and client
        calculate_overhead()
        demonstrate_tcp_states()
        demonstrate_stack_traversal()
        demonstrate_nat_firewall_state()
        demonstrate_timing_channels()
        demonstrate_energy_cost()

        # Try to connect (will fail if no server, but that's okay)
        print_header("Attempting TCP NOP Connection")
        print(f"{Colors.YELLOW}Note: This will fail if no server is running.{Colors.ENDC}")
        print(f"{Colors.YELLOW}Run '{sys.argv[0]} server' in another terminal to start a server.{Colors.ENDC}")
        print()

        stats = tcp_nop_client(verbose=True)

        print_header("Connection Statistics")
        print_info("Total duration", f"{stats['total_time']*1000:.3f} ms")
        print_info("Connected", f"{stats['connected']}")
        if stats.get('connect_time'):
            print_info("Connect time", f"{stats['connect_time']*1000:.3f} ms")
        if stats.get('error'):
            print_info("Error", f"{Colors.RED}{stats['error']}{Colors.ENDC}")
        print()

        print_header("Conclusion")
        print(f"{Colors.BOLD}TCP NOP Summary:{Colors.ENDC}\n")
        print(f"- Minimum {Colors.YELLOW}7 packets{Colors.ENDC} transmitted")
        print(f"- Minimum {Colors.YELLOW}462 bytes{Colors.ENDC} consumed on wire")
        print(f"- Application data transferred: {Colors.RED}{Colors.BOLD}0 bytes{Colors.ENDC}")
        print(f"- NAT and firewall state entries: {Colors.YELLOW}Created and destroyed{Colors.ENDC}")
        print(f"- Energy consumed: {Colors.YELLOW}~670 μJ{Colors.ENDC}")
        print(f"- Forensic evidence: {Colors.YELLOW}Logged in multiple systems{Colors.ENDC}")
        print()
        print(f"{Colors.CYAN}You cannot 'do nothing' over TCP.{Colors.ENDC}")
        print(f"{Colors.CYAN}Every connection is an operation with measurable consequences.{Colors.ENDC}")


if __name__ == '__main__':
    main()
