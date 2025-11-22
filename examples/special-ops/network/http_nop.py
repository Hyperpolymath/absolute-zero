#!/usr/bin/env python3
"""
HTTP NOP - HTTP Request That Returns 204 No Content

This script demonstrates HTTP requests that traverse the entire network stack,
establish TCP connections, send HTTP headers, receive responses, but ultimately
deliver zero content to the application.

HTTP 204 No Content is the protocol's explicit way of saying "I successfully
did nothing." Yet this operation:
- Sends 7+ TCP packets (handshake + data + teardown)
- Sends HTTP request headers (~200-500 bytes)
- Receives HTTP response headers (~100-300 bytes)
- Consumes ~1000+ bytes of bandwidth total
- Creates NAT and firewall state entries
- Occupies ephemeral ports
- Consumes CPU cycles and memory
- Leaves forensic evidence in logs
- Expends measurable energy

This is the application-layer acknowledgment that "nothing happened" - but
getting to that acknowledgment requires substantial infrastructure.
"""

import socket
import time
import sys
from datetime import datetime
from http.server import HTTPServer, BaseHTTPRequestHandler
from urllib.parse import urlparse

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


def print_http_line(direction, line):
    """Print HTTP request/response line"""
    arrow = "→" if direction == "out" else "←"
    color = Colors.BLUE if direction == "out" else Colors.YELLOW
    print(f"{color}{arrow} {line}{Colors.ENDC}")


def demonstrate_http_204():
    """Explain HTTP 204 No Content"""
    print_header("HTTP 204 No Content - The Paradox")

    print(f"{Colors.BOLD}What is HTTP 204?{Colors.ENDC}\n")
    print("HTTP 204 No Content is a success status code that indicates:")
    print(f"{Colors.GREEN}✓ The request was successfully processed{Colors.ENDC}")
    print(f"{Colors.GREEN}✓ The server understood the request{Colors.ENDC}")
    print(f"{Colors.GREEN}✓ The operation completed without error{Colors.ENDC}")
    print(f"{Colors.RED}✗ No content is being returned in the response body{Colors.ENDC}")

    print(f"\n{Colors.BOLD}Common Use Cases:{Colors.ENDC}\n")
    print("1. DELETE requests - resource deleted, nothing to return")
    print("2. PUT requests - resource updated, no need to return it")
    print("3. Tracking pixels - browser loads, server logs, no display")
    print("4. Health checks - 'I'm alive' with no data payload")
    print("5. Fire-and-forget operations - acknowledged, no response needed")

    print(f"\n{Colors.BOLD}The Paradox:{Colors.ENDC}\n")
    print(f"{Colors.CYAN}To communicate 'no content', HTTP must:{Colors.ENDC}")
    print("- Establish a TCP connection (3-way handshake)")
    print("- Send HTTP request headers (method, path, host, etc.)")
    print("- Process request on server")
    print("- Send HTTP response headers (status, date, server, etc.)")
    print("- Close TCP connection (4-way termination)")
    print()
    print(f"{Colors.YELLOW}Result: Hundreds of bytes to say 'nothing to say'{Colors.ENDC}")


def calculate_overhead():
    """Calculate HTTP 204 overhead"""
    print_header("HTTP 204 Network Overhead Calculation")

    # TCP overhead (from tcp_nop.py)
    tcp_handshake = 3 * 66  # SYN, SYN-ACK, ACK
    tcp_teardown = 4 * 66   # FIN, ACK, FIN, ACK

    # HTTP request (typical)
    http_request_line = "DELETE /api/resource/123 HTTP/1.1\r\n"
    http_request_headers = """Host: example.com\r
User-Agent: Python HTTP-NOP/1.0\r
Accept: */*\r
Connection: close\r
\r
"""
    http_request = http_request_line + http_request_headers
    http_request_size = len(http_request.encode())

    # HTTP response (typical 204)
    http_response_line = "HTTP/1.1 204 No Content\r\n"
    http_response_headers = """Date: Sat, 22 Nov 2025 10:30:00 GMT\r
Server: Python HTTP-NOP/1.0\r
Connection: close\r
\r
"""
    http_response = http_response_line + http_response_headers
    http_response_size = len(http_response.encode())

    # IP + TCP headers for data packets
    ip_tcp_header = 20 + 20  # IP + TCP
    ethernet_overhead = 14 + 4 + 8 + 12  # Ethernet + FCS + Preamble + IFG

    # Request packet
    request_packet = ethernet_overhead + ip_tcp_header + http_request_size

    # Response packet
    response_packet = ethernet_overhead + ip_tcp_header + http_response_size

    # Total
    total_overhead = tcp_handshake + request_packet + response_packet + tcp_teardown

    print_info("TCP handshake (3 packets)", f"{tcp_handshake} bytes")
    print_info("HTTP request headers", f"{http_request_size} bytes")
    print_info("Request packet overhead", f"{ethernet_overhead + ip_tcp_header} bytes")
    print_info("Total request packet", f"{request_packet} bytes")
    print()
    print_info("HTTP response headers", f"{http_response_size} bytes")
    print_info("Response packet overhead", f"{ethernet_overhead + ip_tcp_header} bytes")
    print_info("Total response packet", f"{response_packet} bytes")
    print()
    print_info("TCP teardown (4 packets)", f"{tcp_teardown} bytes")
    print()
    print_info("Total packets", "9 (3 handshake + 2 data + 4 teardown)")
    print_info("Total bandwidth consumed", f"{total_overhead} bytes")
    print_info("HTTP response body", f"{Colors.RED}0 bytes (204 No Content){Colors.ENDC}")
    print()
    print_info("Efficiency", f"{Colors.RED}0% (all overhead, no content){Colors.ENDC}")


def demonstrate_http_layers():
    """Demonstrate HTTP layering on top of TCP/IP"""
    print_header("HTTP Over TCP/IP - Layer Upon Layer")

    print(f"{Colors.BOLD}Layer 7: Application (HTTP){Colors.ENDC}")
    print(f"  Request:  {Colors.BLUE}DELETE /api/resource/123 HTTP/1.1{Colors.ENDC}")
    print(f"  Response: {Colors.YELLOW}HTTP/1.1 204 No Content{Colors.ENDC}")
    print(f"  Overhead: ~200-400 bytes of headers")
    print(f"  Effect:   {Colors.RED}None (204 = No Content){Colors.ENDC}")
    print()

    print(f"{Colors.BOLD}Layer 4: Transport (TCP){Colors.ENDC}")
    print(f"  Connection: Three-way handshake")
    print(f"  Data transfer: HTTP request/response")
    print(f"  Termination: Four-way FIN exchange")
    print(f"  Overhead: 7 packets, ~462 bytes minimum")
    print()

    print(f"{Colors.BOLD}Layer 3: Network (IP){Colors.ENDC}")
    print(f"  Routing: Determines path through network")
    print(f"  Fragmentation: May split large HTTP headers")
    print(f"  Overhead: 20 bytes per packet")
    print()

    print(f"{Colors.BOLD}Layer 2: Link (Ethernet){Colors.ENDC}")
    print(f"  Framing: Encapsulates IP packets")
    print(f"  MAC addressing: Local delivery")
    print(f"  Overhead: 38 bytes per packet (header + FCS + preamble + IFG)")
    print()

    print(f"{Colors.BOLD}Layer 1: Physical{Colors.ENDC}")
    print(f"  Encoding: Electrical/optical signals")
    print(f"  Transmission: Actual wire/fiber transfer")
    print(f"  Energy: ~100 nJ per bit")


def demonstrate_http_state():
    """Demonstrate HTTP state despite being 'stateless'"""
    print_header("HTTP 'Stateless' Protocol State")

    print(f"{Colors.BOLD}HTTP is 'Stateless' (Application Layer):{Colors.ENDC}\n")
    print(f"{Colors.GREEN}✓ No session maintained between requests{Colors.ENDC}")
    print(f"{Colors.GREEN}✓ Each request independent{Colors.ENDC}")
    print(f"{Colors.GREEN}✓ Server doesn't remember previous requests{Colors.ENDC}")

    print(f"\n{Colors.BOLD}BUT State Exists Everywhere Else:{Colors.ENDC}\n")

    print(f"{Colors.YELLOW}TCP State:{Colors.ENDC}")
    print("  - Connection state machine (ESTABLISHED, etc.)")
    print("  - Sequence numbers and acknowledgments")
    print("  - Send/receive windows")
    print("  - Retransmission timers")

    print(f"\n{Colors.YELLOW}NAT State:{Colors.ENDC}")
    print("  - Translation table entry")
    print("  - Source IP/port → External IP/port mapping")
    print("  - Timeout: 2+ hours for established TCP")

    print(f"\n{Colors.YELLOW}Firewall State:{Colors.ENDC}")
    print("  - Connection tracking entry")
    print("  - Allow return HTTP response")
    print("  - Byte and packet counters")

    print(f"\n{Colors.YELLOW}Web Server State:{Colors.ENDC}")
    print("  - Active connection list")
    print("  - Socket buffer allocation")
    print("  - Request processing thread/process")
    print("  - Access logs")

    print(f"\n{Colors.YELLOW}Load Balancer State (if present):{Colors.ENDC}")
    print("  - Backend server selection")
    print("  - Session persistence (even for 204)")
    print("  - Health check status")

    print(f"\n{Colors.CYAN}HTTP may be stateless, but the infrastructure is not.{Colors.ENDC}")


def demonstrate_timing_channels():
    """Demonstrate timing channels in HTTP"""
    print_header("Timing Channels in HTTP 204")

    print(f"{Colors.BOLD}Observable Timing Information:{Colors.ENDC}\n")
    print_info("DNS resolution time", "Domain → IP lookup latency")
    print_info("TCP handshake RTT", "Network latency measurement")
    print_info("Request processing time", "Server-side execution time")
    print_info("Response time", "Total round-trip time")
    print_info("Connection close time", "Graceful shutdown duration")

    print(f"\n{Colors.BOLD}Covert Channels:{Colors.ENDC}\n")

    print(f"{Colors.YELLOW}1. Response timing covert channel:{Colors.ENDC}")
    print("   - Fast response (50ms): Encode '0' bit")
    print("   - Slow response (150ms): Encode '1' bit")
    print("   - Bandwidth: ~10 bps")
    print("   - Detection: Statistical timing analysis")

    print(f"\n{Colors.YELLOW}2. HTTP header field encoding:{Colors.ENDC}")
    print("   - Custom headers: X-Request-ID, X-Trace-ID")
    print("   - Encode data in header values")
    print("   - Bandwidth: ~100s of bytes per request")
    print("   - Detection: Header anomaly detection")

    print(f"\n{Colors.YELLOW}3. URL parameter encoding:{Colors.ENDC}")
    print("   - DELETE /api/resource/ENCODED_DATA")
    print("   - Use resource ID to encode information")
    print("   - Bandwidth: Limited by URL length (~2KB)")
    print("   - Detection: URL pattern analysis")

    print(f"\n{Colors.YELLOW}4. HTTP method variation:{Colors.ENDC}")
    print("   - DELETE: '0' bit")
    print("   - PUT: '1' bit")
    print("   - Both can return 204")
    print("   - Bandwidth: 1 bit per request")
    print("   - Detection: Method frequency analysis")


def demonstrate_energy_cost():
    """Calculate energy cost of HTTP 204"""
    print_header("Energy Cost of HTTP 204 No Content")

    # Base TCP energy (from tcp_nop.py)
    tcp_base_energy = 670.0  # μJ

    # Additional energy for HTTP data packets
    nic_tx = 127.0  # μJ per packet
    nic_rx = 52.0   # μJ per packet
    network_hop = 0.6  # μJ per hop
    hops = 5

    # 2 additional packets (HTTP request, HTTP response)
    http_energy = (nic_tx + nic_rx + network_hop * hops) * 2

    total_energy = tcp_base_energy + http_energy

    print_info("TCP connection energy", f"{tcp_base_energy:.1f} μJ")
    print_info("HTTP request packet energy", f"{nic_tx + network_hop * hops:.1f} μJ")
    print_info("HTTP response packet energy", f"{nic_rx + network_hop * hops:.1f} μJ")
    print_info("Total HTTP 204 energy", f"{total_energy:.1f} μJ")
    print()

    # Scale up
    million = 1_000_000
    billion = 1_000_000_000

    energy_million = total_energy * million / 1_000_000  # Joules
    energy_billion = total_energy * billion / 1_000_000   # kJ

    print_info("Energy for 1M HTTP 204s", f"{energy_million:.2f} J")
    print_info("Energy for 1B HTTP 204s", f"{energy_billion:.2f} kJ")
    print()

    # Real-world scenario: Tracking pixels
    print(f"{Colors.BOLD}Real-World Example: Tracking Pixels{Colors.ENDC}\n")
    print("Many websites use 1x1 pixel images for tracking:")
    print("- Browser requests: GET /track.gif?user=12345")
    print("- Server logs request, returns 204 No Content")
    print("- No actual image data transmitted")
    print()

    pixels_per_day = 1_000_000_000  # 1 billion page views
    daily_energy = pixels_per_day * total_energy / 1_000_000 / 1000  # kJ
    annual_energy = daily_energy * 365
    annual_kwh = annual_energy / 3600

    print_info("Tracking pixels per day", f"{pixels_per_day:,}")
    print_info("Daily energy consumption", f"{daily_energy:.2f} kJ")
    print_info("Annual energy consumption", f"{annual_kwh:.2f} kWh")
    print_info("Annual CO2 emissions", f"{annual_kwh * 0.5:.2f} kg CO2e")
    print()
    print(f"{Colors.YELLOW}Significant environmental impact just to log page views.{Colors.ENDC}")


class NopHTTPRequestHandler(BaseHTTPRequestHandler):
    """HTTP request handler that returns 204 No Content for all requests"""

    def log_message(self, format, *args):
        """Override to add colored output"""
        timestamp = datetime.now().strftime("%H:%M:%S.%f")[:-3]
        message = format % args
        print(f"{Colors.CYAN}[{timestamp}] {message}{Colors.ENDC}")

    def send_204_response(self):
        """Send HTTP 204 No Content response"""
        self.send_response(204)
        self.send_header('Server', 'Python HTTP-NOP/1.0')
        self.send_header('Connection', 'close')
        self.end_headers()
        # No body - that's the point of 204

    def do_GET(self):
        """Handle GET requests with 204"""
        print_http_line("in", f"GET {self.path} HTTP/{self.request_version}")
        for header, value in self.headers.items():
            print_http_line("in", f"{header}: {value}")
        print()

        print(f"{Colors.GREEN}Processing request... (doing nothing){Colors.ENDC}\n")

        print_http_line("out", "HTTP/1.1 204 No Content")
        print_http_line("out", f"Server: Python HTTP-NOP/1.0")
        print_http_line("out", f"Connection: close")
        print_http_line("out", "")
        print()

        self.send_204_response()

    def do_POST(self):
        """Handle POST requests with 204"""
        content_length = int(self.headers.get('Content-Length', 0))

        print_http_line("in", f"POST {self.path} HTTP/{self.request_version}")
        for header, value in self.headers.items():
            print_http_line("in", f"{header}: {value}")

        if content_length > 0:
            body = self.rfile.read(content_length)
            print_http_line("in", f"")
            print(f"{Colors.BLUE}→ [Body: {content_length} bytes received and ignored]{Colors.ENDC}")
        print()

        print(f"{Colors.GREEN}Processing request... (doing nothing with data){Colors.ENDC}\n")

        print_http_line("out", "HTTP/1.1 204 No Content")
        print_http_line("out", f"Server: Python HTTP-NOP/1.0")
        print_http_line("out", f"Connection: close")
        print_http_line("out", "")
        print()

        self.send_204_response()

    def do_PUT(self):
        """Handle PUT requests with 204"""
        self.do_POST()  # Same handling

    def do_DELETE(self):
        """Handle DELETE requests with 204"""
        print_http_line("in", f"DELETE {self.path} HTTP/{self.request_version}")
        for header, value in self.headers.items():
            print_http_line("in", f"{header}: {value}")
        print()

        print(f"{Colors.GREEN}Processing request... (pretending to delete){Colors.ENDC}\n")

        print_http_line("out", "HTTP/1.1 204 No Content")
        print_http_line("out", f"Server: Python HTTP-NOP/1.0")
        print_http_line("out", f"Connection: close")
        print_http_line("out", "")
        print()

        self.send_204_response()


def http_nop_client(url='http://127.0.0.1:8000/api/nop', method='DELETE', verbose=True):
    """
    Send HTTP request and receive 204 No Content response.

    Args:
        url: Target URL
        method: HTTP method (GET, POST, PUT, DELETE)
        verbose: Print detailed output

    Returns:
        dict: Request statistics
    """
    if verbose:
        print_header(f"HTTP NOP Client - {method} {url}")

    stats = {
        'start_time': time.time(),
        'end_time': None,
        'status_code': None,
        'error': None
    }

    try:
        parsed_url = urlparse(url)
        host = parsed_url.hostname or '127.0.0.1'
        port = parsed_url.port or 80
        path = parsed_url.path or '/'

        if verbose:
            print_info("Target", f"{host}:{port}")
            print_info("Method", method)
            print_info("Path", path)
            print()

        # Create socket and connect
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)

        if verbose:
            print(f"{Colors.BOLD}Establishing TCP connection...{Colors.ENDC}\n")

        connect_start = time.time()
        sock.connect((host, port))
        connect_time = time.time() - connect_start

        if verbose:
            print_info("TCP connected", f"{connect_time*1000:.3f} ms")
            print()

        # Build HTTP request
        request_line = f"{method} {path} HTTP/1.1\r\n"
        headers = f"Host: {host}\r\nUser-Agent: Python HTTP-NOP/1.0\r\nConnection: close\r\n\r\n"
        request = request_line + headers

        if verbose:
            print(f"{Colors.BOLD}Sending HTTP request...{Colors.ENDC}\n")
            for line in request.split('\r\n'):
                if line:
                    print_http_line("out", line)
            print()

        # Send request
        send_start = time.time()
        sock.sendall(request.encode())
        send_time = time.time() - send_start

        # Receive response
        if verbose:
            print(f"{Colors.BOLD}Receiving HTTP response...{Colors.ENDC}\n")

        recv_start = time.time()
        response = b''
        while True:
            chunk = sock.recv(4096)
            if not chunk:
                break
            response += chunk
        recv_time = time.time() - recv_start

        # Parse response
        response_text = response.decode('utf-8', errors='ignore')
        lines = response_text.split('\r\n')

        if lines:
            status_line = lines[0]
            if verbose:
                print_http_line("in", status_line)

            # Extract status code
            parts = status_line.split(' ', 2)
            if len(parts) >= 2:
                try:
                    stats['status_code'] = int(parts[1])
                except:
                    pass

            # Print headers
            for line in lines[1:]:
                if line and ':' in line:
                    if verbose:
                        print_http_line("in", line)
                elif line == '':
                    break

            if verbose:
                print()
                print_info("Status code", f"{stats['status_code']}")
                print_info("Response time", f"{recv_time*1000:.3f} ms")
                print_info("Response body", f"{Colors.RED}0 bytes (204 No Content){Colors.ENDC}")
                print()

        # Close connection
        sock.close()

        stats['rtt'] = time.time() - connect_start

    except Exception as e:
        stats['error'] = str(e)
        if verbose:
            print(f"{Colors.RED}Error: {e}{Colors.ENDC}")

    stats['end_time'] = time.time()
    stats['total_time'] = stats['end_time'] - stats['start_time']

    return stats


def http_nop_server(host='127.0.0.1', port=8000):
    """Run HTTP NOP server"""
    print_header(f"HTTP NOP Server @ http://{host}:{port}")
    print_info("Server address", f"{host}:{port}")
    print_info("Response", "204 No Content (all requests)")
    print_info("Status", "Press Ctrl+C to stop")
    print()

    server = HTTPServer((host, port), NopHTTPRequestHandler)

    try:
        print(f"{Colors.GREEN}Server ready, waiting for requests...{Colors.ENDC}\n")
        print(f"{Colors.BOLD}{'='*70}{Colors.ENDC}\n")
        server.serve_forever()
    except KeyboardInterrupt:
        print(f"\n{Colors.YELLOW}Shutting down server...{Colors.ENDC}")
        server.shutdown()
        print_info("Server stopped", "")


def main():
    """Main function"""
    if len(sys.argv) > 1 and sys.argv[1] == 'server':
        # Run as server
        host = sys.argv[2] if len(sys.argv) > 2 else '127.0.0.1'
        port = int(sys.argv[3]) if len(sys.argv) > 3 else 8000
        http_nop_server(host, port)
    else:
        # Run demonstrations and client
        demonstrate_http_204()
        calculate_overhead()
        demonstrate_http_layers()
        demonstrate_http_state()
        demonstrate_timing_channels()
        demonstrate_energy_cost()

        # Try HTTP request
        print_header("Attempting HTTP 204 Request")
        print(f"{Colors.YELLOW}Note: This will fail if no server is running.{Colors.ENDC}")
        print(f"{Colors.YELLOW}Run '{sys.argv[0]} server' in another terminal to start a server.{Colors.ENDC}")
        print()

        stats = http_nop_client(verbose=True)

        print_header("Request Statistics")
        print_info("Total duration", f"{stats['total_time']*1000:.3f} ms")
        if stats.get('status_code'):
            status_color = Colors.GREEN if stats['status_code'] == 204 else Colors.RED
            print_info("Status code", f"{status_color}{stats['status_code']}{Colors.ENDC}")
        if stats.get('rtt'):
            print_info("Round-trip time", f"{stats['rtt']*1000:.3f} ms")
        if stats.get('error'):
            print_info("Error", f"{Colors.RED}{stats['error']}{Colors.ENDC}")
        print()

        print_header("Conclusion")
        print(f"{Colors.BOLD}HTTP 204 No Content Summary:{Colors.ENDC}\n")
        print(f"- Minimum {Colors.YELLOW}9 packets{Colors.ENDC} transmitted (TCP + HTTP)")
        print(f"- Minimum {Colors.YELLOW}~1000 bytes{Colors.ENDC} consumed on wire")
        print(f"- HTTP headers sent: {Colors.YELLOW}~200-400 bytes{Colors.ENDC}")
        print(f"- HTTP response body: {Colors.RED}{Colors.BOLD}0 bytes (204 No Content){Colors.ENDC}")
        print(f"- TCP state machine: {Colors.YELLOW}Full traversal{Colors.ENDC}")
        print(f"- Energy consumed: {Colors.YELLOW}~1030 μJ{Colors.ENDC}")
        print(f"- Forensic evidence: {Colors.YELLOW}Logged in web server, firewall, proxy{Colors.ENDC}")
        print()
        print(f"{Colors.CYAN}HTTP 204 is the protocol's way of saying:{Colors.ENDC}")
        print(f"{Colors.CYAN}'I successfully received your request and did nothing.'{Colors.ENDC}")
        print()
        print(f"{Colors.YELLOW}But communicating 'nothing' required substantial infrastructure.{Colors.ENDC}")
        print(f"{Colors.YELLOW}Application-layer NOP, network-layer overhead.{Colors.ENDC}")


if __name__ == '__main__':
    main()
