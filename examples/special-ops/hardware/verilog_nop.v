// Verilog RTL: Hardware Computational No-Operation (CNO)
// Demonstrates silicon-level resource consumption of identity circuits
// File: verilog_nop.v

`timescale 1ns / 1ps

// =============================================================================
// Module: hardware_cno_unit
// Description: RTL implementation of a CNO that demonstrates real hardware cost
// =============================================================================
module hardware_cno_unit #(
    parameter DATA_WIDTH = 64,
    parameter LATENCY_CYCLES = 4
)(
    input  wire                      clk,
    input  wire                      rst_n,
    input  wire                      enable,
    input  wire [DATA_WIDTH-1:0]     data_in,
    input  wire                      valid_in,
    output reg  [DATA_WIDTH-1:0]     data_out,
    output reg                       valid_out,
    output wire                      ready,
    output wire [31:0]               cycle_counter,  // Tracks cycles consumed
    output wire [31:0]               power_metric    // Estimated switching activity
);

    // =========================================================================
    // GATE-LEVEL IMPLEMENTATION BREAKDOWN:
    //
    // For 64-bit CNO with 4-cycle latency:
    //
    // 1. PIPELINE REGISTERS:
    //    - 4 stages × 64 bits = 256 D flip-flops
    //    - Each DFF implementation (standard cell):
    //      * Master latch: 8 transistors (2 inverters, 2 transmission gates)
    //      * Slave latch: 8 transistors
    //      * Clock buffer: 4 transistors
    //      * Total per DFF: 20 transistors
    //    - Pipeline registers: 256 × 20 = 5,120 transistors
    //
    // 2. CONTROL LOGIC:
    //    - Valid bit pipeline: 4 DFFs = 80 transistors
    //    - State machine: 3-bit state = 60 transistors
    //    - Cycle counter: 32-bit counter = 640 transistors
    //    - Power estimator: 32-bit accumulator = 640 transistors
    //    - Mux/control gates: ~200 transistors
    //    - Total control: ~1,620 transistors
    //
    // 3. CLOCK DISTRIBUTION:
    //    - Clock tree to 260+ flip-flops
    //    - Multiple buffer stages for skew control
    //    - H-tree structure: ~100 buffers = 400 transistors
    //    - Clock gating cells (for power): 50 transistors
    //
    // TOTAL TRANSISTOR COUNT: ~7,200 transistors
    //
    // This is comparable to a small ALU, yet performs NO computation!
    // =========================================================================

    // Pipeline stages for CNO
    reg [DATA_WIDTH-1:0] pipe_stage [0:LATENCY_CYCLES-1];
    reg [LATENCY_CYCLES-1:0] pipe_valid;

    // Internal control signals
    reg [2:0] state;
    reg [31:0] total_cycles;
    reg [31:0] switching_count;

    localparam IDLE       = 3'b000;
    localparam LOAD       = 3'b001;
    localparam PROPAGATE  = 3'b010;
    localparam OUTPUT     = 3'b011;

    integer i;

    // Pipeline control process
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Reset all pipeline stages
            for (i = 0; i < LATENCY_CYCLES; i = i + 1) begin
                pipe_stage[i] <= {DATA_WIDTH{1'b0}};
            end
            pipe_valid <= {LATENCY_CYCLES{1'b0}};
            data_out <= {DATA_WIDTH{1'b0}};
            valid_out <= 1'b0;
            state <= IDLE;
            total_cycles <= 32'b0;
            switching_count <= 32'b0;
        end else begin
            // Count every cycle this CNO is active
            if (state != IDLE) begin
                total_cycles <= total_cycles + 1;
            end

            case (state)
                IDLE: begin
                    valid_out <= 1'b0;
                    if (enable && valid_in) begin
                        pipe_stage[0] <= data_in;
                        pipe_valid[0] <= 1'b1;
                        state <= PROPAGATE;

                        // Count bit transitions (for power estimation)
                        switching_count <= switching_count + count_transitions(data_in, pipe_stage[0]);
                    end
                end

                PROPAGATE: begin
                    // Shift through pipeline (the actual CNO operation)
                    for (i = LATENCY_CYCLES-1; i > 0; i = i - 1) begin
                        pipe_stage[i] <= pipe_stage[i-1];
                        pipe_valid[i] <= pipe_valid[i-1];

                        // Track switching activity
                        switching_count <= switching_count + count_transitions(pipe_stage[i-1], pipe_stage[i]);
                    end

                    pipe_valid[0] <= 1'b0;

                    if (pipe_valid[LATENCY_CYCLES-1]) begin
                        state <= OUTPUT;
                    end
                end

                OUTPUT: begin
                    data_out <= pipe_stage[LATENCY_CYCLES-1];
                    valid_out <= 1'b1;
                    state <= IDLE;
                end

                default: state <= IDLE;
            endcase
        end
    end

    // Function to count bit transitions (for power estimation)
    function integer count_transitions;
        input [DATA_WIDTH-1:0] old_val;
        input [DATA_WIDTH-1:0] new_val;
        reg [DATA_WIDTH-1:0] transitions;
        integer count;
        integer j;
        begin
            transitions = old_val ^ new_val;  // XOR gives changing bits
            count = 0;
            for (j = 0; j < DATA_WIDTH; j = j + 1) begin
                count = count + transitions[j];
            end
            count_transitions = count;
        end
    endfunction

    // Output assignments
    assign ready = (state == IDLE);
    assign cycle_counter = total_cycles;
    assign power_metric = switching_count;  // Proportional to dynamic power

    // =========================================================================
    // POWER CONSUMPTION ANALYSIS:
    //
    // Dynamic Power Components:
    // 1. CLOCK NETWORK:
    //    - 260 flip-flops × clock load capacitance
    //    - C_clk ≈ 260 × 2fF = 520 fF (clock pin capacitance)
    //    - Clock tree capacitance: ~500 fF
    //    - Total clock cap: ~1 pF
    //    - P_clock = C × V² × f = 1pF × 0.9² × 1GHz = 810 µW
    //
    // 2. DATA PATH SWITCHING:
    //    - Average switching activity: α = 0.25 (25% of bits toggle per cycle)
    //    - Data path capacitance: 256 DFFs × 5fF = 1.28 pF
    //    - P_data = 0.25 × 1.28pF × 0.9² × 1GHz = 260 µW
    //
    // 3. CONTROL LOGIC:
    //    - Control signals, counters: ~100 µW
    //
    // TOTAL DYNAMIC POWER: ~1.17 mW (during active CNO operation)
    //
    // Static Power (Leakage):
    // - Modern 16nm FinFET process
    // - Subthreshold leakage: ~0.5 nA per transistor
    // - Gate leakage: ~0.1 nA per transistor
    // - Total: 7200 transistors × 0.6nA × 0.9V = 3.9 µW
    //
    // ENERGY PER CNO OPERATION:
    // - 4 cycles @ 1GHz = 4 ns
    // - Energy = Power × Time = 1.17mW × 4ns = 4.68 pJ
    //
    // For 1 billion CNOs per second:
    // - Total power: 4.68 W (just for identity operations!)
    // - Annual energy: 4.68W × 8760 hours = 41 kWh
    // - CO2 emissions: ~20 kg (assuming 0.5 kg/kWh grid carbon intensity)
    // =========================================================================

endmodule


// =============================================================================
// Module: wire_cno
// Description: "Zero-cost" combinational CNO (spoiler: it's not zero-cost)
// =============================================================================
module wire_cno #(
    parameter WIDTH = 32
)(
    input  wire [WIDTH-1:0]  in,
    output wire [WIDTH-1:0]  out
);

    // The ultimate CNO: just wire the input to output
    assign out = in;

    // =========================================================================
    // SYNTHESIS REALITY CHECK:
    //
    // What actually gets synthesized:
    //
    // 1. BUFFER INSERTION:
    //    - Synthesis tool analyzes drive strength requirements
    //    - Input pin capacitance: ~0.5 fF
    //    - Output pin needs to drive: 20 fF load
    //    - Requires buffer chain for drive strength
    //    - Typical: 2-stage buffer (small → large)
    //    - Gates inserted: 2 buffers × 32 bits = 64 buffers
    //    - Transistors: 64 × 4 = 256 transistors
    //
    // 2. SIGNAL INTEGRITY:
    //    - Long wires need repeaters to maintain signal quality
    //    - Wire length budget: 100 µm before repeater
    //    - For cross-chip routing: may need 3-4 repeater stages
    //    - Each repeater: 4 transistors
    //    - Additional: 32 × 3 × 4 = 384 transistors
    //
    // 3. TIMING CLOSURE:
    //    - Setup/hold time requirements may force register insertion
    //    - If timing path too long, becomes pipeline stage
    //    - Worst case: 32 DFFs inserted = 640 transistors
    //
    // REALISTIC IMPLEMENTATION: 300-1000 transistors
    // Even the "free wire" costs silicon area and power!
    // =========================================================================

    // =========================================================================
    // PROPAGATION DELAY ANALYSIS:
    //
    // Combinational path delay components:
    //
    // 1. Input buffer: 15 ps (min size)
    // 2. Wire delay: R × C
    //    - Wire resistance: 0.08 Ω/µm (M3 layer, 16nm process)
    //    - Wire capacitance: 0.15 fF/µm
    //    - 200 µm wire: R = 16Ω, C = 30fF
    //    - RC delay: 480 fs ≈ 0.5 ps
    //    - Elmore delay (distributed RC): ~1.5 ps
    // 3. Intermediate buffers (×2): 30 ps
    // 4. Output buffer: 20 ps
    //
    // TOTAL DELAY: ~65-70 ps
    //
    // This limits maximum frequency:
    // - f_max ≈ 1/(70ps + clock overhead) ≈ 10 GHz (theoretical)
    // - Practical with timing margin: 5 GHz
    //
    // In a pipelined system @ 2 GHz:
    // - This "wire" consumes ~14% of clock period budget
    // - Must be accounted for in timing analysis
    // =========================================================================

endmodule


// =============================================================================
// Module: shift_register_cno
// Description: Shift register implementation of CNO (maximally wasteful)
// =============================================================================
module shift_register_cno #(
    parameter DATA_WIDTH = 8,
    parameter SHIFT_DEPTH = 16  // How many cycles to waste
)(
    input  wire                     clk,
    input  wire                     rst_n,
    input  wire [DATA_WIDTH-1:0]    data_in,
    output wire [DATA_WIDTH-1:0]    data_out
);

    // Shift register chain - data takes SHIFT_DEPTH cycles to pass through
    reg [DATA_WIDTH-1:0] shift_reg [0:SHIFT_DEPTH-1];

    integer i;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (i = 0; i < SHIFT_DEPTH; i = i + 1) begin
                shift_reg[i] <= {DATA_WIDTH{1'b0}};
            end
        end else begin
            shift_reg[0] <= data_in;
            for (i = 1; i < SHIFT_DEPTH; i = i + 1) begin
                shift_reg[i] <= shift_reg[i-1];
            end
        end
    end

    assign data_out = shift_reg[SHIFT_DEPTH-1];

    // =========================================================================
    // RESOURCE UTILIZATION:
    //
    // For 8-bit × 16-stage shift register:
    // - Total flip-flops: 8 × 16 = 128 DFFs
    // - Transistors: 128 × 20 = 2,560 transistors
    // - Silicon area (16nm process):
    //   * DFF area: ~1.0 µm² per DFF
    //   * Total: 128 µm²
    //   * With routing: ~200 µm²
    //
    // Comparison to SRAM:
    // - 128 bits of SRAM: 128 × 0.05 µm² = 6.4 µm²
    // - Shift register is 31× larger than equivalent storage!
    //
    // This CNO wastes both time (16 cycles) and space (200 µm²)
    // =========================================================================

    // =========================================================================
    // PLACE & ROUTE IMPLICATIONS:
    //
    // 1. FLOORPLANNING:
    //    - 16 stages ideally placed linearly for minimum wire length
    //    - Actual placement: may be scattered across die
    //    - Wire length: 8 wires × 16 stages ≈ 1.6 mm total
    //
    // 2. ROUTING CONGESTION:
    //    - 8 parallel wires × 16 connections = 128 wire segments
    //    - Requires multiple metal layers
    //    - May cause routing congestion in dense designs
    //    - Can block routing for functional logic
    //
    // 3. CLOCK DISTRIBUTION:
    //    - All 128 DFFs on same clock domain
    //    - Clock skew budget: ±10 ps
    //    - Requires balanced clock tree
    //    - Clock routing: additional metal resources
    //
    // 4. TIMING CLOSURE:
    //    - Each stage adds setup/hold constraints
    //    - 16 critical paths to verify
    //    - May limit maximum frequency of entire design
    //
    // A CNO that does nothing computationally can dominate physical design!
    // =========================================================================

endmodule


// =============================================================================
// Testbench: Verify CNO behavior and measure resource consumption
// =============================================================================
module tb_hardware_cno;

    parameter DATA_WIDTH = 64;
    parameter LATENCY = 4;

    reg clk;
    reg rst_n;
    reg enable;
    reg [DATA_WIDTH-1:0] data_in;
    reg valid_in;
    wire [DATA_WIDTH-1:0] data_out;
    wire valid_out;
    wire ready;
    wire [31:0] cycle_counter;
    wire [31:0] power_metric;

    // Instantiate CNO unit
    hardware_cno_unit #(
        .DATA_WIDTH(DATA_WIDTH),
        .LATENCY_CYCLES(LATENCY)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .enable(enable),
        .data_in(data_in),
        .valid_in(valid_in),
        .data_out(data_out),
        .valid_out(valid_out),
        .ready(ready),
        .cycle_counter(cycle_counter),
        .power_metric(power_metric)
    );

    // Clock generation: 1 GHz
    initial clk = 0;
    always #0.5 clk = ~clk;  // 0.5 ns = 1 GHz

    // Test stimulus
    initial begin
        $display("=== Hardware CNO Resource Consumption Test ===");
        $display("Configuration: %0d-bit data, %0d-cycle latency", DATA_WIDTH, LATENCY);

        // Reset
        rst_n = 0;
        enable = 0;
        data_in = 0;
        valid_in = 0;
        #5 rst_n = 1;
        #5;

        // Test 1: Single CNO operation
        $display("\nTest 1: Single CNO operation");
        data_in = 64'hDEADBEEF_CAFEBABE;
        valid_in = 1;
        enable = 1;
        #1;
        enable = 0;
        valid_in = 0;

        // Wait for completion
        wait(valid_out == 1);
        #1;

        $display("Input:  0x%h", 64'hDEADBEEF_CAFEBABE);
        $display("Output: 0x%h", data_out);
        $display("Cycles consumed: %0d", cycle_counter);
        $display("Switching events: %0d", power_metric);
        $display("Energy (estimated): %0.2f pJ", power_metric * 0.1);  // Rough estimate

        if (data_out === 64'hDEADBEEF_CAFEBABE) begin
            $display("PASS: Output matches input (identity verified)");
            $display("WASTE: %0d cycles and %0.2f pJ for zero computation!",
                     cycle_counter, power_metric * 0.1);
        end else begin
            $display("FAIL: CNO corrupted data!");
        end

        // Test 2: Continuous CNO operations (measure throughput waste)
        $display("\nTest 2: Continuous CNO stream (100 operations)");
        repeat(100) begin
            wait(ready == 1);
            data_in = $random;
            valid_in = 1;
            enable = 1;
            #1;
            enable = 0;
            valid_in = 0;
        end

        wait(ready == 1);
        #10;

        $display("Total cycles for 100 CNOs: %0d", cycle_counter);
        $display("Average latency: %0.1f cycles", cycle_counter / 100.0);
        $display("Estimated total energy: %0.2f nJ", power_metric * 0.1 / 1000.0);
        $display("Power waste @ 1GHz: %0.2f mW", (power_metric * 0.1) / (cycle_counter * 1.0));

        $display("\n=== Resource Waste Summary ===");
        $display("For 1 billion CNOs/second:");
        $display("- Clock cycles wasted: 4 billion/sec");
        $display("- Power consumption: ~1.17 W");
        $display("- Annual energy waste: ~10.25 kWh");
        $display("- Silicon area: ~0.01 mm²");
        $display("All for operations that produce NO computational value!");

        $finish;
    end

    // Timeout
    initial begin
        #10000;
        $display("ERROR: Testbench timeout");
        $finish;
    end

endmodule
