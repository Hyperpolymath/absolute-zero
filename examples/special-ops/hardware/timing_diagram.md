# Signal Timing Diagrams for Hardware CNO Operations

## Overview

This document provides detailed timing diagrams showing the clock-by-clock behavior of Computational No-Operations (CNOs) at the hardware level. These diagrams demonstrate that CNOs, despite producing no computational output, still consume real clock cycles and exhibit measurable signal transitions.

## Timing Notation

```
Signal Conventions:
  __|‾‾|__     Clock signal (rising/falling edges)
  ________     Logic 0 (low)
  ‾‾‾‾‾‾‾‾     Logic 1 (high)
  <value>      Data value (valid)
  ---<val>---  Data transition
  XXXX         Unknown/undefined
  ////         High-impedance (tri-state)

Timing Markers:
  t0, t1, ...  Time points
  ↑            Rising edge (active)
  ↓            Falling edge
  △            Setup time point
  ▽            Hold time point
```

## 1. Basic 4-Stage Pipeline CNO

### Single Operation Timing

```
Time (ns):    0    5   10   15   20   25   30   35   40   45
              |    |    |    |    |    |    |    |    |    |
Clock (200MHz)|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_
              t0   t1   t2   t3   t4   t5   t6   t7   t8   t9

Enable        _____|‾‾‾‾|________________________________________

Valid_in      _____|‾‾‾‾|________________________________________

Data_in       -----<0xABCD>--------------------------------------
                   [Setup→

Pipeline[0]   -----------<0xABCD>------------------------------
                          ↑t1 Captured

Pipeline[1]   -------------------<0xABCD>----------------------
                                  ↑t2 Propagated

Pipeline[2]   ---------------------------<0xABCD>--------------
                                          ↑t3 Propagated

Pipeline[3]   -----------------------------------<0xABCD>------
                                                  ↑t4 Propagated

Valid_out     ___________________________________________|‾‾‾‾‾

Data_out      -------------------------------------------<0xABCD>
                                                          ↑t4 Output

Busy          ________|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|______
                      t1                                 t4

ANALYSIS:
- Input captured at t1 (5 ns)
- Output valid at t4 (20 ns)
- Latency: 4 clock cycles = 20 ns
- Result: Output = Input (identity, no computation)
- Clock cycles consumed: 4 cycles @ 200 MHz
- Energy consumed: ~4.68 pJ (1.17 mW × 4 ns)
```

### Detailed Single Clock Cycle (Cycle 2, t2)

```
Time:         15.0ns  15.5ns  16.0ns  16.5ns  17.0ns  17.5ns  18.0ns  18.5ns  19.0ns  19.5ns  20.0ns
              |       |       |       |       |       |       |       |       |       |       |
Clock         ________|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|_____________________________
              ↓                               ↑                               ↓
              Falling edge                    Rising edge                     Falling edge

Setup window          [                       △
Hold window                                   ▽]

Clock tree:
  Root buffer _______|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|_____________________________
                     (10ps delay from clk)

  Branch buf  ___________|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|_________________________
                         (30ps total delay - skew!)

Pipeline[0]   <----0xABCD---->
  (held from previous cycle)

Pipeline[1]   <----0x????---->___________________<----0xABCD---->
                              ↑ t2+50ps          (after clock-to-Q delay)
                              Clock-to-Q delay = 45-50ps

Control FSM:
  State       <---PROP--->________<---PROP--->

  Next_state  <---PROP--->________<---PROP--->
                          ↑ t2+30ps
                          (combinational delay)

Mux select    <----1---->________<----1---->
                          ↑ t2+40ps

Data propagation path:
  1. Clock edge arrives:                      t2 + 0ps
  2. Clock tree to FF:                        t2 + 30ps (skew)
  3. FF clock-to-Q:                           t2 + 30ps + 50ps = t2 + 80ps
  4. Routing to mux:                          t2 + 80ps + 20ps = t2 + 100ps
  5. Mux propagation:                         t2 + 100ps + 30ps = t2 + 130ps
  6. Routing to next FF:                      t2 + 130ps + 25ps = t2 + 155ps
  7. Setup time before next clock:            t2 + 155ps (must be < t3 - 35ps)

Timing margin:
  - Period: 5000 ps
  - Critical path: 155 ps
  - Setup time: 35 ps
  - Total consumed: 190 ps
  - Slack: 5000 - 190 = 4810 ps (96% margin!)

OBSERVATION: CNO has HUGE timing slack, indicating wasted potential for faster operation or more useful logic.
```

## 2. Pipelined CNO Stream (Continuous Operations)

```
Clock (200MHz):
     __|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__
     t0  t1  t2  t3  t4  t5  t6  t7  t8  t9  t10 t11 t12 t13 t14 t15 t16

Enable:
     __|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|_________________________________

Valid_in:
     __|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|_________________________________

Data_in:
     --<A>-<B>-<C>-<D>-<E>-<F>-<G>-----------------------------------------

Pipeline[0]:
     ------<A>-<B>-<C>-<D>-<E>-<F>-<G>-<G>-------------------------------

Pipeline[1]:
     ----------<A>-<B>-<C>-<D>-<E>-<F>-<G>-------------------------------

Pipeline[2]:
     --------------<A>-<B>-<C>-<D>-<E>-<F>-<G>---------------------------

Pipeline[3]:
     ------------------<A>-<B>-<C>-<D>-<E>-<F>-<G>-----------------------

Valid_out:
     ______________________|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|____________

Data_out:
     ----------------------<A>-<B>-<C>-<D>-<E>-<F>-<G>-------------------

Busy:
     ______|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾

ANALYSIS:
- Throughput: 1 operation per cycle (maximum pipeline utilization)
- Operations per second: 200 MHz
- All pipeline stages active simultaneously
- Power consumption: MAXIMUM (all flip-flops toggling)
- Each data value (A, B, C, etc.) spends exactly 4 cycles in pipeline
- All 4 cycles produce no computational result
- Wasted cycles: 4 × 7 operations = 28 cycles
- At 200 MHz: 140 ns of pure identity transformation
```

## 3. Power-Optimized CNO with Clock Gating

```
Time (ns):    0    5   10   15   20   25   30   35   40   45   50   55   60
              |    |    |    |    |    |    |    |    |    |    |    |    |
Clock (input) |‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_
              t0   t1   t2   t3   t4   t5   t6   t7   t8   t9   t10  t11  t12

Enable        _____|‾‾‾‾|________________________________________________

Gate_enable   _____|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|____________
              (FSM state != IDLE)

Gated_clock   _____|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_____________________
              IDLE  ←--------- CNO ACTIVE ----------→  IDLE

Data_in       -----<0xDEAD>----------------------------------------------

Pipeline[0]   -----------<0xDEAD>----------------------------------------

Pipeline[1]   -------------------<0xDEAD>--------------------------------

Pipeline[2]   ---------------------------<0xDEAD>------------------------

Pipeline[3]   -----------------------------------<0xDEAD>----------------

Data_out      -------------------------------------------<0xDEAD>--------

Power profile:
Clock pwr     ▁▁▁██████████████████████████████████▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁
              (Reduced by 70% when idle)

Data pwr      ▁▁▁███▄▄▄███▄▄▄███▄▄▄███▄▄▄███▄▄▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁
              (Only active during CNO operation)

Total pwr     ▁▁▁████████████████████████████████▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁
              ~1mW                               ~100µW

POWER SAVINGS:
- Active period (t1 to t9): 8 cycles × 1 mW = 8 pJ
- Without clock gating (t1 to t12): 12 cycles × 1 mW = 12 pJ
- Savings: 33% (but still wastes 8 pJ on identity operation!)
```

## 4. Clock Domain Crossing CNO

### Asynchronous Clock Domain Crossing with 2-FF Synchronizer

```
Time:         0    5   10   15   20   25   30   35   40   45   50   55   60   65
              |    |    |    |    |    |    |    |    |    |    |    |    |    |

ClkA (200MHz) |‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_

ClkB (150MHz)   |‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__
              (Phase offset shown)

Data_A (ClkA) <----0xCAFE---->___________________________________________

CNO_stage[0]  ------<0xCAFE>----------------------------------------------
              (ClkA domain, after 1 cycle)

CNO_stage[1]  ------------<0xCAFE>----------------------------------------
              (ClkA domain, after 2 cycles)

CNO_stage[2]  ------------------<0xCAFE>----------------------------------
              (ClkA domain, after 3 cycles)

Sync_FF1      ----------------------XXXX<0xCAFE>--------------------------
              (ClkB domain)         ↑ Metastable period (~100-500ps)
                                    May capture 0xCAFE or previous value

Sync_FF2      ----------------------------??<0xCAFE>----------------------
                                           ↑ Settled (stable)

Data_B (ClkB) --------------------------------<0xCAFE>--------------------
              (ClkB domain, synchronized)

METASTABILITY ANALYSIS:
- Setup/hold violation at CDC point (t≈20-23ns)
- Sync_FF1 enters metastable state for 100-500ps
- Probability of metastability propagation: e^(-t_settle/τ)
  - τ (time constant): 20-50 ps
  - t_settle (available time): 6.67 ns @ 150 MHz
  - P_meta: e^(-6670/30) ≈ 10^-97 (extremely low)
- Sync_FF2 captures stable value (virtually guaranteed)

LATENCY ANALYSIS:
- ClkA domain: 3 cycles × 5 ns = 15 ns
- CDC synchronizer: 2 cycles × 6.67 ns = 13.34 ns
- Total latency: ~28.34 ns (variable due to phase offset)
- Worst case: 28.34 + 6.67 = 35 ns
- 7 clock cycles total to pass identity through!
```

## 5. Transistor-Level Timing (Single Flip-Flop)

### D Flip-Flop Internal Signals During CNO Capture

```
Time (ps):    0    50   100  150  200  250  300  350  400  450  500
              |    |    |    |    |    |    |    |    |    |    |

Clock         __|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|________________

Data_in       <--------------0---------------><----------1-------------->
                             ↑ Rising edge at t=200ps

Setup region       [△------△]
                   t=150ps  t=200ps

Hold region                 [▽------▽]
                            t=200ps t=250ps

Internal signals (master latch):
  Transmission  _____|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|____________________________
  gate (CLK)          ↑ Opens                 ↑ Closes
                      Master transparent      Master holds

  Latch_node    ---------------<0>---------------<1>-----------------------
                                ↑ Captures D        (holds)

Internal signals (slave latch):
  Transmission  ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|__________________________________
  gate (!CLK)                            ↑ Opens
                                         Slave transparent

  Output_node   <-------X------><-------0--------><------1--------------->
                        (prev)          ↑ Old val  ↑ New val
                                        t=220ps     t=250ps
                                        (Clock-to-Q delay = 50ps)

NMOS/PMOS activity:
  Master TG     OFF→ON→ON→ON→ON→OFF (conducts during high clock)
  NMOS current  0→5mA→0 (charging internal node capacitance)
  PMOS current  0→3mA→0 (if rising transition)

  Slave TG      ON→OFF→OFF→OFF→ON (conducts during low clock)
  Output inv    Switches at t=250ps (both transistors briefly ON)
  Short-circuit current: ~2mA for ~30ps = 60 fC

POWER CALCULATION (single flip-flop, single transition):
  - Internal node capacitance: 2 fF
  - Output capacitance: 5 fF
  - Dynamic energy: C × V² = 7fF × 1.0² = 7 aJ (attojoules)
  - Short-circuit: 2mA × 1.0V × 30ps = 60 aJ
  - Total: 67 aJ per transition per flip-flop

For 137 flip-flops in CNO @ 25% activity:
  - 137 × 0.25 × 67 aJ = 2.3 fJ per clock cycle
  - @ 1 GHz: 2.3 pJ/ns = 2.3 mW (matches earlier calculation!)
```

## 6. Combinational CNO ("Wire") Timing

### Wire Propagation Delay (200 µm routing)

```
Time (ps):    0    50   100  150  200  250  300  350  400  450  500
              |    |    |    |    |    |    |    |    |    |    |

Input signal  <--0-->______<--1-->___________________________________________
                     ↑ 0→1 transition at t=50ps

Wire segment analysis (4 segments × 50µm each):

Segment 1     <--0-->[Delay]<--1-->___________________________________________
              (0-50µm)      ↑ t=50ps + 5ps = 55ps
              RC delay: 10Ω × 10fF = 100fs ≈ negligible
              Buffer delay: 5ps

Segment 2     <--0------>[Delay]<--1-->_______________________________________
              (50-100µm)         ↑ t=55ps + 20ps = 75ps
              RC delay: 10Ω × 20fF = 200fs ≈ negligible
              Wire resistance starting to matter
              Repeater buffer inserted: 20ps delay

Segment 3     <--0---------->[Delay]<--1-->___________________________________
              (100-150µm)             ↑ t=75ps + 20ps = 95ps
              Another repeater: 20ps

Segment 4     <--0-------------->[Delay]<--1-->_______________________________
              (150-200µm)                 ↑ t=95ps + 25ps = 120ps
              Final buffer + wire: 25ps

Output signal <--0------------------>[Delay]<--1-->___________________________
                                             ↑ t=120ps
              Total propagation delay: 70ps for "just a wire"

DETAILED RC ANALYSIS (50 µm segment without buffer):
  - Wire resistance: 0.08 Ω/µm × 50µm = 4Ω
  - Wire capacitance: 0.15 fF/µm × 50µm = 7.5 fF
  - Load capacitance (next gate): 3 fF
  - Total C: 10.5 fF

  - Elmore delay: R × C = 4Ω × 10.5fF = 42 fs
  - 10-90% rise time: 2.2 × RC = 92 fs
  - For 200µm total: 4× longer = 168 fs ≈ 0.2 ps

  But with buffers every 50µm:
  - 4 buffers × 15-20ps = 60-80ps dominates!

POWER DISSIPATION:
  - Wire capacitance: 30 fF (total)
  - Buffer capacitance: 4 × 5 fF = 20 fF
  - Total: 50 fF
  - Energy per transition: 50 fF × 1.0² = 50 aJ
  - @ 1 GHz, 25% activity: 50 aJ × 250 MHz = 12.5 µW per wire
  - For 32-bit CNO: 32 × 12.5 µW = 400 µW (just for wires!)
```

## 7. Multi-Cycle Path CNO with Variable Latency

```
Clock:        __|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__
              t0  t1  t2  t3  t4  t5  t6  t7  t8  t9  t10 t11 t12 t13 t14

Start         _____|‾‾‾‾|___________________________________________________

Data_in       -----<VAL>----------------------------------------------------

Latency_sel   -----<2>--------------------------------------------------------
              (Selects 2-cycle CNO)

Counter       ------<0>---<1>---<2>-<0>-------------------------------------
                    Init  Inc   Done Reset

Pipeline[0]   -----------<VAL>-----------------------------------------------

Pipeline[1]   -------------------<VAL>---------------------------------------
              (Bypassed based on latency_sel)

Pipeline[2]   -------------------<VAL>---------------------------------------
              (Used for 2-cycle mode)

Pipeline[3]   -----------------------------------<VAL>----------------------
              (Bypassed)

Data_out      -------------------<VAL>---------------------------------------
              (Output after 2 cycles)

Alternative timing (latency_sel = 4):

Latency_sel   -----<4>--------------------------------------------------------

Counter       ------<0>---<1>---<2>---<3>---<4>-<0>------------------------

Data_out      -----------------------------------<VAL>----------------------
              (Output after 4 cycles)

CONFIGURABLE WASTE ANALYSIS:
- 2-cycle CNO: Wastes 10 ns @ 200 MHz
- 3-cycle CNO: Wastes 15 ns
- 4-cycle CNO: Wastes 20 ns
- Latency is configurable, but all modes waste time!

Why would anyone do this?
  - "Timing closure" (lazy solution)
  - "Pipeline balancing" (poor architecture)
  - "Legacy compatibility" (technical debt)
```

## 8. Glitch Analysis in CNO Logic

### Hazards in Control Logic

```
Time (ps):    0    100  200  300  400  500  600  700  800  900  1000
              |    |    |    |    |    |    |    |    |    |    |

Clock         __|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|_____________________________
              t0                         t1

State[0]      ‾‾‾‾‾‾‾‾‾‾‾‾\_______________________________________________
                          ↓ t=250ps

State[1]      ____________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
                          ↑ t=280ps (30ps skew!)

Enable signal (State[0] AND State[1]):

  Ideal:      ____________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾

  Actual:     ____________/‾\___/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
                          ↑ ↑ ↑ GLITCH! (30ps wide)
                          | | +-t=280ps (settled)
                          | +---t=265ps (brief low)
                          +-----t=250ps (brief high)

Glitch mechanism:
  1. State[0] falls at t=250ps
  2. AND gate output goes high briefly (State[1] still high)
  3. State[1] rises at t=280ps (was already high, but slower path)
  4. AND gate sees brief false transition
  5. Glitch appears on enable signal

CONSEQUENCES:
  - May trigger spurious operation (if not registered)
  - Increases dynamic power (extra transitions)
  - Can cause metastability in downstream logic
  - Power waste: 2 extra transitions × 5 fF × 1.0² = 10 aJ

MITIGATION:
  - Register all control signals (adds flip-flops = more CNO cost!)
  - Careful timing design (engineering time = money)
  - One-hot encoding (more flip-flops, less glitching)

For CNO with 10 control signals, each with 0.1 glitch probability:
  - Extra transitions per cycle: 10 × 0.1 × 2 = 2
  - Power overhead: 2 × 10 aJ = 20 aJ per cycle
  - @ 1 GHz: 20 mW additional power (2% overhead)
```

## 9. Temperature-Dependent Timing

### CNO Timing Across Temperature Range

```
Scenario: Automotive application (-40°C to 125°C)

At -40°C (Fast corner):
Clock:        __|‾|__|‾|__|‾|__|‾|__|‾|__
              0   1   2   3   4   5 ns (assumes 200 MHz)

Data_in       --<X>----------------------
Pipeline[0]   ----<X>-------------------- (Clock-to-Q: 30ps, fast!)
Pipeline[1]   --------<X>---------------- (Propagation: 120ps)
Pipeline[2]   ------------<X>------------ (Total slack: 3000ps)
Pipeline[3]   ----------------<X>--------
Data_out      --------------------<X>----
              Fast, lots of slack

At 25°C (Typical corner):
Clock:        __|‾|__|‾|__|‾|__|‾|__|‾|__
              0   1   2   3   4   5 ns

Data_in       --<X>----------------------
Pipeline[0]   -----<X>------------------- (Clock-to-Q: 50ps, typical)
Pipeline[1]   ----------<X>--------------- (Propagation: 190ps)
Pipeline[2]   --------------<X>----------- (Total slack: 2500ps)
Pipeline[3]   ------------------<X>-------
Data_out      ----------------------<X>---
              Normal operation

At 125°C (Slow corner):
Clock:        __|‾|__|‾|__|‾|__|‾|__|‾|__
              0   1   2   3   4   5 ns

Data_in       --<X>----------------------
Pipeline[0]   -------<X>----------------- (Clock-to-Q: 90ps, slow!)
Pipeline[1]   -------------<X>----------- (Propagation: 350ps)
Pipeline[2]   -------------------<X>----- (Total slack: 1800ps)
Pipeline[3]   ------------------------<X>-
Data_out      ---------------------------<X> (barely meets timing!)
              Slow, reduced slack

TIMING MARGIN vs TEMPERATURE:
  -40°C: Margin = 3000ps (60% of period) ← Over-designed!
   25°C: Margin = 2500ps (50% of period)
  125°C: Margin = 1800ps (36% of period) ← Still works, but tight

If CNO critical path were 3500ps instead:
  - Works at -40°C and 25°C
  - FAILS at 125°C (data arrives late)
  - Chip non-functional in hot car (automotive failure!)

LEAKAGE vs TEMPERATURE:
  -40°C: 1 µW (low leakage)
   25°C: 15.7 µW (baseline)
  125°C: 1570 µW (100× increase!) ← Exponential with temp

For 100 CNOs in automotive chip:
  @ 125°C: 157 mW leakage (just from CNOs!)
  This is 7.8% of 2W thermal budget - significant!
```

## 10. Comparison: CNO vs Useful Operation

### Side-by-Side Timing: 32-bit CNO vs 32-bit Adder

```
Clock:        __|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__
              0   1   2   3   4   5   6   7   8   9   10 ns

=== CNO OPERATION ===
A_in          --<0x1234>--------------------------------------------------
B_in          --<unused>--------------------------------------------------
CNO_out       --------------<0x1234>--------------------------------------
              (Identity: output = input, 4 cycles)

Power:        ████████████▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁ (1 mW for 4 cycles)
Computation:  NONE (0 bits of information)
Value added:  ZERO

=== ADDER OPERATION (same latency for fair comparison) ===
A_in          --<0x1234>--------------------------------------------------
B_in          --<0x5678>--------------------------------------------------
Sum_out       --------------<0x68AC>--------------------------------------
              (Addition: 0x1234 + 0x5678 = 0x68AC, 4 cycles)

Power:        ████████████▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁ (1.5 mW for 4 cycles)
Computation:  32-bit addition (ripple-carry or CLA)
Value added:  ACTUAL COMPUTATIONAL RESULT

=== COMPARATIVE ANALYSIS ===
Metric                  | CNO         | Adder      | Ratio
------------------------|-------------|------------|--------
Transistors             | 6,294       | 2,500      | 2.5×
Silicon area            | 2,261 µm²   | 1,200 µm²  | 1.9×
Power                   | 1.0 mW      | 1.5 mW     | 0.67×
Clock cycles            | 4           | 4          | 1.0×
Latency                 | 20 ns       | 20 ns      | 1.0×
Computational output    | 0 bits      | 32 bits    | 0%
Useful work             | 0           | 1 addition | 0%

CONCLUSION:
  CNO uses 2.5× more transistors and 1.9× more area than an adder,
  yet produces ZERO computational value. The adder uses slightly more
  power but produces actual mathematical results.

  EVERY CNO IN YOUR DESIGN COULD BE AN ADDER INSTEAD!
```

## Summary of Timing Analysis

### Key Findings

1. **Latency is Real**
   - Even "zero-operation" CNOs consume 4+ clock cycles
   - Latency accumulates in system pipelines
   - Can violate real-time deadlines

2. **Power Consumption is Measurable**
   - Clock network: 500-800 µW
   - Data switching: 200-300 µW
   - Total: ~1 mW per CNO @ 1 GHz
   - NOT zero despite zero computation

3. **Timing Margin is Wasted**
   - CNOs typically have 50-96% timing slack
   - Could run 2-10× faster
   - Or fit more useful logic in same cycle time

4. **Signal Integrity Matters**
   - Glitches in CNO control logic waste power
   - Metastability in clock domain crossing adds latency
   - Requires careful design (engineering cost)

5. **Temperature Effects are Significant**
   - Leakage increases 100× from cold to hot
   - Timing margin decreases by 30-40%
   - Must design for worst-case (over-design for CNO!)

### The Timing Truth

> **"Every nanosecond spent in a CNO is a nanosecond not available for useful computation. Every clock edge that toggles a CNO flip-flop is a clock edge that could have computed something meaningful. The timing diagrams don't lie: CNOs are pure overhead."**

### Design Recommendations

Based on timing analysis:

1. **Eliminate CNOs entirely** - Use retiming, pipelining of useful operations
2. **If unavoidable, minimize stages** - Each stage adds cycle and power
3. **Clock gate aggressively** - Save 70% power when idle
4. **Use combinational bypass** - For short delays, skip pipeline stages
5. **Measure actual waste** - Profile real timing, power, not assumptions

The silicon never lies. These timing diagrams prove CNOs consume real resources.
