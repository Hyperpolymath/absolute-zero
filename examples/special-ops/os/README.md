# OS-Level CNO Examples

This directory contains Computational No-Operation (CNO) examples that demonstrate system call and kernel-level operations which consume significant resources but produce no meaningful computational result.

## Overview

These examples explore the boundary between userspace and kernel space, demonstrating how operations that transition into kernel mode incur substantial overhead even when achieving nothing computationally valuable.

## Examples

### 1. syscall_nop.c - System Call CNO

**Concept**: Execute system calls (getpid) that transition to kernel mode but immediately discard results.

**Key Characteristics**:
- **Kernel Mode Transition**: ~50-200 CPU cycles each direction
- **Context Switch**: No actual task switch, but CPU mode switch (user→kernel→user)
- **TLB Flushes**: Minimal on modern CPUs with PCID, potential partial flush on older architectures
- **Scheduler Impact**: Syscall handler checks for pending signals, potential preemption point
- **Security Checks**: Syscall number validation, capability checks, namespace isolation, seccomp filters, SELinux/AppArmor hooks

**Platforms**: Linux (raw syscall interface), BSD/macOS (getpid wrapper)

**Typical Overhead**: 50-300ns per call

**Compile**: `gcc -o syscall_nop syscall_nop.c`

### 2. sched_yield.c - Scheduler Yield CNO

**Concept**: Voluntarily yield CPU to scheduler, but immediately resume when no other tasks are runnable.

**Key Characteristics**:
- **Kernel Mode Transition**: Syscall overhead + scheduler lock acquisition
- **Context Switch**: Full switch if other tasks runnable; immediate resume if alone (CNO case)
- **TLB Flushes**: Only if context switch occurs; modern tagged TLBs reduce impact
- **Scheduler Impact**: Runqueue examination, priority recalculation (CFS), task moved to end of queue
- **Security Checks**: RLIMIT_RTTIME enforcement, CPU affinity checking, cgroup notifications

**Platforms**: Linux (CFS scheduler), BSD (ULE scheduler), macOS (Mach scheduler)

**Typical Overhead**: 500ns-2μs when alone (CNO), 1-10μs with context switch

**Compile**: `gcc -pthread -o sched_yield sched_yield.c`

### 3. futex_nop.c - Futex Wait/Wake CNO

**Concept**: Use Linux futex (fast userspace mutex) to wait and wake with no actual contention.

**Key Characteristics**:
- **Kernel Mode Transition**: FUTEX_WAIT + FUTEX_WAKE syscalls
- **Context Switch**: None in CNO case (no actual waiting)
- **TLB Flushes**: None if no context switch occurs
- **Scheduler Impact**: No scheduler interaction in CNO case; full blocking/wake cycle if contended
- **Security Checks**: Address validation, operation validation, permissions, namespace checks

**Platforms**: Linux only (futex is Linux-specific; BSD has _umtx_op, macOS has __ulock_wait)

**Typical Overhead**: 200-600ns per wait/wake pair

**Compile**: `gcc -o futex_nop futex_nop.c` (Linux only)

### 4. signal_nop.c - Signal Handler CNO

**Concept**: Send signals to self with a handler that does nothing, exercising signal delivery infrastructure.

**Key Characteristics**:
- **Kernel Mode Transition**: Multiple transitions (send, delivery, handler return)
- **Context Switch**: Within-task context switch (pre-signal context saved/restored)
- **TLB Flushes**: None (same address space)
- **Scheduler Impact**: Signal delivery checked at kernel exit, potential preemption
- **Security Checks**: Permission checks, PID validation, namespace checks, handler address validation, stack validation

**Platforms**: POSIX (Linux, BSD, macOS) with platform-specific delivery mechanisms

**Typical Overhead**: 1-5μs per signal (includes send, deliver, handler, return)

**Compile**: `gcc -o signal_nop signal_nop.c`

### 5. ioctl_nop.c - ioctl Query CNO

**Concept**: Perform ioctl queries to retrieve device information, then immediately discard results.

**Key Characteristics**:
- **Kernel Mode Transition**: Syscall entry + file descriptor lookup + VFS dispatch
- **Context Switch**: None in query case; may block for some ioctls
- **TLB Flushes**: None for queries (same address space)
- **Scheduler Impact**: ioctl is preemption point; may schedule() for blocking operations
- **Security Checks**: FD validation, file permissions, capability checks, namespace isolation, LSM hooks

**Platforms**: POSIX (Linux, BSD, macOS) with platform-specific ioctl commands

**Typical Overhead**: 300ns-2μs depending on device type

**Compile**: `gcc -o ioctl_nop ioctl_nop.c`

## Compilation

All examples can be compiled with gcc or clang:

```bash
# Compile all examples
gcc -o syscall_nop syscall_nop.c
gcc -pthread -o sched_yield sched_yield.c
gcc -o futex_nop futex_nop.c       # Linux only
gcc -o signal_nop signal_nop.c
gcc -o ioctl_nop ioctl_nop.c

# With optimizations (to see CNO survives optimization)
gcc -O2 -o syscall_nop syscall_nop.c
gcc -O2 -pthread -o sched_yield sched_yield.c
```

## Usage

Each example is self-contained and includes benchmarking:

```bash
./syscall_nop
./sched_yield
./futex_nop    # Linux only
./signal_nop
./ioctl_nop
```

## Key Concepts Demonstrated

### Kernel Mode Transitions

All examples demonstrate the cost of transitioning between user mode (ring 3) and kernel mode (ring 0):

1. **Entry**: Save user registers, switch to kernel stack, load kernel page tables
2. **Execution**: Kernel code runs with elevated privileges
3. **Exit**: Restore user registers, switch back to user stack, return to user page tables

**Cost**: ~50-200 CPU cycles each direction on modern hardware

### Context Switching

Context switches occur when the scheduler switches from one task to another:

- **Full context switch**: Save current task state, load next task state, potential TLB flush
- **Within-task switch**: Signal handlers switch context within the same task
- **No switch**: Many CNO examples avoid context switching (pure overhead)

### TLB (Translation Lookaside Buffer) Flushes

TLB caches virtual-to-physical address translations:

- **Modern CPUs**: Tagged TLBs (PCID on x86-64) reduce flush requirements
- **Context switches**: May trigger TLB flush if switching address spaces
- **Same address space**: No TLB flush required

### Scheduler Impact

The kernel scheduler decides which task runs next:

- **Runqueue**: Tasks waiting to run
- **CFS (Completely Fair Scheduler)**: Linux default, uses virtual runtime
- **Preemption points**: System calls and interrupts allow scheduler to run
- **CNO cases**: Scheduler consulted but no actual scheduling work done

### Security Checks

Every kernel operation includes security validation:

1. **Permission checks**: Does the caller have permission?
2. **Capability checks**: Does the caller have required capabilities?
3. **Namespace isolation**: PID, network, mount namespaces
4. **Mandatory Access Control**: SELinux, AppArmor
5. **Seccomp filters**: Syscall filtering and auditing

**Important**: Security checks run even for CNO operations!

## Platform Differences

### Linux
- Most comprehensive examples
- futex is Linux-specific
- CFS scheduler
- Rich ioctl interface
- Real-time signals with queuing

### BSD (FreeBSD, OpenBSD, NetBSD)
- POSIX-compatible
- _umtx_op instead of futex
- ULE scheduler (FreeBSD)
- BSD signal semantics
- BSD-style ioctl

### macOS
- BSD-based
- Mach kernel underneath
- __ulock_wait/__ulock_wake instead of futex
- Mach scheduler
- Mach exception ports + BSD signals

## Performance Comparison

| Operation | Overhead | vs Function Call | vs Computation |
|-----------|----------|------------------|----------------|
| Function call | 1-5ns | 1x | ~3x |
| Simple syscall (getpid) | 50-300ns | 20-60x | 100-1000x |
| Scheduler yield | 500ns-2μs | 100-400x | 1000-6000x |
| Futex (no wait) | 200-600ns | 40-120x | 500-2000x |
| Signal delivery | 1-5μs | 200-1000x | 3000-15000x |
| ioctl query | 300ns-2μs | 60-400x | 1000-6000x |
| Pure computation | ~0.3ns/op | 0.3x | 1x |

## Educational Value

These examples demonstrate:

1. **Overhead of abstraction**: Kernel abstractions have real costs
2. **Security isn't free**: Every operation incurs security checking overhead
3. **Optimize hot paths**: Avoid syscalls in performance-critical code
4. **Understand your tools**: Knowing syscall costs informs design decisions
5. **CNO as a concept**: Work performed doesn't always equal value delivered

## Use Cases

### Performance Testing
- Measure syscall overhead on your system
- Compare different kernel versions
- Benchmark scheduler behavior

### Security Analysis
- Understand security check costs
- Analyze syscall attack surface
- Study kernel hardening impact

### Education
- Teach OS concepts
- Demonstrate kernel/user separation
- Illustrate performance engineering

### Side-Channel Research
- Syscalls as timing sources
- Scheduler behavior as information leak
- Covert channels via kernel operations

## Further Reading

- Linux kernel source: https://kernel.org/
- System call performance: "The Definitive Guide to Linux System Calls" by Ingo Molnar
- Futex documentation: futex(2) man page, "Futexes Are Tricky" by Ulrich Drepper
- Signal handling: signal(7), signal-safety(7) man pages
- VFS layer: "Understanding the Linux Kernel" by Daniel P. Bovet

## License

These examples are part of the Absolute Zero project and are dual-licensed under AGPL-3.0 and PALIMPS licenses.
