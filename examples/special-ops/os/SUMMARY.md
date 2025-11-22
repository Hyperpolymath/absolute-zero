# OS-Level CNO Examples - Summary

## Files Created

All files are located in `/home/user/absolute-zero/examples/special-ops/os/`

### 1. syscall_nop.c (256 lines)
**System Call CNO - getpid() with result discarded**

- **Overhead**: 50-300ns per call
- **Kernel transitions**: User→Kernel→User (2 mode switches)
- **Security checks**: Syscall validation, namespaces, capabilities, seccomp, SELinux/AppArmor
- **Context switch**: None (same thread continues)
- **TLB impact**: Minimal (modern CPUs with PCID)
- **Platform**: Linux (raw syscall), BSD/macOS (wrapper)

**Key insight**: Even "free" syscalls like getpid() incur 100-300ns overhead - 20-300x slower than a function call.

### 2. sched_yield.c (385 lines)
**Scheduler Yield CNO - Yield CPU when no other tasks exist**

- **Overhead**: 500ns-2μs (no contention), 1-10μs (with context switch)
- **Kernel work**: Runqueue scan, scheduling decision, priority recalculation
- **Security checks**: RLIMIT_RTTIME, CPU affinity, cgroup controllers
- **Context switch**: Only if other runnable tasks exist (CNO when alone)
- **TLB impact**: Flush only on actual context switch
- **Scheduler**: Linux CFS, BSD ULE, macOS Mach
- **Platform**: POSIX-compatible (all platforms)

**Key insight**: Scheduler consultation alone costs 500ns-2μs even when it decides to do nothing.

### 3. futex_nop.c (382 lines)
**Futex Wait/Wake CNO - Fast userspace mutex with no contention**

- **Overhead**: 200-600ns per wait/wake pair
- **Kernel work**: Hash computation, waitqueue examination, value checking
- **Security checks**: Address validation, operation validation, permissions
- **Context switch**: None in CNO case (immediate return)
- **TLB impact**: None (no context switch)
- **Platform**: **Linux only** (futex is Linux-specific)
  - BSD alternative: _umtx_op()
  - macOS alternative: __ulock_wait/__ulock_wake

**Key insight**: Futex infrastructure overhead is 200-600ns even when no waiting occurs - the "fast" in "fast userspace mutex" refers to the uncontended userspace-only path.

### 4. signal_nop.c (422 lines)
**Signal Handler CNO - Signal with empty handler**

- **Overhead**: 1-5μs per signal delivery
- **Kernel transitions**: 3 separate transitions (send, delivery, return)
- **Context operations**: Within-task context switch (save/restore registers)
- **Security checks**: Permission checks, PID validation, handler validation, stack checks
- **TLB impact**: None (same address space)
- **Stack switching**: Signal handler stack frame created
- **Platform**: POSIX (Linux, BSD, macOS with platform-specific delivery)

**Key insight**: Signal delivery is ~1000x more expensive than a function call, making signals unsuitable for high-frequency IPC.

### 5. ioctl_nop.c (456 lines)
**ioctl Query CNO - Device query with result discarded**

- **Overhead**: 300ns-2μs depending on device type
- **Kernel layers**: Syscall → FD lookup → VFS dispatch → Driver handler
- **Device variations**:
  - Terminal (TTY): 300-800ns
  - Socket: 400-1000ns
  - Pipe: 200-500ns
  - Block device: 500-2000ns
- **Security checks**: FD validation, permissions, capabilities, LSM hooks
- **Data marshaling**: copy_to_user() overhead even when ignored
- **Platform**: POSIX (Linux, BSD, macOS with different ioctl commands)

**Key insight**: VFS layer and driver dispatch add significant overhead - ioctl is 60-400x slower than function call even for simple queries.

## Cross-Cutting Themes

### Kernel Mode Transitions
All examples demonstrate user↔kernel mode switch overhead:
- **Entry**: Save registers, switch stack, load kernel page tables (~50-200 cycles)
- **Exit**: Restore registers, switch stack, return to user page tables (~50-200 cycles)
- **Total**: ~100-400 cycles minimum, even for trivial operations

### Security Overhead
Every kernel operation includes security validation:
1. Permission/capability checks
2. Namespace isolation enforcement
3. Mandatory Access Control (SELinux/AppArmor)
4. Seccomp filtering
5. Audit logging (if enabled)

**Critical point**: Security checks run even for CNO operations - the kernel cannot know in advance that the result will be discarded.

### Context Switch Spectrum

| Example | Context Switch Type | Overhead |
|---------|-------------------|----------|
| syscall_nop | Mode switch only | ~100-300ns |
| sched_yield | Optional task switch | 500ns-10μs |
| futex_nop | None (CNO case) | ~200-600ns |
| signal_nop | Within-task switch | ~1-5μs |
| ioctl_nop | None (query case) | ~300ns-2μs |

### TLB Flush Behavior

- **No flush**: syscall_nop, futex_nop, signal_nop, ioctl_nop (same address space)
- **Conditional flush**: sched_yield (only if context switch to different process)
- **Modern CPUs**: Tagged TLB (PCID) reduces flush impact significantly

### Scheduler Interaction

- **None**: futex_nop (CNO case)
- **Minimal**: syscall_nop, ioctl_nop (preemption point only)
- **Direct**: sched_yield (explicitly invokes scheduler)
- **Indirect**: signal_nop (delivery checked on kernel exit)

## Performance Hierarchy

From fastest to slowest CNO operation:

1. **syscall_nop**: 50-300ns (simple syscall)
2. **futex_nop**: 200-600ns (hash lookup + waitqueue check)
3. **ioctl_nop**: 300-2000ns (VFS + driver dispatch)
4. **sched_yield**: 500-2000ns (scheduler consultation, no switch)
5. **signal_nop**: 1000-5000ns (3 kernel transitions + context save/restore)

## Platform Coverage

### Linux
- All examples fully implemented
- futex_nop is Linux-specific
- Most detailed kernel interactions documented
- CFS scheduler behavior explained

### BSD (FreeBSD, OpenBSD, NetBSD)
- syscall_nop, sched_yield, signal_nop, ioctl_nop: Full support
- futex_nop: Requires _umtx_op() alternative (not implemented)
- ULE scheduler (FreeBSD)
- BSD signal semantics

### macOS
- syscall_nop, sched_yield, signal_nop, ioctl_nop: Full support
- futex_nop: Requires __ulock_wait/__ulock_wake alternative (not implemented)
- Mach kernel with BSD layer
- Mach exception ports + BSD signals

## Compilation & Usage

```bash
# Compile all (from examples/special-ops/os/)
gcc -o syscall_nop syscall_nop.c
gcc -pthread -o sched_yield sched_yield.c
gcc -o futex_nop futex_nop.c       # Linux only
gcc -o signal_nop signal_nop.c
gcc -o ioctl_nop ioctl_nop.c

# Run benchmarks
./syscall_nop
./sched_yield
./futex_nop    # Linux only
./signal_nop
./ioctl_nop
```

Each program:
- Explains the CNO concept
- Demonstrates basic operation
- Runs benchmarks (10,000-100,000 iterations)
- Reports overhead in nanoseconds/microseconds
- Documents platform-specific behavior

## Educational Outcomes

### What Students Learn

1. **Syscalls aren't free**: Even trivial operations incur 50-300ns overhead
2. **Security has cost**: Every operation includes security validation
3. **Abstraction layers add up**: VFS → driver dispatch adds significant overhead
4. **Scheduler overhead**: Consultation alone costs 500ns-2μs
5. **Signals are expensive**: 1000x slower than function calls
6. **CNO reveals overhead**: By doing nothing useful, we isolate pure overhead

### Performance Engineering Lessons

1. **Avoid syscalls in hot paths**: 20-300x slower than function calls
2. **Batch operations**: Amortize syscall overhead over multiple operations
3. **Use userspace synchronization**: When possible, avoid kernel (futex uncontended path)
4. **Don't use signals for IPC**: Too expensive for high-frequency communication
5. **Cache ioctl results**: Don't repeatedly query device information
6. **Understand your platform**: Overhead varies significantly across OS kernels

## Code Statistics

- **Total lines**: 2,152 (including comments)
- **C code**: 1,901 lines
- **Documentation**: 251 lines (README.md)
- **Average per example**: ~380 lines of heavily documented C code
- **Comment density**: ~60-70% (educational focus)

## Documentation Quality

Each example includes:

1. **Header comment block**:
   - Concept explanation
   - Kernel mode transition overhead
   - Context switch implications
   - TLB flush behavior
   - Scheduler impact
   - Security checks
   - Platform compatibility
   - Measurement details

2. **Inline analysis**:
   - Kernel execution flow
   - Data structure operations
   - Security validation steps
   - Overhead breakdown

3. **"Deeper Dive" section**:
   - Why this is CNO
   - Real-world implications
   - Comparison with alternatives
   - Educational value

## Related Examples

See also in `examples/special-ops/`:
- `atomic/`: Atomic operations CNO (compare-and-swap that always fails)
- `concurrency/`: Lock CNO (acquire/release with no critical section)
- `memory/`: Memory allocation CNO (malloc/free with zero use)
- `synchronization/`: Barrier/semaphore CNO (wait with no coordination)

## License

Part of the Absolute Zero project. Dual-licensed under:
- AGPL-3.0 (see LICENSE-AGPL3.md)
- PALIMPS (see LICENSE-PALIMPS.md)
