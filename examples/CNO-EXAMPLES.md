# CNO Examples - Code with No Output

This directory contains "Absolute Zero" equivalent programs for various popular programming languages. Each example demonstrates a minimal program that executes successfully without producing any output, similar to the Malbolge Absolute Zero concept.

## Overview

CNO (Code with No Output) examples illustrate the minimal runtime overhead and side effects of executing a "do nothing" program in different language interpreters. These examples are useful for:

- Understanding interpreter startup costs
- Analyzing runtime overhead
- Documenting side effects and implicit behaviors
- Performance baselining
- Educational purposes

## Files

### Python - `/examples/python/nop.py`
- **Size**: 1.5 KB
- **Interpreter**: CPython 3.x
- **Startup Time**: ~10-30ms
- **Memory Footprint**: ~5-10 MB
- **Key Side Effects**:
  - `.pyc` bytecode cache creation
  - `sys.modules` population
  - File descriptor initialization
  - Garbage collector setup

### Ruby - `/examples/ruby/nop.rb`
- **Size**: 1.5 KB
- **Interpreter**: MRI (Matz's Ruby Interpreter)
- **Startup Time**: ~20-50ms
- **Memory Footprint**: ~10-20 MB
- **Key Side Effects**:
  - YARV bytecode compilation
  - Global variable initialization
  - ObjectSpace population
  - Signal handler setup

### JavaScript - `/examples/javascript/nop.js`
- **Size**: 2.6 KB
- **Interpreter**: Node.js (V8 engine) and browsers
- **Startup Time**: ~30-60ms (Node.js), <1ms (browser)
- **Memory Footprint**: ~20-30 MB (Node.js), <100 KB (browser)
- **Key Side Effects**:
  - Event loop creation (Node.js)
  - V8 heap initialization
  - Process object population
  - Performance timeline entries

### PHP - `/examples/php/nop.php`
- **Size**: 2.2 KB
- **Interpreter**: PHP-CLI (Zend Engine)
- **Startup Time**: ~10-40ms
- **Memory Footprint**: ~5-15 MB
- **Key Side Effects**:
  - Zend Engine opcode compilation
  - Superglobals initialization
  - OPcache updates (if enabled)
  - Realpath cache population

### Perl - `/examples/perl/nop.pl`
- **Size**: 2.4 KB
- **Interpreter**: Perl 5
- **Startup Time**: ~5-20ms
- **Memory Footprint**: ~5-10 MB
- **Key Side Effects**:
  - Opcode tree compilation
  - Symbol table setup
  - @INC path construction
  - Built-in variables initialization

## Execution

All examples are executable and can be run directly:

```bash
# Python
python3 examples/python/nop.py
./examples/python/nop.py

# Ruby
ruby examples/ruby/nop.rb
./examples/ruby/nop.rb

# JavaScript (Node.js)
node examples/javascript/nop.js
./examples/javascript/nop.js

# PHP
php examples/php/nop.php
./examples/php/nop.php

# Perl
perl examples/perl/nop.pl
./examples/perl/nop.pl
```

## Verification

Each program should:
1. Produce no output to stdout or stderr
2. Exit with code 0 (success)
3. Raise no exceptions or errors
4. Execute in minimal time

Test verification:
```bash
# Template for testing
<interpreter> <file> && echo "Exit code: $?"
# Should only output: "Exit code: 0"
```

## Performance Comparison

Approximate startup times (hardware-dependent):

| Language   | Startup Time | Memory Use | Interpreter Size |
|------------|-------------|------------|------------------|
| Perl       | ~5-20ms     | ~5-10 MB   | Smallest         |
| Python     | ~10-30ms    | ~5-10 MB   | Small            |
| PHP        | ~10-40ms    | ~5-15 MB   | Medium           |
| Ruby       | ~20-50ms    | ~10-20 MB  | Medium           |
| Node.js    | ~30-60ms    | ~20-30 MB  | Largest          |

*Note: Browser JavaScript has negligible overhead as the engine is already running.*

## Educational Value

These examples demonstrate:

1. **Interpreter Overhead**: Even "do nothing" programs have initialization costs
2. **Side Effects**: No program truly does "nothing" - interpreters perform setup
3. **Language Design**: Different approaches to minimalism and defaults
4. **Performance Baseline**: Useful for benchmarking and optimization work
5. **Best Practices**: Proper file structure, pragmas, and documentation

## Relation to Absolute Zero

In Malbolge, "Absolute Zero" refers to a program that executes without output. Due to Malbolge's extreme difficulty, such programs are notable achievements. These CNO examples extend that concept to conventional languages, showing that even in accessible languages, truly minimal programs reveal interesting runtime characteristics.

## Documentation

Each file contains extensive inline comments covering:
- Interpreter behavior and initialization
- Runtime overhead breakdown
- Detailed side effects listing
- Verification procedures
- Language-specific semantics
- Alternative no-op approaches

## License

These examples are part of the Absolute Zero project and are dual-licensed under:
- AGPL-3.0 (see LICENSE-AGPL3.md)
- PALIMPS (see LICENSE-PALIMPS.md)

---

*Last updated: 2025-11-22*
