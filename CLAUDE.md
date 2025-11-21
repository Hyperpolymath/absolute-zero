# CLAUDE.md

## Project Overview

**Absolute Zero** is a Malbolge interpreter and execution environment. Malbolge is an esoteric programming language known for being extremely difficult to program in. This project provides:

- A Malbolge interpreter implementation (`ts/interpreter/malbolge-interpreter.ts`)
- Audit trail capabilities for tracking execution
- Narrative scaffolding for program analysis
- WebAssembly loading utilities

The name "Absolute Zero" refers to a Malbolge snippet that executes without producing any output.

## Project Structure

```
absolute-zero/
├── ts/
│   ├── interpreter/
│   │   └── malbolge-interpreter.ts    # Core Malbolge interpreter
│   ├── audit-trail.ts                 # Execution tracking
│   ├── narrative-scaffold.ts          # Program analysis framework
│   └── wasm-loader.ts                 # WebAssembly utilities
├── index.html                         # Web interface
├── package.json                       # Project configuration
└── tsconfig.json                      # TypeScript configuration
```

## Build System

This is a TypeScript project with a minimal build setup:

- **Build**: `npm run build` - Compiles TypeScript to JavaScript
- **Watch**: `npm run watch` - Watches for changes and recompiles automatically

## Development Guidelines

### TypeScript

- The project uses TypeScript 5.2.2+
- All source code is in the `ts/` directory
- Compiled output follows tsconfig.json settings

### Code Organization

- Keep interpreter logic in `ts/interpreter/`
- Utility modules at the root of `ts/`
- Maintain separation between interpreter core and auxiliary features

### Testing Malbolge Programs

When working with Malbolge code:
- Malbolge is deliberately obscure and difficult
- Programs self-modify during execution
- The character set is limited to specific ASCII values
- Validate programs using the interpreter before committing examples

## Licensing

This project is dual-licensed:
- **AGPL-3.0**: See `LICENSE-AGPL3.md`
- **PALIMPS**: See `LICENSE-PALIMPS.md`

When contributing or modifying code, ensure compliance with both licenses.

## Common Tasks

### Adding New Interpreter Features

1. Modify `ts/interpreter/malbolge-interpreter.ts`
2. Run `npm run build` to compile
3. Test with known Malbolge programs
4. Update documentation if behavior changes

### Debugging

- Use `npm run watch` for continuous compilation
- Check the browser console when running `index.html`
- Audit trail can help trace execution flow

### Working with WebAssembly

- WASM functionality is in `ts/wasm-loader.ts`
- Ensure compatibility with Malbolge's execution model
- Test performance-critical sections

## Context for AI Assistants

### Understanding Malbolge

Malbolge is:
- One of the hardest programming languages to use
- Designed to be nearly impossible to write programs in
- Based on ternary logic and self-modifying code
- Has a very limited instruction set

### Project Philosophy

This project aims to make Malbolge more accessible by:
- Providing a reliable interpreter
- Offering execution visualization through audit trails
- Creating narrative frameworks to explain program behavior

### What NOT to Do

- Don't modify Malbolge code without deep understanding of the language
- Don't assume standard programming paradigms apply
- Don't remove seemingly "useless" code (it may be critical for Malbolge's execution model)
- Don't optimize without profiling (Malbolge's behavior is highly non-intuitive)

## Resources

- Malbolge specification: Research the original language specification
- This project focuses on correct interpretation, not ease of use
- The "Absolute Zero" program demonstrates a minimal valid Malbolge program

## Getting Started

```bash
# Install dependencies
npm install

# Build the project
npm run build

# Open index.html in a browser to run the interpreter
```

## Questions?

For questions about:
- **Malbolge language**: Refer to esoteric programming language resources
- **This implementation**: Check the interpreter source code
- **Project goals**: See README.md

---

*This file helps AI assistants like Claude Code understand the project structure and context.*
