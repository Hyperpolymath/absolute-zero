# Security Policy

## Supported Versions

| Version | Supported          |
| ------- | ------------------ |
| 0.1.x   | :white_check_mark: |

## Security Context

**Absolute Zero** is a formal verification research project. While it contains:
- Proof assistant code (Coq, Lean 4, Z3, Agda, Isabelle)
- Interpreters for esoteric languages (Malbolge, Brainfuck, Whitespace)
- Web interface components

**This is NOT production software**. It is an academic research project exploring the formal verification of Certified Null Operations (CNOs).

## Threat Model

### In Scope

1. **Proof Soundness**: Vulnerabilities in formal proofs that could lead to incorrect theorems
2. **Interpreter Security**: Malicious inputs to Malbolge/Brainfuck/Whitespace interpreters
3. **Container Security**: Issues with the Containerfile or container execution
4. **Dependency Vulnerabilities**: Known CVEs in proof assistant dependencies

### Out of Scope

1. **Web Interface**: This is a demonstration interface, not production-ready
2. **Performance DoS**: Project is not designed for high-load production use
3. **Example Code**: The 30+ language examples are for demonstration only

## Reporting a Vulnerability

**DO NOT** open a public GitHub/GitLab issue for security vulnerabilities.

Instead:

1. **Email**: Send details to `jonathan@metadatastician.art`
2. **Subject**: `[SECURITY] Absolute Zero: [Brief Description]`
3. **Include**:
   - Description of the vulnerability
   - Steps to reproduce
   - Potential impact
   - Suggested fix (if any)

### Response Timeline

- **Acknowledgment**: Within 48 hours
- **Initial Assessment**: Within 7 days
- **Fix Timeline**: Depends on severity
  - Critical (proof soundness): 14 days
  - High (RCE in interpreter): 30 days
  - Medium (dependency CVE): 60 days
  - Low (documentation): Next release

## Known Limitations

### Proof Assistant Limitations

1. **Admitted Statements**: Currently **27 `Admitted`** in Coq proofs and **19 `sorry`** in Lean proofs
   - These are incomplete proofs, not security vulnerabilities
   - See `VERIFICATION_RESULTS.adoc` for status

2. **Axiomatization**: Some theorems rely on axioms
   - `shannon_entropy` axiomatized (should be defined)
   - `second_law` axiomatized (circular reasoning)
   - See `proofs/coq/physics/LandauerDerivation.v`

3. **Floating Point**: ~~Lean 4 used `Float` instead of `Real`~~ (Fixed in commit `063e560`)

### Interpreter Security

1. **Malbolge Interpreter**
   - Turing-complete language
   - Can run indefinitely (no timeout by default)
   - **Mitigation**: Run in sandboxed container

2. **Brainfuck/Whitespace**
   - Python interpreters without resource limits
   - **Mitigation**: Use Podman/Docker with resource constraints

### Web Interface

1. **TypeScript Code**: ⚠️ DEPRECATED - Being migrated to Deno
   - `ts/` directory will be removed
   - Not security-hardened

2. **WASM Module**: `wasm/absolute_zero.wasm`
   - Not integrated with build system
   - Provenance unclear
   - **Recommendation**: Rebuild from source

## Secure Development Practices

### Proof Development

1. **No `Admitted`/`sorry` in production**
   - All proofs must be completed
   - Current status: 68% Coq, 66% Lean

2. **Review axioms carefully**
   - Document why each axiom is necessary
   - Attempt to derive from first principles

3. **Cross-prover verification**
   - Prove same theorem in Coq AND Lean 4
   - Use Z3 for property-based testing

### Code Development

1. **Use Deno (not Node.js)**
   - Built-in security permissions
   - No implicit network/file access

2. **Container isolation**
   - Run all untrusted code in Podman/Docker
   - Use SELinux labels (`-v path:Z`)

3. **Dependency auditing**
   - `deno task check` before releases
   - Monitor CVE databases

## Security Checklist

Before releasing v1.0:

- [ ] Complete all `Admitted` proofs (currently 27)
- [ ] Complete all `sorry` proofs (currently 19)
- [ ] Derive (not axiomatize) Landauer's Principle
- [ ] Replace TypeScript with Deno
- [ ] Rebuild WASM from source
- [ ] Add interpreter timeouts
- [ ] Add resource limits to container
- [ ] Audit all dependencies
- [ ] Enable SELinux/AppArmor in container
- [ ] Add input validation to web interface
- [ ] Set up automated CVE scanning

## Attribution

We use:
- **Coq 8.19**: Formal proof assistant
- **Lean 4**: Dependent type theory prover
- **Z3 4.13**: SMT solver
- **Deno**: Secure TypeScript/JavaScript runtime
- **Podman/Docker**: Container isolation

Please report security issues in these dependencies to their respective maintainers.

## Disclosure Policy

Once a vulnerability is fixed:

1. We will publish a security advisory
2. Credit the reporter (unless they request anonymity)
3. Provide a CVE identifier (if applicable)
4. Document the fix in release notes

## Cryptographic Note

This project does **NOT** implement cryptography. It is a formal verification framework for proving programs do nothing (Certified Null Operations).

If you're looking for verified cryptography, see:
- [Fiat-Crypto](https://github.com/mit-plv/fiat-crypto) (verified elliptic curve cryptography)
- [HACL*](https://github.com/project-everest/hacl-star) (verified crypto library)

## License Implications

This project is dual-licensed:
- **AGPL 3.0**: Open-source use (copyleft)
- **Palimpsest 0.5**: Academic research use

Security fixes will be provided under both licenses.

## Contact

- **Security Issues**: jonathan@metadatastician.art
- **General Issues**: https://github.com/Hyperpolymath/absolute-zero/issues
- **GitLab (full repo)**: https://gitlab.com/maa-framework/6-the-foundation/absolute-zero

---

**Last Updated**: 2025-11-22
**Version**: 0.1.0
