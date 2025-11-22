# Guide to CNO Proofs

A practical guide to proving programs are Certified Null Operations using different proof assistants.

## Quick Reference

| Proof System | Use Case | Difficulty |
|--------------|----------|------------|
| Z3 | Automated SMT | Easy |
| Coq | Constructive proofs | Medium |
| Lean 4 | Modern tactics | Medium |
| Isabelle/HOL | Production systems | Hard |
| Agda | Dependent types | Hard |
| Mizar | Mathematical library | Hard |

## Proof Strategy

### Step 1: Identify CNO Candidates

Programs likely to be CNOs:
- Empty programs
- Single NOP instructions
- Balanced operations (e.g., `+-` in Brainfuck)
- Identity functions

### Step 2: State the Theorem

Format:
```
Theorem <name>: is_CNO(<program>)
```

### Step 3: Prove Four Properties

1. **Termination**: `∀σ. terminates(p, σ)`
2. **Identity**: `∀σ. eval(p, σ) = σ`
3. **Purity**: `∀σ. pure(σ, eval(p, σ))`
4. **Reversibility**: `energy_dissipated(p) = 0`

## Coq Proofs

### Basic Template

```coq
Theorem my_cno_proof : is_CNO my_program.
Proof.
  unfold is_CNO.
  repeat split.
  - (* Termination *)
    intros s. exists (eval my_program s). reflexivity.
  - (* Identity *)
    intros s. unfold eval. simpl. reflexivity.
  - (* Purity *)
    intros s. unfold pure, no_io, no_memory_alloc.
    split; reflexivity.
  - (* Reversibility *)
    unfold thermodynamically_reversible, energy_dissipated.
    intros s. reflexivity.
Qed.
```

### Tactics Cheat Sheet

- `unfold` - Expand definitions
- `intros` - Introduce variables
- `split` - Break conjunctions
- `reflexivity` - Prove `x = x`
- `inversion` - Case analysis on inductive types
- `induction` - Structural induction

### Example: Empty Program

```coq
Theorem empty_is_cno : is_CNO [].
Proof.
  unfold is_CNO.
  repeat split.
  - intros s. exists s. constructor.
  - intros s s' Heval. inversion Heval; subst.
    unfold state_eq. repeat split; try reflexivity.
    unfold mem_eq. reflexivity.
  - intros s s' Heval. inversion Heval; subst.
    unfold pure. split; reflexivity.
  - unfold thermodynamically_reversible.
    intros. reflexivity.
Qed.
```

## Z3 Verification

### SMT-LIB Template

```smt2
; Define CNO property
(define-fun is-cno ((p Program)) Bool
  (forall ((s State))
    (and
      (terminates p s)
      (= (eval p s) s)
      (no-side-effects p s))))

; Assert program is CNO
(assert (is-cno my-program))

; Check
(check-sat)  ; Should return 'sat'
```

### Verification Strategy

1. Model program state
2. Define evaluation semantics
3. Assert CNO properties
4. Run Z3 solver

## Lean 4 Proofs

### Basic Template

```lean
theorem my_cno : isCNO myProgram := by
  unfold isCNO
  constructor
  · -- Termination
    intro s
    exact terminates_always myProgram s
  constructor
  · -- Identity
    intro s
    unfold ProgramState.eq eval
    simp
  constructor
  · -- Purity
    intro s
    unfold pure
    simp
  · -- Reversibility
    unfold thermodynamicallyReversible
    intro s
    rfl
```

### Tactics

- `by` - Start tactic mode
- `intro` - Introduce variables
- `unfold` - Expand definitions
- `simp` - Simplify
- `rfl` - Reflexivity
- `constructor` - Build structure

## Agda Proofs

### Record-Based CNO

```agda
empty-is-cno : IsCNO []
empty-is-cno = record
  { cno-terminates = λ s → terminates-always [] s
  ; cno-identity = λ s → (λ addr → refl) , refl , refl , refl
  ; cno-pure = λ s → refl , (λ addr → refl)
  ; cno-reversible = λ s → refl
  }
```

### Key Concepts

- Records for structured proofs
- Lambda functions for universal quantification
- `refl` for equality proofs

## Isabelle/HOL Proofs

### Declarative Style

```isabelle
theorem empty_is_cno: "is_CNO []"
proof -
  show "∀s. terminates [] s"
    by (auto simp: terminates_def)
  show "∀s. state_eq (eval [] s) s"
    by (auto simp: state_eq_def eval.simps)
  show "∀s. pure s (eval [] s)"
    by (auto simp: pure_def eval.simps)
  show "thermodynamically_reversible []"
    by (auto simp: thermodynamically_reversible_def)
qed
```

### Proof Methods

- `auto` - Automated proof search
- `simp` - Simplification
- `by` - Single-step proof
- `qed` - End proof

## Common Proof Patterns

### Pattern 1: Empty Program

Always a CNO. Trivial proof by reflexivity.

### Pattern 2: Single NOP

Preserves everything except PC. Need to account for PC change.

### Pattern 3: Balanced Operations

Must show operations cancel out.

**Example** (Brainfuck `+-`):
```
Initial: cell[i] = n
After +: cell[i] = n + 1
After -: cell[i] = (n + 1) - 1 = n
```

### Pattern 4: Composition

Use composition theorem:
```
is_CNO(p1) ∧ is_CNO(p2) → is_CNO(p1 · p2)
```

## Debugging Failed Proofs

### Problem: Can't Prove Termination

**Solution**: Check if program actually terminates!
- Add loop bounds
- Verify no infinite loops

### Problem: State Not Preserved

**Solution**: Check for subtle state changes
- PC increment
- Register modifications
- Memory writes

### Problem: Side Effects

**Solution**: Track I/O carefully
- Output operations
- Input operations
- File/network access

## Advanced Techniques

### Proof by Computation

Sometimes you can just evaluate:

```coq
Theorem concrete_cno : is_CNO [Nop].
Proof.
  vm_compute. reflexivity.
Qed.
```

### Proof Automation

Write tactics to automate CNO proofs:

```coq
Ltac solve_cno :=
  unfold is_CNO;
  repeat split;
  try (intros; reflexivity);
  try (intros; simpl; reflexivity).

Theorem auto_cno : is_CNO [].
Proof. solve_cno. Qed.
```

### Counterexample Generation

Use SMT to find counterexamples:

```smt2
(assert (not (is-cno my-program)))
(check-sat)
(get-model)  ; Shows why it's not a CNO
```

## Multi-Prover Verification

For maximum confidence, verify in multiple systems:

1. **Z3**: Quick automated check
2. **Coq**: Detailed constructive proof
3. **Lean**: Modern verification
4. **Isabelle**: Production-grade verification

Agreement across systems increases confidence.

## Resources

- Coq: https://coq.inria.fr/documentation
- Lean 4: https://lean-lang.org/documentation/
- Isabelle: https://isabelle.in.tum.de/documentation.html
- Z3: https://microsoft.github.io/z3guide/

## Conclusion

Proving CNO properties requires:
1. Clear understanding of program semantics
2. Systematic proof strategy
3. Appropriate proof assistant
4. Patience and practice

Start with simple examples (empty program) and build up to complex obfuscated CNOs.

---

**See Also**:
- `proofs/coq/` - Coq proof examples
- `proofs/lean4/` - Lean 4 examples
- `theory.md` - Theoretical foundations
