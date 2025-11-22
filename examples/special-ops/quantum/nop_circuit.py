#!/usr/bin/env python3
"""
Quantum Circuit with No Net Effect: Composite CNOs in Qiskit
=============================================================

This demonstrates quantum Change-Nothing Operations through gate sequences
that cancel out, returning the system to its initial state. These composite
CNOs illustrate deep principles about reversibility, information, and entropy.

CONCEPTS EXPLORED:
1. Self-inverse gates and gate cancellation
2. Reversible computation and Landauer's principle
3. Quantum erasure and information thermodynamics
4. The distinction between logical CNO and physical evolution
5. Decoherence during "round-trip" operations

Run with: python nop_circuit.py
Requires: pip install qiskit qiskit-aer matplotlib
"""

from qiskit import QuantumCircuit, QuantumRegister, ClassicalRegister
from qiskit import transpile
from qiskit_aer import AerSimulator
from qiskit.visualization import plot_histogram, circuit_drawer
import matplotlib.pyplot as plt


def identity_gate_example():
    """
    Example 1: Explicit identity gate

    The I gate is the fundamental quantum CNO.
    Matrix representation: [[1, 0], [0, 1]]
    """
    qc = QuantumCircuit(1, 1, name="Identity Gate")

    # Start in |0⟩
    # Apply identity - changes nothing
    qc.id(0)
    qc.id(0)
    qc.id(0)

    qc.measure(0, 0)

    print("=" * 70)
    print("Example 1: Identity Gate (Fundamental CNO)")
    print("=" * 70)
    print(qc.draw(output='text'))
    print("\nLogical effect: None (CNO)")
    print("Physical reality: Each gate takes time, allowing decoherence")
    print()

    return qc


def self_inverse_gates():
    """
    Example 2: Self-inverse gates (X, Y, Z, H)

    Many quantum gates are self-inverse: G² = I
    Applying them twice creates a CNO.

    REVERSIBILITY: This demonstrates perfect reversibility in quantum mechanics.
    The ability to "undo" operations is fundamental to quantum computation and
    connects to Landauer's principle about energy-free reversible computation.
    """
    qc = QuantumCircuit(4, 4, name="Self-Inverse Gates")

    # Put qubits in superposition
    qc.h(0)
    qc.h(1)
    qc.h(2)
    qc.h(3)

    qc.barrier()

    # Apply self-inverse gates twice (creates CNO)
    qc.x(0)
    qc.x(0)  # X² = I (Pauli-X is self-inverse)

    qc.y(1)
    qc.y(1)  # Y² = I (Pauli-Y is self-inverse)

    qc.z(2)
    qc.z(2)  # Z² = I (Pauli-Z is self-inverse)

    qc.h(3)
    qc.h(3)  # H² = I (Hadamard is self-inverse)

    qc.barrier()

    # All qubits back in superposition (unchanged from after first barrier)
    qc.measure_all()

    print("=" * 70)
    print("Example 2: Self-Inverse Gates")
    print("=" * 70)
    print(qc.draw(output='text'))
    print("\nEach pair of gates cancels: G·G = I")
    print("Logical CNO, but physical time evolution occurred")
    print()

    return qc


def reversible_computation():
    """
    Example 3: Complex computation that reverses itself

    This demonstrates Landauer's principle: reversible computation can be
    performed without energy dissipation. The circuit computes something
    complex, then uncomputes it, achieving a CNO.

    LANDAUER'S PRINCIPLE:
    - Irreversible information erasure requires energy: kT ln(2) per bit
    - Reversible computation can be thermodynamically free
    - Quantum gates are naturally reversible (unitary)
    - This CNO is a thermodynamic CNO in the ideal limit
    """
    qc = QuantumCircuit(3, 3, name="Reversible Computation")

    # Initial state: |000⟩

    # Forward computation: create complex entangled state
    qc.h(0)
    qc.cx(0, 1)
    qc.cx(1, 2)
    qc.t(0)
    qc.t(1)
    qc.s(2)
    qc.cx(2, 1)
    qc.h(2)

    qc.barrier(label="Peak Complexity")

    # Reverse computation: uncompute (apply inverse of each gate in reverse order)
    qc.h(2)
    qc.cx(2, 1)
    qc.sdg(2)  # S† (inverse of S)
    qc.tdg(1)  # T† (inverse of T)
    qc.tdg(0)  # T† (inverse of T)
    qc.cx(1, 2)
    qc.cx(0, 1)
    qc.h(0)

    # Final state: |000⟩ (back where we started - CNO!)

    qc.measure_all()

    print("=" * 70)
    print("Example 3: Reversible Computation (Landauer's Principle)")
    print("=" * 70)
    print(qc.draw(output='text'))
    print("\nComputes complex entanglement, then uncomputes it")
    print("Demonstrates reversible computation → thermodynamic CNO")
    print("In ideal quantum computer: zero energy dissipation")
    print("In reality: decoherence and gate errors cost energy")
    print()

    return qc


def rotation_cycle():
    """
    Example 4: Rotation gates that complete a full cycle

    Rotating by 2π (360°) returns to the same state (with possible global phase).
    This is a continuous version of the CNO concept.

    GEOMETRIC PHASE: Interestingly, doing this can accumulate a global phase
    (Berry phase), which is undetectable by measurement but matters for
    interference. This shows that "no change" can still have subtle effects.
    """
    qc = QuantumCircuit(3, 3, name="Rotation Cycle")

    # Prepare interesting initial state
    qc.h(0)
    qc.rx(0.7, 1)
    qc.ry(1.2, 2)

    qc.barrier()

    # Rotate around X-axis by 2π (4 rotations of π/2)
    qc.rx(3.14159265359/2, 0)
    qc.rx(3.14159265359/2, 0)
    qc.rx(3.14159265359/2, 0)
    qc.rx(3.14159265359/2, 0)

    # Rotate around Y-axis by 2π (8 rotations of π/4)
    for _ in range(8):
        qc.ry(3.14159265359/4, 1)

    # Rotate around Z-axis by 2π (16 rotations of π/8)
    for _ in range(16):
        qc.rz(3.14159265359/8, 2)

    qc.barrier()

    # State unchanged (up to global phase)
    qc.measure_all()

    print("=" * 70)
    print("Example 4: Rotation Cycle (2π = Identity)")
    print("=" * 70)
    print("Circuit too long to display, but conceptually:")
    print("RX(2π) = RY(2π) = RZ(2π) = I (up to global phase)")
    print("\nGlobal phase is unobservable but can affect interference")
    print("This is a 'geometric' CNO with subtle quantum effects")
    print()

    return qc


def measurement_is_not_cno():
    """
    Example 5: Measurement destroys superposition (NOT a CNO)

    This demonstrates what is NOT a quantum CNO. Measurement is irreversible
    and collapses the quantum state, destroying superposition and entanglement.

    NO-CLONING THEOREM:
    Measurement reveals information but destroys it. You cannot clone an unknown
    quantum state, so measurement is fundamentally information-destructive.
    This connects to the arrow of time and entropy increase.
    """
    qc = QuantumCircuit(2, 4, name="Measurement ≠ CNO")

    # Create Bell state (maximally entangled)
    qc.h(0)
    qc.cx(0, 1)

    # Measure (COLLAPSES STATE - not a CNO!)
    qc.measure(0, 0)
    qc.measure(1, 1)

    qc.barrier()

    # Try to "restore" by re-preparing Bell state
    # This is NOT the same state - we've lost quantum information
    qc.h(0)
    qc.cx(0, 1)

    # Measure again
    qc.measure(0, 2)
    qc.measure(1, 3)

    print("=" * 70)
    print("Example 5: Measurement is NOT a CNO")
    print("=" * 70)
    print(qc.draw(output='text'))
    print("\nMeasurement collapses superposition (irreversible!)")
    print("Re-preparing state ≠ undoing measurement")
    print("Quantum information lost forever (no-cloning theorem)")
    print()

    return qc


def decoherence_during_cno():
    """
    Example 6: Noise accumulation during "do nothing" operations

    Even during CNO operations, decoherence occurs. This demonstrates the
    gap between ideal quantum CNOs and physical reality.
    """
    from qiskit_aer.noise import NoiseModel, depolarizing_error, thermal_relaxation_error

    qc = QuantumCircuit(1, 1, name="CNO with Decoherence")

    # Start in superposition
    qc.h(0)

    # Do nothing (with identity gates to consume time)
    for _ in range(10):
        qc.id(0)

    qc.measure(0, 0)

    # Create noise model
    noise_model = NoiseModel()

    # T1 and T2 relaxation times (microseconds)
    t1 = 50.0  # Amplitude damping time
    t2 = 70.0  # Dephasing time
    gate_time = 0.1  # Identity gate time (microseconds)

    # Add thermal relaxation error to identity gates
    error = thermal_relaxation_error(t1, t2, gate_time)
    noise_model.add_all_qubit_quantum_error(error, ['id'])

    print("=" * 70)
    print("Example 6: Decoherence During CNO")
    print("=" * 70)
    print(qc.draw(output='text'))
    print("\nLogical CNO: 10 identity gates change nothing")
    print("Physical reality: T1/T2 relaxation causes decoherence")
    print(f"T1 = {t1} μs, T2 = {t2} μs, gate_time = {gate_time} μs")
    print("\nRunning simulation with noise...")

    # Run with and without noise
    simulator = AerSimulator()

    # Without noise
    compiled = transpile(qc, simulator)
    result = simulator.run(compiled, shots=1000).result()
    counts_ideal = result.get_counts()

    # With noise
    compiled_noisy = transpile(qc, simulator)
    result_noisy = simulator.run(compiled_noisy, shots=1000, noise_model=noise_model).result()
    counts_noisy = result_noisy.get_counts()

    print(f"\nIdeal (no noise): {counts_ideal}")
    print(f"With T1/T2 noise: {counts_noisy}")
    print("\nDecoherence causes measurement bias even for CNO!")
    print()

    return qc, noise_model


def main():
    """
    Main function: Run all examples
    """
    print("\n" + "=" * 70)
    print("QUANTUM CHANGE-NOTHING OPERATIONS (CNOs)")
    print("Exploring Identity, Reversibility, and Information in Quantum Computing")
    print("=" * 70)
    print()

    # Run all examples
    qc1 = identity_gate_example()
    qc2 = self_inverse_gates()
    qc3 = reversible_computation()
    qc4 = rotation_cycle()
    qc5 = measurement_is_not_cno()
    qc6, noise = decoherence_during_cno()

    # Summary
    print("=" * 70)
    print("SUMMARY: Quantum CNOs and Cutting-Edge Physics")
    print("=" * 70)
    print("""
1. IDENTITY GATES: Fundamental quantum CNO, matrix I = [[1,0],[0,1]]
   - Preserves all quantum properties (superposition, entanglement, phase)
   - Used for timing and synchronization in quantum circuits

2. REVERSIBLE COMPUTATION: Gates are unitary (reversible by definition)
   - Connects to Landauer's principle: reversible = thermodynamically free
   - Quantum computation naturally avoids information erasure energy cost
   - "Absolute Zero" in thermodynamic sense: zero dissipation limit

3. DECOHERENCE vs. CNO: Ideal CNO doesn't exist in practice
   - Environmental coupling causes T1 (amplitude damping) and T2 (dephasing)
   - Time evolution ≠ state change in ideal quantum mechanics
   - Physical reality: time → decoherence, even for CNO

4. MEASUREMENT: The anti-CNO
   - Irreversible collapse of superposition
   - Information extraction destroys quantum information
   - No-cloning theorem: cannot copy unknown quantum state
   - Increases entropy (aligns with thermodynamic arrow of time)

5. NO-CLONING THEOREM: Profound limit on quantum CNOs
   - Cannot create independent copy: |ψ⟩ ↛ |ψ⟩⊗|ψ⟩
   - Even "preserve state" (CNO) respects this limit
   - Information is more fundamental than state in quantum mechanics

6. LANDAUER'S PRINCIPLE: Thermodynamic CNO
   - Irreversible erasure: ΔS ≥ k ln(2) → E ≥ kT ln(2)
   - Reversible computation: theoretically zero energy dissipation
   - Quantum gates are reversible → can be energy-free CNOs
   - Connects computation, information, and thermodynamics

CUTTING-EDGE IMPLICATIONS:
- Quantum error correction codes protect CNO operations
- Topological quantum computing: CNO resilience through topology
- Quantum thermodynamics: work extraction from CNO cycles
- Black hole information paradox: quantum CNO at event horizon?
- Quantum foundations: CNO tests of quantum mechanics itself

The quantum CNO is not just "do nothing" - it's a window into the
deepest principles of physics: reversibility, information conservation,
the arrow of time, and the quantum-classical boundary.
    """)

    print("=" * 70)
    print("End of Quantum CNO Examples")
    print("=" * 70)


if __name__ == "__main__":
    main()
