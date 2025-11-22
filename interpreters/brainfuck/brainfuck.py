#!/usr/bin/env python3
"""
Brainfuck Interpreter with CNO Detection

Brainfuck is an esoteric language with only 8 instructions.
This makes it ideal for CNO verification - we can easily prove
when a program does nothing.

Author: Jonathan D. A. Jewell
Project: Absolute Zero
License: AGPL-3.0 / Palimpsest 0.5
"""

from typing import List, Tuple
from dataclasses import dataclass, field


@dataclass
class BrainfuckState:
    """State of the Brainfuck interpreter"""
    memory: List[int] = field(default_factory=lambda: [0] * 30000)
    pointer: int = 0
    program_counter: int = 0
    input_buffer: List[int] = field(default_factory=list)
    output_buffer: List[int] = field(default_factory=list)
    halted: bool = False
    cycles: int = 0
    max_cycles: int = 1000000


class BrainfuckInterpreter:
    """Brainfuck interpreter with CNO detection"""

    def __init__(self, program: str, max_cycles: int = 1000000):
        self.program = program
        self.max_cycles = max_cycles
        self.state = BrainfuckState(max_cycles=max_cycles)

    def step(self) -> None:
        """Execute a single instruction"""
        if self.state.halted or self.state.cycles >= self.max_cycles:
            self.state.halted = True
            return

        if self.state.program_counter >= len(self.program):
            self.state.halted = True
            return

        instruction = self.program[self.state.program_counter]
        self.state.cycles += 1

        if instruction == '>':
            # Move pointer right
            self.state.pointer = (self.state.pointer + 1) % len(self.state.memory)
            self.state.program_counter += 1

        elif instruction == '<':
            # Move pointer left
            self.state.pointer = (self.state.pointer - 1) % len(self.state.memory)
            self.state.program_counter += 1

        elif instruction == '+':
            # Increment cell
            self.state.memory[self.state.pointer] = (
                self.state.memory[self.state.pointer] + 1
            ) % 256
            self.state.program_counter += 1

        elif instruction == '-':
            # Decrement cell
            self.state.memory[self.state.pointer] = (
                self.state.memory[self.state.pointer] - 1
            ) % 256
            self.state.program_counter += 1

        elif instruction == '.':
            # Output cell
            self.state.output_buffer.append(
                self.state.memory[self.state.pointer]
            )
            self.state.program_counter += 1

        elif instruction == ',':
            # Input to cell
            if self.state.input_buffer:
                self.state.memory[self.state.pointer] = self.state.input_buffer.pop(0)
            else:
                self.state.memory[self.state.pointer] = 0
            self.state.program_counter += 1

        elif instruction == '[':
            # Jump forward if cell is zero
            if self.state.memory[self.state.pointer] == 0:
                # Find matching ]
                depth = 1
                pc = self.state.program_counter + 1
                while depth > 0 and pc < len(self.program):
                    if self.program[pc] == '[':
                        depth += 1
                    elif self.program[pc] == ']':
                        depth -= 1
                    pc += 1
                self.state.program_counter = pc
            else:
                self.state.program_counter += 1

        elif instruction == ']':
            # Jump backward if cell is non-zero
            if self.state.memory[self.state.pointer] != 0:
                # Find matching [
                depth = 1
                pc = self.state.program_counter - 1
                while depth > 0 and pc >= 0:
                    if self.program[pc] == ']':
                        depth += 1
                    elif self.program[pc] == '[':
                        depth -= 1
                    pc -= 1
                self.state.program_counter = pc + 1
            else:
                self.state.program_counter += 1

        else:
            # Ignore other characters (comments)
            self.state.program_counter += 1

    def run(self) -> str:
        """Run program to completion"""
        while not self.state.halted:
            self.step()

        # Convert output to string
        return ''.join(chr(c) for c in self.state.output_buffer)

    def is_cno(self) -> Tuple[bool, str]:
        """
        Check if program is a Certified Null Operation

        Returns: (is_cno, reason)
        """
        # Save initial state
        initial_memory = self.state.memory[:]
        initial_pointer = self.state.pointer

        # Run the program
        self.run()

        # Check CNO properties
        if self.state.cycles >= self.max_cycles:
            return False, "Program did not terminate (hit max cycles)"

        if len(self.state.output_buffer) > 0:
            return False, "Program produced output (not pure)"

        # For full CNO verification, we'd check memory equality
        # But for practical purposes, we check key invariants

        # Memory should be unchanged
        memory_unchanged = all(
            self.state.memory[i] == initial_memory[i]
            for i in range(len(self.state.memory))
        )

        if not memory_unchanged:
            return False, "Program modified memory"

        # Pointer should be at initial position
        if self.state.pointer != initial_pointer:
            return False, f"Pointer moved from {initial_pointer} to {self.state.pointer}"

        return True, "Program is a CNO ✓"


def test_cno(program: str, name: str) -> None:
    """Test if a program is a CNO"""
    interpreter = BrainfuckInterpreter(program)
    is_cno, reason = interpreter.is_cno()

    status = "✓" if is_cno else "✗"
    print(f"{name:30s} [{status}] {reason}")


if __name__ == "__main__":
    print("=" * 70)
    print("Brainfuck CNO Detection Tests")
    print("=" * 70)
    print()

    # Test cases
    test_cno("", "Empty program")
    test_cno("This is a comment", "Comments only")
    test_cno("><", "Move right then left")
    test_cno("+-", "Increment then decrement")
    test_cno("+", "Increment (not CNO)")
    test_cno(".", "Output (not CNO)")
    test_cno(">+<", "Move, increment, move back (not CNO)")
    test_cno(">><< >><<", "Multiple balanced moves")
    test_cno("+-+-+-", "Multiple balanced increments")
    test_cno("[+]", "Loop (should be CNO if cell is 0)")
    test_cno("[]", "Empty loop")
    test_cno("+[-]", "Increment then loop to zero (not CNO)")
    test_cno("+>-<", "Increment one cell, decrement another (not CNO)")

    print()
    print("=" * 70)
