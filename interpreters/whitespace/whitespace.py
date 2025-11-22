#!/usr/bin/env python3
"""
Whitespace Interpreter with CNO Detection

Whitespace is an esoteric language that uses only spaces, tabs, and linefeeds.
All other characters are ignored.

Author: Jonathan D. A. Jewell
Project: Absolute Zero
License: AGPL-3.0 / Palimpsest 0.5
"""

from typing import List, Dict, Tuple
from dataclasses import dataclass, field


@dataclass
class WhitespaceState:
    """State of the Whitespace interpreter"""
    stack: List[int] = field(default_factory=list)
    heap: Dict[int, int] = field(default_factory=dict)
    call_stack: List[int] = field(default_factory=list)
    program_counter: int = 0
    output_buffer: List[str] = field(default_factory=list)
    input_buffer: List[str] = field(default_factory=list)
    halted: bool = False
    cycles: int = 0
    max_cycles: int = 1000000


class WhitespaceInterpreter:
    """Whitespace interpreter with CNO detection"""

    def __init__(self, program: str, max_cycles: int = 1000000):
        # Filter to only whitespace characters
        self.program = ''.join(c for c in program if c in ' \t\n')
        self.state = WhitespaceState(max_cycles=max_cycles)
        self.labels: Dict[str, int] = {}
        self._parse_labels()

    def _parse_labels(self) -> None:
        """Pre-parse all labels for jump targets"""
        i = 0
        while i < len(self.program):
            if self._match(i, '\n  '):  # Mark location (label)
                label = self._parse_label(i + 3)
                if label is not None:
                    label_str, offset = label
                    self.labels[label_str] = i
                    i += offset
            i += 1

    def _match(self, pos: int, pattern: str) -> bool:
        """Check if pattern matches at position"""
        return self.program[pos:pos+len(pattern)] == pattern

    def _parse_number(self, pos: int) -> Tuple[int, int]:
        """Parse a number (space=0, tab=1, terminated by newline)"""
        sign = 1
        if pos >= len(self.program):
            return 0, 0

        # First char is sign (space=+, tab=-)
        if self.program[pos] == '\t':
            sign = -1
        pos += 1

        # Parse binary number
        num = 0
        offset = 1
        while pos < len(self.program) and self.program[pos] != '\n':
            num = num * 2 + (1 if self.program[pos] == '\t' else 0)
            pos += 1
            offset += 1

        return sign * num, offset + 1

    def _parse_label(self, pos: int) -> Tuple[str, int]:
        """Parse a label (terminated by newline)"""
        label = []
        offset = 0
        while pos + offset < len(self.program) and self.program[pos + offset] != '\n':
            label.append(self.program[pos + offset])
            offset += 1
        return ''.join(label), offset + 1

    def step(self) -> None:
        """Execute a single instruction"""
        if self.state.halted or self.state.cycles >= self.state.max_cycles:
            self.state.halted = True
            return

        if self.state.program_counter >= len(self.program):
            self.state.halted = True
            return

        pos = self.state.program_counter
        self.state.cycles += 1

        # Stack manipulation (space prefix)
        if self._match(pos, '  '):  # Push number
            num, offset = self._parse_number(pos + 2)
            self.state.stack.append(num)
            self.state.program_counter += 2 + offset

        elif self._match(pos, ' \n '):  # Duplicate top
            if self.state.stack:
                self.state.stack.append(self.state.stack[-1])
            self.state.program_counter += 3

        elif self._match(pos, ' \n\t'):  # Swap top two
            if len(self.state.stack) >= 2:
                self.state.stack[-1], self.state.stack[-2] = \
                    self.state.stack[-2], self.state.stack[-1]
            self.state.program_counter += 3

        elif self._match(pos, ' \n\n'):  # Discard top
            if self.state.stack:
                self.state.stack.pop()
            self.state.program_counter += 3

        # Arithmetic (tab-space prefix)
        elif self._match(pos, '\t   '):  # Addition
            if len(self.state.stack) >= 2:
                b = self.state.stack.pop()
                a = self.state.stack.pop()
                self.state.stack.append(a + b)
            self.state.program_counter += 4

        elif self._match(pos, '\t  \t'):  # Subtraction
            if len(self.state.stack) >= 2:
                b = self.state.stack.pop()
                a = self.state.stack.pop()
                self.state.stack.append(a - b)
            self.state.program_counter += 4

        elif self._match(pos, '\t  \n'):  # Multiplication
            if len(self.state.stack) >= 2:
                b = self.state.stack.pop()
                a = self.state.stack.pop()
                self.state.stack.append(a * b)
            self.state.program_counter += 4

        # Heap access (tab-tab prefix)
        elif self._match(pos, '\t\t '):  # Store to heap
            if len(self.state.stack) >= 2:
                value = self.state.stack.pop()
                address = self.state.stack.pop()
                self.state.heap[address] = value
            self.state.program_counter += 3

        elif self._match(pos, '\t\t\t'):  # Retrieve from heap
            if self.state.stack:
                address = self.state.stack.pop()
                self.state.stack.append(self.state.heap.get(address, 0))
            self.state.program_counter += 3

        # I/O (tab-newline prefix)
        elif self._match(pos, '\t\n  '):  # Output character
            if self.state.stack:
                char_code = self.state.stack.pop()
                self.state.output_buffer.append(chr(char_code % 256))
            self.state.program_counter += 4

        elif self._match(pos, '\t\n \t'):  # Output number
            if self.state.stack:
                num = self.state.stack.pop()
                self.state.output_buffer.append(str(num))
            self.state.program_counter += 4

        # Flow control (newline prefix)
        elif self._match(pos, '\n\n\n'):  # End program
            self.state.halted = True

        else:
            # Unknown instruction or comment
            self.state.program_counter += 1

    def run(self) -> str:
        """Run program to completion"""
        while not self.state.halted:
            self.step()

        return ''.join(self.state.output_buffer)

    def is_cno(self) -> Tuple[bool, str]:
        """Check if program is a Certified Null Operation"""
        # Save initial state
        initial_stack = self.state.stack[:]
        initial_heap = self.state.heap.copy()

        # Run the program
        self.run()

        # Check CNO properties
        if self.state.cycles >= self.state.max_cycles:
            return False, "Program did not terminate"

        if len(self.state.output_buffer) > 0:
            return False, "Program produced output"

        if self.state.stack != initial_stack:
            return False, "Stack was modified"

        if self.state.heap != initial_heap:
            return False, "Heap was modified"

        return True, "Program is a CNO ✓"


def test_cno(program: str, name: str) -> None:
    """Test if a program is a CNO"""
    interpreter = WhitespaceInterpreter(program)
    is_cno, reason = interpreter.is_cno()

    status = "✓" if is_cno else "✗"
    print(f"{name:30s} [{status}] {reason}")


if __name__ == "__main__":
    print("=" * 70)
    print("Whitespace CNO Detection Tests")
    print("=" * 70)
    print()

    # Test cases
    test_cno("", "Empty program")
    test_cno("This is ignored", "Non-whitespace (ignored)")
    test_cno("\n\n\n", "Immediate halt")

    # Push then pop
    test_cno("  \t\n \n\n", "Push 1 then discard")

    # Duplicate then pop twice
    test_cno("  \t\n \n \n\n \n\n", "Push, dup, pop, pop")

    print()
    print("=" * 70)
