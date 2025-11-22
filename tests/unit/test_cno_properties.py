#!/usr/bin/env python3
"""
Unit Tests for CNO Properties

Tests the fundamental properties of Certified Null Operations across
different languages and implementations.

Author: Jonathan D. A. Jewell
Project: Absolute Zero
License: AGPL-3.0 / Palimpsest 0.5
"""

import unittest
import sys
import os

# Add interpreters to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../../interpreters/brainfuck'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../../interpreters/whitespace'))

from brainfuck import BrainfuckInterpreter
from whitespace import WhitespaceInterpreter


class TestCNOProperties(unittest.TestCase):
    """Test fundamental CNO properties"""

    def test_empty_program_terminates(self):
        """Empty programs must terminate"""
        bf = BrainfuckInterpreter("")
        bf.run()
        self.assertTrue(bf.state.halted)
        self.assertLess(bf.state.cycles, 10)

    def test_empty_program_no_output(self):
        """Empty programs must produce no output"""
        bf = BrainfuckInterpreter("")
        bf.run()
        self.assertEqual(len(bf.state.output_buffer), 0)

    def test_empty_program_memory_unchanged(self):
        """Empty programs must not modify memory"""
        bf = BrainfuckInterpreter("")
        initial_memory = bf.state.memory[:]
        bf.run()
        self.assertEqual(bf.state.memory, initial_memory)

    def test_empty_program_is_cno(self):
        """Empty program is a CNO"""
        bf = BrainfuckInterpreter("")
        is_cno, reason = bf.is_cno()
        self.assertTrue(is_cno, f"Empty program should be CNO: {reason}")


class TestBrainfuckCNOs(unittest.TestCase):
    """Test Brainfuck-specific CNOs"""

    def test_balanced_moves(self):
        """><  (move right then left) is a CNO"""
        bf = BrainfuckInterpreter("><")
        is_cno, reason = bf.is_cno()
        self.assertTrue(is_cno, f"Balanced moves should be CNO: {reason}")

    def test_balanced_increment(self):
        """+-  (increment then decrement) is a CNO"""
        bf = BrainfuckInterpreter("+-")
        is_cno, reason = bf.is_cno()
        self.assertTrue(is_cno, f"Balanced increment should be CNO: {reason}")

    def test_multiple_balanced(self):
        """>><<+-+-  (multiple balanced ops) is a CNO"""
        bf = BrainfuckInterpreter(">><<+-+-")
        is_cno, reason = bf.is_cno()
        self.assertTrue(is_cno, f"Multiple balanced ops should be CNO: {reason}")

    def test_output_not_cno(self):
        """.  (output) is NOT a CNO"""
        bf = BrainfuckInterpreter(".")
        is_cno, reason = bf.is_cno()
        self.assertFalse(is_cno, "Output should not be CNO")

    def test_increment_not_cno(self):
        """+  (increment) is NOT a CNO"""
        bf = BrainfuckInterpreter("+")
        is_cno, reason = bf.is_cno()
        self.assertFalse(is_cno, "Increment should not be CNO")

    def test_unbalanced_moves_not_cno(self):
        """>  (unbalanced move) is NOT a CNO"""
        bf = BrainfuckInterpreter(">")
        is_cno, reason = bf.is_cno()
        self.assertFalse(is_cno, "Unbalanced move should not be CNO")


class TestWhitespaceCNOs(unittest.TestCase):
    """Test Whitespace-specific CNOs"""

    def test_empty_whitespace(self):
        """Empty Whitespace program is a CNO"""
        ws = WhitespaceInterpreter("")
        is_cno, reason = ws.is_cno()
        self.assertTrue(is_cno, f"Empty should be CNO: {reason}")

    def test_halt_only(self):
        """\\n\\n\\n (halt) is a CNO"""
        ws = WhitespaceInterpreter("\n\n\n")
        is_cno, reason = ws.is_cno()
        self.assertTrue(is_cno, f"Halt should be CNO: {reason}")

    def test_ignored_chars(self):
        """Non-whitespace chars are ignored, program is CNO"""
        ws = WhitespaceInterpreter("This text is completely ignored")
        is_cno, reason = ws.is_cno()
        self.assertTrue(is_cno, f"Ignored chars should be CNO: {reason}")


class TestCNOComposition(unittest.TestCase):
    """Test composition of CNOs"""

    def test_sequential_cnos(self):
        """Sequential composition of CNOs is a CNO"""
        # ><  followed by  +-
        bf = BrainfuckInterpreter("><+-")
        is_cno, reason = bf.is_cno()
        self.assertTrue(is_cno, f"Sequential CNOs should be CNO: {reason}")

    def test_multiple_compositions(self):
        """Multiple CNO compositions"""
        # Multiple balanced pairs
        bf = BrainfuckInterpreter("><><><+-+-+-")
        is_cno, reason = bf.is_cno()
        self.assertTrue(is_cno, f"Multiple compositions should be CNO: {reason}")


class TestNonCNOs(unittest.TestCase):
    """Test programs that are NOT CNOs"""

    def test_hello_world_not_cno(self):
        """Hello World programs are not CNOs"""
        # Simplified: just output something
        bf = BrainfuckInterpreter("+++++++++[>++++++++<-]>.")
        is_cno, reason = bf.is_cno()
        self.assertFalse(is_cno, "Hello World should not be CNO")

    def test_complex_computation_not_cno(self):
        """Complex computations are not CNOs"""
        bf = BrainfuckInterpreter(">+++++[<+++++>-]")
        is_cno, reason = bf.is_cno()
        self.assertFalse(is_cno, "Complex computation should not be CNO")


class TestPerformance(unittest.TestCase):
    """Performance tests"""

    def test_verification_speed(self):
        """CNO verification should be fast"""
        import time

        programs = ["", "><", "+-", ">><<", "+-+-+-+-"]

        start = time.time()
        for prog in programs:
            bf = BrainfuckInterpreter(prog)
            bf.is_cno()
        elapsed = time.time() - start

        # Should verify all in under 1 second
        self.assertLess(elapsed, 1.0, "Verification too slow")


if __name__ == '__main__':
    # Run tests with verbose output
    unittest.main(verbosity=2)
