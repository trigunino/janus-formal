from __future__ import annotations

import unittest

from scripts.check_symbolic_formulas import run_checks


class SymbolicFormulaTests(unittest.TestCase):
    def test_symbolic_formula_checks_pass(self) -> None:
        failed = [check for check in run_checks() if not check.ok]
        self.assertEqual([], failed)


if __name__ == "__main__":
    unittest.main()

