from __future__ import annotations

import unittest

from scripts.run_p0_eft_holst_membrane_co_optimisation import run_scan


class P0EFTHolstMembraneCoOptimisationTests(unittest.TestCase):
    def test_co_optimisation_runs(self) -> None:
        payload = run_scan()

        self.assertEqual(payload["status"], "holst-membrane-co-optimisation-computed")
        self.assertIn("best_unit_amplitude", payload)
        self.assertGreater(len(payload["rows"]), 10)


if __name__ == "__main__":
    unittest.main()
