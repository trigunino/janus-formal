from __future__ import annotations

import unittest

from scripts.build_lensing_qdet_qcross_derivation_map import BRANCHES


class LensingQdetQcrossDerivationMapTests(unittest.TestCase):
    def test_projection_branches_use_tetrad_map_target(self) -> None:
        branches = {row["branch"]: row for row in BRANCHES}

        self.assertIn("u_minus_to_plus", branches["effective_with_projection"]["q_cross"])
        self.assertIn("L_minus_to_plus", branches["effective_with_projection"]["requirements"])
        self.assertIn("K_plus/K_minus", branches["effective_with_projection"]["requirements"])
        self.assertIn("u_minus_to_plus", branches["proper_density_full"]["q_cross"])
        self.assertIn("K_plus/K_minus", branches["proper_density_full"]["requirements"])

    def test_raw_scale_insert_remains_forbidden(self) -> None:
        branches = {row["branch"]: row for row in BRANCHES}

        self.assertEqual(branches["raw_m20_scale_insert"]["status"], "forbidden")


if __name__ == "__main__":
    unittest.main()
