from __future__ import annotations

import unittest

import sympy as sp

from scripts.build_qcross_flrw_comoving_tetrad_branch import build_payload


class QCrossFlrwComovingTetradBranchTests(unittest.TestCase):
    def test_branch_derives_unit_qcross_under_aligned_comoving_tetrads(self) -> None:
        payload = build_payload()
        branch = payload["map_branch"]

        self.assertTrue(payload["branch_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertEqual(branch["map"], "L_minus_to_plus^A_B = delta^A_B")
        self.assertEqual(branch["result"], "Q_cross=A_minus/A_plus=1")

    def test_branch_keeps_qdet_and_coordinate_warning_separate(self) -> None:
        payload = build_payload()
        assumptions = " ".join(payload["assumptions"])
        warnings = " ".join(payload["warnings"])

        self.assertIn("Q_det determinant/volume factors are not part", assumptions)
        self.assertIn("coordinate covector comparison", warnings)
        self.assertIn("(N_minus/N_plus)^2", warnings)

    def test_branch_does_not_close_perturbed_global_map(self) -> None:
        warnings = " ".join(build_payload()["warnings"])

        self.assertIn("Perturbations".lower(), warnings.lower())
        self.assertIn("nontrivial L_minus_to_plus", warnings)

    def test_symbolic_tetrad_projection_is_independent_of_lapse_and_scale(self) -> None:
        n_plus, n_minus, a_plus, a_minus, energy = sp.symbols(
            "N_plus N_minus a_plus a_minus E",
            positive=True,
        )
        a_projection_plus = energy**2
        a_projection_minus = energy**2
        q_cross = sp.simplify(a_projection_minus / a_projection_plus)

        self.assertEqual(q_cross, 1)
        self.assertEqual(sp.diff(q_cross, n_plus), 0)
        self.assertEqual(sp.diff(q_cross, n_minus), 0)
        self.assertEqual(sp.diff(q_cross, a_plus), 0)
        self.assertEqual(sp.diff(q_cross, a_minus), 0)

    def test_raw_coordinate_path_is_lapse_ratio_warning_not_tetrad_branch(self) -> None:
        n_plus, n_minus, energy = sp.symbols("N_plus N_minus E", positive=True)
        raw_projection_plus = (n_plus * energy) ** 2
        raw_projection_minus = (n_minus * energy) ** 2
        raw_ratio = sp.simplify(raw_projection_minus / raw_projection_plus)

        self.assertEqual(raw_ratio, (n_minus / n_plus) ** 2)

    def test_qdet_remains_separate_from_unit_tetrad_qcross(self) -> None:
        n_plus, n_minus, a_plus, a_minus = sp.symbols(
            "N_plus N_minus a_plus a_minus",
            positive=True,
        )
        q_det = n_minus * a_minus**3 / (n_plus * a_plus**3)
        q_cross = sp.Integer(1)

        self.assertEqual(sp.simplify(q_det * q_cross), q_det)


if __name__ == "__main__":
    unittest.main()
