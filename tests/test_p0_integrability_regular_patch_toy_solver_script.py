from __future__ import annotations

import unittest

from scripts.build_p0_integrability_regular_patch_toy_solver import build_payload


class P0IntegrabilityRegularPatchToySolverTests(unittest.TestCase):
    def test_toy_solver_leaves_free_modes_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "toy-solver-free-modes-remain")
        self.assertFalse(payload["forces_unique_phi_l"])
        self.assertTrue(payload["gauge_fixed_unique_phi_l"])
        self.assertFalse(payload["gauge_fixed_unique_is_derived"])
        self.assertTrue(payload["requires_boundary_data"])
        self.assertTrue(payload["requires_gauge_fixing"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_equations_include_curl_volume_and_lorentz_generator(self) -> None:
        equations = {row["name"]: row for row in build_payload()["equations"]}

        self.assertEqual(equations["curl_free_xi"]["constraint"], "c-b=0")
        self.assertEqual(equations["volume_preserving_linearized"]["constraint"], "a+d=0")
        self.assertIn("omega+omega.T=0", equations["lorentz_generator"]["constraint"])

    def test_solution_family_and_free_modes_are_explicit(self) -> None:
        payload = build_payload()
        solution_text = " ".join(str(row) for row in payload["solution_family"])

        self.assertIn("c", solution_text)
        self.assertIn("b", solution_text)
        self.assertIn("d", solution_text)
        self.assertIn("-a", solution_text)
        self.assertEqual(set(payload["free_modes"]), {"a", "b", "theta"})

    def test_gauge_boundary_conditions_make_trivial_unique_branch_only_by_imposition(self) -> None:
        payload = build_payload()
        conditions = " ".join(row["condition"] for row in payload["gauge_boundary_conditions"])

        self.assertIn("a=0", conditions)
        self.assertIn("b=0", conditions)
        self.assertIn("theta=0", conditions)
        self.assertEqual(payload["gauge_fixed_solution"]["c"], "0")
        self.assertEqual(payload["gauge_fixed_solution"]["d"], "0")


if __name__ == "__main__":
    unittest.main()
