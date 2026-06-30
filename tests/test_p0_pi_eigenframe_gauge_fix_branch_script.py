from __future__ import annotations

import unittest

from scripts.build_p0_pi_eigenframe_gauge_fix_branch import build_payload


class P0PiEigenframeGaugeFixBranchTests(unittest.TestCase):
    def test_pi_branch_is_open_but_algebraic(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["eigenframe_algebra_written"])
        self.assertTrue(payload["can_fix_full_rotation_if_nondegenerate"])
        self.assertFalse(payload["source_derived_pi_evolution"])
        self.assertFalse(payload["unique_omega_found"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_eigen_cases_distinguish_zero_degenerate_and_nondegenerate(self) -> None:
        cases = {row["case"]: row for row in build_payload()["eigen_cases"]}

        self.assertIn("SO(3)", cases["Pi=0"]["remaining_gauge"])
        self.assertIn("no continuous", cases["Pi has three distinct spatial eigenvalues"]["remaining_gauge"])
        self.assertIn("SO(2)", cases["Pi has two equal spatial eigenvalues"]["remaining_gauge"])

    def test_omega_constraints_use_pi_transport(self) -> None:
        constraints = " ".join(build_payload()["omega_constraints"])

        self.assertIn("Omega Pi_to + Pi_to Omega^T", constraints)
        self.assertIn("off-diagonal components", constraints)
        self.assertIn("nondegenerate Pi", constraints)
        self.assertIn("screen rotations", constraints)

    def test_source_requirements_block_prediction(self) -> None:
        requirements = " ".join(build_payload()["source_requirements"])

        self.assertIn("source-derived Pi evolution law", requirements)
        self.assertIn("same L", requirements)
        self.assertIn("Q_cross", requirements)
        self.assertIn("R_plus/R_minus", requirements)


if __name__ == "__main__":
    unittest.main()
