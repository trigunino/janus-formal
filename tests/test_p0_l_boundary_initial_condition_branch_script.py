from __future__ import annotations

import unittest

from scripts.build_p0_l_boundary_initial_condition_branch import build_payload


class P0LBoundaryInitialConditionBranchTests(unittest.TestCase):
    def test_branch_can_fix_constants_but_not_close(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["branch_written"])
        self.assertTrue(payload["can_fix_integration_constants"])
        self.assertFalse(payload["source_boundary_found"])
        self.assertFalse(payload["integrability_proved"])
        self.assertFalse(payload["unique_l_found"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_conditions_include_lorentz_mirror_and_integrability(self) -> None:
        text = " ".join(row["statement"] for row in build_payload()["branch_conditions"])

        self.assertIn("L0^T eta L0=eta", text)
        self.assertIn("L0^{-1}", text)
        self.assertIn("L0=I", text)
        self.assertIn("curvature of Omega", text)

    def test_uniqueness_requires_source_boundary_and_same_l(self) -> None:
        requirements = " ".join(build_payload()["uniqueness_requirements"])

        self.assertIn("zero-divergence PDE", requirements)
        self.assertIn("source symmetry", requirements)
        self.assertIn("integrability", requirements)
        self.assertIn("K and Q_cross", requirements)

    def test_failure_modes_block_lensing_fit(self) -> None:
        failures = " ".join(build_payload()["failure_modes"])

        self.assertIn("fitted lensing normalization", failures)
        self.assertIn("non-unique Q_cross", failures)
        self.assertIn("pressure/Pi", failures)
        self.assertIn("non-comoving perturbations", failures)


if __name__ == "__main__":
    unittest.main()
