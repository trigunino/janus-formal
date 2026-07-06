from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_brane_normal_force_residual import (
    build_payload,
    render_markdown,
)


class BraneNormalForceResidualTests(unittest.TestCase):
    def test_symbolic_residual_is_ready_but_values_block(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["residual_symbolic_ready"])
        self.assertFalse(payload["residual_values_ready"])
        self.assertTrue(payload["strict_Z2_mean_curvature_cancellation_ready"])
        self.assertTrue(payload["strict_Z2_closes_normal_force"])
        self.assertEqual(payload["primary_blocker"], "DeltaK_s_of_a_ready")
        self.assertTrue(payload["gate_passed"])

    def test_formula_instantiates_carter_equation(self) -> None:
        formulas = build_payload()["formulas"]

        self.assertEqual(
            formulas["normal_brane_equation"], "barT_Sigma^{ab} Kbar_ab^rho = f_perp^rho"
        )
        self.assertIn("rho_Sigma Kbar_tau", formulas["isotropic_reduction"])
        self.assertIn("F_defect", formulas["defect_residual"])

    def test_no_defect_claim_without_values(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["strict_Z2_closes_normal_force"])
        self.assertFalse(payload["defect_forced"])
        self.assertFalse(payload["inputs"]["active_metric_embedding_available"])

    def test_markdown_reports_state(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Brane Normal Force Residual", markdown)
        self.assertIn("Symbolic ready: `True`", markdown)


if __name__ == "__main__":
    unittest.main()
