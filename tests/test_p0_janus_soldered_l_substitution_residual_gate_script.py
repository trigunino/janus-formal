from __future__ import annotations

import unittest

import numpy as np

from scripts.build_p0_janus_soldered_l_substitution_residual_gate import (
    ETA2,
    build_payload,
    diagonal_frame_1p1,
    lorentz_residual,
    render_markdown,
    solder_l_other_to_self,
)


class P0JanusSolderedLSubstitutionResidualGateTests(unittest.TestCase):
    def test_soldered_l_is_derived_and_substituted(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "soldered-l-derived-substitution-tested-lorentz-conditional",
        )
        self.assertTrue(payload["l_solder_formula_derived"])
        self.assertTrue(payload["substitutes_k_qcross_vlasov"])
        self.assertTrue(payload["same_l_can_be_used_only_if_lorentz_residual_zero"])
        self.assertEqual(
            payload["metric_pullback_compatibility_artifact"],
            "p0_janus_metric_pullback_compatibility_gate",
        )
        self.assertTrue(payload["lorentz_residual_equivalent_to_metric_pullback_residual"])
        self.assertTrue(payload["mirror_inverse_test_encoded"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])
        self.assertFalse(payload["prediction_ready"])

    def test_metric_compatible_case_closes_lorentz_and_mirror(self) -> None:
        payload = build_payload()
        case = payload["compatible_case"]

        self.assertTrue(payload["compatible_case_lorentz_closed"])
        self.assertTrue(payload["compatible_case_mirror_closed"])
        self.assertLess(case["metric_pullback_residual_max"], 1e-12)
        self.assertLess(case["lorentz_residual_max"], 1e-12)
        self.assertLess(case["mirror_inverse_residual_max"], 1e-12)
        self.assertLess(abs(case["vlasov_shell_residual"]), 1e-12)

    def test_metric_mismatch_exposes_lorentz_and_vlasov_residual(self) -> None:
        payload = build_payload()
        case = payload["mismatch_case"]

        self.assertFalse(payload["mismatch_case_lorentz_closed"])
        self.assertTrue(payload["mismatch_case_mirror_closed"])
        self.assertGreater(case["metric_pullback_residual_max"], 1e-4)
        self.assertGreater(case["lorentz_residual_max"], 1e-4)
        self.assertGreater(abs(case["vlasov_shell_residual"]), 1e-4)

    def test_formula_matches_direct_matrix_computation(self) -> None:
        jac = np.diag([1.2, 0.8])
        frame_self = diagonal_frame_1p1(1.44, 0.64)
        frame_other = diagonal_frame_1p1(1.0, 1.0)

        l_solder = solder_l_other_to_self(jac, frame_self, frame_other)

        np.testing.assert_allclose(l_solder, np.eye(2), atol=1e-12)
        np.testing.assert_allclose(l_solder.T @ ETA2 @ l_solder, ETA2, atol=1e-12)
        np.testing.assert_allclose(lorentz_residual(l_solder), np.zeros((2, 2)), atol=1e-12)

    def test_markdown_reports_conditional_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Soldered-L Substitution Residual", markdown)
        self.assertIn("Substitutes K/Q_cross/Vlasov: True", markdown)
        self.assertIn("Metric pullback compatibility artifact", markdown)
        self.assertIn("Mismatch case Lorentz closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
