from __future__ import annotations

import unittest

from scripts.build_p0_same_l_spin_connection_transport_identity_gate import (
    build_payload,
    render_markdown,
)


class P0SameLSpinConnectionTransportIdentityGateTests(unittest.TestCase):
    def test_spin_connection_identity_closes_algebra_not_physics(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "same-l-spin-connection-identity-algebra-closed-source-open",
        )
        self.assertTrue(payload["covariant_dl_identity_closed"])
        self.assertTrue(payload["coordinate_bridge_derivative_closed"])
        self.assertTrue(payload["mirror_derivative_algebra_closed"])
        self.assertTrue(payload["lorentz_generator_necessary_condition_closed"])
        self.assertFalse(payload["source_selected_l"])
        self.assertFalse(payload["source_selected_omega"])
        self.assertFalse(payload["curvature_integrability_closed"])
        self.assertFalse(payload["bianchi_residuals_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_identities_include_spin_dl_mirror_and_stress_divergence(self) -> None:
        rows = {row["name"]: row for row in build_payload()["identities"]}

        self.assertIn("omega_s,lambda L - L omega_o,lambda", rows["spin_covariant_dl"]["formula"])
        self.assertIn("(D_lambda L)L^{-1}", rows["lorentz_generator"]["formula"])
        self.assertIn("-L^{-1}(D_lambda L)L^{-1}", rows["mirror_derivative"]["formula"])
        self.assertIn("e_s (D L) e_o", rows["coordinate_bridge_derivative"]["formula"])
        self.assertIn("terms[D L]", rows["transported_stress_divergence"]["formula"])
        self.assertIn("terms[D log B4vol]", rows["transported_stress_divergence"]["formula"])

    def test_acceptance_tests_keep_source_selection_and_residuals_open(self) -> None:
        tests = {row["test"]: row for row in build_payload()["acceptance_tests"]}

        self.assertTrue(tests["one_l_stack"]["passed"])
        self.assertTrue(tests["eta_compatibility"]["passed"])
        self.assertFalse(tests["source_selected_l"]["passed"])
        self.assertFalse(tests["curvature_integrability"]["passed"])
        self.assertFalse(tests["bianchi_residuals"]["passed"])

    def test_forbidden_shortcuts_block_scalar_absorption(self) -> None:
        rules = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("do not set D L=0", rules)
        self.assertIn("raw partial L", rules)
        self.assertIn("separate bridges", rules)
        self.assertIn("Q_det", rules)
        self.assertIn("Q_cross", rules)

    def test_markdown_reports_source_open(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Spin-Connection Transport Identity", markdown)
        self.assertIn("Covariant DL identity closed: True", markdown)
        self.assertIn("Source-selected L: False", markdown)
        self.assertIn("Bianchi residuals closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
