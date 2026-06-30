from __future__ import annotations

import unittest

from scripts.build_p0_polar_projection_derivative_obstruction import (
    build_payload,
    render_markdown,
)


class P0PolarProjectionDerivativeObstructionTests(unittest.TestCase):
    def test_artifact_is_open_source_false_and_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "derivative-obstruction-open")
        self.assertEqual(payload["definition"], "L_Lorentz=polar_eta(L_geom)")
        self.assertFalse(payload["source_derived"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["d_lorentz_equals_d_geom"])
        self.assertFalse(payload["projection_derivative_closed"])
        self.assertFalse(payload["square_root_obligation_closed"])

    def test_product_rule_keeps_noncommuting_inverse_square_root_derivative(self) -> None:
        payload = build_payload()
        identities = " ".join(payload["derivative_identities"])
        blockers = " ".join(payload["blockers"])
        rules = " ".join(payload["rejection_rules"])

        self.assertIn("D_alpha L_Lorentz", identities)
        self.assertIn("(D_alpha L_geom) H^{-1/2}", identities)
        self.assertIn("L_geom D_alpha(H^{-1/2})", identities)
        self.assertIn("not just D_alpha L_geom", blockers)
        self.assertIn("does not commute away", blockers)
        self.assertIn("do not drop", rules)

    def test_square_root_derivative_obligation_is_sylvester_type(self) -> None:
        payload = build_payload()
        text = " ".join(
            f"{row['unknown']} {row['obligation']} {row['type']}"
            for row in payload["square_root_obligations"]
        )

        self.assertTrue(all(not row["closed"] for row in payload["square_root_obligations"]))
        self.assertIn("X_alpha = D_alpha H^{1/2}", text)
        self.assertIn("H^{1/2} X_alpha + X_alpha H^{1/2} = D_alpha H", text)
        self.assertIn("Sylvester/Lyapunov-type", text)
        self.assertIn("Y_alpha = D_alpha H^{-1/2}", text)

    def test_regular_component_conditions_and_same_l_obligation_are_explicit(self) -> None:
        payload = build_payload()
        regular = " ".join(payload["regularity_conditions"])
        components = " ".join(payload["component_conditions"])
        blockers = " ".join(payload["blockers"])

        self.assertIn("real smooth square-root branch", regular)
        self.assertIn("eigenvalue/branch-cut crossing", regular)
        self.assertIn("proper/orthochronous Lorentz component", regular)
        self.assertIn("disconnected Lorentz components", components)
        self.assertFalse(payload["same_l_for_k_and_qcross_source_derived"])
        self.assertIn("same-L K/Q_cross obligation remains open", blockers)

    def test_rejects_fitted_shortcut_and_markdown_renders_gate_language(self) -> None:
        payload = build_payload()
        rules = " ".join(payload["rejection_rules"])
        markdown = render_markdown(payload)

        self.assertFalse(payload["fitted_shortcut_allowed"])
        self.assertIn("do not use polar_eta as an observationally fitted shortcut", rules)
        self.assertIn("Fitted shortcut allowed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Source-derived: False", markdown)


if __name__ == "__main__":
    unittest.main()
