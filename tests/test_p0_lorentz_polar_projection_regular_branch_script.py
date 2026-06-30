from __future__ import annotations

import unittest

from scripts.build_p0_lorentz_polar_projection_regular_branch import build_payload, render_markdown


class P0LorentzPolarProjectionRegularBranchTests(unittest.TestCase):
    def test_artifact_is_regular_branch_only_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "regular-branch-artifact")
        self.assertEqual(payload["definition"], "L_Lorentz=polar_eta(L_geom)")
        self.assertTrue(payload["regular_branch_only"])
        self.assertFalse(payload["source_derived"])
        self.assertFalse(payload["d_lorentz_derivative_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_regular_conditions_and_branch_failures_are_explicit(self) -> None:
        payload = build_payload()
        regular = " ".join(payload["regularity_conditions"])
        failures = " ".join(payload["singular_branch_failures"])

        self.assertIn("L_geom is invertible", regular)
        self.assertIn("H=eta^{-1} L_geom^T eta L_geom", regular)
        self.assertIn("real regular square-root branch", regular)
        self.assertIn("det(L_geom)=0", failures)
        self.assertIn("branch cut", failures)
        self.assertIn("wrong orthochronous/proper Lorentz component", failures)

    def test_lorentz_admissible_by_construction_but_not_source_derived(self) -> None:
        payload = build_payload()

        self.assertIn("admissible by construction", payload["lorentz_admissibility"])
        self.assertFalse(payload["source_derived"])
        self.assertIn("not a Janus source derivation", " ".join(payload["rejection_rules"]))

    def test_d_lorentz_derivative_still_needs_projection_derivative(self) -> None:
        derivative_items = " ".join(build_payload()["derivative_open_items"])

        self.assertIn("D_alpha polar_eta(L_geom)", derivative_items)
        self.assertIn("D_alpha H^{-1/2}", derivative_items)
        self.assertIn("raw spin-connection derivatives of L_geom", derivative_items)

    def test_blockers_include_zero_divergence_and_same_l_k_qcross(self) -> None:
        payload = build_payload()
        blockers = " ".join(payload["blockers"])

        self.assertFalse(payload["zero_divergence_pde_closed"])
        self.assertFalse(payload["same_l_for_k_and_qcross"])
        self.assertIn("zero-divergence PDE blocker remains open", blockers)
        self.assertIn("K/Q_cross same-L blocker remains open", blockers)

    def test_markdown_renders_required_gate_language(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Definition: `L_Lorentz=polar_eta(L_geom)`", markdown)
        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("not source-derived", markdown)


if __name__ == "__main__":
    unittest.main()
