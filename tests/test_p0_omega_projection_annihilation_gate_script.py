from __future__ import annotations

import unittest

from scripts.build_p0_omega_projection_annihilation_gate import build_payload, render_markdown


class P0OmegaProjectionAnnihilationGateTests(unittest.TestCase):
    def test_projection_annihilation_gate_is_open_and_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "omega-projection-annihilation-open")
        self.assertEqual(payload["projection_condition"], "P R_Omega P^T=0")
        self.assertTrue(payload["source_derived_projection_required"])
        self.assertFalse(payload["posthoc_observable_projection_allowed"])
        self.assertFalse(payload["observable_fit_allowed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_projection_must_be_shared_with_k_qcross_and_lensing(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["shared_with_k"])
        self.assertTrue(payload["shared_with_q_cross"])
        self.assertTrue(payload["shared_with_lensing"])
        requirements = " ".join(row["requirement"] for row in payload["gate_rows"])
        self.assertIn("same source-derived P", requirements)
        self.assertIn("K, Q_cross, and lensing", requirements)

    def test_forbids_posthoc_projection_and_fit(self) -> None:
        forbidden = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("after computing K/Q_cross/lensing", forbidden)
        self.assertIn("fit P", forbidden)
        self.assertIn("different projections", forbidden)

    def test_markdown_renders_condition_and_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("P R_Omega P^T=0", markdown)
        self.assertIn("Post-hoc observable projection allowed: False", markdown)
        self.assertIn("Observable fit allowed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
