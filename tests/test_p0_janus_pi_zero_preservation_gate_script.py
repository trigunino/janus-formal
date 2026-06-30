from __future__ import annotations

import unittest

from scripts.build_p0_janus_pi_zero_preservation_gate import build_payload, render_markdown


class P0JanusPiZeroPreservationGateTests(unittest.TestCase):
    def test_preservation_identity_contains_trace_free_sources(self) -> None:
        payload = build_payload()
        identity = payload["preservation_identity_target"]

        self.assertIn("D_t Pi_ij", identity)
        self.assertIn("sigma_ij", identity)
        self.assertIn("D_k Q_ijk", identity)
        self.assertIn("S_ij[A_Janus,L,B_4vol]", identity)

    def test_initial_pi_zero_is_not_a_proof(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["pi_zero_initial_condition_is_not_proof"])
        self.assertTrue(payload["pi_zero_preservation_conditions_written"])
        self.assertFalse(payload["pi_zero_source_proved"])
        self.assertFalse(payload["isotropic_dispersion_closed"])

    def test_generation_channels_reject_shortcuts(self) -> None:
        text = " ".join(build_payload()["generation_channels"] + build_payload()["forbidden_shortcuts"])

        self.assertIn("mean-flow shear", text)
        self.assertIn("heat-flux divergence", text)
        self.assertIn("Q_det or Q_cross", text)
        self.assertIn("do not set Q_ijk=0", text)

    def test_no_fit_or_prediction(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_open_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Pi zero source proved: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
