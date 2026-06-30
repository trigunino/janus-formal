from __future__ import annotations

import unittest

from scripts.build_p0_janus_same_l_transport_stack_gate import build_payload, render_markdown


class P0JanusSameLTransportStackGateTests(unittest.TestCase):
    def test_same_l_uses_cover_k_qcross_and_kinetics(self) -> None:
        text = " ".join(build_payload()["same_l_uses"])

        self.assertIn("K_plus", text)
        self.assertIn("Q_cross", text)
        self.assertIn("kinetic", text)
        self.assertIn("DL residuals", text)

    def test_required_identities_reject_scalar_shortcut(self) -> None:
        payload = build_payload()
        identities = " ".join(payload["required_identities"])

        self.assertIn("L^T eta L=eta", identities)
        self.assertIn("same L is used", identities)
        self.assertTrue(payload["same_l_1p1_lorentz_probe_available"])
        self.assertTrue(payload["lgeom_tetrad_map_residual_probe_available"])
        self.assertTrue(payload["lgeom_dl_lie_residual_probe_available"])
        self.assertFalse(payload["dl_source_derived"])
        self.assertFalse(payload["same_l_stack_closed"])

    def test_rejection_rules_block_bad_l(self) -> None:
        rules = " ".join(build_payload()["rejection_rules"])

        self.assertIn("reject L_geom", rules)
        self.assertIn("separate L", rules)
        self.assertIn("fitted", rules)

    def test_no_prediction_claim(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_open_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Same-L stack closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
