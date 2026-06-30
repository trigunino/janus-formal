from __future__ import annotations

import unittest

from scripts.build_p0_janus_phase_space_b4vol_measure_gate import build_payload, render_markdown


class P0JanusPhaseSpaceB4volMeasureGateTests(unittest.TestCase):
    def test_measure_factors_are_separated(self) -> None:
        text = " ".join(build_payload()["measure_factors"])

        self.assertIn("B_4vol", text)
        self.assertIn("dP", text)
        self.assertIn("J_phi", text)
        self.assertIn("Q_det", text)
        self.assertIn("Q_cross", text)

    def test_closure_identities_prevent_double_counting(self) -> None:
        payload = build_payload()
        identities = " ".join(payload["closure_identities"])

        self.assertIn("D_receiver(B_4vol", identities)
        self.assertIn("T^{AB}=int", identities)
        self.assertIn("no double-counting", identities)
        self.assertFalse(payload["b4vol_phase_space_measure_closed"])

    def test_flags_keep_qdet_and_qcross_distinct(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["qdet_not_optical_amplitude"])
        self.assertTrue(payload["qcross_not_density_measure"])
        self.assertTrue(payload["phase_space_measure_probe_available"])
        self.assertTrue(payload["weakfield_b4vol_product_rule_probe_available"])
        self.assertFalse(payload["physics_closed"])

    def test_markdown_reports_open_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("B4vol phase-space measure closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
