from __future__ import annotations

import unittest

from scripts.build_p0_janus_phase_space_measure_probe import build_payload, render_markdown


class P0JanusPhaseSpaceMeasureProbeScriptTests(unittest.TestCase):
    def test_measure_probe_keeps_factors_separate(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["b4vol_weight_explicit"])
        self.assertTrue(payload["qdet_kept_separate"])
        self.assertFalse(payload["qdet_used_as_physical_measure"])
        self.assertNotEqual(payload["metrics"]["mass_unweighted"], payload["metrics"]["mass_with_b4vol"])

    def test_no_physics_claim(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["diagnostic_only"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_boundary(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Q_det used as physical measure: False", markdown)
        self.assertIn("does not derive B4vol or Q_det", markdown)


if __name__ == "__main__":
    unittest.main()
