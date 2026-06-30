from __future__ import annotations

import unittest

from scripts.build_p0_janus_lgeom_tetrad_map_residual_probe import build_payload, render_markdown


class P0JanusLgeomTetradMapResidualProbeScriptTests(unittest.TestCase):
    def test_equal_branch_passes_and_mismatch_fails(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["equal_branch_passes_lorentz"])
        self.assertTrue(payload["mismatched_branch_fails_lorentz"])
        self.assertFalse(payload["raw_lgeom_promoted"])

    def test_no_prediction_claim(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["diagnostic_only"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_no_go_boundary(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Raw Lgeom promoted: False", markdown)
        self.assertIn("does not derive the accepted same-L transport", markdown)


if __name__ == "__main__":
    unittest.main()
