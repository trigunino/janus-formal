from __future__ import annotations

import unittest

from scripts.build_p0_janus_lgeom_dl_lie_residual_probe import build_payload, render_markdown


class P0JanusLgeomDLLieResidualProbeScriptTests(unittest.TestCase):
    def test_lie_residual_rejects_mismatch(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["equal_branch_passes_lie_algebra"])
        self.assertTrue(payload["mismatched_branch_fails_lie_algebra"])
        self.assertFalse(payload["raw_lgeom_promoted"])
        self.assertFalse(payload["dl_source_derived"])

    def test_no_prediction_claim(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["diagnostic_only"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_boundary(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Mismatched branch fails Lie algebra: True", markdown)
        self.assertIn("does not derive a Janus D L law", markdown)


if __name__ == "__main__":
    unittest.main()
