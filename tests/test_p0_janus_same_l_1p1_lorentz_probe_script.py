from __future__ import annotations

import unittest

from scripts.build_p0_janus_same_l_1p1_lorentz_probe import build_payload, render_markdown


class P0JanusSameL1p1LorentzProbeScriptTests(unittest.TestCase):
    def test_lorentz_probe_preserves_trace(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["lorentz_condition_passes"])
        self.assertLess(payload["metrics"]["minkowski_trace_error"], 1e-12)
        self.assertTrue(payload["same_l_used_for_tensor_transform"])

    def test_no_dl_or_prediction_claim(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["dl_source_derived"])
        self.assertTrue(payload["diagnostic_only"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_boundary(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Lorentz condition passes: True", markdown)
        self.assertIn("does not derive the Janus same-L", markdown)


if __name__ == "__main__":
    unittest.main()
