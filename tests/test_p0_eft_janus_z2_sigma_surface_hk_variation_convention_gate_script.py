from __future__ import annotations

import unittest

from scripts.build_p0_eft_janus_z2_sigma_surface_hk_variation_convention_gate import (
    build_payload,
    render_markdown,
)


class SurfaceHKVariationConventionGateTests(unittest.TestCase):
    def test_surface_hk_conventions_are_declared(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["conventions_ready"])
        self.assertEqual(payload["conventions"]["bulk_signature"], "mostly_plus")
        self.assertEqual(payload["conventions"]["metric_variation_index_position"], "delta_h_ab")
        self.assertEqual(payload["conventions"]["z2_orientation"], "epsilon_Z2 = -1")

    def test_markdown_reports_k_convention(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("K_ab =", markdown)
        self.assertIn("mostly_plus", markdown)


if __name__ == "__main__":
    unittest.main()
