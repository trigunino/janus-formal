from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_scross_source_anchor import build_payload


class P0ScrossSourceAnchorTests(unittest.TestCase):
    def test_scross_is_fixed_for_weak_field_but_not_tensor_closure(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertEqual(decision["s_cross_weak_field_value"], "-1")
        self.assertTrue(decision["source_anchored"])
        self.assertFalse(decision["full_tensor_sign_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_sign_matrix_contains_cross_repulsion(self) -> None:
        payload = build_payload()
        cross = [row for row in payload["sign_matrix"] if row["ray_metric"] == "g_plus" and row["source"] == "negative"][0]

        self.assertEqual(cross["s_source"], "-1")
        self.assertIn("negative-lensing", cross["effect"])

    def test_sources_include_m15_and_m30(self) -> None:
        payload = build_payload()
        sources = {row["source"] for row in payload["anchors"]}

        self.assertIn("M15", sources)
        self.assertIn("M30", sources)


if __name__ == "__main__":
    unittest.main()
