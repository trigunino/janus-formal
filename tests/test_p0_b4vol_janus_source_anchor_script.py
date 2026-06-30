from __future__ import annotations

import unittest

from scripts.build_p0_b4vol_janus_source_anchor import build_payload


class P0B4volJanusSourceAnchorTests(unittest.TestCase):
    def test_field_source_anchor_closed_but_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "field-source-anchor-closed-action-bridge-open")
        self.assertTrue(payload["b4vol_field_source_anchor_closed"])
        self.assertFalse(payload["b4vol_pulled_action_anchor_closed"])
        self.assertTrue(payload["single_cross_dust_continuity_admissible"])
        self.assertFalse(payload["full_two_sector_bianchi_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_source_rows_name_m15_m30_and_determinant_ratios(self) -> None:
        rows = " ".join(row["source"] + " " + row["formula"] for row in build_payload()["source_rows"])

        self.assertIn("M15 Eqs. 4a-4b", rows)
        self.assertIn("sqrt(-g_minus/-g_plus)", rows)
        self.assertIn("sqrt(-g_plus/-g_minus)", rows)
        self.assertIn("M30 Eqs. 105a-105b", rows)

    def test_remaining_rows_keep_action_phi_mirror_and_matter_extension_open(self) -> None:
        remaining = " ".join(build_payload()["remaining_rows"])

        self.assertIn("pulled dust action", remaining)
        self.assertIn("phi/L", remaining)
        self.assertIn("inverse consistency", remaining)
        self.assertIn("pressure or Pi", remaining)


if __name__ == "__main__":
    unittest.main()
