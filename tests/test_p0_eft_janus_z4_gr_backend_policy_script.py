from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_gr_backend_policy import build_payload, write_reports


class P0EFTJanusZ4GRBackendPolicyTests(unittest.TestCase):
    def test_policy_selects_safe_gr_baseline(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-gr-backend-policy")
        self.assertTrue(payload["camb_reference_available"])
        self.assertIn(payload["selected_gr_baseline_backend"], {"native", "CAMB-reference"})
        self.assertTrue(payload["default_provider_uses_safe_gr_baseline"])
        self.assertFalse(payload["default_provider_internal_calibration"])
        self.assertEqual(
            payload["native_source_engine_allowed_for_planck"],
            payload["native_gr_matches_standard_gr"],
        )
        self.assertTrue(payload["backend_policy"]["camb_gr_safe_baseline"]["official_planck_allowed"])
        self.assertFalse(payload["backend_policy"]["native_toy_los_debug"]["official_planck_allowed"])
        self.assertTrue(payload["backend_policy"]["camb_gr_plus_z4_delta"]["official_planck_allowed"])
        self.assertFalse(payload["backend_policy"]["camb_gr_plus_z4_delta"]["nonzero_z4_delta_allowed"])
        self.assertEqual(payload["z4_corrections_allowed"], payload["native_gr_matches_standard_gr"])

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_gr_backend_policy.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_gr_backend_policy.md").exists())


if __name__ == "__main__":
    unittest.main()
