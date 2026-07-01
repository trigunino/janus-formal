from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_lensed_remapping_response_gate import build_payload, write_reports


class P0EFTJanusZ4LensedRemappingResponseGateTests(unittest.TestCase):
    def test_lensed_remapping_is_stable_and_not_planck_enabled(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-lensed-remapping-response-gate")
        self.assertEqual(payload["input_unlensed_backend"], "camb_gr_safe_baseline")
        self.assertEqual(payload["input_phiphi_delta"], "weyl_lensing_kernel")
        self.assertFalse(payload["raw_native_los_used_for_planck"])
        self.assertFalse(payload["allowed_to_modify_unlensed_primary"])
        self.assertTrue(payload["allowed_to_modify_phiphi"])
        self.assertTrue(payload["allowed_to_modify_lensed_spectra"])
        self.assertTrue(payload["lambda_zero_identity_passed"])
        self.assertTrue(payload["lensed_TT_response_continuous"])
        self.assertTrue(payload["lensed_TE_response_continuous"])
        self.assertTrue(payload["lensed_EE_response_continuous"])
        self.assertTrue(payload["lensed_remapping_response_gate_passed"])
        self.assertTrue(payload["uniform_phiphi_amplitude_delta_screened_by_normalized_smoothing"])
        self.assertTrue(payload["observable_lensing_shape_delta_required"])
        self.assertFalse(payload["nonzero_z4_planck_allowed"])
        self.assertFalse(payload["official_planck_allowed"])

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_lensed_remapping_response_gate.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_lensed_remapping_response_gate.md").exists())


if __name__ == "__main__":
    unittest.main()
