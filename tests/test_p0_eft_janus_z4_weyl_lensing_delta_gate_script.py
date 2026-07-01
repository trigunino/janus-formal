from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_weyl_lensing_delta_gate import build_payload, write_reports


class P0EFTJanusZ4WeylLensingDeltaGateTests(unittest.TestCase):
    def test_weyl_lensing_delta_is_isolated_and_not_planck_enabled(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-weyl-lensing-delta-gate")
        self.assertTrue(payload["z4_nonzero_requested"])
        self.assertEqual(payload["delta_channel"], "weyl_lensing_kernel")
        self.assertFalse(payload["raw_native_los_used_for_planck"])
        self.assertEqual(payload["phiphi_convention"], "C_L_phiphi")
        self.assertTrue(payload["not_deflection_spectrum"])
        self.assertTrue(payload["not_L4_scaled"])
        self.assertTrue(payload["lambda_zero_identity_passed"])
        self.assertTrue(payload["unlensed_primary_unchanged"])
        self.assertTrue(payload["small_lambda_continuity_passed"])
        self.assertTrue(payload["internal_lensing_response_gate_passed"])
        self.assertEqual(payload["kernel"]["current_delta_classification"], "near_uniform_lensing_amplitude_response")
        self.assertTrue(payload["kernel"]["not_physical_shape_signature"])
        self.assertGreater(payload["kernel"]["amplitude_fraction"], 0.95)
        self.assertLess(payload["kernel"]["shape_fraction"], 0.05)
        self.assertFalse(payload["z4_nonzero_planck_allowed"])
        self.assertFalse(payload["official_planck_allowed"])
        self.assertFalse(payload["allowed_channels"]["allowed_to_modify_unlensed_primary"])
        self.assertTrue(payload["allowed_channels"]["allowed_to_modify_phiphi"])

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_weyl_lensing_delta_gate.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_weyl_lensing_delta_gate.md").exists())


if __name__ == "__main__":
    unittest.main()
