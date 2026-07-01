from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_controlled_deviation_gate import build_payload, write_reports


class P0EFTJanusZ4ControlledDeviationGateTests(unittest.TestCase):
    def test_controlled_delta_gate_preserves_camb_gr_at_zero(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-controlled-deviation-gate")
        self.assertEqual(payload["theory_vector_backend"], "camb_gr_plus_z4_delta")
        self.assertEqual(payload["baseline_backend"], "camb_gr_safe_baseline")
        self.assertEqual(payload["lambda_z4_default"], 0.0)
        self.assertFalse(payload["raw_native_los_used_for_planck"])
        self.assertTrue(payload["channel_deltas_tagged"])
        self.assertTrue(payload["source_level_delta_required_for_physics"])
        self.assertTrue(payload["spectrum_level_delta_debug_only"])
        self.assertTrue(payload["z4_delta_identity_at_zero_passed"])
        self.assertTrue(payload["z4_delta_continuity_passed"])
        self.assertTrue(payload["controlled_z4_delta_gate_passed"])
        self.assertIn("delta_weyl_lensing_kernel", payload["delta_channels"])
        self.assertIn("delta_sw_isw_source", payload["delta_channels"])

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_controlled_deviation_gate.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_controlled_deviation_gate.md").exists())


if __name__ == "__main__":
    unittest.main()
