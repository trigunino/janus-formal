import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_counterterm_alpha_res_extraction_attempt_gate import (
    build_payload,
)


class CountertermAlphaResExtractionAttemptGateTests(unittest.TestCase):
    def test_writes_partial_alpha_and_identifies_tetrad_blocker(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "alpha_partial.json"
            payload = build_payload(output_path=output)

            self.assertTrue(payload["alpha_res_partial_written"])
            self.assertFalse(payload["alpha_res_explicit"])
            self.assertEqual(payload["primary_blocker"], "tetrad_residual_coefficients")
            self.assertEqual(
                payload["tetrad_value_extraction"]["primary_blocker"],
                "nonlinear_closure_lacks_alpha_res_component_values",
            )
            self.assertTrue(output.exists())
            written = json.loads(output.read_text(encoding="utf-8"))
            self.assertEqual(written["alpha_res_status"], "partial")
            self.assertIn("R_h_ab", written["formal_terms"])
            self.assertIn("explicit_R_h_ab_values", written["missing_terms"])
            self.assertIn("explicit_R_K_ab_values", written["missing_terms"])
            self.assertNotIn("connection_residual_channel_coefficients", written["missing_terms"])
            self.assertNotIn("matter_flux_residual_channel_coefficients", written["missing_terms"])
            self.assertEqual(
                written["open_pre_radius_non_GHY_channels"],
                ["metric_non_GHY_trace_R_h", "extrinsic_non_GHY_trace_R_K"],
            )
            self.assertEqual(
                payload["open_remaining_non_GHY_counterterm_channels"],
                ["metric_non_GHY_trace_R_h", "extrinsic_non_GHY_trace_R_K"],
            )


if __name__ == "__main__":
    unittest.main()
