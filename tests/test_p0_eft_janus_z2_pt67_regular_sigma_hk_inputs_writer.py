from __future__ import annotations

import unittest

from scripts.write_p0_eft_janus_z2_pt67_regular_sigma_hk_inputs import build_payload


class Z2PT67RegularSigmaHKInputsWriterTests(unittest.TestCase):
    def test_writer_exports_active_regular_sigma_inputs(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["regular_sigma_pipeline_inputs_ready"])
        self.assertTrue(payload["h_ab_at_sigma"]["nondegenerate"])
        self.assertEqual(payload["DeltaK_PT_transport"]["DeltaK_screen_trace"], 0.0)
        self.assertFalse(payload["provenance"]["uses_observational_fit"])
        self.assertFalse(payload["provenance"]["uses_free_orientation_sign"])


if __name__ == "__main__":
    unittest.main()
