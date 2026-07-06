import json
import tempfile
import unittest
from pathlib import Path

from scripts.write_p0_eft_janus_z2_pt67_cartan_ghy_deltaK_inputs import build_payload
from scripts.write_p0_eft_janus_z2_pt67_regular_sigma_hk_inputs import (
    build_payload as build_hk_payload,
)


class P0EFTJanusZ2PT67CartanGHYDeltaKInputsWriterTests(unittest.TestCase):
    def test_pt67_hk_writes_zero_deltaK_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            hk_path = Path(tmp) / "pt67_hk.json"
            hk_path.write_text(json.dumps(build_hk_payload()), encoding="utf-8")

            payload = build_payload(pt67_hk_path=hk_path)

        self.assertTrue(payload["cartan_ghy_deltaK_inputs_ready"])
        self.assertEqual(payload["DeltaK_s_Z2Sigma"], [0.0, 0.0, 0.0])
        self.assertEqual(payload["DeltaK_tau_Z2Sigma"], [0.0, 0.0, 0.0])
        self.assertEqual(
            payload["jump_convention"],
            "PT_transport_pullback_not_outward_Israel_cut_and_paste",
        )
        self.assertFalse(payload["uses_free_orientation_sign"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["archived_z4_reuse_used"])

    def test_missing_pt67_deltaK_ready_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            hk = build_hk_payload()
            hk["DeltaK_PT_transport"]["DeltaK_ready"] = False
            hk_path = Path(tmp) / "pt67_hk.json"
            hk_path.write_text(json.dumps(hk), encoding="utf-8")

            with self.assertRaises(ValueError):
                build_payload(pt67_hk_path=hk_path)

    def test_nonzero_pt67_deltaK_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            hk = build_hk_payload()
            hk["DeltaK_PT_transport"]["DeltaK_screen_trace"] = 1.0
            hk_path = Path(tmp) / "pt67_hk.json"
            hk_path.write_text(json.dumps(hk), encoding="utf-8")

            with self.assertRaises(ValueError):
                build_payload(pt67_hk_path=hk_path)


if __name__ == "__main__":
    unittest.main()
