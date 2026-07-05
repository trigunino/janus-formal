import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_local_pin_reflection_intertwiner_gate import (
    build_payload,
)


def _frame(*, minus_normal=-1.0, full_embedding=False):
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "sigma_unit_frame_ready": True,
        "unit_normals_plus": [[0.0, 0.0, 0.0, 0.0, 1.0]],
        "unit_normals_minus": [[0.0, 0.0, 0.0, 0.0, minus_normal]],
        "full_embedding_claimed": full_embedding,
    }


class LocalPinReflectionIntertwinerGateTests(unittest.TestCase):
    def test_local_pin_reflection_intertwiner_closes_only_local_algebra(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "frame.json"
            path.write_text(json.dumps(_frame()), encoding="utf-8")

            payload = build_payload(frame_path=path)

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["closure"]["local_Clifford_intertwiner_ready"])
        self.assertFalse(payload["closure"]["global_resolved_tunnel_spinor_lift_ready"])
        self.assertFalse(payload["closure"]["physical_spinor_equivariance_derived"])
        self.assertEqual(payload["scope"]["global_resolved_tunnel_Pin_lift"], "not_claimed")

    def test_missing_normal_reversal_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "frame.json"
            path.write_text(json.dumps(_frame(minus_normal=1.0)), encoding="utf-8")

            payload = build_payload(frame_path=path)

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "z2_normal_reversal_not_satisfied")

    def test_full_embedding_claim_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "frame.json"
            path.write_text(json.dumps(_frame(full_embedding=True)), encoding="utf-8")

            payload = build_payload(frame_path=path)

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "local_intertwiner_must_not_claim_full_embedding")


if __name__ == "__main__":
    unittest.main()
