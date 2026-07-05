import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_local_mit_reflecting_projector_gate import (
    build_payload,
)


def _frame(*, sign=-1.0, full_embedding=False):
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "sigma_unit_frame_ready": True,
        "unit_normals_plus": [[0.0, 0.0, 0.0, 0.0, 1.0]],
        "unit_normals_minus": [[0.0, 0.0, 0.0, 0.0, -1.0]],
        "z2_orientation_sign": sign,
        "full_embedding_claimed": full_embedding,
    }


class LocalMITReflectingProjectorGateTests(unittest.TestCase):
    def test_local_unit_frame_closes_projector_algebra_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "frame.json"
            path.write_text(json.dumps(_frame()), encoding="utf-8")

            payload = build_payload(frame_path=path)

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["closure"]["unit_normal_Clifford_action_ready"])
        self.assertTrue(payload["closure"]["projection_idempotent_ready"])
        self.assertFalse(payload["closure"]["boundary_spinor_satisfies_projector_derived"])
        self.assertEqual(payload["scope"]["physical_boundary_spinor_satisfies_projector"], "not_claimed")

    def test_wrong_orientation_blocks_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "frame.json"
            path.write_text(json.dumps(_frame(sign=1.0)), encoding="utf-8")

            payload = build_payload(frame_path=path)

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "z2_orientation_sign_not_minus_one")

    def test_full_embedding_claim_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "frame.json"
            path.write_text(json.dumps(_frame(full_embedding=True)), encoding="utf-8")

            payload = build_payload(frame_path=path)

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "local_projector_gate_must_not_claim_full_embedding")


if __name__ == "__main__":
    unittest.main()
