import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_unit_throat_frame_input_writer_gate import (
    build_payload,
)


def _active(**extra):
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
    }
    payload.update(extra)
    return payload


class P0EFTJanusZ2SigmaUnitThroatFrameInputWriterGateTests(unittest.TestCase):
    def test_writes_local_frame_without_full_embedding_claim(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            q_path = root / "q.json"
            grid_path = root / "grid.json"
            output_path = root / "frame.json"
            q_path.write_text(
                json.dumps(_active(unit_intrinsic_metric_q_ab=[[1.0, 0.0], [0.0, 1.0]])),
                encoding="utf-8",
            )
            grid_path.write_text(json.dumps(_active(a_grid=[0.5, 1.0])), encoding="utf-8")

            payload = build_payload(q_path=q_path, grid_path=grid_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(written["full_embedding_claimed"])
        self.assertFalse(written["extrinsic_curvature_claimed"])
        self.assertEqual(written["unit_normals_plus"][0], [0.0, 0.0, 0.0, 1.0])
        self.assertEqual(written["tangent_frames_plus"][0][0], [1.0, 0.0, 0.0, 0.0])


if __name__ == "__main__":
    unittest.main()
