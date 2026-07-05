import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_rsigma_solver_collocation_a_grid_input_writer_gate import (
    build_payload,
)


def _q(**overrides):
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "unit_intrinsic_metric_q_ab": [
            [1.0, 0.0, 0.0],
            [0.0, 1.0, 0.0],
            [0.0, 0.0, 1.0],
        ],
    }
    payload.update(overrides)
    return payload


class RSigmaSolverCollocationAGridInputWriterGateTests(unittest.TestCase):
    def test_writes_non_observational_collocation_grid_from_active_q(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            q_path = root / "q.json"
            output_path = root / "grid.json"
            q_path.write_text(json.dumps(_q()), encoding="utf-8")

            payload = build_payload(q_input_path=q_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["a_grid"], [0.25, 0.5, 1.0])
        self.assertEqual(written["grid_role"], "solver_collocation_grid")
        self.assertFalse(written["grid_is_physical_observable"])
        self.assertFalse(written["grid_is_fit_parameter"])

    def test_forbidden_z4_reuse_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            q_path = root / "q.json"
            q_path.write_text(json.dumps(_q(archived_z4_reuse_used=True)), encoding="utf-8")

            payload = build_payload(q_input_path=q_path, output_path=root / "grid.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])

    def test_missing_q_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(q_input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "active_unit_intrinsic_metric_q_ab_inputs")


if __name__ == "__main__":
    unittest.main()
