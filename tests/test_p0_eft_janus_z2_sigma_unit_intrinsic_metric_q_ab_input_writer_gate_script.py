import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_unit_intrinsic_metric_q_ab_input_writer_gate import (
    build_payload,
)


def _rp3(**overrides):
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_curvature_fit_used": False,
        "spatial_topology": {
            "quotient_spatial_slice": "RP3",
            "volume_factor_pi2_R3": 1.0,
        },
    }
    payload.update(overrides)
    return payload


def _gravity(**overrides):
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "scalars": {"gravitational_constant_si_Z2Sigma": 2.0},
    }
    payload.update(overrides)
    return payload


class UnitIntrinsicMetricQabInputWriterGateTests(unittest.TestCase):
    def test_writes_unit_q_ab_from_active_rp3_and_gravity(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            rp3_path = root / "rp3.json"
            gravity_path = root / "gravity.json"
            output_path = root / "q.json"
            rp3_path.write_text(json.dumps(_rp3()), encoding="utf-8")
            gravity_path.write_text(json.dumps(_gravity()), encoding="utf-8")

            payload = build_payload(
                topology_input_path=rp3_path,
                gravity_input_path=gravity_path,
                output_path=output_path,
            )
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["unit_intrinsic_metric_q_ab"][0], [1.0, 0.0, 0.0])
        self.assertEqual(written["intrinsic_dimension"], 3)
        self.assertAlmostEqual(written["kappa_Z2Sigma"], 16.0 * math.pi)

    def test_missing_inputs_block(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                topology_input_path=Path(tmp) / "missing_rp3.json",
                gravity_input_path=Path(tmp) / "missing_gravity.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "active_RP3_slice_and_gravity_inputs")

    def test_forbidden_observational_curvature_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            rp3_path = root / "rp3.json"
            gravity_path = root / "gravity.json"
            rp3_path.write_text(
                json.dumps(_rp3(observational_curvature_fit_used=True)),
                encoding="utf-8",
            )
            gravity_path.write_text(json.dumps(_gravity()), encoding="utf-8")

            payload = build_payload(
                topology_input_path=rp3_path,
                gravity_input_path=gravity_path,
                output_path=root / "q.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
