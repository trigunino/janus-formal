import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_coframe_connection_pullback_components_from_unit_q_gate import (
    build_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_torsion_pullback_components_from_coframe_connection_gate import (
    build_payload as build_torsion_payload,
)


def _q_payload(**overrides):
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "unit_intrinsic_metric_q_ab": [[1.0, 0.0, 0.0], [0.0, 4.0, 0.0], [0.0, 0.0, 9.0]],
    }
    payload.update(overrides)
    return payload


class CoframeConnectionPullbackComponentsFromUnitQGateTests(unittest.TestCase):
    def test_writes_torsionless_coframe_connection_from_q(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            q_path = root / "q.json"
            out_path = root / "coframe.json"
            q_path.write_text(json.dumps(_q_payload()), encoding="utf-8")

            payload = build_payload(input_path=q_path, output_path=out_path)
            written = json.loads(out_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["torsionless_baseline_only"])
        self.assertEqual(written["coframe_e_I_a"][1][1], 2.0)
        self.assertEqual(written["coframe_e_I_a"][2][2], 3.0)

    def test_cartan_torsion_from_baseline_is_zero(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            q_path = root / "q.json"
            coframe_path = root / "coframe.json"
            torsion_path = root / "torsion.json"
            q_path.write_text(json.dumps(_q_payload()), encoding="utf-8")
            build_payload(input_path=q_path, output_path=coframe_path)

            torsion_payload = build_torsion_payload(input_path=coframe_path, output_path=torsion_path)
            written = json.loads(torsion_path.read_text(encoding="utf-8"))

        self.assertTrue(torsion_payload["gate_passed"])
        self.assertEqual(written["torsion_antisymmetry_residual_max_abs"], 0.0)
        self.assertTrue(
            all(
                value == 0.0
                for plane in written["torsion_T_upper_a_bc"]
                for row in plane
                for value in row
            )
        )

    def test_forbidden_provenance_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            q_path = root / "q.json"
            q_path.write_text(
                json.dumps(_q_payload(observational_curvature_fit_used=True)),
                encoding="utf-8",
            )

            payload = build_payload(input_path=q_path, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
