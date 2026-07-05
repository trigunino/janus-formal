import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_torsion_pullback_components_from_coframe_connection_gate import (
    build_payload,
)


def _coframe_connection_input(**overrides):
    omega = [[[0.0 for _ in range(3)] for _ in range(3)] for _ in range(3)]
    omega[0][1][2] = 2.0
    omega[1][0][2] = -2.0
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "coframe_pullback_ready": True,
        "spin_connection_pullback_ready": True,
        "exterior_derivative_coframe_ready": True,
        "selected_route": "cartan_first_structure_equation",
        "q_ab": [[1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0]],
        "coframe_e_I_a": [[1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0]],
        "exterior_de_I_ab": [[[0.0 for _ in range(3)] for _ in range(3)] for _ in range(3)],
        "spin_connection_omega_IJ_a": omega,
    }
    payload.update(overrides)
    return payload


class TorsionPullbackComponentsFromCoframeConnectionGateTests(unittest.TestCase):
    def test_writes_torsion_pullback_components_from_cartan_formula(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "input.json"
            output = root / "torsion.json"
            source.write_text(json.dumps(_coframe_connection_input()), encoding="utf-8")

            payload = build_payload(input_path=source, output_path=output)
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["Sigma_torsion_pullback_ready"])
        self.assertEqual(written["selected_route"], "cartan_pullback_components")
        self.assertLess(written["torsion_antisymmetry_residual_max_abs"], 1e-10)

    def test_blocks_without_spin_connection_readiness(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "input.json"
            source.write_text(
                json.dumps(_coframe_connection_input(spin_connection_pullback_ready=False)),
                encoding="utf-8",
            )

            payload = build_payload(input_path=source, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("spin_connection_pullback_ready", payload["validation_error"])

    def test_blocks_non_antisymmetric_connection(self):
        bad = [[[0.0 for _ in range(3)] for _ in range(3)] for _ in range(3)]
        bad[0][1][2] = 1.0
        bad[1][0][2] = 1.0
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "input.json"
            source.write_text(
                json.dumps(_coframe_connection_input(spin_connection_omega_IJ_a=bad)),
                encoding="utf-8",
            )

            payload = build_payload(input_path=source, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("antisymmetric", payload["validation_error"])

    def test_forbidden_provenance_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "input.json"
            source.write_text(
                json.dumps(_coframe_connection_input(archived_z4_reuse_used=True)),
                encoding="utf-8",
            )

            payload = build_payload(input_path=source, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
