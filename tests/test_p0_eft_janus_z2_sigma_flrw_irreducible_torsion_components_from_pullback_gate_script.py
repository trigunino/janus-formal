import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_flrw_irreducible_torsion_components_from_pullback_gate import (
    build_payload,
)


def _torsion_input(**overrides):
    torsion = [
        [[0.0, 0.0, 0.0], [0.0, 0.0, 2.0], [0.0, -2.0, 0.0]],
        [[0.0, 0.0, -3.0], [0.0, 0.0, 0.0], [3.0, 0.0, 0.0]],
        [[0.0, 4.0, 0.0], [-4.0, 0.0, 0.0], [0.0, 0.0, 0.0]],
    ]
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "Sigma_torsion_pullback_ready": True,
        "selected_route": "cartan_pullback_components",
        "q_ab": [[1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0]],
        "torsion_T_upper_a_bc": torsion,
    }
    payload.update(overrides)
    return payload


class FLRWIrreducibleTorsionComponentsFromPullbackGateTests(unittest.TestCase):
    def test_writes_irreducible_components_from_active_pullback(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "torsion.json"
            output = root / "components.json"
            source.write_text(json.dumps(_torsion_input()), encoding="utf-8")

            payload = build_payload(input_path=source, output_path=output)
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["trace_vector_component_ready"])
        self.assertTrue(written["axial_vector_component_ready"])
        self.assertTrue(written["tensor_torsion_component_ready"])
        self.assertLess(written["reconstruction_residual_max_abs"], 1e-10)

    def test_blocks_without_sigma_torsion_pullback(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "torsion.json"
            source.write_text(
                json.dumps(_torsion_input(Sigma_torsion_pullback_ready=False)),
                encoding="utf-8",
            )

            payload = build_payload(input_path=source, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Sigma_torsion_pullback_ready", payload["validation_error"])

    def test_blocks_non_antisymmetric_torsion(self):
        bad_torsion = [[[0.0 for _ in range(3)] for _ in range(3)] for _ in range(3)]
        bad_torsion[0][1][2] = 1.0
        bad_torsion[0][2][1] = 1.0
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "torsion.json"
            source.write_text(
                json.dumps(_torsion_input(torsion_T_upper_a_bc=bad_torsion)),
                encoding="utf-8",
            )

            payload = build_payload(input_path=source, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("antisymmetric", payload["validation_error"])

    def test_forbidden_provenance_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "torsion.json"
            source.write_text(
                json.dumps(_torsion_input(archived_z4_reuse_used=True)),
                encoding="utf-8",
            )

            payload = build_payload(input_path=source, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
