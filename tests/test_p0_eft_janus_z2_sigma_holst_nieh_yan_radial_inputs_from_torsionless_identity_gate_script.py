import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_holst_nieh_yan_radial_inputs_from_torsionless_identity_gate import (
    build_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rsigma_holst_nieh_yan_radial_term_from_active_inputs_gate import (
    build_payload as build_term_payload,
)


def _torsion_components(*, nonzero: bool = False):
    tensor = [[[0.0 for _ in range(3)] for _ in range(3)] for _ in range(3)]
    if nonzero:
        tensor[0][1][2] = 0.1
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "Sigma_torsion_pullback_ready": True,
        "trace_vector_component_ready": True,
        "axial_vector_component_ready": True,
        "tensor_torsion_component_ready": True,
        "trace_vector_values": [0.0, 0.0, 0.0],
        "axial_totally_antisymmetric_component_values": tensor,
        "tensor_torsion_values": [[[0.0 for _ in range(3)] for _ in range(3)] for _ in range(3)],
    }


def _grid():
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "a_grid": [0.25, 0.5, 1.0],
    }


class HolstNiehYanRadialInputsFromTorsionlessIdentityGateTests(unittest.TestCase):
    def test_writes_zero_radial_inputs_for_torsionless_identity(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            torsion_path = root / "torsion.json"
            grid_path = root / "grid.json"
            output_path = root / "holst_inputs.json"
            torsion_path.write_text(json.dumps(_torsion_components()), encoding="utf-8")
            grid_path.write_text(json.dumps(_grid()), encoding="utf-8")

            payload = build_payload(
                torsion_components_path=torsion_path,
                a_grid_path=grid_path,
                output_path=output_path,
            )
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["torsionless_Nieh_Yan_zero_identity_ready"])
        self.assertEqual(written["E_HolstNiehYan_values"], [0.0, 0.0, 0.0])

    def test_strict_radial_term_writer_accepts_torsionless_zero_identity(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            torsion_path = root / "torsion.json"
            grid_path = root / "grid.json"
            inputs_path = root / "holst_inputs.json"
            term_path = root / "term.json"
            torsion_path.write_text(json.dumps(_torsion_components()), encoding="utf-8")
            grid_path.write_text(json.dumps(_grid()), encoding="utf-8")
            build_payload(torsion_components_path=torsion_path, a_grid_path=grid_path, output_path=inputs_path)

            payload = build_term_payload(input_path=inputs_path, output_path=term_path)
            written = json.loads(term_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["term_name"], "E_HolstNiehYan")
        self.assertEqual(written["term_values"], [0.0, 0.0, 0.0])

    def test_nonzero_torsion_blocks_zero_identity(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            torsion_path = root / "torsion.json"
            grid_path = root / "grid.json"
            torsion_path.write_text(json.dumps(_torsion_components(nonzero=True)), encoding="utf-8")
            grid_path.write_text(json.dumps(_grid()), encoding="utf-8")

            payload = build_payload(
                torsion_components_path=torsion_path,
                a_grid_path=grid_path,
                output_path=root / "out.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("requires all torsion components to vanish", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
