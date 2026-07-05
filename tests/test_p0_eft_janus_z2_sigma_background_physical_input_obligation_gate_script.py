import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_background_physical_input_obligation_gate import (
    build_payload,
)


def _scalar_payload(field: str, provenance_key: str, value: float, provenance: str) -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "scalars": {field: value},
        "scalar_provenance": {provenance_key: provenance},
    }


def _curvature_branch_payload() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "scalars": {
            "H0_Z2Sigma_km_s_Mpc": 70.0,
            "R_curv_Z2Sigma_Mpc": 4000.0,
            "k_Z2Sigma": -1,
        },
        "scalar_provenance": {
            "H0_Z2Sigma": "active_background_scale_gate",
            "R_curv_Z2Sigma": "active_tunnel_embedding_scale",
            "k_Z2Sigma": "active_flrw_spatial_metric_branch",
        },
    }


class P0EFTJanusZ2SigmaBackgroundPhysicalInputObligationGateTests(unittest.TestCase):
    def test_missing_inputs_block_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                h0_input_path=root / "missing_h0.json",
                curvature_branch_input_path=root / "missing_curvature.json",
                gravity_input_path=root / "missing_g.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["background_physical_inputs_ready"])
        self.assertEqual(
            payload["missing_physical_inputs"],
            ["H0_Z2Sigma", "omega_k_Z2Sigma_from_FLRW_branch", "G_Z2Sigma"],
        )
        self.assertTrue(payload["omega_k_formula_ready"])
        self.assertTrue(payload["requires_active_curvature_branch_for_omega_k"])
        self.assertFalse(payload["uses_compressed_planck_lcdm_background"])
        self.assertTrue(payload["mock_inputs_forbidden"])

    def test_valid_inputs_enable_background_physical_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            h0 = root / "h0.json"
            curvature = root / "curvature.json"
            gravity = root / "gravity.json"
            h0.write_text(
                json.dumps(
                    _scalar_payload(
                        "H0_Z2Sigma_km_s_Mpc",
                        "H0_Z2Sigma",
                        70.0,
                        "active_background_scale_gate",
                    )
                ),
                encoding="utf-8",
            )
            curvature.write_text(json.dumps(_curvature_branch_payload()), encoding="utf-8")
            gravity.write_text(
                json.dumps(
                    _scalar_payload(
                        "gravitational_constant_si_Z2Sigma",
                        "G_Z2Sigma",
                        6.67430e-11,
                        "active_low_energy_gravity_convention",
                    )
                ),
                encoding="utf-8",
            )

            payload = build_payload(
                h0_input_path=h0,
                curvature_branch_input_path=curvature,
                gravity_input_path=gravity,
            )

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["background_physical_inputs_ready"])
        self.assertEqual(payload["missing_physical_inputs"], [])


if __name__ == "__main__":
    unittest.main()
