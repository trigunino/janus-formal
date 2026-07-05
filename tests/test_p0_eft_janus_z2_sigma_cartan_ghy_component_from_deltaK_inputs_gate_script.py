import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_component_from_deltaK_inputs_gate import (
    build_payload,
)


def _deltaK_input():
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": [0.25, 0.5, 1.0],
        "DeltaK_s_Z2Sigma": [2.0, 4.0, 8.0],
        "DeltaK_tau_Z2Sigma": [5.0, 10.0, 20.0],
        "z2_orientation_sign": 1.0,
        "DeltaK_provenance": "active tunnel embedding extrinsic curvature derivation",
    }


def _background_scalars():
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "H0_Z2Sigma_km_s_Mpc": 70.0,
        "omega_k_Z2Sigma": 0.0,
        "gravitational_constant_si_Z2Sigma": 6.67430e-11,
        "critical_normalization": {
            "rho_crit0_Z2Sigma_kg_m3": 1.0,
            "kappa_Z2Sigma_SI": 10.0,
            "kappa_rho_crit0_Z2Sigma_SI": 10.0,
            "gravitational_constant_source": "active low-energy G convention",
        },
        "scalar_provenance": {
            "H0_Z2Sigma": "active time-gauge normalization",
            "omega_k_Z2Sigma": "active projective curvature derivation",
            "G_Z2Sigma": "active low-energy G convention",
        },
    }


class P0EFTJanusZ2SigmaCartanGHYComponentFromDeltaKInputsGateTests(unittest.TestCase):
    def test_missing_inputs_block_component_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                deltaK_input_path=Path(tmp) / "deltaK.json",
                background_scalar_path=Path(tmp) / "background.json",
                output_path=Path(tmp) / "cartan.json",
            )

        self.assertFalse(payload["deltaK_input_exists"])
        self.assertFalse(payload["cartan_ghy_component_values_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertIn("deltaK_input_writer", payload["upstream_frontiers"])
        self.assertIn(
            "active_DeltaK_s_tau_inputs",
            payload["nearest_cartan_component_frontier"]["blocks"],
        )
        self.assertTrue(payload["nearest_cartan_component_frontier"]["diagnostic_only"])

    def test_active_inputs_write_cartan_components(self):
        with tempfile.TemporaryDirectory() as tmp:
            deltaK_path = Path(tmp) / "deltaK.json"
            background_path = Path(tmp) / "background.json"
            output_path = Path(tmp) / "cartan.json"
            deltaK_path.write_text(json.dumps(_deltaK_input()), encoding="utf-8")
            background_path.write_text(json.dumps(_background_scalars()), encoding="utf-8")

            payload = build_payload(
                deltaK_input_path=deltaK_path,
                background_scalar_path=background_path,
                output_path=output_path,
            )
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["component_route"], "cartan_ghy_from_active_deltaK")
        self.assertEqual(written["flrw_components_over_rho_crit0"]["cartan_ghy_rho"], [0.6, 1.2, 2.4])
        self.assertEqual(written["flrw_components_over_rho_crit0"]["cartan_ghy_p"], [0.1, 0.2, 0.4])
        self.assertFalse(written["archived_z4_reuse_used"])

    def test_forbidden_deltaK_provenance_blocks_component_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            deltaK = _deltaK_input()
            deltaK["DeltaK_provenance"] = "Planck LCDM prior"
            deltaK_path = Path(tmp) / "deltaK.json"
            background_path = Path(tmp) / "background.json"
            output_path = Path(tmp) / "cartan.json"
            deltaK_path.write_text(json.dumps(deltaK), encoding="utf-8")
            background_path.write_text(json.dumps(_background_scalars()), encoding="utf-8")

            payload = build_payload(
                deltaK_input_path=deltaK_path,
                background_scalar_path=background_path,
                output_path=output_path,
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
