import tempfile
import unittest
import json
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_bao_active_primitive_physical_input_obligation_gate import (
    build_payload,
)
from tests.test_p0_eft_janus_z2_sigma_active_inputs_to_official_bao_gate_script import (
    _background_inputs,
    _early_inputs,
    _flrw_inputs,
)


def _omega_k_inputs() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "scalars": {
            "omega_k_Z2Sigma": -0.02,
            "h0_R_curv_over_c_Z2Sigma": 7.0,
            "k_Z2Sigma": 1,
        },
        "scalar_provenance": {
            "omega_k_Z2Sigma": "active_scale_free_curvature_derivation",
        },
    }


class P0EFTJanusZ2SigmaBAOActivePrimitivePhysicalInputObligationGateTests(unittest.TestCase):
    def test_missing_active_inputs_block_bao_chi2(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                background_input_path=root / "background_scalar_inputs.json",
                omega_k_input_path=root / "background_scale_free_omega_k_inputs.json",
                flrw_input_path=root / "flrw_component_inputs.json",
                early_input_path=root / "early_plasma_inputs.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["scale_free_primitive_physics_ready"])
        self.assertFalse(payload["desi_dr2_bao_chi2_allowed"])
        self.assertEqual(
            payload["missing_physical_input_groups"],
            ["scale_free_omega_k_inputs", "flrw_component_inputs", "early_plasma_inputs"],
        )
        self.assertIn("E_Z2Sigma", payload["primitive_obligations"])
        self.assertIn("Gamma_drag_over_H0_Z2Sigma", payload["primitive_obligations"])
        self.assertTrue(payload["policy"]["compressed_planck_lcdm_forbidden"])
        self.assertTrue(payload["policy"]["archived_z4_forbidden"])
        self.assertTrue(payload["policy"]["mock_active_inputs_forbidden"])

    def test_valid_active_inputs_allow_bao_chi2_path(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            background = root / "background_scalar_inputs.json"
            omega_k = root / "background_scale_free_omega_k_inputs.json"
            flrw = root / "flrw_component_inputs.json"
            early = root / "early_plasma_inputs.json"
            background.write_text(json.dumps(_background_inputs()), encoding="utf-8")
            omega_k.write_text(json.dumps(_omega_k_inputs()), encoding="utf-8")
            flrw.write_text(json.dumps(_flrw_inputs()), encoding="utf-8")
            early.write_text(json.dumps(_early_inputs()), encoding="utf-8")

            payload = build_payload(
                background_input_path=background,
                omega_k_input_path=omega_k,
                flrw_input_path=flrw,
                early_input_path=early,
            )

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["scale_free_primitive_physics_ready"])
        self.assertTrue(payload["desi_dr2_bao_chi2_allowed"])
        self.assertEqual(payload["missing_physical_input_groups"], [])


if __name__ == "__main__":
    unittest.main()
