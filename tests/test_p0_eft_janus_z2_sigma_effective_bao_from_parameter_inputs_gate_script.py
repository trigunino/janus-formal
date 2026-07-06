import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

from scripts.build_p0_eft_janus_z2_sigma_effective_bao_from_parameter_inputs_gate import (
    build_payload,
)


def _parameter_payload() -> dict:
    z = np.geomspace(1.0, 1.0e5, 256) - 1.0
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "effective_parameter_inputs",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "full_no_fit_prediction_ready": False,
        "effective_initial_data": {
            "R_Sigma_over_ell_collar_Z2Sigma": 1.0,
            "projected_baryon_number_charge_Z2Sigma": 2.0,
        },
        "effective_initial_data_provenance": {
            "R_Sigma_over_ell_collar_Z2Sigma": "declared_effective_initial_data",
            "projected_baryon_number_charge_Z2Sigma": "declared_effective_initial_data",
        },
        "z_grid": z.tolist(),
        "E_Z2Sigma": np.sqrt(0.3 * (1.0 + z) ** 3 + 0.7).tolist(),
        "c_s_over_c_Z2Sigma": np.full_like(z, 1.0 / np.sqrt(3.0)).tolist(),
        "Gamma_drag_over_H0_Z2Sigma": (1.0e5 / (1.0 + z)).tolist(),
        "omega_k_Z2Sigma": 0.0,
        "z_max": float(z[-1]),
        "z_d_bracket": [100.0, 2000.0],
        "primitive_provenance": {
            "E_Z2Sigma": "effective_background_equation",
            "c_s_over_c_Z2Sigma": "effective_plasma_equation",
            "Gamma_drag_over_H0_Z2Sigma": "effective_drag_equation",
            "omega_k_Z2Sigma": "effective_curvature_convention",
        },
    }


class JanusZ2SigmaEffectiveBAOFromParameterInputsGateTest(unittest.TestCase):
    def test_missing_parameter_input_blocks(self):
        payload = build_payload(parameter_input_path=Path("__missing_params__.json"))
        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertEqual(payload["primary_blocker"], "effective_bao_parameter_inputs_json")

    def test_valid_parameter_input_writes_manifests_and_runs(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            param = tmpdir / "effective_bao_parameter_inputs.json"
            closure = tmpdir / "effective_closure_inputs.json"
            primitives = tmpdir / "effective_bao_scale_free_primitive_inputs.json"
            param.write_text(json.dumps(_parameter_payload()), encoding="utf-8")
            payload = build_payload(
                parameter_input_path=param,
                closure_output_path=closure,
                primitive_output_path=primitives,
            )

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["manifests_written"])
        self.assertTrue(payload["effective_bao_end_to_end_ready"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertGreater(payload["chi2_DESI_DR2_BAO_effective"], 0.0)


if __name__ == "__main__":
    unittest.main()

