import unittest

import numpy as np

from src.janus_lab.z2_sigma_effective_parameter_inputs import (
    validate_effective_bao_parameter_inputs,
)


def _payload() -> dict:
    z = np.geomspace(1.0, 1.0e5, 64) - 1.0
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


class Z2SigmaEffectiveParameterInputsTest(unittest.TestCase):
    def test_valid_parameter_input_is_canonicalized(self):
        payload = validate_effective_bao_parameter_inputs(_payload())
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertEqual(payload["source"], "effective_parameter_inputs")
        self.assertEqual(len(payload["z_grid"]), 64)

    def test_rejects_archived_z4(self):
        payload = _payload()
        payload["archived_z4_reuse_used"] = True
        with self.assertRaisesRegex(ValueError, "Forbidden/false-required"):
            validate_effective_bao_parameter_inputs(payload)

    def test_rejects_misaligned_arrays(self):
        payload = _payload()
        payload["E_Z2Sigma"] = payload["E_Z2Sigma"][:-1]
        with self.assertRaisesRegex(ValueError, "align"):
            validate_effective_bao_parameter_inputs(payload)


if __name__ == "__main__":
    unittest.main()

