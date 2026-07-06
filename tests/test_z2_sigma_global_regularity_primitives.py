import unittest

from src.janus_lab.z2_sigma_global_regularity_primitives import (
    validate_and_materialize_freg_components,
)


def _payload() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_global_regularity_primitives",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "torus_replacement_used": False,
        "full_no_fit_prediction_ready": False,
        "lambda_grid": [1.0, 2.0, 3.0],
        "collar_coordinate_u_grid": [0.0, 1.0],
        "normal_connection_omega_perp_lambda_u": [
            [[[1.0]], [[1.0]]],
            [[[0.0]], [[0.0]]],
            [[[1.0]], [[1.0]]],
        ],
        "deck_frame_map_lambda": [[[1.0]], [[1.0]], [[1.0]]],
        "h_plus_endpoint_lambda": [[[1.0]], [[1.0]], [[1.0]]],
        "h_minus_endpoint_lambda": [[[1.0]], [[1.0]], [[1.0]]],
        "tau_Z2_pullback_matrix_on_endpoint_tangents": [[[1.0]], [[1.0]], [[1.0]]],
        "endpoint_metric_norm": [1.0, 1.0, 1.0],
        "S_Sigma_divergence_lambda": [[0.0], [0.0], [0.0]],
        "bulk_normal_flux_jump_lambda": [[0.0], [0.0], [0.0]],
        "surface_vector_norm": [1.0, 1.0, 1.0],
        "root_tolerance": 1.0e-12,
        "primitive_provenance": {
            "normal_connection_omega_perp_lambda_u": "active_collar_connection",
            "endpoint_collar_metrics_and_z2_pullback": "active_deck_pullback",
            "sigma_stress_and_bulk_normal_flux": "active_surface_bianchi",
        },
    }


class Z2SigmaGlobalRegularityPrimitivesTest(unittest.TestCase):
    def test_materializes_components_and_unique_root(self):
        payload = validate_and_materialize_freg_components(_payload())
        self.assertEqual(payload["regularity_roots"], [2.0])
        self.assertTrue(payload["R_Sigma_over_ell_collar_selected"])
        self.assertGreater(payload["F_reg"][0], 0.0)
        self.assertEqual(payload["F_reg"][1], 0.0)

    def test_rejects_torus_replacement(self):
        payload = _payload()
        payload["torus_replacement_used"] = True
        with self.assertRaisesRegex(ValueError, "torus_replacement_used"):
            validate_and_materialize_freg_components(payload)


if __name__ == "__main__":
    unittest.main()
