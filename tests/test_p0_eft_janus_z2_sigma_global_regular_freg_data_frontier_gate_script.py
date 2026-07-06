import unittest

from scripts.derive_p0_eft_janus_z2_sigma_global_regular_freg_data_frontier_gate import (
    build_payload,
)


class JanusZ2SigmaGlobalRegularFregDataFrontierGateTest(unittest.TestCase):
    def test_lists_concrete_primitives_for_each_freg_component(self):
        payload = build_payload()
        frontier = payload["frontier"]
        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["all_primitives_ready"])
        self.assertEqual(payload["primary_blocker"], "active_freg_primitives_not_materialized")
        self.assertIn("normal_connection_omega_perp_lambda_u", frontier["normal_frame_holonomy_defect"]["needed_primitives"])
        self.assertIn("tau_Z2_pullback_matrix_on_endpoint_tangents", frontier["collar_endpoint_mismatch"]["needed_primitives"])
        self.assertIn("bulk_normal_flux_jump_lambda", frontier["junction_bianchi_defect"]["needed_primitives"])

    def test_forbids_external_shortcuts(self):
        payload = build_payload()
        self.assertFalse(payload["compressed_planck_lcdm_background_used"])
        self.assertFalse(payload["archived_z4_reuse_used"])
        self.assertFalse(payload["observational_fit_used"])
        self.assertFalse(payload["torus_replacement_used"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])


if __name__ == "__main__":
    unittest.main()
