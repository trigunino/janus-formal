import unittest

from scripts.derive_p0_eft_janus_z2_sigma_global_regular_functional_components_gate import (
    build_payload,
)


class JanusZ2SigmaGlobalRegularFunctionalComponentsGateTest(unittest.TestCase):
    def test_decomposes_freg_into_three_geometric_components(self):
        payload = build_payload()
        components = payload["F_reg_components"]
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertFalse(payload["torus_replacement_used"])
        self.assertFalse(payload["observational_fit_used"])
        self.assertEqual(
            set(components),
            {
                "normal_frame_holonomy_defect",
                "collar_endpoint_mismatch",
                "junction_bianchi_defect",
            },
        )
        self.assertIn("normal_frame_holonomy_defect", payload["F_reg_formula"])

    def test_blocks_radius_selection_until_components_have_active_data(self):
        payload = build_payload()
        self.assertFalse(payload["F_reg_value_ready"])
        self.assertFalse(payload["radius_selection_ready"])
        self.assertEqual(
            payload["primary_blocker"],
            "active_collar_metric_connection_and_flux_data",
        )
        self.assertIn(
            "derive active normal connection omega_perp(lambda_Sigma,u)",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
