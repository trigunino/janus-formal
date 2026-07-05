import unittest

from scripts.build_p0_eft_janus_z2_sigma_matter_flux_route_investigation import (
    build_payload,
)


class P0EFTJanusZ2SigmaMatterFluxRouteInvestigationTests(unittest.TestCase):
    def test_investigation_is_diagnostic_and_chooses_constructive_route(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["diagnostic_only"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(
            payload["winner_for_next_work"],
            "coupled_RSigma_embedding_flux_closure",
        )
        self.assertEqual(
            payload["transparency_route"]["physical_status"],
            "blocked_until_no_normal_current_and_bulk_flux_cancellation_are_derived",
        )
        self.assertEqual(
            payload["coupled_route"]["physical_status"],
            "open_but_constructive_to_primitive_Sigma_inputs",
        )

    def test_negative_mass_principle_is_gravitational_not_thermodynamic_shortcut(self):
        payload = build_payload()
        principle = payload["negative_mass_principle"]

        self.assertTrue(principle["negative_gravitational_sector_present"])
        self.assertTrue(principle["gravitational_sign_is_Z2_projection_sign"])
        self.assertFalse(principle["thermodynamic_negative_density_assumed"])
        self.assertTrue(principle["thermodynamic_density_must_be_supplied_or_derived"])
        self.assertTrue(principle["rho_eff_shortcut_forbidden"])

    def test_next_required_targets_primitive_sigma_inputs(self):
        payload = build_payload()

        self.assertIn("derive_sector_metric_on_sigma_inputs", payload["next_required"])
        self.assertIn("derive_active_tunnel_embedding_geometry_inputs", payload["next_required"])
        self.assertIn("then_compute_F_a_and_E_matterFlux_without_fit", payload["next_required"])
        self.assertTrue(payload["recommendation"]["no_zero_flux_shortcut"])


if __name__ == "__main__":
    unittest.main()
