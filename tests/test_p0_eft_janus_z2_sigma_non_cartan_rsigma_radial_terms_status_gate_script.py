import unittest

from scripts.build_p0_eft_janus_z2_sigma_non_cartan_rsigma_radial_terms_status_gate import (
    build_payload,
)


class NonCartanRSigmaRadialTermsStatusGateTests(unittest.TestCase):
    def test_default_status_reports_missing_terms(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertFalse(payload["gate_passed"])
        self.assertIn("E_matterFlux", payload["missing_non_cartan_terms"])
        self.assertIn("E_counterterm", payload["missing_non_cartan_terms"])
        self.assertIn("derive_E_counterterm_radial_term_manifest", payload["next_required"])

    def test_ready_injected_terms_pass(self):
        payload = build_payload(
            holst_payload={
                "holst_nieh_yan_radial_block_of_a_ready": True,
                "primary_blocker": "none",
            },
            holst_radial_term_payload={
                "E_HolstNiehYan_from_active_inputs_written": True,
                "primary_blocker": "none",
            },
            matter_flux_payload={
                "E_matterFlux_zero_from_transparency_written": True,
                "primary_blocker": "none",
            },
            counterterm_payload={
                "counterterm_radial_block_of_a_ready": True,
                "primary_blocker": "none",
            },
        )

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["missing_non_cartan_terms"], [])
        self.assertEqual(payload["primary_blocker"], "none")

    def test_active_projection_route_can_satisfy_matter_flux_term(self):
        payload = build_payload(
            holst_payload={
                "holst_nieh_yan_radial_block_of_a_ready": True,
                "primary_blocker": "none",
            },
            holst_radial_term_payload={
                "E_HolstNiehYan_from_active_inputs_written": True,
                "primary_blocker": "none",
            },
            matter_flux_payload={
                "E_matterFlux_zero_from_transparency_written": False,
                "primary_blocker": "active_Sigma_transparency_manifest",
            },
            matter_flux_active_projection_payload={
                "E_matterFlux_from_active_projection_written": True,
                "primary_blocker": "none",
            },
            counterterm_payload={
                "counterterm_radial_block_of_a_ready": True,
                "primary_blocker": "none",
            },
        )

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["terms"]["E_matterFlux"]["routes"]["active_projection_ready"])
        self.assertFalse(payload["terms"]["E_matterFlux"]["routes"]["transparency_ready"])

    def test_structural_holst_without_manifest_still_blocks(self):
        payload = build_payload(
            holst_payload={
                "holst_nieh_yan_radial_block_of_a_ready": True,
                "primary_blocker": "none",
            },
            holst_radial_term_payload={
                "E_HolstNiehYan_from_active_inputs_written": False,
                "primary_blocker": "active_holst_nieh_yan_radial_inputs",
            },
            matter_flux_payload={
                "E_matterFlux_zero_from_transparency_written": True,
                "primary_blocker": "none",
            },
            counterterm_payload={
                "counterterm_radial_block_of_a_ready": True,
                "primary_blocker": "none",
            },
        )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("E_HolstNiehYan", payload["missing_non_cartan_terms"])
        self.assertTrue(payload["terms"]["E_HolstNiehYan"]["routes"]["structural_block_ready"])
        self.assertFalse(payload["terms"]["E_HolstNiehYan"]["routes"]["active_inputs_manifest_ready"])

    def test_next_required_only_reports_missing_terms(self):
        payload = build_payload(
            holst_payload={
                "holst_nieh_yan_radial_block_of_a_ready": True,
                "primary_blocker": "none",
            },
            holst_radial_term_payload={
                "E_HolstNiehYan_from_active_inputs_written": True,
                "primary_blocker": "none",
            },
            matter_flux_payload={
                "E_matterFlux_zero_from_transparency_written": False,
                "primary_blocker": "active_Sigma_transparency_manifest",
            },
            counterterm_payload={
                "counterterm_radial_block_of_a_ready": False,
                "primary_blocker": "tetrad_residual_channel",
            },
        )

        self.assertNotIn("derive_E_HolstNiehYan_radial_term_manifest", payload["next_required"])
        self.assertIn("derive_E_matterFlux_radial_term_manifest", payload["next_required"])
        self.assertIn("derive_E_counterterm_radial_term_manifest", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
