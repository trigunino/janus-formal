import unittest
from unittest.mock import patch

from scripts.build_p0_eft_janus_z2_sigma_matter_flux_transparency_gate import build_payload


class P0EFTJanusZ2SigmaMatterFluxTransparencyGateTests(unittest.TestCase):
    def test_transparency_criteria_are_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["transparency_criteria_declared"])
        self.assertTrue(payload["criteria"]["normal_matter_current_gate_declared"])
        self.assertTrue(payload["criteria"]["projected_Dirac_normal_current_gate_declared"])
        self.assertTrue(payload["criteria"]["bulk_stress_normal_flux_cancellation_gate_declared"])
        self.assertIn("F_a^Z2Sigma", payload["sufficient_condition"])
        self.assertTrue(payload["criteria"]["observational_fit_forbidden"])
        self.assertIn("normal_matter_current", payload["upstream_frontiers"])
        self.assertIn("projected_dirac_normal_current", payload["upstream_frontiers"])
        self.assertIn("bulk_stress_flux", payload["upstream_frontiers"])

    def test_active_transparency_is_not_derived_yet(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["normal_matter_current_readiness_ready"])
        self.assertFalse(payload["closure"]["bulk_stress_normal_flux_projection_ready"])
        self.assertFalse(payload["closure"]["no_normal_matter_current_derived"])
        self.assertFalse(payload["closure"]["active_Sigma_transparency_derived"])
        self.assertFalse(payload["active_sigma_transparency_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_solution_certificate")
        self.assertIn(
            "normal_matter_current_readiness_ready = false",
            payload["current_frontier"],
        )
        self.assertFalse(payload["upstream_frontiers"]["normal_matter_current"]["ready"])
        self.assertEqual(
            payload["upstream_frontiers"]["normal_matter_current_readiness"]["primary_blocker"],
            "R_Sigma_solution_certificate",
        )
        self.assertFalse(payload["upstream_frontiers"]["bulk_stress_flux"]["projection_ready"])
        self.assertIn("pass_normal_matter_current_gate", payload["next_required"])
        self.assertIn("pass_projected_Dirac_normal_current_gate", payload["next_required"])
        self.assertIn("pass_bulk_stress_normal_flux_cancellation_gate", payload["next_required"])
        self.assertIn("if_transparency_fails_compute_active_flux_F_a_of_a", payload["next_required"])
        self.assertTrue(payload["nearest_transparency_subfrontier_declared"])
        self.assertTrue(payload["nearest_transparency_subfrontier_diagnostic_only"])
        self.assertEqual(payload["nearest_transparency_subfrontier"]["block"], "R_Sigma_solution_certificate")
        self.assertEqual(
            payload["nearest_transparency_subfrontier"]["gate"],
            "P0EFTJanusZ2SigmaNormalMatterCurrentReadinessGate",
        )
        self.assertIn(
            "prove or reject J_n^Z2Sigma = 0",
            payload["nearest_transparency_subfrontier"]["required"],
        )

    def test_transparency_does_not_pass_without_upstream_guards(self):
        normal_current = {
            "status": "mock-normal-current",
            "no_normal_matter_current_ready": False,
            "closure": {"no_normal_matter_current_derived": True},
        }
        normal_readiness = {
            "status": "mock-normal-readiness",
            "normal_matter_current_readiness_ready": False,
            "still_open": ["active_embedding_ready"],
        }
        dirac_normal = {
            "status": "mock-dirac-normal",
            "projected_dirac_normal_current_ready": False,
            "no_normal_dirac_current_ready": False,
            "closure": {"no_normal_matter_current_derived": True},
        }
        bulk_flux = {
            "status": "mock-bulk-flux",
            "bulk_stress_normal_flux_projection_ready": False,
            "bulk_stress_normal_flux_cancellation_ready": False,
            "closure": {
                "bulk_stress_normal_projection_zero_derived": True,
                "Z2_flux_cancellation_derived": True,
            },
        }
        with patch(
            "scripts.build_p0_eft_janus_z2_sigma_matter_flux_transparency_gate.build_normal_matter_current_payload",
            return_value=normal_current,
        ), patch(
            "scripts.build_p0_eft_janus_z2_sigma_matter_flux_transparency_gate.build_normal_matter_current_readiness_payload",
            return_value=normal_readiness,
        ), patch(
            "scripts.build_p0_eft_janus_z2_sigma_matter_flux_transparency_gate.build_projected_dirac_normal_current_payload",
            return_value=dirac_normal,
        ), patch(
            "scripts.build_p0_eft_janus_z2_sigma_matter_flux_transparency_gate.build_bulk_stress_flux_payload",
            return_value=bulk_flux,
        ):
            payload = build_payload()

        self.assertTrue(payload["closure"]["no_normal_matter_current_derived"])
        self.assertTrue(payload["closure"]["bulk_stress_normal_projection_zero_derived"])
        self.assertFalse(payload["closure"]["normal_matter_current_readiness_ready"])
        self.assertFalse(payload["closure"]["projected_dirac_normal_current_ready"])
        self.assertFalse(payload["closure"]["bulk_stress_normal_flux_projection_ready"])
        self.assertFalse(payload["active_sigma_transparency_ready"])


if __name__ == "__main__":
    unittest.main()
