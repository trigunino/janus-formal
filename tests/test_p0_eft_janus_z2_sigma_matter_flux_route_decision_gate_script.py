import unittest
from unittest.mock import patch

from scripts.build_p0_eft_janus_z2_sigma_matter_flux_route_decision_gate import build_payload


class P0EFTJanusZ2SigmaMatterFluxRouteDecisionGateTests(unittest.TestCase):
    def test_route_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["matter_flux_route_ledger_declared"])
        self.assertTrue(payload["declared"]["transparency_route_declared"])
        self.assertTrue(payload["declared"]["active_projection_route_declared"])
        self.assertTrue(payload["declared"]["route_choice_by_fit_forbidden"])

    def test_route_is_not_decided_without_derivation(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["transparency_derived"])
        self.assertFalse(payload["closure"]["active_flux_projection_ready"])
        self.assertFalse(payload["closure"]["matter_flux_route_decided"])
        self.assertFalse(payload["matter_flux_route_decision_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_solution_certificate")
        self.assertEqual(
            payload["upstream_frontiers"]["transparency"]["primary_blocker"],
            "R_Sigma_solution_certificate",
        )
        self.assertIn("transparency_normal_current_readiness_ready", payload["upstream_contract"])
        self.assertIn("active_projection_sigma_normals_ready", payload["upstream_contract"])
        self.assertIn("choose_route_from_derivation_not_observational_fit", payload["next_required"])

    def test_route_decision_consumes_transparency_gate(self):
        transparency = {
            "status": "mock-transparency",
            "active_sigma_transparency_ready": True,
            "current_frontier": [],
            "primary_blocker": "none",
        }
        active_projection = {
            "status": "mock-active-projection",
            "active_flux_projection_ready": False,
            "closure": {},
        }
        with patch(
            "scripts.build_p0_eft_janus_z2_sigma_matter_flux_route_decision_gate.build_transparency_payload",
            return_value=transparency,
        ), patch(
            "scripts.build_p0_eft_janus_z2_sigma_matter_flux_route_decision_gate.build_active_projection_payload",
            return_value=active_projection,
        ):
            payload = build_payload()

        self.assertTrue(payload["closure"]["transparency_derived"])
        self.assertEqual(payload["selected_route"], "transparent")
        self.assertTrue(payload["matter_flux_route_decision_ready"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")


if __name__ == "__main__":
    unittest.main()
