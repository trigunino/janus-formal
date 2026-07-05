import unittest

from scripts.build_p0_eft_janus_z2_sigma_matter_flux_active_projection_gate import build_payload


class P0EFTJanusZ2SigmaMatterFluxActiveProjectionGateTests(unittest.TestCase):
    def test_active_flux_projection_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["active_flux_projection_ledger_declared"])
        self.assertTrue(payload["declared"]["transparency_not_assumed"])
        self.assertTrue(payload["declared"]["bulk_stress_of_a_gate_declared"])
        self.assertTrue(payload["declared"]["bulk_stress_normal_flux_cancellation_gate_declared"])
        self.assertIn("T_munu^+", payload["formula"]["plus_flux"])

    def test_active_flux_projection_waits_for_bulk_stress_and_embedding(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_bulk_stress_of_a_ready"])
        self.assertFalse(payload["closure"]["embedding_of_a_ready"])
        self.assertFalse(payload["closure"]["Sigma_tangents_ready"])
        self.assertFalse(payload["closure"]["Sigma_normals_ready"])
        self.assertFalse(payload["active_flux_projection_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_solution_certificate")
        self.assertEqual(
            payload["upstream_frontiers"]["bulk_stress_normal_flux"]["primary_blocker"],
            "R_Sigma_solution_certificate",
        )
        self.assertIn("pass_bulk_stress_of_a_gate", payload["next_required"])
        self.assertIn("pass_bulk_stress_normal_flux_cancellation_gate_or_record_nonzero_flux", payload["next_required"])
        self.assertIn("derive_active_embedding_tangents_and_normals_of_a", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
