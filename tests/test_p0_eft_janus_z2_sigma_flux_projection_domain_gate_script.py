import unittest

from scripts.build_p0_eft_janus_z2_sigma_flux_projection_domain_gate import build_payload


class P0EFTJanusZ2SigmaFluxProjectionDomainGateTests(unittest.TestCase):
    def test_domain_ledger_declares_minimal_geometry(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["flux_projection_domain_ledger_declared"])
        self.assertTrue(payload["closure"]["coorientation_ready"])
        self.assertTrue(payload["declared"]["no_independent_frame_fit"])
        self.assertTrue(payload["declared"]["observational_fit_forbidden"])
        self.assertIn("embedding_geometry_manifest", payload["upstream_frontiers"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_solution_certificate")

    def test_domain_does_not_unlock_flux_without_embedding_frames(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["regular_embedding_ready"])
        self.assertFalse(payload["closure"]["embedding_geometry_manifest_valid"])
        self.assertFalse(payload["closure"]["embedding_of_a_ready"])
        self.assertFalse(payload["closure"]["Sigma_tangents_ready"])
        self.assertFalse(payload["closure"]["Sigma_normals_ready"])
        self.assertFalse(payload["flux_projection_domain_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertIn("derive_tangent_frames_and_unit_normals", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
