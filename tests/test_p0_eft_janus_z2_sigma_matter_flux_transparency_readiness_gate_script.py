import unittest

from scripts.build_p0_eft_janus_z2_sigma_matter_flux_transparency_readiness_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaMatterFluxTransparencyReadinessGateTests(unittest.TestCase):
    def test_transparency_criteria_are_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["matter_flux_transparency_readiness_ledger_declared"])
        self.assertIn("J_n^Z2Sigma", payload["criteria"]["current"])
        self.assertIn("F_a^Z2Sigma", payload["criteria"]["stress_flux"])

    def test_transparency_remains_blocked_on_active_data(self):
        payload = build_payload()

        self.assertFalse(payload["readiness"]["active_embedding_ready"])
        self.assertFalse(payload["readiness"]["Sigma_normals_ready"])
        self.assertFalse(payload["readiness"]["no_normal_matter_current_ready"])
        self.assertFalse(payload["matter_flux_transparency_readiness_ready"])


if __name__ == "__main__":
    unittest.main()
