import unittest

from scripts.build_p0_eft_janus_z2_sigma_normal_matter_current_readiness_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaNormalMatterCurrentReadinessGateTests(unittest.TestCase):
    def test_current_projection_formulae_are_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["normal_matter_current_readiness_ledger_declared"])
        self.assertIn("J_n^Z2Sigma", payload["formulae"]["z2_current"])
        self.assertEqual(payload["formulae"]["transparency_test"], "J_n^Z2Sigma = 0")

    def test_current_readiness_remains_blocked_on_projected_current_and_normals(self):
        payload = build_payload()

        self.assertFalse(payload["readiness"]["Sigma_normals_ready"])
        self.assertFalse(payload["readiness"]["projected_Dirac_matter_current_ready"])
        self.assertFalse(payload["readiness"]["no_normal_matter_current_derived"])
        self.assertFalse(payload["normal_matter_current_readiness_ready"])


if __name__ == "__main__":
    unittest.main()
