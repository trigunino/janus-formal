import unittest

from scripts.build_p0_eft_janus_z2_sigma_projected_dirac_action_readiness_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaProjectedDiracActionReadinessGateTests(unittest.TestCase):
    def test_standard_dirac_holst_formulae_are_ready(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["projected_dirac_action_readiness_ledger_declared"])
        self.assertTrue(payload["readiness"]["curved_Dirac_action_formula_ready"])
        self.assertTrue(payload["readiness"]["Holst_fermion_coupling_formula_ready"])

    def test_projected_action_waits_for_active_pullbacks_and_spinors(self):
        payload = build_payload()

        self.assertFalse(payload["readiness"]["coframe_connection_pullback_ready"])
        self.assertFalse(payload["readiness"]["plus_minus_spinor_projection_ready"])
        self.assertFalse(payload["readiness"]["Z2_projected_Dirac_action_ready"])
        self.assertFalse(payload["projected_dirac_action_readiness_ready"])


if __name__ == "__main__":
    unittest.main()
