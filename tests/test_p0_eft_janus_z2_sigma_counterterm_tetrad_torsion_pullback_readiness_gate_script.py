import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_torsion_pullback_readiness_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaCountertermTetradTorsionPullbackReadinessGateTests(unittest.TestCase):
    def test_readiness_records_closed_commutation_and_formula(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["torsion_pullback_readiness_ledger_declared"])
        self.assertTrue(payload["readiness"]["oriented_pullback_commutation_ready"])
        self.assertTrue(payload["readiness"]["ambient_torsion_formula_ready"])

    def test_readiness_remains_blocked_on_embedding_and_basis(self):
        payload = build_payload()

        self.assertFalse(payload["readiness"]["active_embedding_ready"])
        self.assertFalse(payload["readiness"]["coframe_connection_pullback_ready"])
        self.assertFalse(payload["readiness"]["torsion_pullback_variation_allowed_basis_ready"])
        self.assertFalse(payload["torsion_pullback_readiness_ready"])


if __name__ == "__main__":
    unittest.main()
