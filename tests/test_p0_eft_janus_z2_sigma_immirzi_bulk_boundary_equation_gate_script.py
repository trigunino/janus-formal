import unittest

from scripts.build_p0_eft_janus_z2_sigma_immirzi_bulk_boundary_equation_gate import build_payload


class P0EFTJanusZ2SigmaImmirziBulkBoundaryEquationGateTests(unittest.TestCase):
    def test_bulk_boundary_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["immirzi_bulk_boundary_ledger_declared"])
        self.assertTrue(payload["declared"]["scalar_Immirzi_Holst_variation_imported"])
        self.assertTrue(payload["declared"]["Nieh_Yan_variation_imported"])
        self.assertTrue(payload["declared"]["torsion_pullback_on_Sigma_gate_declared"])

    def test_bulk_boundary_equation_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["bulk_Immirzi_equation_reduced"])
        self.assertFalse(payload["closure"]["Sigma_boundary_condition_reduced"])
        self.assertFalse(payload["immirzi_bulk_boundary_equation_ready"])
        self.assertIn("pass_torsion_pullback_on_Sigma_gate", payload["next_required"])
        self.assertIn("feed_equations_to_Immirzi_profile_of_a_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
