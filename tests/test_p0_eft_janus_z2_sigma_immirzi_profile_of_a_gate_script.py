import unittest

from scripts.build_p0_eft_janus_z2_sigma_immirzi_profile_of_a_gate import build_payload


class P0EFTJanusZ2SigmaImmirziProfileOfAGateTests(unittest.TestCase):
    def test_immirzi_profile_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["immirzi_profile_ledger_declared"])
        self.assertTrue(payload["declared"]["Barbero_Immirzi_scalar_field_imported"])
        self.assertTrue(payload["declared"]["Nieh_Yan_coupling_imported"])
        self.assertTrue(payload["declared"]["Immirzi_bulk_boundary_equation_gate_declared"])

    def test_immirzi_profile_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["bulk_Immirzi_equation_ready"])
        self.assertFalse(payload["closure"]["Sigma_boundary_condition_ready"])
        self.assertFalse(payload["immirzi_profile_of_a_ready"])
        self.assertIn("pass_Immirzi_bulk_boundary_equation_gate", payload["next_required"])
        self.assertIn("feed_Immirzi_profile_to_torsion_stress_and_Dirac_Holst_vertex_gates", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
