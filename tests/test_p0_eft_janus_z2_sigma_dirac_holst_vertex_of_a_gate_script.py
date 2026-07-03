import unittest

from scripts.build_p0_eft_janus_z2_sigma_dirac_holst_vertex_of_a_gate import build_payload


class P0EFTJanusZ2SigmaDiracHolstVertexOfAGateTests(unittest.TestCase):
    def test_vertex_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dirac_holst_vertex_ledger_declared"])
        self.assertTrue(payload["declared"]["Holst_fermion_four_fermion_vertex_imported"])
        self.assertIn("generic_vertex", payload["formulas"])

    def test_vertex_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["torsion_field_solution_of_a_ready"])
        self.assertFalse(payload["closure"]["projected_vertex_ready"])
        self.assertFalse(payload["dirac_holst_vertex_of_a_ready"])
        self.assertIn("pass_Immirzi_profile_of_a_gate", payload["next_required"])
        self.assertIn("feed_matrix_elements_to_Dirac_thermal_cross_section_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
