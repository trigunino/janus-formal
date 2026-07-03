import unittest

from scripts.build_p0_eft_janus_z2_sigma_dirac_thermal_cross_section_of_a_gate import build_payload


class P0EFTJanusZ2SigmaDiracThermalCrossSectionOfAGateTests(unittest.TestCase):
    def test_cross_section_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dirac_thermal_cross_section_ledger_declared"])
        self.assertTrue(payload["declared"]["Gondolo_Gelmini_relativistic_average_imported"])
        self.assertTrue(payload["declared"]["Dirac_Holst_vertex_gate_declared"])
        self.assertIn("thermal_average", payload["formulas"])

    def test_cross_section_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_matrix_element_ready"])
        self.assertFalse(payload["closure"]["projected_thermal_cross_section_of_a_ready"])
        self.assertFalse(payload["dirac_thermal_cross_section_of_a_ready"])
        self.assertIn("pass_Dirac_Holst_vertex_of_a_gate", payload["next_required"])
        self.assertIn("feed_cross_sections_to_Dirac_interaction_rate_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
