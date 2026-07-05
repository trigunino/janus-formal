import unittest

from scripts.build_p0_eft_janus_z2_sigma_normal_matter_current_gate import build_payload


class P0EFTJanusZ2SigmaNormalMatterCurrentGateTests(unittest.TestCase):
    def test_normal_matter_current_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["normal_matter_current_ledger_declared"])
        self.assertTrue(payload["declared"]["Noether_current_formula_imported"])
        self.assertTrue(payload["declared"]["plus_minus_matter_current_gate_declared"])
        self.assertTrue(payload["declared"]["projected_Dirac_matter_current_gate_declared"])
        self.assertTrue(payload["declared"]["projected_Dirac_normal_current_gate_declared"])
        self.assertTrue(payload["declared"]["normal_projection_criterion_declared"])
        self.assertIn("J_n^Z2Sigma", payload["formula"]["z2_projected_normal_current"])

    def test_no_normal_current_is_not_derived_without_currents_and_normals(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_matter_current_ready"])
        self.assertFalse(payload["closure"]["Sigma_normals_ready"])
        self.assertFalse(payload["closure"]["no_normal_matter_current_derived"])
        self.assertFalse(payload["no_normal_matter_current_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_solution_certificate")
        self.assertIn("pass_plus_minus_matter_current_gate", payload["next_required"])
        self.assertIn("pass_projected_Dirac_matter_current_gate", payload["next_required"])
        self.assertIn("pass_projected_Dirac_normal_current_gate", payload["next_required"])
        self.assertIn("pass_tangent_normal_orientation_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
