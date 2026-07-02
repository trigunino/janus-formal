import unittest

from scripts.build_p0_eft_janus_z4_unique_equation_master_gate import build_payload


class P0EFTJanusZ4UniqueEquationMasterGateTests(unittest.TestCase):
    def test_unique_master_gate_declares_upstream_generator(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-unique-equation-master-gate")
        self.assertTrue(payload["frozen_patchwork_branches_acknowledged"])
        self.assertTrue(payload["master_variable_declared"])
        self.assertEqual(payload["master_variable_name"], "U_Z4")
        self.assertTrue(payload["master_operator_declared"])
        self.assertTrue(payload["master_source_declared"])
        self.assertEqual(payload["master_equation_form"], "L_Z4[U_Z4] = J_Z4")
        self.assertTrue(payload["Z4_parity_declared"])
        self.assertTrue(payload["boundary_or_orbifold_conditions_declared"])
        self.assertTrue(payload["GR_limit_declared"])
        self.assertTrue(payload["plus_minus_reconstruction_declared"])
        self.assertTrue(payload["observable_projection_declared"])
        self.assertFalse(payload["master_equation_solved"])
        self.assertFalse(payload["independent_deltaSlip_allowed"])
        self.assertFalse(payload["independent_Doppler_allowed"])
        self.assertFalse(payload["independent_Pi_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])


if __name__ == "__main__":
    unittest.main()
