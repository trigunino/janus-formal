import unittest

from scripts.run_p0_eft_janus_z4_planck_lensing_input_dependence_gate import build_payload


class P0EFTJanusZ4PlanckLensingInputDependenceGateTests(unittest.TestCase):
    def test_lensing_input_dependence_scaffold(self):
        payload = build_payload(run_official=False)

        self.assertEqual(payload["status"], "janus-z4-planck-lensing-input-dependence-gate")
        self.assertTrue(payload["C_phi_phi_frozen"])
        self.assertFalse(payload["z4_lensing_delta_enabled"])
        self.assertTrue(payload["primary_CMB_delta_enabled_in_B_D"])
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["native_toy_los_used"])
        self.assertFalse(payload["official_likelihood_requested"])
        self.assertFalse(payload["official_likelihood_executed"])
        self.assertIn("A_phiphi_GR_CMB_GR", payload["spectra_paths"])
        self.assertIn("B_phiphi_GR_CMB_acoustic_delta", payload["spectra_paths"])
        self.assertIn("C_phiphi_control_CMB_GR", payload["spectra_paths"])
        self.assertIn("D_phiphi_control_CMB_acoustic_delta", payload["spectra_paths"])


if __name__ == "__main__":
    unittest.main()
