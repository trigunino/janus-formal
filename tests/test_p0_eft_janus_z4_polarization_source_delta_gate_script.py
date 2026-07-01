import unittest

from scripts.build_p0_eft_janus_z4_polarization_source_delta_gate import SUBCHANNELS, build_payload


class P0EFTJanusZ4PolarizationSourceDeltaGateTests(unittest.TestCase):
    def test_polarization_source_delta_gate(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-polarization-source-delta-gate")
        self.assertEqual(tuple(payload["subchannels"]), SUBCHANNELS)
        self.assertEqual(payload["source_level"], "E_transfer_source")
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["native_toy_los_used"])
        self.assertFalse(payload["recombination_delta_enabled"])
        self.assertFalse(payload["visibility_delta_enabled"])
        self.assertFalse(payload["background_projection_changed"])
        self.assertFalse(payload["r_s_changed"])
        self.assertFalse(payload["r_d_changed"])
        self.assertFalse(payload["primordial_delta_enabled"])
        self.assertFalse(payload["lensing_delta_enabled"])
        self.assertTrue(payload["C_phi_phi_unchanged"])
        self.assertEqual(payload["deltaSlip_Z4"], "explicit_zero_until_derived")
        self.assertTrue(payload["metric_split_respected"])
        self.assertTrue(payload["Theta2_source_tagged"])
        self.assertTrue(payload["Pi_source_tagged"])
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertTrue(payload["lambda_zero_identity_passed"])
        self.assertTrue(payload["small_lambda_continuity_passed"])
        self.assertTrue(payload["polarization_source_delta_gate_passed"])
        for name in SUBCHANNELS:
            self.assertGreater(payload["source_norms"][name], 0.0)
            self.assertTrue(payload["small_lambda_scan"][name]["0.0"]["ok"])


if __name__ == "__main__":
    unittest.main()
