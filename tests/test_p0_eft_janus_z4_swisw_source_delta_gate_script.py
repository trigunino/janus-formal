import unittest

from scripts.build_p0_eft_janus_z4_swisw_source_delta_gate import build_payload


class P0EFTJanusZ4SWISWSourceDeltaGateTests(unittest.TestCase):
    def test_late_isw_source_delta_gate(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-swisw-source-delta-gate")
        self.assertEqual(payload["delta_channel"], "late_ISW_delta")
        self.assertEqual(payload["delta_level"], "source")
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["native_toy_los_used"])
        self.assertFalse(payload["raw_native_los_used_for_planck"])
        self.assertFalse(payload["visibility_delta_enabled"])
        self.assertFalse(payload["recombination_delta_enabled"])
        self.assertFalse(payload["acoustic_phase_delta_enabled"])
        self.assertFalse(payload["polarization_source_delta_enabled"])
        self.assertFalse(payload["primordial_spectrum_delta_enabled"])
        self.assertFalse(payload["early_ISW_delta_enabled"])
        self.assertTrue(payload["late_ISW_delta_enabled"])
        self.assertTrue(payload["lambda_zero_identity_passed"])
        self.assertTrue(payload["small_lambda_continuity_passed"])
        self.assertTrue(payload["late_isw_is_more_isolable_than_early_isw"])
        self.assertTrue(payload["swisw_source_delta_gate_passed"])
        self.assertFalse(payload["official_planck_trial_allowed"])


if __name__ == "__main__":
    unittest.main()
