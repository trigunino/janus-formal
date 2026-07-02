import unittest

from scripts.build_p0_eft_janus_z4_standalone_teee_handshake_gate import build_payload


class P0EFTJanusZ4StandaloneTEEEHandshakeGateTests(unittest.TestCase):
    def test_standalone_teee_handshake_gate(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-standalone-teee-handshake-gate")
        self.assertTrue(payload["standalone_highl_TE_available"])
        self.assertTrue(payload["standalone_highl_EE_available"])
        self.assertTrue(payload["standalone_highl_TE_EE_acquired"])
        self.assertTrue(payload["gr_reference_handshake_report_present"])
        self.assertTrue(payload["candidate_must_remain_frozen"])
        self.assertTrue(payload["no_parameter_retuning"])
        self.assertTrue(payload["no_new_delta_channel"])
        self.assertTrue(payload["no_slip_opening"])
        self.assertTrue(payload["no_recombination_opening"])
        self.assertTrue(payload["no_visibility_opening"])
        self.assertTrue(payload["no_mirror_sector_opening"])
        self.assertTrue(payload["no_primordial_shape_opening"])
        self.assertTrue(payload["no_lensing_z4_extra"])
        self.assertTrue(payload["no_raw_native_toy_LOS"])
        self.assertTrue(payload["closed_boltzmann_candidate_highl_decomposition_trial_allowed"])
        self.assertFalse(payload["full_planck_validation_allowed"])
        self.assertTrue(payload["standalone_teee_handshake_gate_passed"])
        for value in payload["convention_checks"].values():
            self.assertTrue(value)


if __name__ == "__main__":
    unittest.main()
