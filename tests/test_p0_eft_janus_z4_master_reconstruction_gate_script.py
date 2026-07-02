import unittest

from scripts.build_p0_eft_janus_z4_master_reconstruction_gate import build_payload


class P0EFTJanusZ4MasterReconstructionGateTests(unittest.TestCase):
    def test_master_reconstruction_declares_all_maps_as_blocked(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-reconstruction-gate")
        self.assertTrue(payload["unique_equation_master_gate_passed"])
        self.assertTrue(payload["all_reconstruction_maps_declared"])
        self.assertTrue(payload["missing_maps_are_blocked_not_free"])
        for key, status in payload["reconstruction_maps"].items():
            self.assertEqual(status, "blocked_until_master_reconstruction", key)
        self.assertFalse(payload["all_maps_derived_from_same_U_Z4"])
        self.assertFalse(payload["independent_downstream_source_allowed"])
        self.assertFalse(payload["free_reconstruction_coefficient_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])


if __name__ == "__main__":
    unittest.main()
