import unittest

from scripts.build_p0_eft_janus_z4_master_to_observable_map_gate import build_payload


class P0EFTJanusZ4MasterToObservableMapGateTests(unittest.TestCase):
    def test_observable_maps_are_all_from_master_generator(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-to-observable-map-gate")
        self.assertTrue(payload["master_constraint_consistency_gate_passed"])
        self.assertTrue(payload["observable_functionals_declared"])
        self.assertTrue(payload["all_observable_maps_derived_from_same_U_Z4"])
        for key in ("S_T_Z4", "S_E_Z4", "S_lens_Z4", "Doppler_Z4", "Theta0_Z4", "Pi_Z4", "Slip_Z4"):
            self.assertIn(key, payload["observable_functionals"])
        self.assertFalse(payload["independent_temperature_patch_allowed"])
        self.assertFalse(payload["independent_Doppler_patch_allowed"])
        self.assertFalse(payload["independent_Pi_patch_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])


if __name__ == "__main__":
    unittest.main()
