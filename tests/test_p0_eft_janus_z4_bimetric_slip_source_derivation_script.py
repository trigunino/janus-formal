import unittest

from scripts.build_p0_eft_janus_z4_bimetric_slip_source_derivation import build_payload


class P0EFTJanusZ4BimetricSlipSourceDerivationTests(unittest.TestCase):
    def test_source_equation_is_derived_but_candidate_stays_blocked(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-bimetric-slip-source-derivation")
        self.assertTrue(payload["slip_source_equation_derived"])
        self.assertTrue(payload["slip_is_derived"])
        self.assertFalse(payload["free_slip_parameter"])
        self.assertFalse(payload["free_eta_ratio"])
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["raw_toy_LOS"])
        self.assertIn("Lap_TF(delta_slip_Z4)", payload["source_operator"])
        self.assertFalse(payload["value_slip_transport_closed"])
        self.assertTrue(payload["boundary_green_or_normal_mode_required"])
        self.assertFalse(payload["derived_slip_candidate_enabled"])
        self.assertFalse(payload["planck_trial_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
