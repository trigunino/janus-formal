import unittest

from scripts.build_p0_eft_janus_z4_theta2_tight_coupling_closure_gate import build_payload


class P0EFTJanusZ4Theta2TightCouplingClosureGateTests(unittest.TestCase):
    def test_theta2_tight_coupling_closure(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-theta2-tight-coupling-closure-gate")
        self.assertEqual(payload["theta2_previous_status"], "source_tagged_effective")
        self.assertEqual(payload["theta2_new_status"], "tight_coupling_derived_effective")
        self.assertFalse(payload["boltzmann_hierarchy_closed"])
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["native_toy_los_used"])
        self.assertFalse(payload["visibility_delta_enabled"])
        self.assertFalse(payload["recombination_delta_enabled"])
        self.assertFalse(payload["background_projection_changed"])
        self.assertFalse(payload["r_s_changed"])
        self.assertFalse(payload["r_d_changed"])
        self.assertFalse(payload["primordial_delta_enabled"])
        self.assertTrue(payload["lensing_C_phi_phi_frozen"])
        self.assertTrue(payload["slip_frozen"])
        self.assertTrue(payload["theta2_depends_on_k_over_kappadot"])
        self.assertTrue(payload["theta2_response_vanishes_as_k_over_kappadot_to_zero"])
        self.assertTrue(payload["theta2_response_regular_when_visibility_peaks"])
        self.assertTrue(payload["theta2_response_smooth_in_k"])
        self.assertTrue(payload["theta2_response_smooth_in_tau"])
        self.assertTrue(payload["theta2_tight_coupling_closure_gate_passed"])


if __name__ == "__main__":
    unittest.main()
