import unittest

from scripts.build_p0_eft_janus_z4_metric_potential_split_gate import build_payload


class P0EFTJanusZ4MetricPotentialSplitGateTests(unittest.TestCase):
    def test_metric_potential_split_gate(self):
        payload = build_payload()
        diagnostics = payload["diagnostics"]

        self.assertEqual(payload["status"], "janus-z4-metric-potential-split-gate")
        self.assertEqual(payload["delta_level"], "metric_potential_source")
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["native_toy_los_used"])
        self.assertTrue(payload["shared_weyl_delta_preserved"])
        self.assertTrue(payload["deltaPhi_plus_deltaPsi_equals_X_Z4"])
        self.assertTrue(payload["deltaPhi_minus_deltaPsi_equals_deltaSlip_Z4"])
        self.assertTrue(payload["slip_delta_explicitly_tagged"])
        self.assertEqual(payload["slip_source"], "explicit_zero_closure_until_derived")
        self.assertTrue(payload["no_arbitrary_phi_psi_split"])
        self.assertTrue(payload["no_independent_phi_source"])
        self.assertTrue(payload["no_independent_psi_source"])
        self.assertFalse(payload["eta_ratio_used_as_primary"])
        self.assertTrue(payload["eta_diagnostic_guarded"])
        self.assertFalse(payload["recombination_delta_enabled"])
        self.assertFalse(payload["visibility_delta_enabled"])
        self.assertFalse(payload["acoustic_delta_enabled"])
        self.assertFalse(payload["polarization_delta_enabled"])
        self.assertFalse(payload["primordial_delta_enabled"])
        self.assertTrue(diagnostics["deltaPsi_force_term_norm"] > 0.0)
        self.assertTrue(diagnostics["deltaPhi_dot_source_term_norm"] > 0.0)
        self.assertTrue(payload["metric_potential_split_gate_passed"])
        self.assertTrue(payload["early_acoustic_driving_gate_allowed"])
        self.assertFalse(payload["official_planck_trial_allowed"])


if __name__ == "__main__":
    unittest.main()
