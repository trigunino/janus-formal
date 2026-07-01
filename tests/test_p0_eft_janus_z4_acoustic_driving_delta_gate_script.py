import unittest

from scripts.build_p0_eft_janus_z4_acoustic_driving_delta_gate import build_payload


class P0EFTJanusZ4AcousticDrivingDeltaGateTests(unittest.TestCase):
    def test_acoustic_driving_delta_gate(self):
        payload = build_payload()
        metrics = payload["source_metrics"]
        scan = payload["small_lambda_scan"]

        self.assertEqual(payload["status"], "janus-z4-acoustic-driving-delta-gate")
        self.assertEqual(payload["delta_level"], "temperature_source")
        self.assertTrue(payload["metric_potential_split_gate_required"])
        self.assertTrue(payload["metric_split_used"])
        self.assertEqual(payload["deltaSlip_Z4"], "explicit_zero_until_derived")
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["native_toy_los_used"])
        self.assertTrue(payload["diagnostic_response_proxy_used"])
        self.assertFalse(payload["recombination_delta_enabled"])
        self.assertFalse(payload["visibility_delta_enabled"])
        self.assertFalse(payload["visibility_function_changed"])
        self.assertFalse(payload["recombination_changed"])
        self.assertFalse(payload["background_projection_changed"])
        self.assertFalse(payload["r_s_changed"])
        self.assertFalse(payload["r_d_changed"])
        self.assertFalse(payload["primordial_delta_enabled"])
        self.assertFalse(payload["polarization_source_delta_enabled"])
        self.assertTrue(payload["EE_unlensed_unchanged"])
        self.assertTrue(payload["C_phi_phi_unchanged"])
        self.assertTrue(payload["TT_unlensed_may_change"])
        self.assertTrue(payload["TE_unlensed_may_change"])
        self.assertTrue(metrics["SW_surface_component_norm"] > 0.0)
        self.assertTrue(metrics["early_ISW_component_norm"] > 0.0)
        self.assertTrue(metrics["max_delta_source_near_recombination"] > 0.0)
        self.assertTrue(metrics["max_delta_source_near_equality"] > 0.0)
        self.assertFalse(payload["late_isw_leakage"])
        self.assertEqual(scan["0.0"]["TT_first_peak_shift"], 0.0)
        self.assertEqual(scan["0.0"]["TE_first_zero_shift"], 0.0)
        self.assertTrue(all(row["EE_unchanged"] for row in scan.values()))
        self.assertTrue(payload["lambda_zero_identity_passed"])
        self.assertTrue(payload["small_lambda_continuity_passed"])
        self.assertTrue(payload["acoustic_driving_delta_gate_passed"])
        self.assertTrue(payload["official_planck_acoustic_driving_trial_allowed"])
        self.assertFalse(payload["official_planck_trial_allowed"])


if __name__ == "__main__":
    unittest.main()
