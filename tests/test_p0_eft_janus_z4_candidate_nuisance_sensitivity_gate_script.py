import unittest

from scripts.build_p0_eft_janus_z4_candidate_nuisance_sensitivity_gate import build_payload


class P0EFTJanusZ4CandidateNuisanceSensitivityGateTests(unittest.TestCase):
    def test_nuisance_sensitivity_gate(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-candidate-nuisance-sensitivity-gate")
        self.assertTrue(payload["lambda_frozen"])
        self.assertTrue(payload["no_new_z4_physics"])
        self.assertTrue(payload["nuisance_perturbations_applied_symmetrically"])
        self.assertTrue(payload["gain_survives_small_nuisance_perturbations"])
        self.assertTrue(payload["gain_sign_stable"])
        self.assertTrue(payload["TE_cost_remains_small"])
        self.assertTrue(payload["EE_not_degraded"])
        self.assertTrue(payload["foreground_calibration_sensitivity_reported"])
        self.assertEqual(payload["candidate_status"], "nuisance_sensitivity_checked_candidate")
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])
        self.assertTrue(payload["gate_passed"])


if __name__ == "__main__":
    unittest.main()
