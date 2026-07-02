import unittest

from scripts.build_p0_eft_janus_z4_closed_boltzmann_candidate_robustness_gate import build_payload


class P0EFTJanusZ4ClosedBoltzmannCandidateRobustnessGateTests(unittest.TestCase):
    def test_candidate_robustness_gate(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-closed-boltzmann-candidate-robustness-gate")
        self.assertTrue(payload["best_point_stable"])
        self.assertTrue(payload["local_curvature_detected"])
        self.assertTrue(payload["lambda_best_not_edge"])
        self.assertTrue(payload["gain_survives_lmax_variation"])
        self.assertTrue(payload["gain_survives_TCA_switch_variation"])
        self.assertTrue(payload["delta_chi2_available_remains_below_minus_5"])
        self.assertTrue(payload["TE_EE_smoothness_remains_pass"])
        self.assertTrue(payload["transport_guards_remain_pass"])
        self.assertTrue(payload["lmax_convergence_remains_pass"])
        self.assertTrue(payload["closed_boltzmann_candidate_robustness_gate_passed"])
        self.assertFalse(payload["full_planck_verdict"])


if __name__ == "__main__":
    unittest.main()
