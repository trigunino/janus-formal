import unittest

from scripts.run_p0_eft_janus_z4_closed_boltzmann_candidate_highl_decomposition_trial import (
    FROZEN_LAMBDA_E,
    FROZEN_LAMBDA_T,
    build_payload,
)


class P0EFTJanusZ4ClosedBoltzmannCandidateHighLDecompositionTrialTests(unittest.TestCase):
    def test_highl_decomposition_trial_scaffold(self):
        payload = build_payload(run_official=False)

        self.assertEqual(payload["status"], "janus-z4-closed-boltzmann-candidate-highl-decomposition-trial")
        self.assertEqual(payload["lambda_T"], FROZEN_LAMBDA_T)
        self.assertEqual(payload["lambda_E"], FROZEN_LAMBDA_E)
        self.assertTrue(payload["candidate_rerun_unchanged"])
        self.assertTrue(payload["no_parameter_retuning"])
        self.assertTrue(payload["no_new_z4_physics"])
        self.assertFalse(payload["run_official_executed"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
