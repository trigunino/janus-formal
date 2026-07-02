import unittest

from scripts.build_p0_eft_janus_z4_candidate_cosmology_parameter_policy_gate import build_payload


class P0EFTJanusZ4CandidateCosmologyParameterPolicyGateTests(unittest.TestCase):
    def test_cosmology_policy(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-candidate-cosmology-parameter-policy-gate")
        self.assertFalse(payload["backend_uses_static_spectra_tables"])
        self.assertTrue(payload["cosmological_transfer_regeneration_available"])
        self.assertTrue(all(not fixed for fixed in payload["cosmology_parameters_fixed"].values()))
        self.assertTrue(payload["standard_cosmology_profiled"])
        self.assertEqual(payload["lambda_policy"], "frozen_from_candidate_spec_after_internal_trials")
        self.assertTrue(payload["lambda_frozen"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
