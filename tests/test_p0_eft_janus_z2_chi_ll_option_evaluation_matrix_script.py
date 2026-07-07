import unittest

from scripts.build_p0_eft_janus_z2_chi_ll_option_evaluation_matrix import build_payload


class ChiLLOptionEvaluationMatrixTests(unittest.TestCase):
    def test_observations_do_not_choose_free_chi(self):
        payload = build_payload()
        policy = payload["observation_policy"]

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(policy["use_observations_to_choose_free_chi_LL"])
        self.assertTrue(policy["use_observations_after_theory_closure"])

    def test_all_current_options_are_listed(self):
        options = build_payload()["options"]

        self.assertIn("explicit_state_chi_LL", options)
        self.assertIn("S2_flux_quantized_chi_LL", options)
        self.assertIn("Souriau_Noether_mass_orbit", options)
        self.assertIn("minimal_LL_gauge_action", options)
        self.assertIn("UV_scale_chi_LL", options)

    def test_flux_plus_gauge_action_are_recommended_first(self):
        ranking = build_payload()["recommended_order"]

        self.assertEqual(ranking[0], "S2_flux_quantized_chi_LL")
        self.assertEqual(ranking[1], "minimal_LL_gauge_action")


if __name__ == "__main__":
    unittest.main()
