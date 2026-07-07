import unittest

from scripts.build_p0_eft_janus_z2_sigma_ngap_selection_law_registry import build_payload


class SigmaNgapSelectionLawRegistryTests(unittest.TestCase):
    def test_registry_keeps_family_but_no_unique_prediction(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["N_gap_unique_prediction_ready"])
        self.assertTrue(payload["N_gap_family_ready"])
        self.assertEqual(payload["current_best_status"], "discrete_superselection_family")

    def test_diagnostics_and_observation_are_not_selection_laws(self):
        laws = build_payload()["laws"]

        self.assertEqual(laws["internal_spectral_horizon_ranking"]["kind"], "diagnostic_ranking_not_selector")
        self.assertFalse(laws["internal_spectral_horizon_ranking"]["selects_unique_N_gap"])
        self.assertEqual(laws["observation_trial"]["kind"], "external_rejection_or_ranking_not_internal_law")
        self.assertFalse(laws["observation_trial"]["selects_unique_N_gap"])

    def test_primitive_flux_no_go_is_recorded(self):
        payload = build_payload()

        self.assertTrue(payload["primitive_flux_standard_no_go"])
        self.assertEqual(payload["laws"]["primitive_flux_unit_law"]["status"], "closed_negative_on_standard_bibliography")


if __name__ == "__main__":
    unittest.main()
