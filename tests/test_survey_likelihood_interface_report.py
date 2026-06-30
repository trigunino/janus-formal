from __future__ import annotations

import unittest

from scripts.build_survey_likelihood_interface_report import (
    build_payload,
    require_survey_layer_ready,
)


class SurveyLikelihoodInterfaceReportTests(unittest.TestCase):
    def test_report_is_interface_only(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["self_test_chi2"], 0.0)
        self.assertEqual(payload["self_test_n_params"], 0)
        self.assertIn("full positive-definite covariance", payload["requirements"])
        self.assertFalse(payload["survey_layer_ready"])
        self.assertFalse(payload["can_call_outputs_predictions"])

    def test_missing_survey_inputs_are_machine_readable(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["missing_survey_inputs"],
            ["n_z", "tomographic_bins", "observed_vector", "covariance", "mask_window"],
        )
        self.assertTrue(
            all(item["blocks_prediction_label"] for item in payload["survey_input_checklist"])
        )

    def test_absent_survey_layer_refuses_prediction_claim(self) -> None:
        payload = build_payload()

        with self.assertRaisesRegex(RuntimeError, "Refusing to label outputs as predictions"):
            require_survey_layer_ready(payload)


if __name__ == "__main__":
    unittest.main()
