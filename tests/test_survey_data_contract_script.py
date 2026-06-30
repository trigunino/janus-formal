from __future__ import annotations

import unittest

from scripts.build_survey_data_contract import build_payload, validate_survey_contract


def valid_contract() -> dict:
    return {
        "survey_id": "mock-survey",
        "observable_name": "mock-shear",
        "n_z": {"z": [0.5, 1.0], "weights": [0.4, 0.6]},
        "tomographic_bins": [{"z_min": 0.0, "z_max": 1.5}],
        "observed_vector": [1.0, 2.0],
        "prediction_vector_id": "janus-fixed-prediction-v1",
        "covariance": [[1.0, 0.0], [0.0, 1.0]],
        "mask_window": {"description": "full-sky mock"},
        "nuisance_parameters_declared": [],
        "n_fit_parameters": 0,
    }


class SurveyDataContractTests(unittest.TestCase):
    def test_missing_contract_blocks_readiness(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["survey_layer_ready"])
        self.assertIn("survey_id", payload["validation"]["missing"])

    def test_valid_minimal_contract_is_ready(self) -> None:
        payload = build_payload(valid_contract())

        self.assertTrue(payload["survey_layer_ready"])
        self.assertEqual(payload["validation"]["errors"], [])
        self.assertEqual(payload["validation"]["dimension"], 2)

    def test_malformed_covariance_is_rejected(self) -> None:
        contract = valid_contract()
        contract["covariance"] = [[1.0, 2.0], [2.0, 1.0]]

        validation = validate_survey_contract(contract)

        self.assertFalse(validation["ready"])
        self.assertIn("covariance must be positive definite", validation["errors"])

    def test_nonzero_fit_parameters_are_rejected(self) -> None:
        contract = valid_contract()
        contract["n_fit_parameters"] = 1

        validation = validate_survey_contract(contract)

        self.assertFalse(validation["ready"])
        self.assertIn("n_fit_parameters must be zero", " ".join(validation["errors"]))


if __name__ == "__main__":
    unittest.main()
