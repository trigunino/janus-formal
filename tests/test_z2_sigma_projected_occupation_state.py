import unittest

from src.janus_lab.z2_sigma_projected_occupation_state import (
    validate_projected_occupation_state_payload,
)


def _payload():
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "explicit_state_initial_data",
        "full_no_fit_prediction_ready": False,
        "N_occ_Z2Sigma": 7.0,
        "N_occ_provenance": "declared_superselection_state_initial_data",
    }


class Z2SigmaProjectedOccupationStateTest(unittest.TestCase):
    def test_valid_payload_is_canonicalized(self):
        payload = validate_projected_occupation_state_payload(_payload())

        self.assertEqual(payload["N_occ_Z2Sigma"], 7.0)
        self.assertFalse(payload["full_no_fit_prediction_ready"])

    def test_rejects_no_fit_claim(self):
        payload = _payload()
        payload["full_no_fit_prediction_ready"] = True
        with self.assertRaisesRegex(ValueError, "full_no_fit_prediction_ready"):
            validate_projected_occupation_state_payload(payload)

    def test_rejects_forbidden_provenance(self):
        for bad in ["Planck", "LCDM", "Z4", "fit", "bao_scan"]:
            payload = _payload()
            payload["N_occ_provenance"] = bad
            with self.assertRaisesRegex(ValueError, "Forbidden N_occ provenance"):
                validate_projected_occupation_state_payload(payload)

    def test_rejects_non_positive_occupation(self):
        payload = _payload()
        payload["N_occ_Z2Sigma"] = 0.0
        with self.assertRaisesRegex(ValueError, "positive and finite"):
            validate_projected_occupation_state_payload(payload)


if __name__ == "__main__":
    unittest.main()
