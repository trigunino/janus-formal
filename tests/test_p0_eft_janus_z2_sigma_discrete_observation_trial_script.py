import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_discrete_sector_observation_trial import build_payload


class SigmaDiscreteObservationTrialTests(unittest.TestCase):
    def test_active_trial_blocks_without_observable_map(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["trial_ready"])
        self.assertIn("sector_observable_map_derived", payload["blocked_by"])
        self.assertFalse(payload["unique_prediction_claim_allowed"])

    def test_declared_trial_ranks_fixed_sectors_without_unique_claim(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "trial.json"
            path.write_text(
                json.dumps(
                    {
                        "provenance": "active_sector_observable_map_declared",
                        "sector_observable_map_derived": True,
                        "observational_data_vector_declared": True,
                        "non_overlap_accounting_declared": True,
                        "channels": [
                            {
                                "name": "bridge_mass_window",
                                "observable_key": "M_bridge_kg",
                                "target": 4.05e-8,
                                "sigma": 5.0e-10,
                                "min": 3.9e-8,
                                "max": 4.2e-8,
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(path)

        self.assertTrue(payload["trial_ready"])
        self.assertEqual(payload["surviving_sectors"], [4])
        self.assertTrue(payload["unique_sector_selected_by_trial"])
        self.assertFalse(payload["unique_prediction_claim_allowed"])

    def test_continuous_fit_blocks_trial(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "trial.json"
            path.write_text(
                json.dumps(
                    {
                        "provenance": "active_sector_observable_map_declared",
                        "sector_observable_map_derived": True,
                        "observational_data_vector_declared": True,
                        "non_overlap_accounting_declared": True,
                        "continuous_fit_used": True,
                        "channels": [{"observable_key": "R_s_m", "min": 1e-35}],
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(path)

        self.assertFalse(payload["trial_ready"])
        self.assertIn("continuous_fit_forbidden", payload["blocked_by"])


if __name__ == "__main__":
    unittest.main()
