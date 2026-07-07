import unittest

from scripts.build_p0_eft_janus_z2_sigma_observation_data_inventory import build_payload


class SigmaObservationDataInventoryTests(unittest.TestCase):
    def test_inventory_finds_local_data_but_no_sector_map(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["observation_data_inventory_ready"])
        self.assertIn("desi_dr2_bao", payload["reusable_raw_datasets"])
        self.assertFalse(payload["sector_observable_map_derived"])
        self.assertFalse(payload["trial_can_run_now"])

    def test_legacy_scores_are_not_reusable_as_z2_evidence(self):
        datasets = build_payload()["datasets"]

        self.assertFalse(datasets["desi_dr2_bao"]["existing_model_scores_reusable_for_Z2Sigma"])
        self.assertFalse(datasets["planck2018_priors"]["sector_to_observable_map_available"])


if __name__ == "__main__":
    unittest.main()
