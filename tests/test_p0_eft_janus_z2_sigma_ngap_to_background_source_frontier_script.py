import unittest

from scripts.build_p0_eft_janus_z2_sigma_ngap_to_background_source_frontier import build_payload


class SigmaNgapToBackgroundSourceFrontierTests(unittest.TestCase):
    def test_frontier_blocks_observable_map_without_background_source(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["discrete_family_ready"])
        self.assertFalse(payload["N_gap_to_background_source_ready"])
        self.assertFalse(payload["sector_to_observable_map_derived"])
        self.assertFalse(payload["DESI_BAO_trial_unblocked"])
        self.assertIn("E_Z2Sigma(a)^2", payload["missing_effective_primitives"])

    def test_existing_throat_quantities_are_not_background_sources(self):
        payload = build_payload()

        self.assertTrue(payload["sector_rows"])
        self.assertTrue(all(row["available_throat_quantities_only"] for row in payload["sector_rows"]))
        self.assertFalse(payload["channels"]["LL_bridge_tension_source"]["can_emit_E_Z2Sigma_of_a"])


if __name__ == "__main__":
    unittest.main()
