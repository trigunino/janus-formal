import unittest

from scripts.build_p0_eft_janus_z2_alpha_state_sector_advantage_gate import build_payload


class AlphaStateSectorAdvantageGateTests(unittest.TestCase):
    def test_allows_only_methodological_advantage(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["proceed_with_alpha_state_sector"])
        self.assertTrue(payload["methodological_pipeline_advantage_over_published_janus"])
        self.assertFalse(payload["physical_predictive_advantage_over_published_janus"])
        self.assertFalse(payload["our_branch"]["full_no_fit_prediction_ready"])

    def test_blocks_if_physical_predictive_advantage_is_required(self):
        payload = build_payload(require_physical_predictive_advantage=True)

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["proceed_with_alpha_state_sector"])


if __name__ == "__main__":
    unittest.main()
