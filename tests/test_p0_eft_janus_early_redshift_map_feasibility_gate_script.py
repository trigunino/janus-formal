import unittest

from janus_lab.janus_phase_space_occupation_search import (
    early_redshift_map_feasibility_payload,
)


class JanusEarlyRedshiftMapFeasibilityGateTests(unittest.TestCase):
    def test_required_exponent_is_above_simple_eq40_maps(self):
        payload = early_redshift_map_feasibility_payload()

        self.assertGreater(payload["required_exponent_s"], 3.0)
        self.assertLess(payload["required_exponent_s"], 4.0)

    def test_only_speculative_four_power_reaches_target(self):
        payload = early_redshift_map_feasibility_payload()
        rows = {row["name"]: row for row in payload["candidate_maps"]}

        self.assertFalse(rows["published_M18_geometric_redshift"]["reaches_target"])
        self.assertFalse(rows["Eq40_phase_space_occupation_volume"]["reaches_target"])
        self.assertTrue(rows["four_volume_or_action_phase_map"]["reaches_target"])
        self.assertFalse(rows["four_volume_or_action_phase_map"]["derived"])


if __name__ == "__main__":
    unittest.main()
