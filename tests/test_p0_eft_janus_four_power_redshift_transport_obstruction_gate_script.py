import unittest

from janus_lab.janus_phase_space_occupation_search import (
    four_power_redshift_transport_obstruction_payload,
)


class JanusFourPowerRedshiftTransportObstructionGateTests(unittest.TestCase):
    def test_s4_is_useful_but_not_source_derived(self):
        payload = four_power_redshift_transport_obstruction_payload()

        self.assertTrue(payload["result"]["s4_numerically_useful"])
        self.assertFalse(payload["result"]["s4_source_derived"])
        self.assertFalse(payload["result"]["s4_promotable"])

    def test_occupation_plus_redshift_is_rejected_as_frequency_map(self):
        payload = four_power_redshift_transport_obstruction_payload()
        rows = {row["name"]: row for row in payload["candidate_decompositions"]}

        self.assertEqual(
            rows["geometric_redshift_plus_occupation_volume"]["verdict"],
            "invalid_as_redshift",
        )


if __name__ == "__main__":
    unittest.main()
