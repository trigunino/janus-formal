import unittest

from janus_lab.janus_phase_space_occupation_search import (
    redshift_exponent_q0_compatibility_payload,
)


class JanusRedshiftExponentQ0CompatibilityGateTests(unittest.TestCase):
    def test_low_power_maps_force_q0_near_zero(self):
        payload = redshift_exponent_q0_compatibility_payload()
        rows = {row["name"]: row for row in payload["rows"]}

        self.assertGreater(rows["geometric_s1"]["required_q0"], -0.001)
        self.assertGreater(rows["clock_s3_over_2"]["required_q0"], -0.01)

    def test_high_power_map_is_closest_to_published_q0(self):
        payload = redshift_exponent_q0_compatibility_payload()
        rows = {row["name"]: row for row in payload["rows"]}

        self.assertFalse(rows["occupation_volume_s3"]["within_two_sigma"])
        self.assertTrue(rows["four_volume_phase_s4"]["within_two_sigma"])
        self.assertLess(
            rows["four_volume_phase_s4"]["sigma_offset_from_published_q0"],
            rows["occupation_volume_s3"]["sigma_offset_from_published_q0"],
        )


if __name__ == "__main__":
    unittest.main()
