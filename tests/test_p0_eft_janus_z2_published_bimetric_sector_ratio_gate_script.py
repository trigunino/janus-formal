import unittest

from scripts.build_p0_eft_janus_z2_published_bimetric_sector_ratio_gate import (
    build_payload,
)


class PublishedBimetricSectorRatioGateTests(unittest.TestCase):
    def test_extracts_relative_ratio_only(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["relative_sector_ratio_ready"])
        self.assertFalse(payload["absolute_density_scale_ready"])
        self.assertAlmostEqual(
            payload["ratio_payload"]["rho_minus0_over_rho_plus0"], -19.0
        )

    def test_forbids_turning_ratio_into_density(self):
        payload = build_payload()

        self.assertIn(
            "do_not_turn_5_95_ratio_into_absolute_density",
            payload["forbidden_shortcuts"],
        )


if __name__ == "__main__":
    unittest.main()
