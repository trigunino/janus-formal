import unittest

from scripts.build_p0_eft_janus_z4_gauge_fixing_variation_uniqueness_gate import (
    build_payload,
)


class P0EFTJanusZ4GaugeFixingVariationUniquenessGateTests(unittest.TestCase):
    def test_gauge_scaffold_ready_but_uniqueness_open(self):
        payload = build_payload()

        self.assertTrue(payload["gauge_fixing_scaffold_ready"])
        self.assertFalse(payload["gauge_fixing_variation_unique"])
        self.assertIn(
            "residual_gauge_freedom_removed_by_janus_geometry",
            payload["remaining_gauge_obligations"],
        )
        self.assertIn(
            "gauge_fixed_boundary_variation_unique",
            payload["remaining_gauge_obligations"],
        )
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
