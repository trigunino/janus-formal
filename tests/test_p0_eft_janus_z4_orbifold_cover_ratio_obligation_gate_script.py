import unittest

from scripts.build_p0_eft_janus_z4_orbifold_cover_ratio_obligation_gate import (
    build_payload,
)


class P0EFTJanusZ4OrbifoldCoverRatioObligationGateTests(unittest.TestCase):
    def test_local_interfaces_ready_but_global_cover_ratio_open(self):
        payload = build_payload()

        self.assertTrue(payload["orbifold_local_interfaces_ready"])
        self.assertFalse(payload["janus_cover_ratio_derived"])
        self.assertIn(
            "global_euler_holonomy_class_computed",
            payload["remaining_orbifold_obligations"],
        )
        self.assertIn(
            "global_volume_ratio_unique_two_to_one",
            payload["remaining_orbifold_obligations"],
        )
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
