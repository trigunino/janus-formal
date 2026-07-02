import unittest

from scripts.build_p0_eft_janus_z4_ward_atomic_closure_gate import build_payload


class P0EFTJanusZ4WardAtomicClosureGateTests(unittest.TestCase):
    def test_ward_current_scaffold_ready_but_global_closure_open(self):
        payload = build_payload()

        self.assertTrue(payload["ward_current_scaffold_ready"])
        self.assertFalse(payload["ward_closure_ready"])
        self.assertIn(
            "current_plus_cancels_weighted_minus",
            payload["remaining_ward_obligations"],
        )
        self.assertIn(
            "anomaly_vanishes_globally",
            payload["remaining_ward_obligations"],
        )
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
