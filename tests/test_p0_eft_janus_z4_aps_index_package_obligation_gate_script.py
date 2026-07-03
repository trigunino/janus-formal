import unittest

from scripts.build_p0_eft_janus_z4_aps_index_package_obligation_gate import build_payload


class P0EFTJanusZ4APSIndexPackageObligationGateTests(unittest.TestCase):
    def test_local_interfaces_ready_but_global_aps_package_open(self):
        payload = build_payload()

        self.assertTrue(payload["aps_local_interfaces_ready"])
        self.assertFalse(payload["aps_index_package_closed"])
        self.assertIn(
            "pin_minus_lift_squared_minus_one",
            payload["remaining_aps_obligations"],
        )
        self.assertIn(
            "aps_boundary_projector_fredholm",
            payload["remaining_aps_obligations"],
        )
        self.assertTrue(payload["external_theorem_blocker"])
        self.assertEqual(
            payload["obligation_provenance"]["pin_minus_lift_squared_minus_one"]["status"],
            "external_or_missing_internal_theorem",
        )
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
