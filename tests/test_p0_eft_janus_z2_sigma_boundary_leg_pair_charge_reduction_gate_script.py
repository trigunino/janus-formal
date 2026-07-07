import unittest

from scripts.build_p0_eft_janus_z2_sigma_boundary_leg_pair_charge_reduction_gate import (
    build_payload,
)


class BoundaryLegPairChargeReductionGateTests(unittest.TestCase):
    def test_pair_is_ready_but_charge_is_zero(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["pair_evaluation_ready"])
        self.assertFalse(payload["nonzero_boundary_state_ready"])
        self.assertEqual(payload["primary_blocker"], "renormalized_unit_charge_zero")

    def test_uses_both_legs_and_opposite_normals(self):
        payload = build_payload()
        readiness = payload["readiness"]

        self.assertTrue(readiness["plus_leg_evaluated"])
        self.assertTrue(readiness["minus_leg_evaluated"])
        self.assertTrue(readiness["opposite_normals_verified"])


if __name__ == "__main__":
    unittest.main()
