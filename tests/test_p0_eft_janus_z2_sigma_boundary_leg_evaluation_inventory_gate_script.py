import unittest

from scripts.build_p0_eft_janus_z2_sigma_boundary_leg_evaluation_inventory_gate import (
    build_payload,
)


class BoundaryLegEvaluationInventoryGateTests(unittest.TestCase):
    def test_symbolic_inventory_ready_but_numeric_state_blocked(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["boundary_leg_symbolic_inventory_ready"])
        self.assertFalse(payload["numeric_boundary_state_ready"])
        self.assertIn("boundary_projection_charge_ready", payload["primary_blockers"])
        self.assertIn("global_bimetric_state_ready", payload["primary_blockers"])

    def test_forbids_single_leg_and_reference_zero_shortcuts(self):
        payload = build_payload()

        self.assertIn("do_not_evaluate_only_one_boundary_leg", payload["forbidden_shortcuts"])
        self.assertIn("do_not_use_reference_zero_as_positive_source", payload["forbidden_shortcuts"])


if __name__ == "__main__":
    unittest.main()
