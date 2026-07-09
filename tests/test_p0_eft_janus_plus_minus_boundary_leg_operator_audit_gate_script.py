import unittest

from janus_lab.janus_phase_space_occupation_search import (
    plus_minus_boundary_leg_operator_audit_payload,
)


class JanusPlusMinusBoundaryLegOperatorAuditGateTests(unittest.TestCase):
    def test_boundary_legs_have_at_most_two_levels_without_sym4_transfer(self):
        payload = plus_minus_boundary_leg_operator_audit_payload()
        rows = {row["name"]: row for row in payload["operator_candidates"]}

        self.assertEqual(payload["inputs"]["Hilbert_dimension"], 1001)
        self.assertEqual(rows["leg_difference_operator"]["max_levels"], 2)
        self.assertFalse(rows["leg_difference_operator"]["can_order_1001_states"])

    def test_legs_help_only_as_doublet_factor(self):
        payload = plus_minus_boundary_leg_operator_audit_payload()

        self.assertTrue(payload["no_fit_conclusion"]["plus_minus_legs_supply_nontrivial_operator"])
        self.assertFalse(payload["no_fit_conclusion"]["plus_minus_legs_alone_supply_1001_ordering"])
        self.assertTrue(payload["no_fit_conclusion"]["still_need_sym4_internal_transfer"])
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
