import unittest

from scripts.build_p0_eft_janus_z2_sigma_primitive_flux_law_closure_audit import (
    build_payload,
)


class PrimitiveFluxLawClosureAuditTests(unittest.TestCase):
    def test_standard_bibliography_closes_unique_route_as_no_go(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["N_gap_equals_abs_n_derived"])
        self.assertTrue(payload["standard_bibliography_closes_as_no_go"])
        self.assertEqual(payload["recommended_active_route"], "N_gap_superselection_family")

    def test_charge_partitions_show_total_c1_does_not_count_punctures(self):
        examples = build_payload()["charge_partition_examples"]

        self.assertIn([2], examples["c1_2_partitions"])
        self.assertIn([1, 1], examples["c1_2_partitions"])
        self.assertIn([3], examples["c1_3_partitions"])
        self.assertIn([1, 1, 1], examples["c1_3_partitions"])

    def test_reopen_route_requires_boundary_state_law(self):
        required = build_payload()["required_to_reopen_unique_route"]

        self.assertIn("Janus_PT_boundary_state_selects_primitive_charge", required)
        self.assertIn("fusion_of_unit_fluxes_forbidden_by_superselection", required)


if __name__ == "__main__":
    unittest.main()
