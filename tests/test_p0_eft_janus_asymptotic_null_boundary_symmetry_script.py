import unittest

from scripts.build_p0_eft_janus_asymptotic_null_boundary_candidate_matrix_gate import (
    build_payload as build_matrix,
)
from scripts.build_p0_eft_janus_asymptotic_null_boundary_charge_derivation_gate import (
    build_payload as build_charge,
)
from scripts.build_p0_eft_janus_asymptotic_null_boundary_alpha_bridge_gate import (
    build_payload as build_alpha,
)
from scripts.build_p0_eft_janus_asymptotic_null_boundary_exhaustion_verdict_gate import (
    build_payload as build_verdict,
)


class AsymptoticNullBoundarySymmetryTests(unittest.TestCase):
    def test_candidate_matrix_identifies_best_route_but_blocks_live_charge(self):
        payload = build_matrix()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["bms_route_ready"])
        self.assertFalse(payload["internal_null_charge_route_ready"])
        self.assertEqual(
            payload["best_route"],
            "internal_null_PT_bridge_if_promoted_to_real_null_boundary_with_integrable_charge",
        )

    def test_charge_derivation_does_not_derive_janus_mass(self):
        payload = build_charge()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["boundary_mass_charge_derived"])
        self.assertFalse(payload["M_bridge_charge_available"])
        self.assertIn("BMS", payload["route_checks"])
        self.assertIn("Newman_Penrose", payload["route_checks"])

    def test_alpha_bridge_remains_conditional(self):
        payload = build_alpha()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["M_bridge_derived"])
        self.assertFalse(payload["alpha_generated_no_fit"])
        self.assertIn("boundary_mass_charge_not_derived", payload["blocked_by"])

    def test_exhaustion_verdict(self):
        payload = build_verdict()

        self.assertTrue(payload["all_routes_audited"])
        self.assertFalse(payload["boundary_mass_charge_derived"])
        self.assertFalse(payload["no_fit_alpha_generated"])
        self.assertEqual(
            payload["final_branch_status"],
            "best_next_framework_but_missing_Janus_null_boundary_data",
        )


if __name__ == "__main__":
    unittest.main()
