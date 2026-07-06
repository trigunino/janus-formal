import unittest

from scripts.derive_p0_eft_janus_z2_sigma_no_extension_frontier_summary_gate import (
    build_payload,
)


class JanusZ2SigmaNoExtensionFrontierSummaryGateTest(unittest.TestCase):
    def test_frontier_records_remaining_no_extension_blockers(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["policy"]["extension_allowed"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertTrue(
            payload["no_extension_route_exhausted_for_observational_BAO"]
        )
        self.assertTrue(payload["blockers"]["R_Sigma_modulus"]["open"])
        self.assertTrue(payload["blockers"]["projected_baryon_charge"]["open"])
        self.assertIn(
            "R_Sigma_not_fixed_by_existing_action", payload["primary_blockers"]
        )
        self.assertIn(
            "absolute_projected_Noether_charge_not_fixed",
            payload["primary_blockers"],
        )
        routes = payload["no_extension_routes_tested"]
        self.assertTrue(routes["collar_reduction_to_surface_Rh"]["operator_found"])
        self.assertFalse(routes["collar_reduction_to_surface_Rh"]["coefficient_fixed"])
        self.assertFalse(routes["regular_throat_condition"]["R_Sigma_fixed"])
        self.assertTrue(
            routes["APS_Pin_projected_charge_selection"][
                "charge_class_constraints_found"
            ]
        )
        self.assertFalse(
            routes["APS_Pin_projected_charge_selection"]["absolute_charge_fixed"]
        )


if __name__ == "__main__":
    unittest.main()
