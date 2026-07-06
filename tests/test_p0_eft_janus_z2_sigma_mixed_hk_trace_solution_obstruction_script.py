import unittest

from scripts.derive_p0_eft_janus_z2_sigma_mixed_hk_trace_solution_obstruction import (
    build_payload,
)


class MixedHKTraceSolutionObstructionTests(unittest.TestCase):
    def test_mixed_hk_minimal_solution_requires_gHY_like_linear_k(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(
            payload["solution_family"]["coefficient_conditions"]["c1"],
            "4*epsilon_Z2/kappa_Z2Sigma",
        )
        self.assertTrue(payload["obstruction"]["linear_K_required"])
        self.assertFalse(payload["obstruction"]["dirichlet_h_only_minimal_counterterm_closes"])
        self.assertTrue(payload["obstruction"]["cartan_GHY_like"])
        self.assertFalse(payload["obstruction"]["counterterm_non_duplication_policy_satisfied"])
        self.assertFalse(payload["obstruction"]["minimal_mixed_hK_counterterm_closes"])
        self.assertFalse(payload["decision"]["dirichlet_h_only_selected"])
        self.assertFalse(payload["decision"]["mixed_hK_minimal_counterterm_selected"])
        self.assertTrue(payload["decision"]["active_counterterm_must_be_non_GHY_density"])
        self.assertEqual(
            payload["decision"]["selected_remaining_route"],
            "derive_non_GHY_tunnel_density_or_repartition_radius_blocks",
        )


if __name__ == "__main__":
    unittest.main()
