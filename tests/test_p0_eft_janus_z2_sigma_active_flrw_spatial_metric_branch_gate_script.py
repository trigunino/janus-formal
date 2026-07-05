import unittest

from scripts.build_p0_eft_janus_z2_sigma_active_flrw_spatial_metric_branch_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaActiveFLRWSpatialMetricBranchGateTests(unittest.TestCase):
    def test_spatial_metric_contract_ready_but_values_blocked(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["projective_tunnel_two_fold_topology_ready"])
        self.assertFalse(payload["topology_alone_fixes_spatial_metric_branch"])
        self.assertTrue(payload["flrw_spatial_metric_contract_declared"])
        self.assertTrue(payload["curvature_sign_domain_declared"])
        self.assertEqual(payload["curvature_sign_allowed_values"], [-1, 0, 1])
        self.assertTrue(payload["curvature_radius_symbol_declared"])
        self.assertEqual(
            payload["spatial_scalar_curvature_relation"],
            "R3_Z2Sigma = 6*k_Z2Sigma/R_curv_Z2Sigma^2",
        )
        self.assertTrue(payload["requires_active_tunnel_embedding_X_plus_minus_of_a"])
        self.assertTrue(payload["requires_active_induced_spatial_metric_on_FLRW_slices"])
        self.assertFalse(payload["flrw_spatial_metric_branch_values_ready"])
        self.assertFalse(payload["curvature_sign_values_ready"])
        self.assertFalse(payload["curvature_radius_values_ready"])
        self.assertFalse(payload["gate_passed"])

    def test_spatial_metric_branch_forbids_external_fit_or_archived_inputs(self):
        payload = build_payload()

        self.assertFalse(payload["uses_compressed_planck_lcdm_background"])
        self.assertFalse(payload["uses_archived_z4_background"])
        self.assertFalse(payload["uses_observational_curvature_fit"])


if __name__ == "__main__":
    unittest.main()
