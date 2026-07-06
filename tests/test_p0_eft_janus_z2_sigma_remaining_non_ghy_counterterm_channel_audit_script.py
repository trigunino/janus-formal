import unittest

from scripts.derive_p0_eft_janus_z2_sigma_remaining_non_ghy_counterterm_channel_audit import (
    build_payload,
)


class RemainingNonGHYCountertermChannelAuditTests(unittest.TestCase):
    def test_known_channels_zero_under_no_extension_policy(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["known_zero_after_partition"]["linear_K_GHY_channel"])
        self.assertTrue(payload["known_zero_after_partition"]["first_order_boundary_topological_channel"])
        self.assertTrue(payload["known_zero_after_partition"]["PT67_smooth_joint_corner_exact_channel"])
        self.assertTrue(payload["known_zero_after_partition"]["torsion_pullback_channel"])
        self.assertTrue(payload["known_zero_after_partition"]["immirzi_radial_contraction"])
        self.assertTrue(payload["known_zero_after_partition"]["local_projected_spinor_residual_channel"])
        self.assertTrue(payload["known_zero_after_partition"]["perfect_fluid_matter_flux_residual_channel"])
        self.assertTrue(payload["known_zero_after_partition"]["full_immirzi_nonradial_channel"])
        self.assertFalse(payload["open_non_GHY_channels"]["metric_non_GHY_trace_R_h"])
        self.assertFalse(payload["open_non_GHY_channels"]["extrinsic_non_GHY_trace_R_K"])
        self.assertFalse(payload["open_non_GHY_channels"]["spinor_residual_channel"])
        self.assertFalse(payload["open_non_GHY_channels"]["full_immirzi_nonradial_R_chi"])
        self.assertFalse(payload["open_non_GHY_channels"]["connection_residual_channel"])
        self.assertTrue(payload["post_radius_embedding_channels"]["embedding_residual_channel"])
        self.assertNotIn("embedding_residual_channel", payload["open_non_GHY_channels"])
        self.assertFalse(payload["open_non_GHY_channels"]["matter_flux_residual_channel"])
        self.assertFalse(payload["open_non_GHY_channels"]["non_topological_cross_action_sigma_source"])
        self.assertTrue(payload["cross_action_audit"]["no_extension_policy_forbids_cross_action"])
        self.assertNotIn("derive_or_eliminate_matter_flux_residual_channel", payload["next_required"])
        self.assertIn("connection", payload["residual_channel_frontiers"])
        self.assertFalse(any(payload["open_non_GHY_channels"].values()))
        self.assertTrue(payload["remaining_non_GHY_channel_absence_proved"])
        self.assertTrue(payload["E_counterterm_zero_conditionally_allowed"])
        self.assertTrue(payload["E_counterterm_zero_under_no_extension_policy"])
        self.assertFalse(payload["E_counterterm_ready"])


if __name__ == "__main__":
    unittest.main()
