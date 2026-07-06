import unittest

from scripts.derive_p0_eft_janus_z2_sigma_counterterm_trace_target_resolution import (
    build_payload,
)


class CountertermTraceTargetResolutionTests(unittest.TestCase):
    def test_trace_payload_is_blocked_without_non_ghy_absence_and_scross(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(
            payload["derivation"][
                "finite_israel_trace_partitioned_into_Cartan_GHY_junction"
            ]
        )
        self.assertTrue(
            payload["derivation"]["mixed_hK_trace_match_requires_linear_K_duplicate"]
        )
        self.assertEqual(payload["derivation"]["counterterm_c1_after_partition"], "0")
        self.assertFalse(payload["trace_targets"]["counterterm_trace_residual_inputs_allowed"])
        self.assertEqual(payload["decision"], "do_not_emit_counterterm_trace_residual_inputs")
        self.assertIn("metric_non_GHY_trace_R_h", payload["primary_blockers"])
        self.assertIn("extrinsic_non_GHY_trace_R_K", payload["primary_blockers"])
        self.assertIn("cross_action_source_accepted", payload["primary_blockers"])
        self.assertIn("do_not_use_linear_K_counterterm_duplicate", payload["forbidden_shortcuts"])


if __name__ == "__main__":
    unittest.main()
