import unittest

from scripts.derive_p0_eft_janus_z2_sigma_cartan_ghy_junction_trace_partition_audit import (
    build_payload,
)


class CartanGHYJunctionTracePartitionAuditTests(unittest.TestCase):
    def test_finite_throat_trace_is_partitioned_out_of_counterterm(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["junction_trace"]["surface_stress_trace"], "S = 12/(kappa_Z2Sigma R)")
        self.assertTrue(payload["partition"]["finite_throat_trace_carried_by_junction"])
        self.assertEqual(payload["partition"]["linear_K_counterterm_residual_after_partition"], "0")
        self.assertEqual(payload["partition"]["counterterm_c1_after_partition"], "0")
        self.assertTrue(payload["linear_K_partition_closed"])
        self.assertFalse(payload["E_counterterm_ready"])
        self.assertIn(
            "do_not_claim_full_E_counterterm_zero_from_linear_K_partition_only",
            payload["forbidden_shortcuts"],
        )


if __name__ == "__main__":
    unittest.main()
