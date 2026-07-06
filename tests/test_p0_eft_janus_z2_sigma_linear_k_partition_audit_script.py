import unittest

from scripts.derive_p0_eft_janus_z2_sigma_linear_k_partition_audit import build_payload


class LinearKPartitionAuditTests(unittest.TestCase):
    def test_linear_k_is_partition_issue_not_new_counterterm(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["comparison"]["same_operator"], "sqrt(|h|) K")
        self.assertFalse(payload["comparison"]["independent_counterterm_allowed"])
        self.assertTrue(payload["decision"]["must_be_partitioned_into_Cartan_GHY_or_junction_sector"])
        self.assertFalse(payload["decision"]["counterterm_linear_K_residual_allowed"])
        self.assertIn("do_not_duplicate_sqrt_h_K_operator_in_L_ct", payload["forbidden_shortcuts"])


if __name__ == "__main__":
    unittest.main()
