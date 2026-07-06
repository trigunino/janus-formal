import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_minimal_basis_dual_route_decision_gate import (
    build_payload,
)


class CountertermMinimalBasisDualRouteDecisionGateTests(unittest.TestCase):
    def test_trace_route_blocks_and_nonzero_route_is_parametric_only(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertFalse(payload["routes"]["active_trace_solution_route"]["ready"])
        self.assertEqual(payload["routes"]["active_trace_solution_route"]["status"], "blocked")
        self.assertTrue(payload["routes"]["nonzero_parametric_E_counterterm_route"]["ready"])
        self.assertEqual(
            payload["routes"]["nonzero_parametric_E_counterterm_route"]["status"],
            "parametric_only",
        )
        self.assertTrue(payload["decision"]["do_not_claim_E_counterterm_zero"])
        self.assertTrue(payload["decision"]["do_not_fit_c1_c2_c3"])


if __name__ == "__main__":
    unittest.main()
