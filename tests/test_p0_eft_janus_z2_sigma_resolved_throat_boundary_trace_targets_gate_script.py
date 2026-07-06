import unittest

from scripts.build_p0_eft_janus_z2_sigma_resolved_throat_boundary_trace_targets_gate import (
    build_payload,
)


class ResolvedThroatBoundaryTraceTargetsGateTests(unittest.TestCase):
    def test_trace_targets_are_declared_but_not_faked(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["geometry_condition"]["Sigma_is_geometric_boundary_interface"])
        self.assertEqual(
            payload["geometry_condition"]["induced_metric_equivariant"],
            "tau_Z2^* h_ab = h_ab",
        )
        self.assertEqual(
            payload["geometry_condition"]["extrinsic_curvature_reversal"],
            "tau_Z2^* K_ab = -K_ab",
        )
        self.assertTrue(payload["trace_targets"]["R_h_trace_required"])
        self.assertTrue(payload["trace_targets"]["R_K_trace_required"])
        self.assertFalse(payload["trace_targets"]["R_h_trace_derived"])
        self.assertFalse(payload["trace_targets"]["R_K_trace_derived"])
        self.assertFalse(payload["gate_passed"])
        self.assertIn("do_not_fit_c1_c2_c3", payload["forbidden_shortcuts"])


if __name__ == "__main__":
    unittest.main()
