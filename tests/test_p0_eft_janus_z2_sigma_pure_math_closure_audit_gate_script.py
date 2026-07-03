import unittest

from scripts.build_p0_eft_janus_z2_sigma_pure_math_closure_audit_gate import build_payload


class P0EFTJanusZ2SigmaPureMathClosureAuditGateTests(unittest.TestCase):
    def test_active_core_is_z2_sigma_and_hard_locks_block_no_fit(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(
            payload["hard_theorem_target_registry"],
            "p0_eft_janus_z2_sigma_hard_theorem_target_registry",
        )
        self.assertTrue(payload["z2_tunnel_core_closed"])
        self.assertTrue(payload["legacy_z4_archived"])
        self.assertTrue(payload["hard_locks"]["rp4_pin_sign_computed"])
        self.assertTrue(payload["hard_locks"]["sigma_aps_pin_lift_obligations_declared"])
        self.assertTrue(payload["hard_locks"]["sigma_aps_local_throat_model_closed"])
        self.assertTrue(payload["hard_locks"]["sigma_eta_zero_mode_cancellation_closed"])
        self.assertTrue(payload["hard_locks"]["sigma_parity_anomaly_cancellation_closed"])
        self.assertTrue(payload["hard_locks"]["sigma_aps_trace_regularization_closed"])
        self.assertTrue(payload["hard_locks"]["sigma_aps_pin_lift_closed"])
        self.assertTrue(payload["hard_locks"]["around_sigma_z2_transport_closed"])
        self.assertTrue(payload["hard_locks"]["projective_cover_survives_tunnel_surgery"])
        self.assertTrue(payload["hard_locks"]["projective_tunnel_ratio_closed"])
        self.assertTrue(payload["hard_locks"]["sigma_boundary_support_declared"])
        self.assertTrue(payload["hard_locks"]["sigma_boundary_variational_package_declared"])
        self.assertTrue(payload["hard_locks"]["sigma_boundary_nonlinear_residual_closed"])
        self.assertTrue(payload["hard_locks"]["sigma_boundary_action_closed"])
        self.assertTrue(payload["z2_sigma_model_closed_without_axioms"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])
        self.assertTrue(payload["observational_validation_required_for_full_cosmology"])
        self.assertEqual(payload["next_required"], [])


if __name__ == "__main__":
    unittest.main()
