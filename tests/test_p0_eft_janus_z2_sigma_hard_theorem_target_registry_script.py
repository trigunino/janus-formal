import unittest

from scripts.build_p0_eft_janus_z2_sigma_hard_theorem_target_registry import build_payload


class P0EFTJanusZ2SigmaHardTheoremTargetRegistryTests(unittest.TestCase):
    def test_registry_targets_active_z2_sigma_locks(self):
        payload = build_payload()

        self.assertTrue(payload["registry_complete"])
        self.assertTrue(payload["all_hard_targets_closed"])
        self.assertIn("rp4_tunnel_pin_sign", payload["targets"])
        self.assertIn("projective_tunnel_cover_ratio_2_to_1", payload["targets"])
        self.assertIn("sigma_boundary_action", payload["targets"])
        self.assertTrue(payload["targets"]["rp4_tunnel_pin_sign"]["rp4_base_pin_sign_computed"])
        self.assertTrue(payload["targets"]["rp4_tunnel_pin_sign"]["rp4_base_pin_plus_exists"])
        self.assertFalse(payload["targets"]["rp4_tunnel_pin_sign"]["rp4_base_pin_minus_exists"])
        self.assertTrue(
            payload["targets"]["rp4_tunnel_pin_sign"]["sigma_aps_pin_lift_obligations_declared"]
        )
        self.assertTrue(
            payload["targets"]["rp4_tunnel_pin_sign"]["sigma_aps_local_throat_model_closed"]
        )
        self.assertTrue(
            payload["targets"]["rp4_tunnel_pin_sign"]["sigma_eta_zero_mode_cancellation_closed"]
        )
        self.assertTrue(
            payload["targets"]["rp4_tunnel_pin_sign"]["sigma_parity_anomaly_cancellation_closed"]
        )
        self.assertTrue(
            payload["targets"]["rp4_tunnel_pin_sign"]["sigma_aps_trace_regularization_closed"]
        )
        self.assertTrue(
            payload["targets"]["rp4_tunnel_pin_sign"]["sigma_aps_boundary_pin_lift_closed"]
        )
        self.assertNotIn(
            "eta_zero_mode_cancellation_global",
            payload["targets"]["rp4_tunnel_pin_sign"]["accepted_import_must_prove"],
        )
        self.assertNotIn(
            "parity_anomaly_cancellation_global",
            payload["targets"]["rp4_tunnel_pin_sign"]["accepted_import_must_prove"],
        )
        self.assertTrue(payload["targets"]["rp4_tunnel_pin_sign"]["closed"])
        self.assertTrue(
            payload["targets"]["projective_tunnel_cover_ratio_2_to_1"][
                "two_fold_cover_survives_tunnel_surgery"
            ]
        )
        self.assertTrue(
            payload["targets"]["projective_tunnel_cover_ratio_2_to_1"][
                "around_sigma_z2_transport_closed"
            ]
        )
        self.assertTrue(
            payload["targets"]["projective_tunnel_cover_ratio_2_to_1"][
                "cover_to_quotient_volume_ratio_two"
            ]
        )
        self.assertTrue(
            payload["targets"]["projective_tunnel_cover_ratio_2_to_1"][
                "ratio_unique_by_cover_degree"
            ]
        )
        self.assertFalse(
            payload["targets"]["projective_tunnel_cover_ratio_2_to_1"][
                "phenomenological_sheet_split_inferred"
            ]
        )
        self.assertTrue(
            payload["targets"]["projective_tunnel_cover_ratio_2_to_1"]["closed"]
        )
        self.assertTrue(payload["targets"]["sigma_boundary_action"]["sigma_boundary_support_declared"])
        self.assertTrue(
            payload["targets"]["sigma_boundary_action"]["antipodal_fixed_point_boundary_forbidden"]
        )
        self.assertTrue(
            payload["targets"]["sigma_boundary_action"][
                "sigma_boundary_variational_package_declared"
            ]
        )
        self.assertTrue(
            payload["targets"]["sigma_boundary_action"][
                "nonlinear_residual_obstruction_isolated"
            ]
        )
        self.assertTrue(payload["targets"]["sigma_boundary_action"]["sigma_supported_counterterm_unique"])
        self.assertTrue(
            payload["targets"]["sigma_boundary_action"]["counterterm_variation_cancels_residual"]
        )
        self.assertTrue(
            payload["targets"]["sigma_boundary_action"]["sigma_boundary_nonlinear_residual_closed"]
        )
        self.assertTrue(payload["targets"]["sigma_boundary_action"]["closed"])
        self.assertTrue(payload["z2_sigma_hard_targets_closed"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])
        self.assertTrue(payload["observational_validation_required_for_full_cosmology"])


if __name__ == "__main__":
    unittest.main()
