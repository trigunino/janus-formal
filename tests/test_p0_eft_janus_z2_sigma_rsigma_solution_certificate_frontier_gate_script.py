import unittest
import tempfile
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_rsigma_solution_certificate_frontier_gate import (
    build_payload,
)


class RSigmaCertificateFrontierGateTests(unittest.TestCase):
    def test_frontier_blocks_finite_certificate_without_counterterm(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            holst = root / "holst.json"
            matter = root / "matter.json"
            holst.write_text(
                Path("outputs/active_z2_sigma/rsigma_E_HolstNiehYan.json").read_text(
                    encoding="utf-8"
                ),
                encoding="utf-8",
            )
            matter.write_text(
                Path("outputs/active_z2_sigma/rsigma_E_matterFlux.json").read_text(
                    encoding="utf-8"
                ),
                encoding="utf-8",
            )
            payload = build_payload(
                term_paths={
                    "E_HolstNiehYan": holst,
                    "E_matterFlux": matter,
                    "E_counterterm": root / "missing_counterterm.json",
                }
            )

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["known_noncartan_without_counterterm_zero"])
        self.assertFalse(payload["counterterm_radial_term_available"])
        self.assertTrue(payload["cartan_ghy_symbolic_R_block_ready"])
        self.assertFalse(payload["cartan_ghy_numeric_of_a_ready"])
        self.assertEqual(
            payload["cartan_ghy_symbolic_R_block"]["E_CartanGHY_of_R"],
            "6 eps_Z2 sqrt(det(q)) R_Sigma / kappa_Z2Sigma",
        )
        self.assertFalse(payload["finite_RSigma_certificate_currently_possible"])
        self.assertEqual(payload["primary_blocker"], "counterterm_trace_residual_inputs_R_h_R_K")
        self.assertTrue(
            payload["remaining_non_GHY_counterterm_channels"]["metric_non_GHY_trace_R_h"]
        )
        self.assertTrue(
            payload["remaining_non_GHY_counterterm_channels"]["extrinsic_non_GHY_trace_R_K"]
        )
        self.assertEqual(
            payload["open_remaining_non_GHY_counterterm_channels"],
            ["metric_non_GHY_trace_R_h", "extrinsic_non_GHY_trace_R_K"],
        )
        self.assertFalse(payload["active_first_action"]["assembled"])
        self.assertEqual(
            payload["active_first_action"]["primary_blocker"],
            "cross_action_source_accepted",
        )
        self.assertFalse(payload["active_first_action"]["S_cross_source_accepted"])
        self.assertIn(
            "use_symbolic_E_CartanGHY_of_R_in_E_RSigma_before_solving_R_Sigma_of_a",
            payload["next_required"],
        )
        self.assertIn(
            "derive_or_eliminate_metric_non_GHY_trace_R_h",
            payload["next_required"],
        )
        self.assertIn(
            "run_counterterm_minimal_basis_coefficient_solver_gate",
            payload["next_required"],
        )
        self.assertTrue(payload["post_radius_embedding_manifest_route"]["prepared"])
        self.assertEqual(
            payload["post_radius_embedding_manifest_route"]["unblocked_only_by"],
            "active_no_fit_R_Sigma_solution_certificate",
        )
        self.assertTrue(
            payload["post_radius_embedding_manifest_route"][
                "does_not_close_S_cross_or_Bianchi"
            ]
        )
        self.assertIn(
            "then_run_rsigma_solution_to_embedding_curvature_branch_gate",
            payload["next_required"],
        )
        self.assertIn(
            "keep_S_cross_blocker_separate_from_RSigma_counterterm_trace_blocker",
            payload["next_required"],
        )
        self.assertIn("do_not_use_toy_exact_model_as_certificate", payload["forbidden_shortcuts"])


if __name__ == "__main__":
    unittest.main()
