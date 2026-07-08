import unittest

from scripts.build_p0_eft_the_janus_cosmological_model_2024_reference_gate import (
    build_payload,
)


class Janus2024ReferenceGateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = build_payload()

    def test_reference_is_materialized(self):
        payload = self.payload
        self.assertEqual(
            payload["status"], "the-janus-cosmological-model-2024-reference-gate"
        )
        self.assertTrue(payload["the_janus_cosmological_model_2024_reference_recreated"])
        self.assertTrue(payload["published_bulk_bimetric_equations_present"])
        self.assertTrue(payload["active_two_metric_flrw_reference_object_present"])
        self.assertTrue(payload["active_k_equals_kbar_equals_minus_one_branch_present"])
        self.assertTrue(payload["published_k_equals_kbar_equals_minus_one_branch_present"])
        self.assertTrue(payload["active_global_energy_equation_present"])
        self.assertTrue(payload["active_sector_density_law_present"])
        self.assertTrue(payload["active_two_metric_rhs_present"])
        self.assertTrue(payload["paper_native_observational_anchors_present"])
        self.assertFalse(payload["published_cited_exact_shape_present"])
        self.assertFalse(payload["paper_native_plus_history_present"])
        self.assertFalse(payload["paper_published_observation_reference_present"])
        self.assertFalse(payload["active_bulk_observable_path_present"])
        self.assertFalse(payload["active_absolute_normalization_contract_present"])
        self.assertFalse(payload["published_absolute_density_normalization_present"])
        self.assertEqual(
            payload["published_absolute_density_normalization_kind"],
            "missing",
        )

    def test_reference_keeps_proxy_distinction(self):
        payload = self.payload
        self.assertTrue(payload["paper_structured_reference_ready"])
        self.assertTrue(payload["paper_only_branch_ready"])
        self.assertTrue(payload["paper_plus_cited_comparison_branch_ready"])
        self.assertFalse(payload["like_for_like_with_paper"])
        self.assertFalse(payload["paper_like_for_like_reference_ready"])
        self.assertTrue(payload["paper_explicit_only_reference_ready"])
        self.assertFalse(payload["strict_paper_only_reference_ready"])
        self.assertTrue(payload["repo_implicit_closure_forbidden"])
        self.assertTrue(payload["paper_cited_helper_objects_present"])
        self.assertFalse(payload["paper_cited_helper_objects_active"])
        self.assertEqual(
            payload["active_background_reference_path_kind"],
            "paper_equations_and_anchors_only",
        )
        self.assertFalse(payload["active_background_reference_path_is_full_published_bulk"])
        self.assertEqual(payload["missing_for_like_for_like"], [])
        self.assertIn(
            "published_bulk_bimetric_equations",
            payload["paper_explicitly_fixed_objects"],
        )
        self.assertIn(
            "absolute_density_normalization",
            payload["paper_underdetermined_objects"],
        )
        self.assertIn(
            "published_cited_exact_shape_proxy_q0_u0",
            payload["paper_cited_but_not_explicit_objects"],
        )
        self.assertTrue(payload["manifest"]["branch_classes"]["paper_only"]["active"])
        self.assertFalse(
            payload["manifest"]["branch_classes"]["paper_plus_cited_comparison"]["active"]
        )
        self.assertIn(
            "paper_native_absolute_density_normalization_not_materialized",
            payload["missing_for_strict_paper_only"],
        )
        self.assertIn(
            "paper_native_two_metric_background_history_not_materialized",
            payload["missing_for_strict_paper_only"],
        )

    def test_reference_flags_remaining_cleanup(self):
        payload = self.payload
        self.assertEqual(payload["repo_added_closures"], [])
        self.assertIn(
            "published_cited_observational_calibration",
            payload["excluded_repo_helpers"],
        )
        self.assertFalse(payload["the_janus_cosmological_model_2024_branch_frozen"])
        self.assertTrue(payload["active_bulk_completion_required"])
        self.assertFalse(payload["active_bulk_observational_run_executed"])


if __name__ == "__main__":
    unittest.main()
