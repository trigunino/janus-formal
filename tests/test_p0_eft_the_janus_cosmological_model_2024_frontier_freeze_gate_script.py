import unittest

from scripts.build_p0_eft_the_janus_cosmological_model_2024_frontier_freeze_gate import (
    build_payload,
)


class Janus2024FrontierFreezeGateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = build_payload()

    def test_frontier_is_explicitly_frozen(self):
        payload = self.payload
        self.assertEqual(
            payload["status"],
            "the-janus-cosmological-model-2024-frontier-freeze-gate",
        )
        self.assertTrue(payload["the_janus_cosmological_model_2024_frontier_branch_frozen"])
        self.assertTrue(payload["current_source_set_exploration_exhausted"])
        self.assertFalse(payload["full_prediction_closed_with_current_source_set"])
        self.assertTrue(payload["no_more_progress_without_enlarging_allowed_source_set"])
        self.assertTrue(
            payload["current_branch_verdict"][
                "observational_closure_requires_new_theoretical_input"
            ]
        )
        self.assertEqual(
            payload["current_branch_verdict"]["acceptable_next_move"],
            "start_new_branch_with_enlarged_theoretical_source_set",
        )

    def test_freeze_keeps_frontier_blockers_visible(self):
        payload = self.payload
        summary = payload["source_boundary_summary"]
        self.assertTrue(summary["step1_sn_pipeline_reached_boundary"])
        self.assertFalse(summary["step2_strict_paper_only_closed"])
        self.assertFalse(summary["step3_strict_paper_only_closed"])
        self.assertFalse(summary["step4_native_bao_ruler_closed"])
        self.assertFalse(summary["step5_absolute_background_input_ready"])
        self.assertFalse(summary["step6_native_cmb_opened"])


if __name__ == "__main__":
    unittest.main()
