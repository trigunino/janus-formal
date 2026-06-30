from __future__ import annotations

import unittest

from scripts.build_p0_eft_cosmology_conditional_bridge import build_payload, render_markdown


class P0EFTCosmologyConditionalBridgeTests(unittest.TestCase):
    def test_boundary_ready_does_not_mean_full_cosmology_ready(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["boundary_sector_conditionally_ready"])
        self.assertTrue(status["can_feed_ds_perturbation_pipeline"])
        self.assertFalse(status["full_cosmology_prediction_ready"])
        self.assertFalse(status["matter_vlasov_closed"])
        self.assertFalse(status["prediction_ready_unconditional"])

    def test_observables_remain_downstream(self) -> None:
        bridge = build_payload()["cosmology_bridge"]

        self.assertIn("remain downstream", bridge["observables"])
        self.assertIn("not closed", bridge["vlasov_matter_sector"])

    def test_obligations_include_ds_and_matter(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("dS scalar/tensor", obligations)
        self.assertIn("matter/Vlasov", obligations)

    def test_markdown_keeps_full_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("full_cosmology_prediction_ready: False", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
