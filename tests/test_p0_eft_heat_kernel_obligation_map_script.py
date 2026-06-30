from __future__ import annotations

import unittest

from scripts.build_p0_eft_heat_kernel_obligation_map import build_payload, render_markdown


class P0EFTHeatKernelObligationMapTests(unittest.TestCase):
    def test_heat_kernel_derivation_is_not_done(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["obligation_map_written"])
        self.assertFalse(status["heat_kernel_operator_specified"])
        self.assertFalse(status["seeley_dewitt_coefficients_computed"])
        self.assertFalse(status["double_dual_generated"])
        self.assertFalse(status["prediction_ready"])

    def test_required_inputs_are_explicit(self) -> None:
        inputs = {row["id"]: row for row in build_payload()["required_inputs"]}

        self.assertFalse(inputs["HK1"]["available_now"])
        self.assertFalse(inputs["HK2"]["available_now"])
        self.assertFalse(inputs["HK3"]["available_now"])
        self.assertFalse(inputs["HK4"]["available_now"])
        self.assertTrue(inputs["HK5"]["available_now"])

    def test_chain_mentions_projection_and_matching(self) -> None:
        chain = " ".join(build_payload()["heat_kernel_chain"])

        self.assertIn("heat-kernel expansion", chain)
        self.assertIn("Horndeski/double-dual", chain)
        self.assertIn("dS contact closure", chain)

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("prediction_ready: False", markdown)
        self.assertIn("bulk field spectrum", markdown)


if __name__ == "__main__":
    unittest.main()
