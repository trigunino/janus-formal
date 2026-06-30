from __future__ import annotations

import unittest

from scripts.build_p0_eft_kink_lensing_growth_bridge import build_payload, render_markdown


class P0EFTKinkLensingGrowthBridgeTests(unittest.TestCase):
    def test_kink_ready_value_not_ready_growth_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["lensing_kink_ready_conditionally"])
        self.assertFalse(status["lensing_value_ready"])
        self.assertTrue(status["growth_equation_target_encoded"])
        self.assertFalse(status["growth_solver_implemented"])
        self.assertFalse(status["full_cosmology_prediction_ready"])

    def test_lensing_does_not_use_value_slip(self) -> None:
        lensing = build_payload()["lensing"]

        self.assertIn("not used", lensing["value_slip"])
        self.assertIn("refraction", lensing["photon_effect"])

    def test_growth_obligations_name_no_fit(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("S_kink", obligations)
        self.assertIn("no-fit", obligations)

    def test_markdown_keeps_full_ready_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("lensing_kink_ready_conditionally: True", markdown)
        self.assertIn("full_cosmology_prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
