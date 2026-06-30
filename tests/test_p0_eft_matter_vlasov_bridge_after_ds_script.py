from __future__ import annotations

import unittest

from scripts.build_p0_eft_matter_vlasov_bridge_after_ds import build_payload, render_markdown


class P0EFTMatterVlasovBridgeAfterDSTests(unittest.TestCase):
    def test_matter_bridge_is_defined_but_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["ds_boundary_inputs_available"])
        self.assertTrue(status["matter_bridge_defined"])
        self.assertFalse(status["vlasov_equation_derived"])
        self.assertFalse(status["phase_space_measure_closed"])
        self.assertFalse(status["prediction_ready_unconditional"])

    def test_bridge_names_distribution_and_moments(self) -> None:
        bridge = build_payload()["matter_bridge"]

        self.assertIn("f_plus", bridge["required_distribution"])
        self.assertIn("rho, pressure, Pi", bridge["closure_target"])

    def test_obligations_target_transport_and_lensing(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("phase-space measure", obligations)
        self.assertIn("lensing/growth", obligations)

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("matter-vlasov-open", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
