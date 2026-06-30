from __future__ import annotations

import unittest

from scripts.build_p0_eft_run10b_orbifold_flux_integer_theorem import build_payload, render_markdown


class P0EFTRun10BOrbifoldFluxIntegerTheoremTests(unittest.TestCase):
    def test_run10b_interface_ready(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run10b_flux_integer_interface_ready"])
        self.assertTrue(status["integer_flux_to_branch_indices_arrow_formalized"])
        self.assertTrue(status["run10b_orientation_rule_interface_ready"])
        self.assertTrue(status["orientation_to_branch_selection_arrow_formalized"])
        self.assertTrue(status["run10b_flux_quantization_law_interface_ready"])
        self.assertTrue(status["quantization_law_to_integer_flux_arrow_formalized"])

    def test_integer_flux_and_orientation_are_closed(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["integer_flux_law_proved"])
        self.assertTrue(status["janus_orientation_rule_proved"])
        self.assertTrue(status["orbifold_global_theorem_proved"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_integer_flux(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("P0EFTOrbifoldFluxIntegerTheorem", markdown)
        self.assertIn("P0EFTOrbifoldFluxOrientationRule", markdown)
        self.assertIn("P0EFTOrbifoldFluxQuantizationLaw", markdown)
        self.assertIn("P0EFTOrbifoldIntegerFluxLaw", markdown)
        self.assertIn("P0EFTOrbifoldJanusOrientationRule", markdown)
        self.assertIn("branchIndicesComputed", markdown)


if __name__ == "__main__":
    unittest.main()
