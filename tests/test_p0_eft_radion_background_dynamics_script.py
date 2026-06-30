from __future__ import annotations

import unittest

from scripts.build_p0_eft_radion_background_dynamics import build_payload, render_markdown


class P0EFTRadionBackgroundDynamicsTests(unittest.TestCase):
    def test_radion_kg_structured_but_sources_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["radion_KG_structure_encoded"])
        self.assertTrue(status["Omega_T_extraction_encoded"])
        self.assertFalse(status["potential_V_fixed_from_Janus_action"])
        self.assertFalse(status["spinor_boundary_source_fixed"])
        self.assertFalse(status["Omega_T_no_fit_ready"])

    def test_omega_extraction_is_from_chi_x(self) -> None:
        equation = build_payload()["equation"]

        self.assertIn("chi_x^2", equation["torsion_density"])
        self.assertIn("chi_xx", equation["kg_x_form"])

    def test_obligations_require_same_action_sources(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("V(chi)", obligations)
        self.assertIn("RUN 1 boundary terms", obligations)

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Omega_T_no_fit_ready: False", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
