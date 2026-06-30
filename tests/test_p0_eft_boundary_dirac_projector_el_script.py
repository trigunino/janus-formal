from __future__ import annotations

import unittest

from scripts.build_p0_eft_boundary_dirac_projector_el import build_payload, render_markdown


class P0EFTBoundaryDiracProjectorELTests(unittest.TestCase):
    def test_boundary_el_route_is_conditionally_encoded(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["boundary_dirac_term_identified"])
        self.assertTrue(status["bulk_surface_variation_identified"])
        self.assertTrue(status["boundary_el_route_encoded"])
        self.assertTrue(status["cayley_no_go_preserved"])
        self.assertTrue(status["projector_from_boundary_el_conditionally"])
        self.assertFalse(status["janus_coefficients_make_factorization_proved"])
        self.assertFalse(status["prediction_ready"])

    def test_projector_derivation_uses_boundary_equation_not_cayley(self) -> None:
        derivation = build_payload()["projector_derivation"]

        self.assertIn("gamma^n", derivation["boundary_equation_form"])
        self.assertIn("P_chiral", derivation["projector"])
        self.assertIn("boundary EL constraints", derivation["cayley_relation"])

    def test_remaining_work_is_coefficient_factorization_and_aps(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("factor as gamma^n", obligations)
        self.assertIn("APS domain", obligations)

    def test_markdown_keeps_ready_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("janus_coefficients_make_factorization_proved: False", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
