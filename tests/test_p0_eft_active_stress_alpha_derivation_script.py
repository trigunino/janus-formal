from __future__ import annotations

import unittest

from scripts.build_p0_eft_active_stress_alpha_derivation import build_payload, render_markdown


class P0EFTActiveStressAlphaDerivationTests(unittest.TestCase):
    def test_alpha_is_defined_but_not_derived(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["active_stress_definition_encoded"])
        self.assertTrue(status["contorsion_quadratic_source_identified"])
        self.assertTrue(status["alpha_definition_encoded"])
        self.assertFalse(status["contorsion_contractions_computed"])
        self.assertFalse(status["pi_moment_closed"])
        self.assertFalse(status["alpha_Janus_derived"])

    def test_mu_form_uses_meff_gap(self) -> None:
        alpha = build_payload()["alpha"]

        self.assertIn("3H(a)^2/2", alpha["mu_form"])
        self.assertIn("rho_crit", alpha["definition"])

    def test_obligations_include_pi_or_isotropy_branch(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("contorsion contractions", obligations)
        self.assertIn("Pi", obligations)
        self.assertIn("isotropy", obligations)

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("alpha_Janus_derived: False", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
