from __future__ import annotations

import unittest

from scripts.build_p0_eft_b4vol_solder_derivation import build_payload, render_markdown


class P0EFTB4volSolderDerivationTests(unittest.TestCase):
    def test_b4vol_is_derived_but_measure_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["b4vol_derived_from_tetrad_soldering"])
        self.assertTrue(status["b4vol_linked_to_lambda_logdet"])
        self.assertTrue(status["mass_shell_lapse_factor_identified"])
        self.assertFalse(status["mass_shell_lapse_factor_closed"])
        self.assertFalse(status["active_source_measure_closed"])

    def test_solder_formula_contains_determinant_ratio(self) -> None:
        solder = build_payload()["solder"]

        self.assertIn("det(E_other_to_self)/det(E_self)", solder["b4vol"])
        self.assertIn("log B4vol", solder["log_link"])

    def test_obligations_include_det_l_and_lapse(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("det(L_solder)", obligations)
        self.assertIn("p^0/lapse", obligations)

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("mass_shell_lapse_factor_closed: False", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
