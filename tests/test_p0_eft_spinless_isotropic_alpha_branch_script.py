from __future__ import annotations

import unittest

from scripts.build_p0_eft_spinless_isotropic_alpha_branch import build_payload, render_markdown


class P0EFTSpinlessIsotropicAlphaBranchTests(unittest.TestCase):
    def test_isotropic_branch_is_conditional_and_partial(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["isotropic_spinless_branch_defined"])
        self.assertTrue(status["pi_zero_conditionally"])
        self.assertTrue(status["contorsion_combination_computed"])
        self.assertFalse(status["torsion_energy_normalization_derived"])
        self.assertFalse(status["alpha_iso_fully_derived"])
        self.assertFalse(status["prediction_ready_unconditional"])

    def test_pin_values_give_seven_sixths(self) -> None:
        alpha = build_payload()["alpha"]

        self.assertIn("7/6", alpha["with_pin_values"])
        self.assertIn("(7/6)*Omega_torsion", alpha["result"])

    def test_general_branch_remains_open(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["theorem_status"]["general_anisotropic_branch_closed"])
        self.assertIn("not general", payload["assumptions"]["validity"])

    def test_markdown_keeps_ready_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("alpha_iso_fully_derived: False", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
