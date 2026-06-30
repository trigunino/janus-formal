from __future__ import annotations

import unittest

from scripts.build_p0_eft_thin_shell_tetrad_chirality_target import build_payload, render_markdown


class P0EFTThinShellTetradChiralityTargetTests(unittest.TestCase):
    def test_tetrad_sign_is_target_not_claimed(self) -> None:
        payload = build_payload()
        status = payload["theorem_status"]

        self.assertTrue(status["orbifold_solder_form_identified"])
        self.assertTrue(status["normal_reversal_mechanism_identified"])
        self.assertFalse(status["tetrad_sign_transition_derived"])
        self.assertEqual(payload["tetrad_transition"]["target"], "PT(E_plus^0)|_Sigma = -E_minus^0")

    def test_thin_shell_chirality_is_target_not_claimed(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["trace_torsion_shell_identified"])
        self.assertTrue(status["thin_shell_integration_specified"])
        self.assertFalse(status["spinor_jump_condition_derived"])
        self.assertFalse(status["chiral_boundary_projector_derived"])
        self.assertFalse(status["chiral_projector_equals_aps_domain"])
        self.assertFalse(status["prediction_ready"])

    def test_obligations_are_calculational(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("delta coefficient", obligations)
        self.assertIn("integrate the Dirac-Cartan equation", obligations)
        self.assertIn("equivalent to the required boundary chirality", obligations)

    def test_markdown_names_no_hand_boundary_projector(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("without choosing a boundary projector by hand", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
