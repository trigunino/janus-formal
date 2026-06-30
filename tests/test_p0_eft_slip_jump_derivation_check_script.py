from __future__ import annotations

import unittest

from scripts.build_p0_eft_slip_jump_derivation_check import build_payload, render_markdown


class P0EFTSlipJumpDerivationCheckTests(unittest.TestCase):
    def test_derivative_slip_closed_but_value_slip_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["perturbed_jump_structure_encoded"])
        self.assertTrue(status["stf_anisotropic_source_identified"])
        self.assertTrue(status["derivative_jump_slip_source_closed"])
        self.assertFalse(status["algebraic_value_slip_derived"])
        self.assertTrue(status["requires_boundary_green_function_or_normal_mode"])

    def test_target_is_not_claimed_directly(self) -> None:
        target = build_payload()["target"]

        self.assertFalse(target["derived_directly"])
        self.assertIn("normal-mode", target["reason"])

    def test_obligations_name_green_function(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("Green function", obligations)
        self.assertIn("lensing potential", obligations)

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("algebraic_value_slip_derived: False", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
