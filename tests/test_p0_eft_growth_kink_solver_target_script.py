from __future__ import annotations

import unittest

from scripts.build_p0_eft_growth_kink_solver_target import build_payload, render_markdown


class P0EFTGrowthKinkSolverTargetTests(unittest.TestCase):
    def test_growth_jump_system_encoded_but_solver_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["growth_state_defined"])
        self.assertTrue(status["kink_jump_condition_encoded"])
        self.assertTrue(status["delta_continuity_encoded"])
        self.assertTrue(status["geff_ansatz_marked_unproved"])
        self.assertFalse(status["growth_solver_implemented"])
        self.assertFalse(status["fsigma8_prediction_ready"])

    def test_delta_continuity_and_derivative_jump_are_explicit(self) -> None:
        system = build_payload()["growth_system"]

        self.assertIn("delta_+=delta_-", system["jump_condition"])
        self.assertIn("growth velocity jumps", system["non_singularity"])

    def test_geff_candidate_is_not_claimed(self) -> None:
        geff = build_payload()["geff"]

        self.assertIn("target-to-derive", geff["safe_status"])
        self.assertIn("candidate", " ".join(geff.keys()))

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("growth_solver_implemented: False", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
