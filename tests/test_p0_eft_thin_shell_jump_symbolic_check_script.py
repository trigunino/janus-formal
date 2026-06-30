from __future__ import annotations

import unittest

from scripts.build_p0_eft_thin_shell_jump_symbolic_check import build_payload, render_markdown


class P0EFTThinShellJumpSymbolicCheckTests(unittest.TestCase):
    def test_jump_condition_is_derived_but_projector_is_not(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["thin_shell_delta_integrated"])
        self.assertTrue(status["spinor_jump_condition_derived"])
        self.assertFalse(status["chiral_projector_derived_from_trace_torsion_alone"])
        self.assertTrue(status["requires_axial_or_boundary_clifford_factor"])
        self.assertFalse(status["prediction_ready"])

    def test_report_identifies_missing_clifford_factor(self) -> None:
        payload = build_payload()

        self.assertIn("gamma^n gamma5", payload["algebraic_check"]["missing_condition"])
        self.assertIn("M_T", " ".join(payload["obligations"]))

    def test_markdown_records_no_forced_projector(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("trace torsion alone gives a jump matrix", markdown)
        self.assertIn("not yet force the chiral projector", markdown)


if __name__ == "__main__":
    unittest.main()
