from __future__ import annotations

import unittest

from scripts.build_p0_eft_trace_only_structure_test import build_payload, render_markdown


class P0EFTTraceOnlyStructureTestTests(unittest.TestCase):
    def test_trace_only_does_not_generate_double_dual(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["trace_only_structure_test_done"])
        self.assertTrue(status["trace_only_generates_basic_curvature_radion_terms"])
        self.assertFalse(status["trace_only_generates_double_dual"])
        self.assertFalse(status["trace_only_closes_k4"])
        self.assertFalse(status["prediction_ready"])

    def test_axial_and_dual_sectors_absent(self) -> None:
        structures = build_payload()["generated_structures"]

        self.assertFalse(structures["axial_torsion_sector"])
        self.assertFalse(structures["epsilon_dual_curvature_sector"])
        self.assertFalse(structures["double_dual_horndeski_complete"])

    def test_spin_holonomy_named_as_next_need(self) -> None:
        missing = " ".join(build_payload()["missing_for_closure"])

        self.assertIn("spin-holonomy", missing)
        self.assertIn("chiral/axial", missing)

    def test_markdown_keeps_trace_insufficient(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("trace_only_generates_double_dual: False", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
