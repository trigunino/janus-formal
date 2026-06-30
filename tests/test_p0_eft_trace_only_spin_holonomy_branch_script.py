from __future__ import annotations

import unittest

from scripts.build_p0_eft_trace_only_spin_holonomy_branch import build_payload, render_markdown


class P0EFTTraceOnlySpinHolonomyBranchTests(unittest.TestCase):
    def test_trace_only_is_first_but_not_expected_sufficient(self) -> None:
        payload = build_payload()
        status = payload["theorem_status"]

        self.assertTrue(status["trace_only_branch_ready_to_test"])
        self.assertFalse(status["trace_only_expected_sufficient"])
        self.assertFalse(payload["trace_only_branch"]["predicted_to_close_required_deltaN"])
        self.assertFalse(status["prediction_ready"])

    def test_spin_holonomy_contingency_fixes_axial_conditionally(self) -> None:
        payload = build_payload()
        branch = payload["spin_holonomy_branch"]

        self.assertEqual(branch["condition"], "q_T = 1, q_A = sign(Sigma)/sqrt(6)")
        self.assertTrue(payload["theorem_status"]["q_A_fixed_conditionally"])
        self.assertFalse(payload["theorem_status"]["pt_spin_holonomy_proved"])

    def test_not_sourced_from_published_janus_yet(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["spin_holonomy_branch"]["source_derived_from_published_janus"])
        self.assertFalse(payload["theorem_status"]["heat_kernel_computed"])

    def test_markdown_names_branch_order(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("test trace torsion first", markdown)
        self.assertIn("q_A=sign(Sigma)/sqrt(6)", markdown)


if __name__ == "__main__":
    unittest.main()
