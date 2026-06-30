from __future__ import annotations

import unittest

from scripts.build_p0_eft_boundary_nieh_yan_counterterm_check import build_payload, render_markdown


class P0EFTBoundaryNiehYanCountertermCheckTests(unittest.TestCase):
    def test_single_nieh_yan_is_insufficient(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["nieh_yan_counterterm_tested"])
        self.assertTrue(status["nieh_yan_cancels_m_C_with_kappa"])
        self.assertFalse(status["nieh_yan_cancels_m_I"])
        self.assertFalse(status["nieh_yan_generates_required_m_G"])
        self.assertFalse(status["single_nieh_yan_term_closes_run1"])
        self.assertFalse(status["prediction_ready"])

    def test_kappa_solution_only_cancels_c_residue(self) -> None:
        ny = build_payload()["nieh_yan"]

        self.assertEqual(ny["solution_for_m_C"], "kappa = 2*q_A*Delta_chi")
        self.assertIn("m_I remains", ny["remaining_failure"])
        self.assertIn("m_G remains 0", ny["remaining_failure"])

    def test_obligations_name_remaining_sources(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("identity residue", obligations)
        self.assertIn("produces m_G", obligations)

    def test_markdown_records_insufficient_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("single_nieh_yan_counterterm_insufficient", markdown.replace("-", "_"))
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
