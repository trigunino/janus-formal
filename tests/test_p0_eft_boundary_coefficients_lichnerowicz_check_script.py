from __future__ import annotations

import unittest

from scripts.build_p0_eft_boundary_coefficients_lichnerowicz_check import build_payload, render_markdown


class P0EFTBoundaryCoefficientsLichnerowiczCheckTests(unittest.TestCase):
    def test_run1_coefficients_remain_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run1_physical_slots_defined"])
        self.assertTrue(status["run1_matching_equation_ready"])
        self.assertTrue(status["run1_literal_candidate_evaluated"])
        self.assertFalse(status["run1_literal_candidate_matches"])
        self.assertTrue(status["run1_requires_extra_derived_boundary_cancellation"])
        self.assertFalse(status["run1_matching_proved_from_janus_coefficients"])
        self.assertFalse(status["prediction_ready"])

    def test_literal_candidate_has_forbidden_residues(self) -> None:
        candidate = build_payload()["candidate_run1"]

        self.assertEqual(candidate["coefficients_without_common_i"]["m_I"], "4*q_T*Delta_chi")
        self.assertEqual(candidate["coefficients_without_common_i"]["m_G"], "0")
        self.assertEqual(candidate["coefficients_without_common_i"]["m_C"], "-2*q_A*Delta_chi")
        self.assertIn("fails RUN 1", candidate["literal_verdict"])

    def test_run2_zero_modes_close_only_for_riemannian_aps_boundary(self) -> None:
        payload = build_payload()
        status = payload["theorem_status"]

        self.assertTrue(status["run2_lichnerowicz_zero_mode_argument_encoded"])
        self.assertTrue(status["run2_zero_modes_absent_on_riemannian_compact_boundary"])
        self.assertFalse(status["run2_lorentzian_dS3_spectrum_defined"])
        self.assertIn("Riemannian compact", payload["run2"]["aps_boundary_type"])

    def test_obligations_keep_exact_ratio_as_remaining_work(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("m_I trace residue", obligations)
        self.assertIn("m_C residue", obligations)
        self.assertIn("m_G=sigma*eps_n*m_N", obligations)
        self.assertIn("Riemannian APS boundary", obligations)

    def test_markdown_keeps_ready_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("run1_literal_candidate_matches: False", markdown)
        self.assertIn("run1_matching_proved_from_janus_coefficients: False", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
