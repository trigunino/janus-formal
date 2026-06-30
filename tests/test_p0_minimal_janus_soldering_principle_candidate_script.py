from __future__ import annotations

import unittest

from scripts.build_p0_minimal_janus_soldering_principle_candidate import (
    build_payload,
    render_markdown,
)


class P0MinimalJanusSolderingPrincipleCandidateTests(unittest.TestCase):
    def test_candidate_is_explicitly_not_closed(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "new-principle-candidate-not-source-derived")
        self.assertTrue(payload["new_axiom_candidate"])
        self.assertFalse(payload["source_derived"])
        self.assertTrue(payload["zero_rustine_if_source_derived"])
        self.assertFalse(payload["prediction_ready"])

    def test_equations_define_phi_l_omega_and_b4vol(self) -> None:
        equations = " ".join(build_payload()["candidate_equations"])

        self.assertIn("phi_plus_to_minus(phi_minus_to_plus(x))=x", equations)
        self.assertIn("L_plus_to_minus=L_minus_to_plus^{-1}", equations)
        self.assertIn("eta_cd L^c_a L^d_b=eta_ab", equations)
        self.assertIn("Omega = L^{-1}", equations)
        self.assertIn("B_4vol=J_phi*S_slice", equations)

    def test_acceptance_tests_forbid_scalar_absorption_and_fit(self) -> None:
        acceptance = " ".join(build_payload()["acceptance_tests"])

        self.assertIn("not fitted", acceptance)
        self.assertIn("same L", acceptance)
        self.assertIn("R_plus=0", acceptance)
        self.assertIn("R_minus=0", acceptance)
        self.assertIn("Q_det/Q_cross scalar absorption is forbidden", acceptance)

    def test_markdown_reports_verdict_and_blockers(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Minimal Janus Soldering", markdown)
        self.assertIn("Source derived: False", markdown)
        self.assertIn("S_relative", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
