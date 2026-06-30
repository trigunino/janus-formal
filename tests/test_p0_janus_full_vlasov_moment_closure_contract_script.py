from __future__ import annotations

import unittest

from scripts.build_p0_janus_full_vlasov_moment_closure_contract import build_payload, render_markdown


class P0JanusFullVlasovMomentClosureContractTests(unittest.TestCase):
    def test_phase_space_equation_and_moments_are_written(self) -> None:
        payload = build_payload()
        moments = " ".join(row["definition"] for row in payload["moment_definitions"])

        self.assertIn("A^i_Janus", payload["phase_space_equation"])
        self.assertIn("P_ij", moments)
        self.assertIn("Q_ijk", moments)
        self.assertIn("Pi_ij", moments)
        self.assertTrue(payload["moment_functionals_defined"])

    def test_qijk_is_computed_not_truncated(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["qijk_computed_not_truncated"])
        self.assertFalse(payload["finite_moment_closure_claimed"])
        self.assertFalse(payload["eos_prho_source_derived"])
        self.assertTrue(payload["vlasov_geodesic_force_target_available"])
        self.assertTrue(payload["eos_prho_no_go_vlasov_gate_available"])

    def test_source_requirements_keep_janus_traceability(self) -> None:
        requirements = " ".join(build_payload()["source_requirements"])

        self.assertIn("Janus geodesics", requirements)
        self.assertIn("same L_minus_to_plus", requirements)
        self.assertIn("B_4vol", requirements)
        self.assertIn("without sigma8/S8", requirements)

    def test_no_fit_or_prediction(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_open_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Q_ijk computed not truncated: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
