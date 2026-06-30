from __future__ import annotations

import unittest

from scripts.build_p0_eft_boundary_run1_run2_calculation import build_payload, render_markdown


class P0EFTBoundaryRun1Run2CalculationTests(unittest.TestCase):
    def test_run1_conditions_are_exact_and_open(self) -> None:
        payload = build_payload()
        run1 = payload["run1"]
        status = payload["theorem_status"]

        self.assertEqual(run1["factorization_conditions"]["m_I"], "0")
        self.assertEqual(run1["factorization_conditions"]["m_C"], "0")
        self.assertIn("sigma*eps_n*m_N", run1["factorization_conditions"]["m_G"])
        self.assertTrue(status["run1_symbolic_conditions_computed"])
        self.assertFalse(status["run1_factorization_proved_for_generic_coefficients"])

    def test_run2_commutator_conditions_are_explicit(self) -> None:
        payload = build_payload()
        run2 = payload["run2"]
        status = payload["theorem_status"]

        self.assertEqual(run2["aps_operator"], "A_APS=N*D_Sigma")
        self.assertIn("D_Sigma anticommutes with G", run2["sufficient_geometry_conditions"])
        self.assertTrue(status["run2_commutation_proved_from_conditions"])
        self.assertFalse(status["run2_zero_modes_controlled"])

    def test_physical_inputs_are_still_required(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run1_requires_physical_coefficients"])
        self.assertTrue(status["run2_requires_actual_boundary_spectrum"])
        self.assertFalse(status["prediction_ready"])

    def test_markdown_records_not_ready(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("m_G=sigma*eps_n*m_N", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
