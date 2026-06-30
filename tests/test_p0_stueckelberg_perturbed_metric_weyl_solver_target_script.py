from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_perturbed_metric_weyl_solver_target import build_payload


class P0PerturbedMetricWeylSolverTargetTests(unittest.TestCase):
    def test_solver_target_defined_but_not_solved(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["weyl_solver_target_defined"])
        self.assertFalse(decision["perturbed_metric_solved"])
        self.assertTrue(decision["pm_proxy_replacement_path_defined"])
        self.assertFalse(payload["prediction_ready"])

    def test_equations_include_metric_perturbation_and_weyl_output(self) -> None:
        payload = build_payload()
        equations = " ".join(row["equation"] for row in payload["equations"])

        self.assertIn("delta G_plus", equations)
        self.assertIn("C_plus[k,m,k,m]", equations)
        self.assertIn("R_plus[k,k]", equations)

    def test_outputs_include_bianchi_and_pm_comparison(self) -> None:
        payload = build_payload()
        outputs = " ".join(payload["required_outputs"])

        self.assertIn("Bianchi residual", outputs)
        self.assertIn("PM reduced Ricci diagnostic", outputs)


if __name__ == "__main__":
    unittest.main()
