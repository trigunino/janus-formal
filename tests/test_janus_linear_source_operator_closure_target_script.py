from __future__ import annotations

import unittest

from scripts.build_janus_linear_source_operator_closure_target import build_payload


class JanusLinearSourceOperatorClosureTargetTests(unittest.TestCase):
    def test_operator_closure_is_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "source-operator-closure-open")
        self.assertFalse(payload["source_operator_closed"])
        self.assertFalse(payload["source_derived_ic_ready"])
        self.assertFalse(payload["source_derived_beta_ready"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_cover_omegas_amplitude_and_theta(self) -> None:
        objects = {row["object"] for row in build_payload()["closure_rows"]}

        self.assertIn("Omega_plus(a)", objects)
        self.assertIn("Omega_minus_eff(a)", objects)
        self.assertIn("A_J", objects)
        self.assertIn("theta_s(k,a)", objects)

    def test_checks_forbid_fit_and_branch_mismatch(self) -> None:
        checks = " ".join(build_payload()["consistency_checks"])

        self.assertIn("one branch supplies density", checks)
        self.assertIn("Q_det", checks)
        self.assertIn("H(a)=H0 E_J(a)", checks)
        self.assertIn("no sigma8/S8/survey", checks)
        self.assertIn("constant Omega", checks)


if __name__ == "__main__":
    unittest.main()
