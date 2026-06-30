from __future__ import annotations

import unittest

from scripts.build_janus_linear_theta_beta_derivation import (
    beta_mode_from_theta,
    build_payload,
    theta_from_growth_derivative,
)


class JanusLinearThetaBetaDerivationTests(unittest.TestCase):
    def test_theta_relation_is_calculated(self) -> None:
        self.assertEqual(theta_from_growth_derivative(0.5, 2.0, 0.25), -0.25)
        self.assertEqual(theta_from_growth_derivative(1.0, 3.0, -0.5), 1.5)

    def test_beta_mode_requires_positive_k_and_c(self) -> None:
        self.assertAlmostEqual(beta_mode_from_theta(299792.458, 2.0), 0.5)

        with self.assertRaisesRegex(ValueError, "k=0"):
            beta_mode_from_theta(1.0, 0.0)
        with self.assertRaisesRegex(ValueError, "speed_of_light"):
            beta_mode_from_theta(1.0, 1.0, speed_of_light=0.0)

    def test_payload_is_conditional_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "conditional-derivation-open")
        self.assertTrue(payload["theta_relation_checked"])
        self.assertFalse(payload["source_operator_closed"])
        self.assertFalse(payload["source_derived_beta_ready"])
        self.assertFalse(payload["prediction_ready"])

    def test_payload_keeps_source_and_l_gates_open(self) -> None:
        text = " ".join(build_payload()["blockers"])

        self.assertIn("Janus operator", text)
        self.assertIn("k=0", text)
        self.assertIn("L_minus_to_plus", text)
        self.assertIn("A_J", text)


if __name__ == "__main__":
    unittest.main()
