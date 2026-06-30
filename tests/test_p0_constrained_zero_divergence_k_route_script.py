from __future__ import annotations

import unittest

from scripts.build_p0_constrained_zero_divergence_k_route import build_payload


class P0ConstrainedZeroDivergenceKRouteTests(unittest.TestCase):
    def test_route_is_bounded_but_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["route"], "constrained-variational-zero-divergence-k")
        self.assertEqual(payload["status"], "proposal-open-new-axiom-risk")
        self.assertFalse(payload["source_derived"])
        self.assertTrue(payload["new_axiom_risk"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_functional_solves_k_plus_k_minus_without_observational_fit(self) -> None:
        payload = build_payload()
        objective = payload["functional"]["objective"]
        forbidden = " ".join(payload["forbidden_shortcuts"])

        self.assertEqual(payload["functional"]["type"], "covariant-local")
        self.assertIn("K_plus^{mu nu}", payload["functional"]["unknowns"])
        self.assertIn("K_minus^{mu nu}", payload["functional"]["unknowns"])
        self.assertIn("minimize", objective)
        self.assertIn("observational amplitudes", objective)
        self.assertIn("observational fit", forbidden)
        self.assertIn("independent Q_cross tuning", forbidden)

    def test_constraints_cover_divergence_symmetry_l_qcross_and_gauge(self) -> None:
        constraints = " ".join(row["condition"] for row in build_payload()["constraints"])

        self.assertIn("nabla_plus_nu K_plus", constraints)
        self.assertIn("nabla_minus_nu K_minus", constraints)
        self.assertIn("K_plus^{mu nu}=K_plus^{nu mu}", constraints)
        self.assertIn("K_minus^{mu nu}=K_minus^{nu mu}", constraints)
        self.assertIn("Q_cross", constraints)
        self.assertIn("same L", constraints)
        self.assertIn("boundary data", constraints)
        self.assertIn("gauge fixing", constraints)

    def test_acceptance_gate_requires_derivation_and_no_fit(self) -> None:
        gate = " ".join(build_payload()["acceptance_gate"])

        self.assertIn("local covariant functional", gate)
        self.assertIn("Euler-Lagrange", gate)
        self.assertIn("nabla_plus K_plus=0", gate)
        self.assertIn("nabla_minus K_minus=0", gate)
        self.assertIn("same L used for Q_cross", gate)
        self.assertIn("boundary and gauge conditions", gate)
        self.assertIn("no observational fit", gate)


if __name__ == "__main__":
    unittest.main()
