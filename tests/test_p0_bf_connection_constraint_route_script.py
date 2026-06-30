from __future__ import annotations

import unittest

from scripts.build_p0_bf_connection_constraint_route import build_payload


class P0BfConnectionConstraintRouteTests(unittest.TestCase):
    def test_route_is_new_axiom_and_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["route"], "bf-connection-constraint-closure")
        self.assertEqual(payload["status"], "proposal-open-new-axiom-risk")
        self.assertTrue(payload["new_axiom_risk"])
        self.assertFalse(payload["full_equations_close"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_route_treats_omega_and_l_as_gauge_fields(self) -> None:
        payload = build_payload()
        fields = " ".join(payload["gauge_fields"])
        targets = " ".join(row["constraint"] for row in payload["constraint_targets"])

        self.assertEqual(payload["constraint_mechanism"], "BF/Lagrange-multiplier")
        self.assertIn("Omega_alpha", fields)
        self.assertIn("L", fields)
        self.assertIn("R_Omega", targets)
        self.assertIn("D_alpha L - Omega_alpha L", targets)

    def test_tests_el_and_separate_residuals_without_fits(self) -> None:
        payload = build_payload()
        tests = " ".join(payload["tests_whether"])
        gate = " ".join(payload["acceptance_gate"])

        self.assertFalse(payload["allows_fitted_observables"])
        self.assertIn("Euler-Lagrange equations can produce E_L", tests)
        self.assertIn("R_plus and R_minus can be separated", tests)
        self.assertIn("without fitted observables", tests)
        self.assertIn("no fitted observables", gate)

    def test_same_l_controls_k_and_qcross(self) -> None:
        payload = build_payload()
        targets = " ".join(row["constraint"] for row in payload["constraint_targets"])
        gate = " ".join(payload["acceptance_gate"])

        self.assertTrue(payload["same_l_for_k_and_qcross"])
        self.assertIn("same L", targets)
        self.assertIn("K_plus", targets)
        self.assertIn("Q_cross", targets)
        self.assertIn("same L controls K_plus/K_minus and Q_cross", gate)

    def test_formal_variations_expose_missing_source_curvature(self) -> None:
        payload = build_payload()
        action = " ".join(payload["action_terms"])
        variations = " ".join(payload["formal_variations"])
        obstructions = " ".join(payload["open_obstructions"])

        self.assertIn("F_Omega - Phi_R[source Janus]", action)
        self.assertIn("D L - Omega L", action)
        self.assertIn("delta B: F_Omega = Phi_R[source Janus]", variations)
        self.assertIn("delta Omega/delta L", variations)
        self.assertIn("Phi_R is the decisive missing object", obstructions)
        self.assertIn("new axiom", obstructions)


if __name__ == "__main__":
    unittest.main()
