from __future__ import annotations

import unittest

from scripts.build_p0_optimal_transport_matching_route import build_payload


class P0OptimalTransportMatchingRouteTests(unittest.TestCase):
    def test_route_is_bounded_new_axiom_risk_and_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["route"], "optimal-transport-geometric-matching")
        self.assertEqual(payload["status"], "proposal-open-new-axiom-risk")
        self.assertFalse(payload["source_derived"])
        self.assertTrue(payload["new_axiom_risk"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_phi_is_measure_matching_map_with_ot_or_monge_ampere_constraint(self) -> None:
        payload = build_payload()
        equations = " ".join(payload["candidate_equations"].values())
        conditions = " ".join(row["condition"] for row in payload["matching_conditions"])

        self.assertIn("phi: M_plus -> M_minus", payload["map"]["symbol"])
        self.assertIn("mass/measure matching map", payload["map"]["role"])
        self.assertIn("phi_* mu_plus = mu_minus", equations)
        self.assertIn("delta_phi C", equations)
        self.assertIn("det(D phi)", equations)
        self.assertIn("Covariant optimal transport", {row["item"] for row in payload["matching_conditions"]})
        self.assertIn("Monge-Ampere-like constraint", {row["item"] for row in payload["matching_conditions"]})
        self.assertIn("Janus sector sources", conditions)

    def test_same_phi_l_must_generate_k_terms_and_qcross(self) -> None:
        payload = build_payload()
        closure = " ".join(payload["closure_targets"])
        conditions = " ".join(row["condition"] for row in payload["matching_conditions"])

        self.assertIn("K_plus", closure)
        self.assertIn("K_minus", closure)
        self.assertIn("Q_cross", closure)
        self.assertIn("same phi/L", conditions)
        self.assertIn("induced L", closure)

    def test_forbids_observational_fitting(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden_shortcuts"])
        gate = " ".join(payload["acceptance_gate"])

        self.assertIn("fit phi to observations", forbidden)
        self.assertIn("fit transport cost", forbidden)
        self.assertIn("tune Q_cross separately", forbidden)
        self.assertIn("without observational fitting", gate)
        self.assertIn("source-derived rather than survey-normalized", gate)


if __name__ == "__main__":
    unittest.main()
