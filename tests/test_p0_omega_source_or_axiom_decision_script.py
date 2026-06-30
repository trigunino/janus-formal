from __future__ import annotations

import unittest

from scripts.build_p0_omega_source_or_axiom_decision import build_payload


class P0OmegaSourceOrAxiomDecisionTests(unittest.TestCase):
    def test_decision_is_open_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "omega-source-or-axiom-open")
        self.assertTrue(payload["janus_source_trace_required"])
        self.assertTrue(payload["janus_source_omega_traceability_audit_available"])
        self.assertFalse(payload["janus_source_trace_closed"])
        self.assertTrue(payload["transport_axiom_route_available"])
        self.assertTrue(payload["transport_axiom_acceptance_gate_available"])
        self.assertFalse(payload["transport_axiom_adopted"])
        self.assertTrue(payload["projection_route_available"])
        self.assertTrue(payload["omega_next_decision_matrix_available"])
        self.assertFalse(payload["omega_residual_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_cover_source_axiom_and_projection_routes(self) -> None:
        text = " ".join(row["route"] + row["status"] + row["needed"] for row in build_payload()["decision_rows"])

        self.assertIn("janus_source_trace", text)
        self.assertIn("Omega_u u=0", text)
        self.assertIn("transport_axiom", text)
        self.assertIn("shared L/Omega", text)
        self.assertIn("projection_annihilation", text)
        self.assertIn("P R_Omega P^T=0", text)


if __name__ == "__main__":
    unittest.main()
