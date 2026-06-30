from __future__ import annotations

import unittest

from scripts.build_p0_omega_next_decision_matrix import build_payload


class P0OmegaNextDecisionMatrixTests(unittest.TestCase):
    def test_decision_matrix_keeps_prediction_blocked(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "omega-next-decision-open")
        self.assertTrue(payload["external_source_search_required"])
        self.assertTrue(payload["external_janus_omega_source_search_gate_available"])
        self.assertTrue(payload["axiom_candidate_allowed"])
        self.assertFalse(payload["axiom_candidate_adopted"])
        self.assertFalse(payload["prediction_use_allowed"])
        self.assertFalse(payload["omega_residual_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_decisions_cover_source_axiom_and_prediction_block(self) -> None:
        text = " ".join(row["decision"] + row["rule"] for row in build_payload()["decisions"])

        self.assertIn("search_external_source_first", text)
        self.assertIn("D_u L", text)
        self.assertIn("write_axiom_candidate", text)
        self.assertIn("adopted=false", text)
        self.assertIn("use_axiom_in_prediction", text)
        self.assertIn("forbidden", text)


if __name__ == "__main__":
    unittest.main()
