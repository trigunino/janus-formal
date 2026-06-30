from __future__ import annotations

import unittest

from scripts.build_p0_phi_scouple_source_or_axiom_decision import build_payload


class P0PhiScoupleSourceOrAxiomDecisionTests(unittest.TestCase):
    def test_source_not_found_and_axiom_not_adopted(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertEqual(payload["status"], "source-not-found-minimal-axiom-defined-not-adopted")
        self.assertFalse(decision["source_derived_phi_or_scouple_found"])
        self.assertFalse(decision["can_close_dynamic_selection_without_new_axiom"])
        self.assertTrue(decision["minimal_axiom_route_available"])
        self.assertFalse(decision["anti_rustine_gate_passed"])
        self.assertFalse(decision["variational_acceptance_gate_passed"])
        self.assertTrue(decision["multiple_no_fit_candidates_remain_possible"])
        self.assertFalse(decision["axiom_adopted"])
        self.assertTrue(payload["new_axiom_required_for_progress"])
        self.assertTrue(payload["anti_rustine_gate_available"])
        self.assertEqual(payload["anti_rustine_gate_status"], "not-forced-family-remains-open")
        self.assertFalse(payload["prediction_ready"])

    def test_source_scan_names_found_and_missing_parts(self) -> None:
        text = " ".join(row["source"] + row["found"] + row["missing"] for row in build_payload()["source_scan_rows"])

        self.assertIn("M15", text)
        self.assertIn("determinant cross-source", text)
        self.assertIn("M30", text)
        self.assertIn("Bianchi", text)
        self.assertIn("no unique variational phi/L selector", text)
        self.assertIn("source-derived rule fixing Phi/Phi_bar", text)

    def test_minimal_axiom_ties_mirror_b4vol_l_qcross_and_acceptance_tests(self) -> None:
        axiom = build_payload()["minimal_axiom"]
        text = axiom["statement"] + " ".join(axiom["mandatory_constraints"]) + " ".join(axiom["acceptance_tests"])

        self.assertIn("S_couple", text)
        self.assertIn("mirror", text)
        self.assertIn("B_4vol", text)
        self.assertIn("L_plus_to_minus", text)
        self.assertIn("Q_cross", text)
        self.assertIn("R_plus=R_minus=0", text)
        self.assertIn("pressure/Pi", text)


if __name__ == "__main__":
    unittest.main()
