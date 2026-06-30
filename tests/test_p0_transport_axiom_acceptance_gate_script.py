from __future__ import annotations

import unittest

from scripts.build_p0_transport_axiom_acceptance_gate import build_payload, render_markdown


class P0TransportAxiomAcceptanceGateTests(unittest.TestCase):
    def test_gate_requires_axiom_if_source_derivation_fails_but_predicts_false(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "transport-axiom-acceptance-gate-open")
        self.assertFalse(payload["source_derivation_closed"])
        self.assertTrue(payload["bounded_external_source_search_performed"])
        self.assertTrue(payload["external_source_search_omega_transport_audit_available"])
        self.assertTrue(payload["external_source_search_scouple_phi_audit_available"])
        self.assertTrue(payload["du_l_omega_dynamic_derivation_attempt_available"])
        self.assertTrue(payload["omega_source_no_go_axiom_boundary_available"])
        self.assertTrue(payload["explicit_axiom_required_if_not_derived"])
        self.assertTrue(payload["transport_axiom_candidate_statement_available"])
        self.assertTrue(payload["explicit_axiom_written"])
        self.assertFalse(payload["explicit_axiom_accepted"])
        self.assertFalse(payload["accepted_and_tested"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["prediction_claim"])

    def test_acceptance_criteria_cover_required_gates(self) -> None:
        names = {row["criterion"] for row in build_payload()["acceptance_criteria"]}

        self.assertIn("source_derivation_exhausted", names)
        self.assertIn("axiom_statement_complete", names)
        self.assertIn("mirror_consistency", names)
        self.assertIn("dust_scope_locked", names)
        self.assertIn("no_rustine_compliance", names)
        self.assertIn("tested_before_acceptance", names)

    def test_axiom_must_bind_same_l_omega_mirror_k_qcross_and_dust_scope(self) -> None:
        payload = build_payload()
        text = " ".join(payload["axiom_must_state"].values())

        self.assertTrue(payload["rank_one_dust_scope"])
        self.assertFalse(payload["pressure_pi_extension_closed"])
        self.assertIn("Omega_alpha=(D_alpha L)L^{-1}", text)
        self.assertIn("Omega_u u=0", text)
        self.assertIn("L_plus_to_minus=L_minus_to_plus^{-1}", text)
        self.assertIn("K transport", text)
        self.assertIn("Q_cross", text)
        self.assertIn("rank-one dust", text)

    def test_no_rustine_rules_forbid_fits_and_duplicate_transport(self) -> None:
        rules = " ".join(build_payload()["no_rustine_rules"])

        self.assertIn("lensing/growth data", rules)
        self.assertIn("one transport map for K and another for Q_cross", rules)
        self.assertIn("scalar factor", rules)
        self.assertIn("gauge convention", rules)
        self.assertIn("unaccepted or untested", rules)

    def test_markdown_renders_decision_and_false_prediction(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Explicit axiom required if not derived: True", markdown)
        self.assertIn("Explicit axiom written: True", markdown)
        self.assertIn("Explicit axiom accepted: False", markdown)
        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Prediction claim: False", markdown)
        self.assertIn("Only after acceptance and tests", markdown)


if __name__ == "__main__":
    unittest.main()
