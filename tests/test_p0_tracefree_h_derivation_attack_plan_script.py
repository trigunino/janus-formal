from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_derivation_attack_plan import (
    build_payload,
    render_markdown,
)


class P0TracefreeHDerivationAttackPlanTests(unittest.TestCase):
    def test_plan_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "tracefree-h-derivation-attack-plan-open")
        self.assertEqual(payload["branches_accepted"], 0)
        self.assertFalse(payload["action_basis_accepted"])
        self.assertTrue(payload["formal_variations_recorded"])
        self.assertFalse(payload["action_filter_accepts_branch"])
        self.assertFalse(payload["action_measure_variation_ready"])
        self.assertFalse(payload["frechet_log_adjoint_ready"])
        self.assertFalse(payload["qtf_to_h_chain_rule_ready"])
        self.assertFalse(payload["quadratic_qtf_h_el_ready"])
        self.assertFalse(payload["linear_qtf_xtf_h_el_ready"])
        self.assertFalse(payload["xtf_source_contract_ready"])
        self.assertEqual(payload["best_xtf_candidate"], "janus_coupled_stress_stf")
        self.assertTrue(payload["coupled_stress_transport_algebra_closed"])
        self.assertFalse(payload["coupled_stress_transport_acceptance_closed"])
        self.assertEqual(
            payload["same_l_bridge_stack_artifact"],
            "p0_same_l_bridge_induces_m_k_qcross_gate",
        )
        self.assertTrue(payload["same_l_bridge_stack_algebra_closed"])
        self.assertFalse(payload["same_l_bridge_stack_source_selected"])
        self.assertFalse(payload["derivative_branch_ready"])
        self.assertFalse(payload["linear_xtf_provenance_ready"])
        self.assertFalse(payload["same_bridge_dependency_ready"])
        self.assertFalse(payload["source_action_provenance_ready"])
        self.assertFalse(payload["linear_coupling_accepted"])
        self.assertFalse(payload["accepted_as_prediction_input"])
        self.assertFalse(payload["source_selection_closed"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_target_and_template_equations_are_variational(self) -> None:
        payload = build_payload()
        equations = " ".join(payload["template_equations"])

        self.assertIn("P_STF", payload["target_equation"])
        self.assertIn("S_TF^Janus", payload["target_equation"])
        self.assertIn("delta S_Janus/delta H", equations)
        self.assertIn("E_H - S_TF", equations)

    def test_branches_are_named_but_unaccepted(self) -> None:
        rows = {row["branch"]: row for row in build_payload()["branches"]}

        self.assertEqual(
            set(rows),
            {"source_variation", "linear_coupling", "derivative_operator", "bf_gl_constraint"},
        )
        self.assertFalse(any(row["accepted"] for row in rows.values()))
        self.assertIn("same bridge", rows["linear_coupling"]["requires"])
        self.assertIn("stability", rows["derivative_operator"]["requires"])

    def test_action_basis_terms_are_carried_into_plan(self) -> None:
        terms = set(build_payload()["action_basis_terms"])

        self.assertIn("tr_qtf2", terms)
        self.assertIn("dqtf_kinetic", terms)
        self.assertIn("qtf_pi_tf", terms)
        self.assertIn("qtf_phi_sigma", terms)
        self.assertIn("bf_gl_constraints", terms)

    def test_action_filter_best_next_branch_is_carried_into_plan(self) -> None:
        branch = build_payload()["best_next_branch"]

        self.assertEqual(branch["classes"], ["derivative kinetic", "linear couplings"])
        self.assertFalse(branch["allowed_now"])
        self.assertIn("source/action provenance", branch["condition"])

    def test_markdown_reports_next_math_tasks(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Derivation Attack Plan", markdown)
        self.assertIn("Branches accepted: 0/4", markdown)
        self.assertIn("Action Basis Terms", markdown)
        self.assertIn("Action Filter", markdown)
        self.assertIn("formal variations recorded: `True`", markdown)
        self.assertIn("action filter accepts branch: `False`", markdown)
        self.assertIn("action measure variation ready: `False`", markdown)
        self.assertIn("p0_tracefree_h_action_measure_variation_gate", markdown)
        self.assertIn("FrechetLog adjoint ready: `False`", markdown)
        self.assertIn("p0_tracefree_h_frechet_log_adjoint_gate", markdown)
        self.assertIn("Q_TF to H chain rule ready: `False`", markdown)
        self.assertIn("p0_tracefree_h_qtf_to_h_chain_rule_gate", markdown)
        self.assertIn("quadratic Q_TF H-EL ready: `False`", markdown)
        self.assertIn("p0_tracefree_h_quadratic_qtf_h_el_gate", markdown)
        self.assertIn("linear Q_TF X_TF H-EL ready: `False`", markdown)
        self.assertIn("p0_tracefree_h_linear_qtf_xtf_h_el_gate", markdown)
        self.assertIn("X_TF source contract ready: `False`", markdown)
        self.assertIn("p0_tracefree_h_xtf_source_provenance_variation_contract", markdown)
        self.assertIn("best X_TF candidate: `janus_coupled_stress_stf`", markdown)
        self.assertIn("coupled-stress transport algebra closed: `True`", markdown)
        self.assertIn("p0_tracefree_h_janus_coupled_stress_stf_transport_gate", markdown)
        self.assertIn("same-L bridge stack algebra closed: `True`", markdown)
        self.assertIn("same-L bridge stack source selected: `False`", markdown)
        self.assertIn("derivative branch ready: `False`", markdown)
        self.assertIn("linear X_TF provenance ready: `False`", markdown)
        self.assertIn("same bridge dependency ready: `False`", markdown)
        self.assertIn("source/action provenance ready: `False`", markdown)
        self.assertIn("compute delta S/delta H", markdown)
        self.assertIn("FrechetLog_H", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
