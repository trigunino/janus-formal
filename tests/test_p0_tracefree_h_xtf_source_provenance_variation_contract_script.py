from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_xtf_source_provenance_variation_contract import (
    build_payload,
    render_markdown,
)


class P0TracefreeHXtfSourceProvenanceVariationContractTests(unittest.TestCase):
    def test_contract_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "xtf-source-provenance-variation-contract-open")
        self.assertEqual(payload["target_channel"], "H_TF/Q_TF")
        self.assertEqual(payload["best_non_rustine_candidate"], "janus_coupled_stress_stf")
        self.assertTrue(payload["coupled_stress_transport_algebra_closed"])
        self.assertFalse(payload["coupled_stress_transport_acceptance_closed"])
        self.assertEqual(
            payload["same_l_bridge_stack_artifact"],
            "p0_same_l_bridge_induces_m_k_qcross_gate",
        )
        self.assertTrue(payload["same_l_bridge_stack_algebra_closed"])
        self.assertFalse(payload["same_l_bridge_stack_source_selected"])
        self.assertFalse(payload["any_candidate_accepted"])
        self.assertFalse(payload["contract_closed"])
        self.assertFalse(payload["source_action_provenance_closed"])
        self.assertFalse(payload["same_bridge_closed"])
        self.assertFalse(payload["dependency_variation_closed"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_best_candidate_is_janus_coupled_stress_stf(self) -> None:
        payload = build_payload()
        rows = {row["candidate"]: row for row in payload["source_candidates"]}

        self.assertIn("janus_coupled_stress_stf", rows)
        self.assertIn("P_STF(T_self + B4vol T_other_to_self)", rows["janus_coupled_stress_stf"]["source_shape"])
        self.assertIn("M15 Eqs. 4a-4b", rows["janus_coupled_stress_stf"]["source_anchor"])
        self.assertTrue(rows["janus_coupled_stress_stf"]["conditional_promotion"])
        self.assertFalse(rows["janus_coupled_stress_stf"]["accepted"])
        self.assertIn("same bridge", rows["janus_coupled_stress_stf"]["blocker"])

    def test_contract_records_candidate_family_and_variation_ledger(self) -> None:
        payload = build_payload()
        candidates = {row["candidate"] for row in payload["source_candidates"]}
        ledger = " ".join(payload["variation_ledger"])

        self.assertEqual(
            candidates,
            {
                "janus_coupled_stress_stf",
                "Pi_TF",
                "Weyl_shear",
                "Vlasov_quadrupole",
                "Phi_Sigma_or_N_alpha",
            },
        )
        self.assertIn("L_log,H^*[P_STF(X_TF)]", ledger)
        self.assertIn("delta X_TF", ledger)
        self.assertIn("delta_P_STF", ledger)
        self.assertIn("delta_mu", ledger)

    def test_acceptance_tests_forbid_rustines(self) -> None:
        tests = " ".join(build_payload()["acceptance_tests"])

        self.assertIn("published/source-action provenance", tests)
        self.assertIn("covariant 4D symmetric trace-free rank-2", tests)
        self.assertIn("same bridge", tests)
        self.assertIn("no residual fit", tests)
        self.assertIn("determinant/B4vol trace", tests)
        self.assertIn("R_plus=R_minus=0", tests)

    def test_markdown_reports_best_candidate_and_verdict(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("X_TF Source Provenance Variation Contract", markdown)
        self.assertIn("janus_coupled_stress_stf", markdown)
        self.assertIn("P_STF(T_self + B4vol T_other_to_self)", markdown)
        self.assertIn("Coupled-stress transport algebra closed: True", markdown)
        self.assertIn("Same-L bridge stack algebra closed: True", markdown)
        self.assertIn("Same-L bridge stack source selected: False", markdown)
        self.assertIn("p0_tracefree_h_janus_coupled_stress_stf_transport_gate", markdown)
        self.assertIn("Any candidate accepted: False", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
