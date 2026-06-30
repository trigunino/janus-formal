from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_linear_qtf_xtf_h_el_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHLinearQtfXtfHELTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "tracefree-h-linear-qtf-xtf-h-el-gate-open")
        self.assertEqual(payload["target_channel"], "H_TF/Q_TF")
        self.assertTrue(payload["formal_nonzero_source_shape_recorded"])
        self.assertEqual(payload["best_xtf_candidate"], "janus_coupled_stress_stf")
        self.assertIn("P_STF(T_self + B4vol T_other_to_self)", payload["best_xtf_source_shape"])
        self.assertTrue(payload["coupled_stress_transport_algebra_closed"])
        self.assertFalse(payload["coupled_stress_transport_acceptance_closed"])
        self.assertFalse(payload["frechet_log_adjoint_ready"])
        self.assertFalse(payload["xtf_source_contract_closed"])
        self.assertFalse(payload["xtf_provenance_closed"])
        self.assertFalse(payload["same_bridge_closed"])
        self.assertFalse(payload["projector_dependency_closed"])
        self.assertFalse(payload["action_measure_variation_closed"])
        self.assertTrue(payload["dependency_terms_required"])
        self.assertFalse(payload["residual_xtf_allowed"])
        self.assertFalse(payload["janus_source_action_provenance"])
        self.assertFalse(payload["accepted_as_closure"])
        self.assertFalse(payload["accepted_as_prediction_input"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_derivation_steps_include_nonzero_source_shape(self) -> None:
        rows = {row["step"]: row for row in build_payload()["derivation_steps"]}

        self.assertIn("Q_TF^{ab} X_TF_ab", rows["candidate_density"]["formula"])
        self.assertIn("<X_TF, delta Q_TF>", rows["qtf_variation"]["formula"])
        self.assertIn("1/2 L_log,H^*[P_STF(X_TF)]", rows["base_h_source"]["formula"])
        self.assertIn("delta X_TF", rows["dependency_variation"]["formula"])
        self.assertIn("delta_mu", rows["full_el_shape"]["formula"])

    def test_blockers_prevent_residual_source_use(self) -> None:
        text = " ".join(build_payload()["blockers"])

        self.assertIn("X_TF provenance is open", text)
        self.assertIn("same-bridge", text)
        self.assertIn("projector variation", text)
        self.assertIn("B4vol/J/lapse", text)
        self.assertIn("residual X_TF", text)

    def test_markdown_reports_nonzero_shape_but_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Linear Q_TF X_TF H EL", markdown)
        self.assertIn("Base H source: `1/2 L_log,H^*[P_STF(X_TF)]`", markdown)
        self.assertIn("Best X_TF candidate: `janus_coupled_stress_stf`", markdown)
        self.assertIn("Coupled-stress transport algebra closed: True", markdown)
        self.assertIn("Coupled-stress transport acceptance closed: False", markdown)
        self.assertIn("X_TF source contract closed: False", markdown)
        self.assertIn("X_TF provenance closed: False", markdown)
        self.assertIn("Action measure variation closed: False", markdown)
        self.assertIn("Residual X_TF allowed: False", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
