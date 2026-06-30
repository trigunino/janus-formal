from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_quadratic_qtf_h_el_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHQuadraticQtfHELTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "tracefree-h-quadratic-qtf-h-el-gate-open")
        self.assertEqual(payload["target_channel"], "H_TF/Q_TF")
        self.assertTrue(payload["formal_h_gradient_recorded"])
        self.assertTrue(payload["homogeneous_only"])
        self.assertFalse(payload["action_measure_variation_closed"])
        self.assertFalse(payload["janus_source_action_provenance"])
        self.assertFalse(payload["nonzero_source_selected"])
        self.assertFalse(payload["accepted_as_closure"])
        self.assertFalse(payload["coefficient_fit_allowed"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_derivation_steps_include_h_gradient(self) -> None:
        rows = {row["step"]: row for row in build_payload()["derivation_steps"]}

        self.assertIn("Tr(Q_TF^2)", rows["candidate_density"]["formula"])
        self.assertIn("2 <Q_TF, delta Q_TF>", rows["qtf_variation"]["formula"])
        self.assertIn("L_log,H[delta H]", rows["h_chain"]["formula"])
        self.assertIn("L_log,H^*[P_STF(Q_TF)]", rows["base_h_gradient"]["formula"])
        self.assertIn("delta_mu", rows["homogeneous_el"]["formula"])

    def test_blockers_prevent_rustine_use(self) -> None:
        text = " ".join(build_payload()["blockers"])

        self.assertIn("Janus source/action provenance", text)
        self.assertIn("B4vol/J/lapse", text)
        self.assertIn("projector variation", text)
        self.assertIn("homogeneous", text)
        self.assertIn("observational fit", text)

    def test_markdown_reports_formal_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Quadratic Q_TF H EL", markdown)
        self.assertIn("G_H^base = L_log,H^*[P_STF(Q_TF)]", markdown)
        self.assertIn("Action measure variation closed: False", markdown)
        self.assertIn("Homogeneous only: True", markdown)
        self.assertIn("Coefficient fit allowed: False", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
