from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_frechet_log_adjoint_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHFrechetLogAdjointGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "tracefree-h-frechet-log-adjoint-gate-open")
        self.assertEqual(payload["target_channel"], "H_TF/Q_TF")
        self.assertTrue(payload["spectral_adjoint_recorded"])
        self.assertTrue(payload["self_adjoint_only_on_spd_branch"])
        self.assertFalse(payload["commuting_shortcut_allowed"])
        self.assertTrue(payload["offdiagonal_kernel_required"])
        self.assertFalse(payload["source_provenance_closed"])
        self.assertFalse(payload["accepted_as_closure"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_spectral_rules_record_kernel_adjoint_and_gradient(self) -> None:
        rows = {row["rule"]: row for row in build_payload()["spectral_rules"]}

        self.assertIn("f^[1](lambda_i,lambda_j)", rows["frechet_log_kernel"]["formula"])
        self.assertIn("f^[1](li,lj)", rows["divided_difference"]["formula"])
        self.assertIn("<B,L_log,H[A]>", rows["self_adjoint_spd_branch"]["formula"])
        self.assertIn("L_log,H^*", rows["qtf_to_h_gradient"]["formula"])
        self.assertIn("deltaP_STF", rows["qtf_to_h_gradient"]["formula"])

    def test_requirements_keep_branch_inner_product_and_projector(self) -> None:
        text = " ".join(build_payload()["requirements"])

        self.assertIn("regular spectral/log branch", text)
        self.assertIn("same inner product", text)
        self.assertIn("same L/Omega/tetrad", text)
        self.assertIn("projector variation", text)
        self.assertIn("Janus source/action provenance", text)

    def test_forbidden_routes_block_scalar_shortcuts(self) -> None:
        text = " ".join(build_payload()["forbidden_routes"])

        self.assertIn("scalar H^{-1}", text)
        self.assertIn("off-diagonal divided-difference", text)
        self.assertIn("determinant trace", text)
        self.assertIn("source closure", text)

    def test_markdown_reports_adjoint_gate(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("FrechetLog Adjoint", markdown)
        self.assertIn("L_log,H[A]_ij", markdown)
        self.assertIn("G_H = 1/2 L_log,H^*", markdown)
        self.assertIn("Commuting shortcut allowed: False", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
