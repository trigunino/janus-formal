from __future__ import annotations

import unittest

from scripts.build_p0_falpha_from_jacobian_tetrad_identity_target import build_payload, render_markdown


class P0FalphaFromJacobianTetradIdentityTargetTests(unittest.TestCase):
    def test_identity_closes_numerically_but_not_physically(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "falpha-from-jacobian-tetrad-identity-target-open")
        self.assertTrue(payload["dl_identity_written"])
        self.assertTrue(payload["dl_identity_numeric_closes"])
        self.assertLess(payload["numeric_probe"]["max_abs_dl_identity_residual"], 1e-12)
        self.assertTrue(payload["jacobian_integrability_required"])
        self.assertFalse(payload["source_selected_jacobian_found"])
        self.assertFalse(payload["falpha_source_derived"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_include_j_l_and_curl_gate(self) -> None:
        text = " ".join(row["identity"] for row in build_payload()["identity_rows"])

        self.assertIn("J = e_plus L e_minus", text)
        self.assertIn("D L =", text)
        self.assertIn("D_[a J^mu_b]=0", text)

    def test_no_observational_fit(self) -> None:
        self.assertFalse(build_payload()["uses_observational_fit"])

    def test_markdown_keeps_open_source_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("DL identity numeric closes: True", markdown)
        self.assertIn("Source-selected Jacobian found: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
