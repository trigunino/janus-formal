from __future__ import annotations

import unittest

from scripts.build_p0_dlogb4vol_jacobian_lapse_slice_identity_target import (
    build_payload,
    render_markdown,
)


class P0DlogB4volJacobianLapseSliceIdentityTargetTests(unittest.TestCase):
    def test_identity_closes_numerically_but_not_physically(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "dlogb4vol-jacobian-lapse-slice-identity-target-open")
        self.assertTrue(payload["identity_written"])
        self.assertTrue(payload["identity_numeric_closes"])
        self.assertTrue(payload["mirror_reciprocity_numeric_closes"])
        self.assertLess(payload["numeric_probe"]["max_abs_identity_residual"], 1e-12)
        self.assertFalse(payload["source_selected_measure_found"])
        self.assertFalse(payload["same_phi_j_used_by_cuu_falpha_b4vol"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_separate_jacobian_lapse_slice_and_mirror(self) -> None:
        text = " ".join(row["identity"] for row in build_payload()["identity_rows"])

        self.assertIn("J_phi", text)
        self.assertIn("N_source/N_receiver", text)
        self.assertIn("sqrt(gamma_source)/sqrt(gamma_receiver)", text)
        self.assertIn("B_4vol_minus_from_plus = 1/B_4vol_plus_from_minus", text)

    def test_no_qdet_qcross_absorption(self) -> None:
        self.assertFalse(build_payload()["qdet_qcross_absorption_used"])

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Identity numeric closes: True", markdown)
        self.assertIn("Mirror reciprocity numeric closes: True", markdown)
        self.assertIn("Source-selected measure found: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
