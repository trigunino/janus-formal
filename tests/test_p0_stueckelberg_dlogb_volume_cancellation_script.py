from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_dlogb_volume_cancellation import build_payload, render_markdown


class P0StueckelbergDlogBVolumeCancellationTests(unittest.TestCase):
    def test_dlogb_absorption_is_conditional_not_full_closure(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "dlogb-volume-cancellation-conditional")
        self.assertTrue(payload["dlogb_absorbable_into_effective_density"])
        self.assertTrue(payload["closes_density_part_conditionally"])
        self.assertFalse(payload["closes_full_residual"])
        self.assertFalse(payload["prediction_ready"])

    def test_identities_combine_dphi_and_dlogb(self) -> None:
        identities = " ".join(row["equation"] for row in build_payload()["identities"])

        self.assertIn("D_phi rho_minus", identities)
        self.assertIn("D_plus log B_minus_to_plus", identities)
        self.assertIn("D_phi rho_plus", identities)
        self.assertIn("D_minus log B_plus_to_minus", identities)

    def test_conditions_keep_qdet_and_qcross_separate(self) -> None:
        conditions = " ".join(build_payload()["conditions"])

        self.assertIn("density/volume measure only", conditions)
        self.assertIn("Q_cross remains a separate optical projection factor", conditions)
        self.assertIn("no extra multiplication by B", conditions)

    def test_remaining_terms_are_velocity_and_connection(self) -> None:
        remaining = " ".join(build_payload()["remaining_after_absorption"])

        self.assertIn("D_L", remaining)
        self.assertIn("connection difference", remaining)
        self.assertIn("effective-density continuity", remaining)

    def test_markdown_reports_no_prediction(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Q_det/Q_cross separate: True", markdown)


if __name__ == "__main__":
    unittest.main()
