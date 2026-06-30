from __future__ import annotations

import unittest

from scripts.build_p0_eft_boundary_cartan_ghy_conversion_check import build_payload, render_markdown


class P0EFTBoundaryCartanGHYConversionCheckTests(unittest.TestCase):
    def test_cartan_ghy_generates_gamma5_but_not_identity(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["cartan_ghy_conversion_tested"])
        self.assertTrue(status["cartan_ghy_can_generate_m_G"])
        self.assertFalse(status["cartan_ghy_cancels_m_I"])
        self.assertFalse(status["cartan_ghy_plus_nieh_yan_closes_run1"])
        self.assertFalse(status["prediction_ready"])

    def test_matching_equations_show_identity_block(self) -> None:
        equations = build_payload()["coefficients"]["matching_equations"]

        self.assertEqual(equations["identity"], "4*q_T*Delta_chi = 0")
        self.assertIn("beta", equations["gamma5"])

    def test_obligations_name_identity_channel(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("identity-channel", obligations)
        self.assertIn("Delta_chi=0", obligations)

    def test_markdown_records_insufficient_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("cartan_ghy_cancels_m_I: False", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
