from __future__ import annotations

import unittest

from scripts.build_p0_eft_boundary_factorization_aps_bridge import build_payload, render_markdown


class P0EFTBoundaryFactorizationAPSBridgeTests(unittest.TestCase):
    def test_final_targets_are_encoded_but_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["boundary_factorization_target_encoded"])
        self.assertTrue(status["coefficient_matching_required"])
        self.assertTrue(status["aps_operator_defined_as_gamma_n_D_sigma"])
        self.assertFalse(status["factorization_proved"])
        self.assertFalse(status["chiral_to_aps_bridge_proved"])
        self.assertFalse(status["prediction_ready"])

    def test_aps_bridge_uses_correct_operator(self) -> None:
        bridge = build_payload()["aps_bridge"]

        self.assertIn("gamma^n D_Sigma", bridge["aps_operator"])
        self.assertIn("[A_APS, gamma5]=0", bridge["commutation_target"])
        self.assertIn("zero modes", bridge["zero_mode_caveat"])

    def test_obligations_include_coefficients_and_zero_modes(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("M_bulk_flux", obligations)
        self.assertIn("selected chiral half-space", obligations)
        self.assertIn("zero modes", obligations)

    def test_markdown_does_not_claim_ready(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("factorization_proved: False", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
