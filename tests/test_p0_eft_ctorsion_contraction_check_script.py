from __future__ import annotations

import unittest

from scripts.build_p0_eft_ctorsion_contraction_check import build_payload, render_markdown


class P0EFTCTorsionContractionCheckTests(unittest.TestCase):
    def test_ctorsion_remains_open_without_ec_normalization(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["trace_axial_ansatz_loaded"])
        self.assertTrue(status["contraction_target_encoded"])
        self.assertFalse(status["EC_normalization_fixed"])
        self.assertFalse(status["C_torsion_derived"])
        self.assertFalse(status["alpha_iso_fully_derived"])

    def test_convention_sensitivity_is_recorded(self) -> None:
        contraction = build_payload()["contraction"]

        self.assertIn("convention-sensitive", contraction["known_issue"])
        self.assertIn("C_EC", contraction["minimal_positive_branch"])

    def test_obligations_forbid_fit_parameter(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("normalization", obligations)
        self.assertIn("avoid treating C_EC as fit", obligations)

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("C_torsion_derived: False", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
