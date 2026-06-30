from __future__ import annotations

import unittest

from scripts.build_p0_eft_torsion_energy_normalization import build_payload, render_markdown


class P0EFTTorsionEnergyNormalizationTests(unittest.TestCase):
    def test_normalization_reduced_to_ctorsion(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["torsion_energy_scaling_encoded"])
        self.assertTrue(status["omega_torsion_definition_encoded"])
        self.assertTrue(status["normalization_reduced_to_C_torsion"])
        self.assertFalse(status["C_torsion_derived"])
        self.assertFalse(status["alpha_iso_fully_derived"])

    def test_alpha_mentions_ctorsion(self) -> None:
        alpha = build_payload()["alpha_iso"]

        self.assertIn("C_torsion", alpha["remaining_constant"])
        self.assertIn("Omega_torsion", alpha["previous"])

    def test_obligations_include_exact_contraction(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("exact Cartan contorsion contraction", obligations)
        self.assertIn("Delta_chi", obligations)

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("C_torsion_derived: False", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
