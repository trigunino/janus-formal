from __future__ import annotations

import unittest

from scripts.build_p0_density_measure_closure_condition import build_payload


class P0DensityMeasureClosureConditionTests(unittest.TestCase):
    def test_density_measure_terms_are_required_but_open(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["product_rule_terms_written"])
        self.assertTrue(payload["d_log_b_terms_required"])
        self.assertFalse(payload["source_convention_fixed"])
        self.assertFalse(payload["b_gradients_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_product_rule_contains_d_log_b_terms(self) -> None:
        terms = " ".join(build_payload()["product_rule_terms"])

        self.assertIn("D_plus_B log(B_plus)", terms)
        self.assertIn("D_minus_B log(B_minus)", terms)
        self.assertIn("D_plus_B(B_plus K_plus", terms)
        self.assertIn("D_minus_B(B_minus K_minus", terms)

    def test_both_sectors_require_measure_closure(self) -> None:
        rows = {row["sector"]: row for row in build_payload()["dust_closure_requirements"]}

        self.assertIn("B_plus", rows["plus"]["extra_measure_term"])
        self.assertIn("selected density measure", rows["plus"]["closure_condition"])
        self.assertIn("B_minus", rows["minus"]["extra_measure_term"])
        self.assertIn("selected density measure", rows["minus"]["closure_condition"])

    def test_conventions_separate_4volume_3volume_and_effective_density(self) -> None:
        names = {row["name"] for row in build_payload()["admissible_conventions"]}

        self.assertIn("field_equation_4volume", names)
        self.assertIn("dust_flux_3volume", names)
        self.assertIn("effective_density_absorbs_B", names)

    def test_forbids_raw_amplitude_and_qdet_qcross_merge(self) -> None:
        forbidden = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("do not drop D log B", forbidden)
        self.assertIn("lensing amplitude", forbidden)
        self.assertIn("do not merge Q_det with Q_cross", forbidden)


if __name__ == "__main__":
    unittest.main()
