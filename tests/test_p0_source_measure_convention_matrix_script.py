from __future__ import annotations

import unittest

from scripts.build_p0_source_measure_convention_matrix import build_payload


class P0SourceMeasureConventionMatrixTests(unittest.TestCase):
    def test_matrix_fixes_names_without_claiming_closure(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["explicit_measure_names_fixed"])
        self.assertTrue(payload["single_active_convention_required"])
        self.assertIsNone(payload["accepted_convention"])
        self.assertFalse(payload["source_convention_fixed"])
        self.assertFalse(payload["prediction_ready"])

    def test_4volume_3volume_and_effective_density_are_distinct(self) -> None:
        measures = {row["symbol"]: row for row in build_payload()["explicit_measures"]}

        self.assertTrue(measures["B_4vol_plus_from_minus"]["contains_lapse"])
        self.assertFalse(measures["V3_dust_plus_from_minus"]["contains_lapse"])
        self.assertIn("not both", measures["rho_eff_plus_from_minus"]["definition"])

    def test_candidates_are_not_admissible_for_prediction(self) -> None:
        candidates = build_payload()["convention_candidates"]

        self.assertEqual(len(candidates), 3)
        self.assertTrue(all(not row["admissible_for_prediction"] for row in candidates))

    def test_invariants_prevent_qdet_qcross_double_counting(self) -> None:
        invariants = " ".join(build_payload()["invariants"])
        rejection_tests = " ".join(build_payload()["rejection_tests"])

        self.assertIn("exactly one density measure", invariants)
        self.assertIn("Q_det", invariants)
        self.assertIn("Q_cross", invariants)
        self.assertIn("multiplying rho_eff by Q_det again", rejection_tests)
        self.assertIn("replacing B_4vol with V3_dust", rejection_tests)


if __name__ == "__main__":
    unittest.main()
