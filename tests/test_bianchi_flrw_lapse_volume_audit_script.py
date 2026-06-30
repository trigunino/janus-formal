from __future__ import annotations

import unittest

from scripts.build_bianchi_flrw_lapse_volume_audit import build_payload


class BianchiFlrwLapseVolumeAuditTests(unittest.TestCase):
    def test_determinant_formula_includes_lapse_and_volume(self) -> None:
        payload = build_payload()
        setup = " ".join(payload["metric_setup"])

        self.assertTrue(payload["determinant_formula_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertIn("N_s a_s^3", setup)
        self.assertIn("(N_minus a_minus^3)/(N_plus a_plus^3)", setup)
        self.assertIn("sqrt(det(gamma_minus)/det(gamma_plus))", setup)

    def test_quartic_case_requires_lapse_ratio(self) -> None:
        rows = {row["case"]: row for row in build_payload()["gauge_cases"]}

        self.assertEqual(rows["common_cosmic_time"]["det4_metric_plus"], "(a_minus/a_plus)^3")
        self.assertEqual(
            rows["sector_conformal_lapse_ratio"]["condition"],
            "N_minus/N_plus=a_minus/a_plus",
        )
        self.assertEqual(
            rows["sector_conformal_lapse_ratio"]["det4_metric_plus"],
            "(a_minus/a_plus)^4",
        )

    def test_guards_block_lensing_amplitude_and_double_count(self) -> None:
        guards = " ".join(build_payload()["guards"])

        self.assertIn("do not identify det4_metric_plus with weight3_dust_plus", guards)
        self.assertIn("gamma_minus equals gamma_plus", guards)
        self.assertIn("not use either cubic or quartic scale ratio as a lensing amplitude", guards)
        self.assertIn("Q_cross optical projection remains a separate derivation", guards)


if __name__ == "__main__":
    unittest.main()
