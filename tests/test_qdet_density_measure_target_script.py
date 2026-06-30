from __future__ import annotations

import unittest

from scripts.build_qdet_density_measure_target import build_payload


class QDetDensityMeasureTargetTests(unittest.TestCase):
    def test_density_branches_separate_effective_and_proper(self) -> None:
        payload = build_payload()
        branches = {row["name"]: row for row in payload["branches"]}

        self.assertEqual(branches["positive_effective"]["q_det"], "1")
        self.assertEqual(branches["negative_proper"]["q_det"], "B_plus")
        self.assertEqual(branches["raw_flrw_scale_ratio"]["status"], "forbidden shortcut")
        self.assertFalse(payload["physics_closed"])
        self.assertIn(
            "T_s^{mu nu}",
            payload["identities"]["anisotropic_stress_source"],
        )

    def test_double_counting_rules_keep_qdet_and_qcross_separate(self) -> None:
        payload = build_payload()
        rules = " ".join(payload["anti_double_counting_rules"])

        self.assertIn("Q_det acts on density", rules)
        self.assertIn("Q_cross acts on optical", rules)
        self.assertIn("W_minus = Q_cross", rules)
        self.assertIn("W_minus = B_plus Q_cross", rules)
        self.assertIn("L_minus_to_plus", " ".join(payload["missing_for_closure"]))


if __name__ == "__main__":
    unittest.main()
