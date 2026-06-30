from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_janus_ricci_sign_substitution_gate import build_payload


class P0JanusRicciSignSubstitutionGateTests(unittest.TestCase):
    def test_sign_location_fixed_but_value_open(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["sign_location_fixed"])
        self.assertFalse(decision["janus_cross_sign_value_derived"])
        self.assertTrue(decision["can_use_reduced_sachs_diagnostic"])
        self.assertFalse(payload["prediction_ready"])

    def test_substitution_contains_cross_sign_and_mirror(self) -> None:
        payload = build_payload()
        forms = " ".join(row["form"] for row in payload["substitutions"])

        self.assertIn("s_cross", forms)
        self.assertIn("mirror(s_cross)", forms)

    def test_rules_forbid_qcross_or_qdet_sign_hiding(self) -> None:
        payload = build_payload()
        rules = " ".join(payload["sign_rules"])

        self.assertIn("not in optical post-normalization", rules)
        self.assertIn("Q_det", rules)
        self.assertIn("mirror signs", rules)


if __name__ == "__main__":
    unittest.main()
