from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_sachs_optical_source_gate import build_payload


class P0SachsOpticalSourceGateTests(unittest.TestCase):
    def test_sachs_gate_defined_but_not_prediction_ready(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["sachs_gate_defined"])
        self.assertTrue(decision["popt_partially_matches_sachs_source"])
        self.assertFalse(decision["janus_sign_derived"])
        self.assertFalse(payload["prediction_ready"])

    def test_chain_contains_null_focusing_and_stress_projection(self) -> None:
        payload = build_payload()
        formulas = " ".join(row["formula"] for row in payload["sachs_chain"])

        self.assertIn("R_{mu nu} k^mu k^nu", formulas)
        self.assertIn("k_mu k_nu T_to", formulas)

    def test_blockers_keep_qdet_and_sign_separate(self) -> None:
        payload = build_payload()
        blockers = " ".join(payload["blockers"])

        self.assertIn("positive/negative mass sign", blockers)
        self.assertIn("Q_det", blockers)
        self.assertIn("same transported T_to", blockers)


if __name__ == "__main__":
    unittest.main()
