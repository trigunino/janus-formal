from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_sheet_optical_no_fit_gate import build_payload


class P0SheetOpticalNoFitGateTests(unittest.TestCase):
    def test_independent_lensing_amplitudes_are_forbidden(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["optical_no_fit_gate_defined"])
        self.assertFalse(decision["independent_lensing_amplitudes_allowed"])
        self.assertFalse(decision["source_derived_optics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rules_keep_same_distribution_and_qdet_separate(self) -> None:
        payload = build_payload()
        rules = " ".join(row["rule"] for row in payload["optical_rules"])

        self.assertIn("same sheets or f_to", rules)
        self.assertIn("sum_s Q_cross", rules)
        self.assertIn("not lensing amplitudes", rules)

    def test_failure_modes_block_observational_normalization(self) -> None:
        payload = build_payload()
        failures = " ".join(payload["failure_modes"])

        self.assertIn("independently from transported mass", failures)
        self.assertIn("match observations", failures)


if __name__ == "__main__":
    unittest.main()
