from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_sheet_diagnostic_execution_gate import build_payload


class P0SheetDiagnosticExecutionGateTests(unittest.TestCase):
    def test_diagnostic_allowed_but_prediction_blocked(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["diagnostic_execution_allowed"])
        self.assertFalse(decision["prediction_execution_allowed"])
        self.assertEqual(decision["simulation_scope"], "diagnostic-only-sheet-aware")
        self.assertFalse(payload["prediction_ready"])

    def test_required_outputs_track_residuals_and_q_separation(self) -> None:
        payload = build_payload()
        outputs = " ".join(payload["required_outputs"])

        self.assertIn("caustic flag", outputs)
        self.assertIn("mirror support mismatch", outputs)
        self.assertIn("Q_det and Q_cross", outputs)

    def test_blocked_items_include_sigma8_and_pressure(self) -> None:
        payload = build_payload()
        blocked = " ".join(payload["blocked"])

        self.assertIn("sigma8", blocked)
        self.assertIn("pressure/Pi", blocked)
        self.assertIn("physical lensing prediction", blocked)


if __name__ == "__main__":
    unittest.main()
