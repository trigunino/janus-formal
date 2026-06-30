from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_weyl_shear_diagnostic_gate import build_payload


class P0WeylShearDiagnosticGateTests(unittest.TestCase):
    def test_weyl_shear_defined_but_open(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["weyl_shear_equation_defined"])
        self.assertTrue(decision["ricci_weyl_separated"])
        self.assertFalse(decision["weyl_source_derived_from_janus_metric"])
        self.assertFalse(payload["prediction_ready"])

    def test_equations_include_weyl_screen_contraction(self) -> None:
        payload = build_payload()
        equations = " ".join(row["equation"] for row in payload["equations"])

        self.assertIn("C_{mu alpha nu beta}", equations)
        self.assertIn("R_kk", equations)

    def test_shortcuts_block_qcross_absorption_and_fit(self) -> None:
        payload = build_payload()
        shortcuts = " ".join(payload["blocked_shortcuts"])

        self.assertIn("Q_cross_sachs", shortcuts)
        self.assertIn("fit", shortcuts)
        self.assertIn("standard E-mode", shortcuts)


if __name__ == "__main__":
    unittest.main()
