from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_membrane_polarization_transport import build_payload, write_reports


class P0EFTJanusZ4MembranePolarizationTransportTests(unittest.TestCase):
    def test_z4_transport_is_branch_only_and_scored(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-membrane-polarization-transport")
        self.assertTrue(payload["branch_only_diagnostic"])
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["planck_validation_claimed"])
        self.assertFalse(payload["observational_planck_gate_passed"])
        self.assertEqual(payload["membrane"]["a_sigma"], "2/3")
        self.assertEqual(payload["z4_generator_angle"], "pi/2")
        self.assertIsInstance(payload["safe_solver_integration_recommended"], bool)
        self.assertIn("score", payload["z4_quarter_turn"])
        self.assertIn("te_restored", payload["z4_quarter_turn"]["score"])
        self.assertIn("ee_preserved_or_improved", payload["z4_quarter_turn"]["score"])

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_membrane_polarization_transport.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_membrane_polarization_transport.md").exists())


if __name__ == "__main__":
    unittest.main()
