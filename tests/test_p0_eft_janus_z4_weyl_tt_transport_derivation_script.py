from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_weyl_tt_transport_derivation import build_payload, write_reports


class P0EFTJanusZ4WeylTTTransportDerivationTests(unittest.TestCase):
    def test_derivation_closes_symbolic_guards(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-weyl-tt-transport-derivation")
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["planck_validation_claimed"])
        self.assertTrue(payload["weyl_lensing_derivation"]["derived"])
        self.assertTrue(payload["tt_transport_beyond_leading"]["derived"])
        self.assertEqual(payload["weyl_lensing_derivation"]["leak_residual_after_no_leak"], "0")
        self.assertEqual(payload["tt_transport_beyond_leading"]["clock_residual"], "0")

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_weyl_tt_transport_derivation.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_weyl_tt_transport_derivation.md").exists())


if __name__ == "__main__":
    unittest.main()
