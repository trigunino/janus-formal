from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_action_upstream_transport import build_payload, write_reports


class P0EFTJanusZ4ActionUpstreamTransportScriptTests(unittest.TestCase):
    def test_upstream_transport_closes_internal_triad_without_planck_claim(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["upstream_action_transport_ready"])
        self.assertTrue(payload["cmb_z4_physical_closure_triad_ready"])
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["planck_validation_claimed"])
        self.assertEqual(payload["polarization"]["coefficients"], {"c_q": "1", "c_v": "0", "c_z4": "0"})
        self.assertEqual(payload["scalar"]["coefficients"]["a_S"], "0")
        self.assertEqual(payload["scalar"]["coefficients"]["a_B"], "1")
        self.assertEqual(payload["weyl_lensing"]["coefficients"], {"b_G": "1", "b_W": "1", "b_D": "0", "b_X": "0"})

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_action_upstream_transport.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_action_upstream_transport.md").exists())


if __name__ == "__main__":
    unittest.main()
