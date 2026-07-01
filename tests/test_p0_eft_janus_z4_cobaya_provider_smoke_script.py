from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_cobaya_provider_smoke import build_payload, write_reports


class P0EFTJanusZ4CobayaProviderSmokeScriptTests(unittest.TestCase):
    def test_provider_exposes_finite_cmb_cls(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["finite_cls"])
        self.assertTrue(payload["has_tt_te_ee_pp"])
        self.assertTrue(payload["ell_factor_supported"])
        self.assertTrue(payload["units_supported"])
        self.assertFalse(payload["legacy_camb_fork_required"])
        self.assertFalse(payload["official_planck_likelihood_executed"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_cobaya_provider_smoke.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_cobaya_provider_smoke.md").exists())
        self.assertGreaterEqual(payload["ell_max"], 1000)


if __name__ == "__main__":
    unittest.main()
