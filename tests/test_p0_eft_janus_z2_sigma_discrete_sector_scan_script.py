import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_discrete_sector_observation_readiness_gate import (
    build_payload as readiness,
)
from scripts.build_p0_eft_janus_z2_sigma_discrete_sector_scan import build_payload as scan


class SigmaDiscreteSectorScanTests(unittest.TestCase):
    def test_readiness_blocks_without_contract(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = readiness(Path(tmp) / "missing.json")

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["observation_readiness"])
        self.assertIn("non_overlap_accounting_declared", payload["blocked_by"])

    def test_readiness_accepts_nonfit_contract_with_active_family(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "ready.json"
            path.write_text(
                json.dumps(
                    {
                        "non_overlap_accounting_declared": True,
                        "physical_priors_declared": True,
                        "observation_can_only_reject_or_rank_sectors": True,
                        "provenance": "active_discrete_sector_readiness",
                    }
                ),
                encoding="utf-8",
            )
            payload = readiness(path)

        self.assertTrue(payload["observation_readiness"])

    def test_scan_rejects_or_keeps_fixed_sectors_without_unique_claim(self):
        payload = scan()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["unique_prediction_claim_allowed"])

    def test_scan_blocks_continuous_fit(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "scan.json"
            path.write_text(json.dumps({"fixed_ranges_only": True, "continuous_fit_used": True}), encoding="utf-8")
            payload = scan(path)

        self.assertFalse(payload["scan_ready"])
        self.assertIn("no_continuous_fit", payload["blocked_by"])


if __name__ == "__main__":
    unittest.main()
