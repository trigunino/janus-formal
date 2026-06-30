from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_curved_branch_longitudinal_aether_check import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_curved_branch_longitudinal_aether_check.py"


class DeriveSVTCurvedBranchLongitudinalAetherCheckScriptTests(unittest.TestCase):
    def run_script_payload(self) -> dict:
        with tempfile.TemporaryDirectory() as tmpdir:
            env = os.environ.copy()
            env["JANUS_REPORT_DIR"] = tmpdir
            subprocess.run(
                [sys.executable, str(SCRIPT)],
                cwd=ROOT,
                env=env,
                capture_output=True,
                text=True,
                check=True,
            )
            return json.loads(
                (Path(tmpdir) / "svt_curved_branch_longitudinal_aether_check.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_proposed_delta_is_not_required_delta(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["proposed_delta_N"], "312*a^2*k^2")
        self.assertNotEqual(payload["proposed_delta_N"], payload["required_delta_for_alpha_5392"])
        self.assertFalse(payload["verdict"]["proposed_delta_makes_alpha_5392"])

    def test_proposed_delta_does_not_synchronize_zeros(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["verdict"]["proposed_delta_synchronizes_zeros"])
        self.assertNotEqual(payload["corrected_zero_gap_with_proposed_delta"], "0")
        self.assertFalse(payload["verdict"]["prediction_ready"])

    def test_required_delta_closes_alpha_algebraically(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["residual_after_required_delta"], "0")
        self.assertEqual(payload["corrected_alpha_with_required_delta"], "5392")
        self.assertTrue(payload["verdict"]["required_delta_makes_alpha_5392"])
        self.assertTrue(payload["verdict"]["required_delta_alpha_constant"])
        self.assertFalse(payload["verdict"]["prediction_ready"])

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_curved_branch_longitudinal_aether_check")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
