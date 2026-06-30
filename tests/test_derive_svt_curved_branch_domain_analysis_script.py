from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_curved_branch_domain_analysis import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_curved_branch_domain_analysis.py"


class DeriveSVTCurvedBranchDomainAnalysisScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_curved_branch_domain_analysis.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_alpha_zeros_are_not_identical(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["alpha"]["zeros_identical"])
        self.assertEqual(payload["alpha"]["gap_den_minus_num"], "4*a^2*(-H + 2*a^2)/339")

    def test_negative_band_refutes_global_positivity(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["negative_band"]["alpha_negative"])
        self.assertFalse(payload["verdict"]["alpha_global_positive"])
        self.assertFalse(payload["verdict"]["cs2_global_nonnegative"])
        self.assertFalse(payload["verdict"]["prediction_ready"])

    def test_beta_positive_but_not_enough(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["verdict"]["beta_global_positive"])
        self.assertTrue(payload["beta"]["positive_for_a_positive_k_positive"])

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_curved_branch_domain_analysis")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
