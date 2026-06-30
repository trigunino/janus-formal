from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_curved_branch_effective_mode import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_curved_branch_effective_mode.py"


class DeriveSVTCurvedBranchEffectiveModeScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_curved_branch_effective_mode.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_effective_mode_kernels_are_extracted(self) -> None:
        payload = build_payload()

        self.assertIn("alpha_dS", payload["kernels"])
        self.assertIn("beta_dS", payload["kernels"])
        self.assertIn("cs2", payload["kernels"])
        self.assertIn("alpha_dS", payload["witness_kernels"])
        self.assertFalse(payload["prediction_ready"])

    def test_assumptions_are_explicit(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["assumptions"]["v"], 1)
        self.assertEqual(payload["assumptions"]["boundary_constraint"], "chi = 2*Mpl2*psi")
        self.assertTrue(payload["assumptions"]["aether_eliminated"])
        self.assertFalse(payload["fit_used"])

    def test_sample_domain_reports_signs_without_claiming_global_closure(self) -> None:
        payload = build_payload()
        samples = payload["sample_domain_H_sqrt_half_a1"]

        self.assertEqual([row["k"] for row in samples], ["1/2", "1", "2"])
        self.assertTrue(any(row["alpha_positive"] for row in samples))
        self.assertIn("prove alpha_dS", " ".join(payload["still_open_primitives"]))

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_curved_branch_effective_mode")


if __name__ == "__main__":
    unittest.main()
