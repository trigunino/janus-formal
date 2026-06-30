from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_cartan_spin_connection_and_background import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_cartan_spin_connection_and_background.py"


class DeriveSVTCartanSpinConnectionAndBackgroundScriptTests(unittest.TestCase):
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
                (
                    Path(tmpdir)
                    / "svt_cartan_spin_connection_and_background.json"
                ).read_text(encoding="utf-8")
            )

    def test_spin_connection_reproduces_cartan_ghy_traces(self) -> None:
        payload = build_payload()
        curvature = payload["extrinsic_curvature"]

        self.assertEqual(curvature["K_plus_trace_from_spin"], "3*dpsi_p + k^2*zeta")
        self.assertIn("dchi", curvature["K_minus_trace_from_spin"])
        self.assertTrue(curvature["matches_cartan_ghy_K_plus"])
        self.assertTrue(curvature["matches_cartan_ghy_K_minus"])

    def test_background_balance_reveals_tension_mismatch(self) -> None:
        payload = build_payload()
        balance = payload["background_balance"]

        self.assertEqual(balance["required_T_memb"], "3*(mHR2*v + mHR2 + v - 1)")
        self.assertEqual(balance["old_witness_T30_residual"], "-24")
        self.assertEqual(balance["balanced_witness_T6_residual"], "0")
        self.assertFalse(balance["old_witness_T30_is_balanced"])
        self.assertTrue(balance["balanced_witness_T6_is_balanced"])
        self.assertFalse(payload["prediction_ready"])

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_cartan_spin_connection_and_background")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
