from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_scalar_effective_action import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_scalar_effective_action.py"


class DeriveSVTScalarEffectiveActionScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_scalar_effective_action.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_effective_kernels_are_extracted(self) -> None:
        payload = build_payload()
        kernels = payload["exact_kernels"]

        self.assertIn("alpha_scalar_exact_k", kernels)
        self.assertIn("beta_scalar_exact_k", kernels)
        self.assertIn("psi2_kernel", kernels)
        self.assertNotEqual(kernels["alpha_scalar_exact_k"], "0")
        self.assertNotEqual(kernels["beta_scalar_exact_k"], "0")

    def test_supplied_gauge_and_constraints_are_recorded(self) -> None:
        payload = build_payload()
        gauge = payload["gauge_and_constraints"]

        self.assertEqual(gauge["psi_minus"], "-psi_plus/v")
        self.assertEqual(gauge["phi_plus"], "0")
        self.assertEqual(gauge["zeta"], "0")
        self.assertFalse(payload["fit_used"])
        self.assertFalse(payload["prediction_ready"])

    def test_low_k_series_and_pole_warning_are_reported(self) -> None:
        payload = build_payload()

        self.assertIn("alpha_scalar", payload["low_k_series"])
        self.assertIn("beta_scalar", payload["low_k_series"])
        self.assertIn("4*mHR2*v", payload["stability_conditions"]["poles"])

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_scalar_effective_action")
        self.assertIn("EH plus", " ".join(payload["closed_primitives"]))


if __name__ == "__main__":
    unittest.main()
