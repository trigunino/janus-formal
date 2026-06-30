from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_cartan_ghy_surface_density import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_cartan_ghy_surface_density.py"


class DeriveSVTCartanGHYSurfaceDensityScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_cartan_ghy_surface_density.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_surface_bridge_matches_previous_variation_term(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["surface_bridge"],
            "-k^2*zeta*(2*Mpl2*psi_p*sqrt(v) - chi)/sqrt(v)",
        )
        self.assertTrue(payload["bridge_matches_previous_surface_term"])

    def test_traces_and_remaining_scope_are_explicit(self) -> None:
        payload = build_payload()

        self.assertIn("K_plus_trace", payload["input_traces"])
        self.assertIn("K_minus_trace", payload["input_traces"])
        self.assertFalse(payload["fit_used"])
        self.assertFalse(payload["prediction_ready"])
        self.assertIn("spin connection", " ".join(payload["still_open_primitives"]))

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_cartan_ghy_surface_density")


if __name__ == "__main__":
    unittest.main()
