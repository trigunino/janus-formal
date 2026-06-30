from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_curved_branch_constraints import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_curved_branch_constraints.py"


class DeriveSVTCurvedBranchConstraintsScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_curved_branch_constraints.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_curved_constraints_are_encoded(self) -> None:
        payload = build_payload()
        constraints = payload["constraints"]

        self.assertIn("H", constraints["lapse_plus"])
        self.assertIn("H", constraints["shift_plus"])
        self.assertIn("H", constraints["bending"])
        self.assertIn("B_p", payload["solutions"])
        self.assertIn("B_m", payload["solutions"])
        self.assertEqual(payload["solutions"]["lapse_compatibility_v1"], "0")

    def test_prediction_ready_remains_false_until_full_action_reinjection(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["fit_used"])
        self.assertFalse(payload["prediction_ready"])
        self.assertIn("no dS kinetic", " ".join(payload["still_open_primitives"]))

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_curved_branch_constraints")


if __name__ == "__main__":
    unittest.main()
