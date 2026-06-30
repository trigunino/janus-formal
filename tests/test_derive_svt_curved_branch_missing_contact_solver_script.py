from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_curved_branch_missing_contact_solver import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_curved_branch_missing_contact_solver.py"


class DeriveSVTCurvedBranchMissingContactSolverScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_curved_branch_missing_contact_solver.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_missing_contact_closes_required_delta_without_k_pole(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["closes_required_delta"])
        self.assertFalse(payload["missing_contact_has_k_pole"])
        self.assertTrue(payload["verdict"]["local_in_k"])
        self.assertTrue(payload["verdict"]["algebraic_closure_found"])

    def test_missing_contact_is_not_claimed_source_derived(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["verdict"]["sourced_from_action"])
        self.assertFalse(payload["verdict"]["prediction_ready"])
        self.assertFalse(payload["fit_used"])
        self.assertIn("inverse matching", " ".join(payload["needed_inputs"]))

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_curved_branch_missing_contact_solver")


if __name__ == "__main__":
    unittest.main()
