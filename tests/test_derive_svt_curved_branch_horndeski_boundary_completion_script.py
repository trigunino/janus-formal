from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_curved_branch_horndeski_boundary_completion import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_curved_branch_horndeski_boundary_completion.py"


class DeriveSVTCurvedBranchHorndeskiBoundaryCompletionScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_curved_branch_horndeski_boundary_completion.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_boundary_completion_closes_k4_conditionally(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["verdict"]["boundary_completion_is_required_by_horndeski_variation"])
        self.assertTrue(payload["verdict"]["boundary_completion_closes_k4_block"])
        self.assertTrue(payload["verdict"]["coefficient_is_fixed_conditionally"])

    def test_janus_source_still_missing(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["verdict"]["requires_new_horndeski_radion_axiom"])
        self.assertFalse(payload["verdict"]["source_derived_from_janus"])
        self.assertFalse(payload["verdict"]["prediction_ready"])

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_curved_branch_horndeski_boundary_completion")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
