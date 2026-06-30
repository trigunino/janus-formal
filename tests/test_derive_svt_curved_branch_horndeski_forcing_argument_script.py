from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_curved_branch_horndeski_forcing_argument import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_curved_branch_horndeski_forcing_argument.py"


class DeriveSVTCurvedBranchHorndeskiForcingArgumentScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_curved_branch_horndeski_forcing_argument.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_horndeski_is_unique_survivor_under_filters(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["verdict"]["horndeski_radion_forced_by_filters"])
        self.assertEqual(len(payload["survivors"]), 1)
        self.assertEqual(payload["survivors"][0]["name"], "einstein_tensor_derivative_coupling")

    def test_not_directly_forced_by_published_janus(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["verdict"]["forced_directly_by_published_janus"])
        self.assertTrue(payload["verdict"]["new_axiom_if_filters_not_accepted_as_janus_principle"])
        self.assertFalse(payload["verdict"]["prediction_ready"])

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_curved_branch_horndeski_forcing_argument")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
