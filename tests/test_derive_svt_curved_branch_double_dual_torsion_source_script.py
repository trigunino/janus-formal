from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_curved_branch_double_dual_torsion_source import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_curved_branch_double_dual_torsion_source.py"


class DeriveSVTCurvedBranchDoubleDualTorsionSourceScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_curved_branch_double_dual_torsion_source.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_double_dual_is_unique_under_filters(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["verdict"]["double_dual_source_generates_horndeski"])
        self.assertTrue(payload["verdict"]["unique_under_extended_cartan_orbifold_filters"])
        self.assertEqual(len(payload["selected_by_filters"]), 1)

    def test_not_unconditional_published_janus(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["verdict"]["requires_extended_janus_cartan_principle"])
        self.assertFalse(payload["verdict"]["source_derived_from_janus"])
        self.assertFalse(payload["verdict"]["prediction_ready"])

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_curved_branch_double_dual_torsion_source")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
