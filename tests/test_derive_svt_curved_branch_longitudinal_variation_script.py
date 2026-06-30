from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_curved_branch_longitudinal_variation import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_curved_branch_longitudinal_variation.py"


class DeriveSVTCurvedBranchLongitudinalVariationScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_curved_branch_longitudinal_variation.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_a0_constraint_is_solved(self) -> None:
        payload = build_payload()

        self.assertIn("dzeta_A", payload["A0_solution"])
        self.assertIn("dchi", payload["A0_solution"])
        self.assertTrue(payload["verdict"]["A0_constraint_solved"])

    def test_required_delta_is_not_derived_by_this_lagrangian_alone(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["matches_required_delta"])
        self.assertFalse(payload["verdict"]["zetaA_reduction_closed"])
        self.assertFalse(payload["verdict"]["required_delta_derived"])
        self.assertFalse(payload["verdict"]["prediction_ready"])

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_curved_branch_longitudinal_variation")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
