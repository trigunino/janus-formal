from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_background_branch_classifier import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_background_branch_classifier.py"


class DeriveSVTBackgroundBranchClassifierScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_background_branch_classifier.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_witnesses_classify_minkowski_vs_curved_branch(self) -> None:
        payload = build_payload()
        witnesses = payload["witnesses"]

        self.assertEqual(witnesses["old_T30_v1_m1_Mpl4"]["branch"], "curved_background")
        self.assertEqual(witnesses["old_T30_v1_m1_Mpl4"]["tensor_stability_margin"], "2")
        self.assertEqual(witnesses["minkowski_T6_v1_m1_Mpl4"]["branch"], "minkowski")
        self.assertEqual(witnesses["minkowski_T6_v1_m1_Mpl4"]["tensor_stability_margin"], "-22")
        self.assertEqual(witnesses["weak_mHR_T06_v1_m01_Mpl4"]["tensor_stability_margin"], "-11/5")

    def test_prediction_ready_remains_false_for_curved_branch(self) -> None:
        payload = build_payload()
        verdict = payload["verdict"]

        self.assertTrue(verdict["T30_is_tensor_stable"])
        self.assertFalse(verdict["T30_is_minkowski"])
        self.assertTrue(verdict["T6_is_minkowski"])
        self.assertFalse(verdict["T6_is_tensor_stable"])
        self.assertFalse(verdict["prediction_ready"])

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_background_branch_classifier")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
