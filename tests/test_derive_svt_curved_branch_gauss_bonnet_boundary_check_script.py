from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_curved_branch_gauss_bonnet_boundary_check import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_curved_branch_gauss_bonnet_boundary_check.py"


class DeriveSVTCurvedBranchGaussBonnetBoundaryCheckScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_curved_branch_gauss_bonnet_boundary_check.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_standard_gauss_bonnet_boundary_is_not_enough(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["gb_only_can_close_required_target"])
        self.assertFalse(payload["verdict"]["standard_lovelock_GB_boundary_sufficient"])
        self.assertTrue(payload["verdict"]["requires_beyond_GB_boundary_derivative_terms"])
        self.assertFalse(payload["verdict"]["prediction_ready"])

    def test_missing_derivative_families_are_explicit(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["standard_gauss_bonnet_boundary_families"]["D_i_K_D_i_K"])
        self.assertFalse(payload["standard_gauss_bonnet_boundary_families"]["laplacian_K_squared"])
        self.assertTrue(payload["required_gradient_families"]["needs_D_i_K_D_i_K_like_block"])
        self.assertTrue(payload["required_gradient_families"]["needs_laplacian_K_squared_like_block"])

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_curved_branch_gauss_bonnet_boundary_check")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
