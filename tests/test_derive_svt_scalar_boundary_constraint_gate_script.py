from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_scalar_boundary_constraint_gate import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_scalar_boundary_constraint_gate.py"


class DeriveSVTScalarBoundaryConstraintGateScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_scalar_boundary_constraint_gate.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_constraint_closes_only_conditionally(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["constraint"]["residual"], "-2*Mpl2*psi_p*sqrt(v) + chi")
        self.assertFalse(payload["constraint"]["implemented_as_derived_from_action"])
        self.assertTrue(payload["gate"]["conditional_no_ghost_closed"])
        self.assertFalse(payload["gate"]["unconditional_no_ghost_closed"])
        self.assertFalse(payload["gate"]["prediction_ready"])

    def test_reduced_mode_sample_is_positive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["reduced_scalar_mode"]["sample_Mpl2_4_v_1_alpha"], "5392")
        self.assertTrue(payload["reduced_scalar_mode"]["sample_positive"])

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_scalar_boundary_constraint_gate")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
