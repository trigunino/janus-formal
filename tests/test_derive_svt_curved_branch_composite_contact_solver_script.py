from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_curved_branch_composite_contact_solver import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_curved_branch_composite_contact_solver.py"


class DeriveSVTCurvedBranchCompositeContactSolverScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_curved_branch_composite_contact_solver.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_two_constant_coefficients_do_not_span_target(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["has_constant_gamma_solution"])
        self.assertFalse(payload["verdict"]["two_constant_coefficients_close_target"])
        self.assertFalse(payload["verdict"]["prediction_ready"])

    def test_candidate_limitations_are_explicit(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["verdict"]["uK_has_k_tower_after_zeta_elimination"])
        self.assertTrue(payload["verdict"]["uK_has_inverse_k_pole_after_zeta_elimination"])
        self.assertFalse(payload["verdict"]["ghy_has_k_tower"])
        self.assertFalse(payload["verdict"]["ghy_has_inverse_k_pole"])
        self.assertIn("additional independent local invariants", " ".join(payload["needed_inputs"]))

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_curved_branch_composite_contact_solver")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
