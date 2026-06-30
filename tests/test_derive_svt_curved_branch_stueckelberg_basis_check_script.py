from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_curved_branch_stueckelberg_basis_check import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_curved_branch_stueckelberg_basis_check.py"


class DeriveSVTCurvedBranchStueckelbergBasisCheckScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_curved_branch_stueckelberg_basis_check.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_literal_lagrangian_does_not_solve_to_claimed_velocity(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["literal_dL_ddtilde_solution"], "0")
        self.assertFalse(payload["literal_matches_claimed_solution"])
        self.assertFalse(payload["verdict"]["literal_formula_solves_to_claimed_velocity"])

    def test_velocity_repair_still_does_not_match_required_delta(self) -> None:
        payload = build_payload()
        variant = payload["velocity_coupled_variant"]

        self.assertIn("22*H*a*psi", variant["solution"])
        self.assertFalse(variant["matches_required_delta"])
        self.assertFalse(payload["verdict"]["velocity_variant_matches_required_delta"])
        self.assertFalse(payload["verdict"]["prediction_ready"])

    def test_shifted_action_candidate_is_evaluated(self) -> None:
        payload = build_payload()
        candidate = payload["shifted_action_candidate"]

        self.assertIn("B_p_solution", candidate)
        self.assertIn("dtilde_solution", candidate)
        self.assertIn("normalized_deltaN", candidate)
        self.assertEqual(
            payload["verdict"]["shifted_action_candidate_matches_required_delta"],
            candidate["matches_required_delta"],
        )
        self.assertFalse(payload["verdict"]["prediction_ready"])

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_curved_branch_stueckelberg_basis_check")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
