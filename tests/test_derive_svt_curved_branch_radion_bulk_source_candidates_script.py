from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_curved_branch_radion_bulk_source_candidates import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_curved_branch_radion_bulk_source_candidates.py"


class DeriveSVTCurvedBranchRadionBulkSourceCandidatesScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_curved_branch_radion_bulk_source_candidates.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_bulk_pair_does_not_close_k4_block(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["verdict"]["bulk_pair_sufficient"])
        self.assertTrue(payload["verdict"]["requires_horndeski_boundary_completion"])
        self.assertFalse(payload["verdict"]["prediction_ready"])

    def test_completed_family_spans_target_but_is_not_source_derived(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["verdict"]["completed_family_can_span_target"])
        self.assertFalse(payload["verdict"]["source_derived_from_janus"])
        self.assertEqual(
            payload["with_boundary_completion_constant_solutions"],
            [{"bnd": "1", "eta": "1", "xi": "1"}],
        )

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_curved_branch_radion_bulk_source_candidates")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
