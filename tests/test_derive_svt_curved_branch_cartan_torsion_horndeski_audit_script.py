from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_curved_branch_cartan_torsion_horndeski_audit import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_curved_branch_cartan_torsion_horndeski_audit.py"


class DeriveSVTCurvedBranchCartanTorsionHorndeskiAuditScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_curved_branch_cartan_torsion_horndeski_audit.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_minimal_cartan_does_not_force_horndeski(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["verdict"]["text_claim_valid_as_written"])
        self.assertFalse(payload["verdict"]["minimal_cartan_pure_janus_sufficient"])
        self.assertTrue(payload["verdict"]["needs_nonminimal_curvature_torsion_principle"])

    def test_next_route_is_double_dual_nonminimal(self) -> None:
        payload = build_payload()

        routes = {item["name"]: item for item in payload["viable_cartan_routes"]}
        self.assertTrue(routes["nonminimal_double_dual_curvature_torsion"]["can_force_horndeski"])
        self.assertFalse(payload["verdict"]["source_derived_from_janus"])
        self.assertFalse(payload["verdict"]["prediction_ready"])

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_curved_branch_cartan_torsion_horndeski_audit")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
