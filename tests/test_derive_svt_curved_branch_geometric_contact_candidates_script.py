from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_curved_branch_geometric_contact_candidates import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_curved_branch_geometric_contact_candidates.py"


class DeriveSVTCurvedBranchGeometricContactCandidatesScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_curved_branch_geometric_contact_candidates.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_target_requires_gradient_tower(self) -> None:
        payload = build_payload()
        terms = payload["target_terms"]

        self.assertTrue(terms["has_k2_term"])
        self.assertTrue(terms["has_k4_term"])
        self.assertTrue(terms["has_no_k_terms"])

    def test_candidate_filter_selects_aether_K_or_composite(self) -> None:
        payload = build_payload()
        verdict = payload["verdict"]

        self.assertFalse(verdict["nieh_yan_alone_sufficient"])
        self.assertFalse(verdict["radion_GHY_alone_sufficient"])
        self.assertTrue(verdict["aether_K_surface_is_best_single_candidate"])
        self.assertTrue(verdict["composite_AetherK_plus_GHY_is_best_next_test"])
        self.assertFalse(verdict["prediction_ready"])

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_curved_branch_geometric_contact_candidates")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
