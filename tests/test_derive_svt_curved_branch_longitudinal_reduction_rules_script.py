from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_curved_branch_longitudinal_reduction_rules import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_curved_branch_longitudinal_reduction_rules.py"


class DeriveSVTCurvedBranchLongitudinalReductionRulesScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_curved_branch_longitudinal_reduction_rules.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_normalization_map_runs_but_does_not_match_required_delta(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["verdict"]["normalization_map_applied"])
        self.assertTrue(payload["verdict"]["minimal_contact_reduction_closed"])
        self.assertFalse(payload["matches_required_delta"])
        self.assertFalse(payload["verdict"]["required_delta_derived"])
        self.assertFalse(payload["verdict"]["prediction_ready"])

    def test_residual_records_missing_curvature_contact_terms(self) -> None:
        payload = build_payload()

        self.assertIn("H", payload["residual"])
        self.assertIn("a^4", payload["residual"])
        self.assertIn("curvature-contact", " ".join(payload["needed_inputs"]))

    def test_supplied_complete_formula_is_evaluated(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["verdict"]["supplied_complete_formula_evaluated"])
        self.assertIn("normalized_complete_deltaN", payload)
        self.assertIn("complete_residual", payload)
        self.assertEqual(
            payload["verdict"]["required_delta_derived"],
            payload["complete_matches_required_delta"],
        )

    def test_revised_surface_spin_torsion_formula_is_evaluated(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["verdict"]["revised_surface_spin_torsion_formula_evaluated"])
        self.assertIn("normalized_revised_deltaN", payload)
        self.assertIn("revised_residual", payload)
        self.assertEqual(
            payload["verdict"]["required_delta_derived"],
            payload["revised_matches_required_delta"],
        )

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_curved_branch_longitudinal_reduction_rules")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
