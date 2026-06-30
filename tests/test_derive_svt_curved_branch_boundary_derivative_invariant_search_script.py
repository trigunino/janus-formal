from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_curved_branch_boundary_derivative_invariant_search import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_curved_branch_boundary_derivative_invariant_search.py"


class DeriveSVTCurvedBranchBoundaryDerivativeInvariantSearchScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_curved_branch_boundary_derivative_invariant_search.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_low_order_boundary_terms_do_not_span_target(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["verdict"]["low_order_K_only_boundary_terms_sufficient"])
        self.assertTrue(payload["verdict"]["requires_spatial_derivatives_of_extrinsic_curvature"])
        self.assertFalse(payload["verdict"]["source_derived_from_janus"])
        self.assertFalse(payload["verdict"]["prediction_ready"])

    def test_derivative_extension_is_explicit(self) -> None:
        payload = build_payload()

        self.assertIn("D_i_K_D_i_K_family", payload["candidate_extension"])
        self.assertIn("laplacian_K_squared_family", payload["candidate_extension"])
        self.assertTrue(payload["verdict"]["requires_nonconstant_background_coefficients"])

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_curved_branch_boundary_derivative_invariant_search")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
