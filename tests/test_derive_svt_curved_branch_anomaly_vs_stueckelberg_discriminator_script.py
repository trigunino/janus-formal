from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_curved_branch_anomaly_vs_stueckelberg_discriminator import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_curved_branch_anomaly_vs_stueckelberg_discriminator.py"


class DeriveSVTCurvedBranchAnomalyVsStueckelbergDiscriminatorScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_curved_branch_anomaly_vs_stueckelberg_discriminator.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_scaling_prefers_stueckelberg_route(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["verdict"]["pure_ward_chern_anomaly_supported_by_scaling"])
        self.assertTrue(payload["verdict"]["bulk_radion_stueckelberg_supported_by_scaling"])
        self.assertFalse(payload["verdict"]["prediction_ready"])

    def test_discriminant_features_are_explicit(self) -> None:
        payload = build_payload()
        features = payload["discriminant_features"]

        self.assertFalse(features["target_has_log_a"])
        self.assertTrue(features["target_has_H2_background_terms"])
        self.assertTrue(features["target_has_H_times_k2_terms"])
        self.assertTrue(features["target_has_pure_k4_boundary_laplacian_term"])

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_curved_branch_anomaly_vs_stueckelberg_discriminator")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
