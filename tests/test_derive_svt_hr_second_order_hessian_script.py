from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_hr_second_order_hessian import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_hr_second_order_hessian.py"


class DeriveSVTHRSecondOrderHessianScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_hr_second_order_hessian.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_tensor_vector_and_scalar_hessians_are_projected(self) -> None:
        payload = build_payload()
        hessians = payload["projected_hessians"]

        self.assertNotEqual(hessians["tensor"], "0")
        self.assertNotEqual(hessians["vector"], "0")
        self.assertEqual(len(hessians["scalar_lapse_spatial"]), 2)
        self.assertEqual(len(hessians["scalar_lapse_spatial"][0]), 2)

    def test_scalar_constraints_remain_open(self) -> None:
        payload = build_payload()
        closure = payload["closure"]

        self.assertTrue(closure["tensor_projected_hr_hessian_closed"])
        self.assertTrue(closure["vector_projected_hr_hessian_closed"])
        self.assertTrue(closure["scalar_raw_lapse_spatial_hessian_closed"])
        self.assertFalse(closure["scalar_reduced_after_constraints_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_script_writes_report_and_declares_needed_inputs(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_hr_second_order_hessian")
        self.assertIn("lapse", " ".join(payload["needed_inputs"]))
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
