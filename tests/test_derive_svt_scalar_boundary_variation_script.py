from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_scalar_boundary_variation import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_scalar_boundary_variation.py"


class DeriveSVTScalarBoundaryVariationScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_scalar_boundary_variation.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_zeta_variation_derives_boundary_constraint(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["variations"]["dL_dzeta"],
            "k^2*(-2*Mpl2*psi_p*v^(7/2) + chi*v^3)/v^(7/2)",
        )
        self.assertEqual(
            payload["constraint"]["from_zeta_variation"],
            "-2*Mpl2*psi_p*sqrt(v) + chi",
        )
        self.assertTrue(payload["constraint"]["matches_gate_residual"])

    def test_hr_term_is_present_but_zeta_independent(self) -> None:
        payload = build_payload()

        self.assertIn("mHR2", payload["terms"]["hr_psi"])
        self.assertEqual(payload["variations"]["d_hr_dzeta"], "0")

    def test_reduced_mode_remains_conditionally_positive(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["gate"]["variation_from_supplied_surface_density_closed"])
        self.assertFalse(payload["gate"]["surface_density_derived_from_full_cartan_ghy"])
        self.assertTrue(payload["gate"]["conditional_no_ghost_closed"])
        self.assertFalse(payload["gate"]["prediction_ready"])
        self.assertEqual(payload["reduced_scalar_mode"]["sample_Mpl2_4_v_1_alpha"], "5392")

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_scalar_boundary_variation")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
