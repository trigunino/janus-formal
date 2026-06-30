from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_remaining_primitive_fronts import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_remaining_primitive_fronts.py"


class DeriveSVTRemainingPrimitiveFrontsScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_remaining_primitive_fronts.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_hr_projector_and_ghy_induced_measure_are_derived(self) -> None:
        payload = build_payload()
        coeffs = payload["derived_coefficients"]

        self.assertEqual(
            coeffs["hr_temporal_projector_weight"],
            "3*v^2 + 3*v + 1",
        )
        self.assertEqual(
            coeffs["scalar_beta_hr_projector"],
            "Mpl2*mHR2*v*(3*v^2 + 3*v + 1)",
        )
        self.assertEqual(coeffs["ghy_israel_induced_measure"], "v")
        self.assertEqual(
            coeffs["scalar_beta_ghy_israel_induced"],
            "membraneTension*v",
        )

    def test_radion_double_well_mass_normalization_remains_open(self) -> None:
        payload = build_payload()
        coeffs = payload["derived_coefficients"]

        self.assertEqual(coeffs["radion_double_well_mass2"], "8*lambdaPhi*v^2")
        self.assertEqual(coeffs["current_radion_mass_component"], "2*lambdaPhi*v^2")
        self.assertEqual(payload["radion_mass_difference"], "6*lambdaPhi*v^2")
        self.assertFalse(
            payload["fronts"]["radion_potential_mass"][
                "mass_normalization_matches_current"
            ]
        )

    def test_scope_and_prediction_status_are_explicit(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["fit_used"])
        self.assertEqual(payload["free_parameters_fitted_to_data"], [])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(
            payload["fronts"]["hr_matrix_branch"][
                "full_non_diagonal_matrix_variation_closed"
            ]
        )
        self.assertFalse(
            payload["fronts"]["ghy_israel"]["full_extrinsic_curvature_jump_closed"]
        )

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_remaining_primitive_fronts")
        self.assertIn("radion mass normalization", payload["next_step"])


if __name__ == "__main__":
    unittest.main()
