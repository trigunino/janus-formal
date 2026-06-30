from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_spatial_radion_primitives import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_spatial_radion_primitives.py"


class DeriveSVTSpatialRadionPrimitivesScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_spatial_radion_primitive_derivation.json")
                .read_text(encoding="utf-8")
            )

    def test_spatial_gradient_and_radion_stiffness_match_expected(self) -> None:
        payload = build_payload()
        coeffs = payload["derived_coefficients"]

        self.assertTrue(payload["all_expected_matches"])
        self.assertTrue(all(payload["matches_expected"].values()))
        self.assertEqual(coeffs["vector_beta_gravity"], "Mpl2*v")
        self.assertEqual(coeffs["scalar_beta_gravity"], "Mpl2*v")
        self.assertEqual(coeffs["scalar_alpha_radion"], "2*lambdaPhi*v^2")

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_spatial_radion_primitive_derivation")
        self.assertEqual(
            payload["status"],
            "spatial_gradient_and_radion_stiffness_primitives_closed",
        )

    def test_no_fit_and_remaining_terms_are_explicit(self) -> None:
        payload = build_payload()
        remaining = " ".join(payload["still_open_primitives"])

        self.assertFalse(payload["fit_used"])
        self.assertEqual(payload["free_parameters_fitted_to_data"], [])
        self.assertFalse(payload["prediction_ready"])
        self.assertIn("Hassan-Rosen", remaining)
        self.assertIn("GHY/Israel", remaining)
        self.assertIn("potential mass", remaining)

    def test_radion_stiffness_profile_is_background_evaluated(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["background_measure"], "v")
        self.assertIn("lambdaPhi", payload["radion_stiffness_profile"])
        self.assertEqual(payload["radion_stiffness_at_background"], "2*lambdaPhi*v^2")


if __name__ == "__main__":
    unittest.main()
