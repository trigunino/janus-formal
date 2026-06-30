from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_hr_membrane_primitives import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_hr_membrane_primitives.py"


class DeriveSVTHRMembranePrimitivesScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_hr_membrane_primitive_derivation.json")
                .read_text(encoding="utf-8")
            )

    def test_hr_weight_and_membrane_terms_match_expected(self) -> None:
        payload = build_payload()
        coeffs = payload["derived_coefficients"]

        self.assertEqual(payload["hr_square_root_scalar_weight"], "3*v^2 + 3*v + 1")
        self.assertTrue(payload["all_expected_matches"])
        self.assertTrue(all(payload["matches_expected"].values()))
        self.assertEqual(coeffs["scalar_beta_membrane"], "membraneTension*v")
        self.assertEqual(
            coeffs["scalar_beta_hr"],
            "Mpl2*mHR2*v*(3*v^2 + 3*v + 1)",
        )

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_hr_membrane_primitive_derivation")
        self.assertEqual(
            payload["status"],
            "hr_square_root_and_membrane_gradient_primitives_closed",
        )

    def test_still_open_scope_is_explicit(self) -> None:
        payload = build_payload()
        remaining = " ".join(payload["still_open_primitives"])

        self.assertFalse(payload["fit_used"])
        self.assertEqual(payload["free_parameters_fitted_to_data"], [])
        self.assertFalse(payload["prediction_ready"])
        self.assertIn("full HR square-root matrix variation", remaining)
        self.assertIn("GHY/Israel", remaining)
        self.assertIn("radion potential mass", remaining)

    def test_beta_line_is_declared_not_fitted(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["hr_beta_line"],
            {
                "beta1": 1,
                "beta2": 3,
                "beta3": 3,
                "beta4": 1,
                "note": "beta4 is not used by this scalar-gradient weight",
            },
        )


if __name__ == "__main__":
    unittest.main()
