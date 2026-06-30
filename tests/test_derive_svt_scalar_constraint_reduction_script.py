from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_scalar_constraint_reduction import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_scalar_constraint_reduction.py"


class DeriveSVTScalarConstraintReductionScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_scalar_constraint_reduction.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_constraints_and_solutions_are_reported(self) -> None:
        payload = build_payload()

        self.assertIn("lapse_plus", payload["constraint_equations"])
        self.assertIn("shift_plus", payload["constraint_equations"])
        self.assertIn("bending", payload["constraint_equations"])
        self.assertIn("dphi_from_lapse_plus", payload["solutions"])
        self.assertIn("B_p", payload["solutions"])
        self.assertIn("B_m", payload["solutions"])
        self.assertIn("zeta_after_lapse", payload["solutions"])

    def test_lapse_compatibility_is_explicit(self) -> None:
        payload = build_payload()

        self.assertIn("psi_p", payload["lapse_compatibility_condition"])
        self.assertIn("psi_m", payload["lapse_compatibility_condition"])
        self.assertFalse(payload["prediction_ready"])

    def test_radion_canonical_mass_uses_user_specification(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["canonical_radion"]["field_definition"], "chi = deltaPhi/sqrt(v)")
        self.assertEqual(payload["canonical_radion"]["mass2"], "8*lambdaPhi*v^3")

    def test_script_writes_report_and_keeps_fit_false(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_scalar_constraint_reduction")
        self.assertFalse(payload["fit_used"])
        self.assertIn("full EH scalar quadratic action", " ".join(payload["needed_inputs"]))


if __name__ == "__main__":
    unittest.main()
