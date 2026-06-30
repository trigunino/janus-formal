from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_scalar_exact_hr_source_reduction import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_scalar_exact_hr_source_reduction.py"


class DeriveSVTScalarExactHRSourceReductionScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_scalar_exact_hr_source_reduction.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_hessian_coefficients_match_supplied_inputs(self) -> None:
        payload = build_payload()
        coeffs = payload["hessian_coefficients"]

        self.assertEqual(coeffs["H_phi_phi"], "3*(v + 1)/2")
        self.assertEqual(coeffs["H_BB"], "4*v/(v + 1)")
        self.assertEqual(coeffs["H_psi_psi"], "3*(v + 1)/v")
        self.assertEqual(coeffs["H_zeta_zeta"], "3*k^2*(v - 1)")

    def test_exact_sources_close_constraints_conditionally(self) -> None:
        payload = build_payload()
        verdict = payload["verdict"]

        self.assertTrue(verdict["hr_sources_closed"])
        self.assertTrue(verdict["shift_constraints_closed"])
        self.assertTrue(verdict["bending_generic_solution_closed"])
        self.assertTrue(verdict["lapse_difference_closed"])
        self.assertTrue(verdict["lapse_compatibility_still_required"])
        self.assertTrue(verdict["phi_sum_gauge_free"])
        self.assertFalse(payload["prediction_ready"])

    def test_lapse_shift_and_bending_solutions_are_explicit(self) -> None:
        payload = build_payload()
        solutions = payload["solutions"]

        self.assertIn("psi_p", solutions["phi_p_minus_phi_m"])
        self.assertIn("psi_m", solutions["lapse_compatibility_after_substitution"])
        self.assertIn("dpsi_p", solutions["B_p"])
        self.assertIn("dpsi_m", solutions["B_m"])
        self.assertEqual(solutions["zeta_generic"], "0")

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_scalar_exact_hr_source_reduction")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
