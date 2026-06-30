from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_scalar_aether_constraint_check import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_scalar_aether_constraint_check.py"


class DeriveSVTScalarAetherConstraintCheckScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_scalar_aether_constraint_check.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_aether_input_is_non_dynamic_but_missing_cross_terms(self) -> None:
        payload = build_payload()
        aether = payload["aether_input"]

        self.assertFalse(aether["time_derivative_of_deltaA0"])
        self.assertFalse(aether["provided_velocity_cross_terms"])
        self.assertEqual(aether["quadratic_term"], "v*k^2*deltaA0^2/2")

    def test_schur_reduction_marks_no_ghost_unclosed(self) -> None:
        payload = build_payload()
        diagnostics = payload["diagnostics"]
        verdict = payload["verdict"]

        self.assertIn("C1^2", diagnostics["K11_after_elimination"])
        self.assertTrue(diagnostics["K11_after_elimination"].startswith("-"))
        self.assertTrue(diagnostics["K11_after_elimination_is_more_negative_for_positive_v"])
        self.assertEqual(
            diagnostics["schur_correction_sign_for_positive_HAA"],
            "negative_semidefinite",
        )
        self.assertFalse(diagnostics["full_no_ghost_proved"])
        self.assertTrue(verdict["generic_positive_HAA_constraint_cannot_fix_negative_K11"])
        self.assertTrue(verdict["requires_missing_cross_terms_or_opposite_sign_HAA"])
        self.assertFalse(payload["prediction_ready"])

    def test_no_cross_case_reduces_to_previous_two_field_matrix(self) -> None:
        payload = build_payload()
        matrix = payload["no_cross_reduced_2x2"]

        self.assertEqual(matrix[0][1], "3*Mpl2/sqrt(v)")
        self.assertEqual(matrix[1][1], "1")

    def test_cartan_candidate_is_checked_on_declared_witness(self) -> None:
        payload = build_payload()
        candidate = payload["cartan_candidate"]
        sample = candidate["sample_Mpl2_4_v_1"]

        self.assertEqual(candidate["H_AA"], "-v")
        self.assertEqual(candidate["C1"], "-2*Mpl2/v^2")
        self.assertEqual(candidate["C2"], "-2*Mpl2/v^(3/2)")
        self.assertEqual(sample["k11"], "16")
        self.assertEqual(sample["k22"], "65")
        self.assertEqual(sample["determinant"], "-4736")
        self.assertFalse(candidate["sample_positive_definite"])
        self.assertFalse(
            payload["verdict"]["cartan_candidate_closes_witness_Mpl2_4_v_1"]
        )

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_scalar_aether_constraint_check")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
