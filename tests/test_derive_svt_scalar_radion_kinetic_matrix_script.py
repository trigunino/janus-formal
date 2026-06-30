from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_scalar_radion_kinetic_matrix import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_scalar_radion_kinetic_matrix.py"


class DeriveSVTScalarRadionKineticMatrixScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_scalar_radion_kinetic_matrix.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_radion_mixing_is_included(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["basis"], ["psi_plus", "chi"])
        self.assertEqual(payload["radion"]["kinetic_entry"], "1")
        self.assertEqual(payload["radion"]["mixing_entry"], "3*Mpl2/sqrt(v)")

    def test_negative_determinant_is_not_marked_no_ghost(self) -> None:
        payload = build_payload()
        verdict = payload["verdict"]

        self.assertTrue(verdict["positive_eigenvalue_exists"])
        self.assertTrue(verdict["negative_eigenvalue_also_exists_if_det_negative"])
        self.assertFalse(verdict["full_two_field_no_ghost_proved"])
        self.assertTrue(verdict["needs_constraint_or_extra_scalar_sector"])
        self.assertFalse(payload["prediction_ready"])

    def test_supplied_low_order_matrix_keeps_indefinite_warning(self) -> None:
        payload = build_payload()
        diag = payload["supplied_low_order_diagnostics"]

        self.assertIn("-6*Mpl2", diag["k11"])
        self.assertIn("-3*Mpl2", diag["determinant"])
        self.assertIn("3*Mpl2*v^3", diag["determinant"])
        self.assertFalse(diag["positive_definite_by_sylvester"])
        self.assertTrue(diag["indefinite_if_det_negative"])

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_scalar_radion_kinetic_matrix")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
