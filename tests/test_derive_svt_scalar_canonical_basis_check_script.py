from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_scalar_canonical_basis_check import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_scalar_canonical_basis_check.py"


class DeriveSVTScalarCanonicalBasisCheckScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_scalar_canonical_basis_check.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_invertible_basis_change_preserves_determinant_sign(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["basis_change_jacobian_det"], "1")
        self.assertEqual(
            payload["sample_Mpl2_4_v_1"]["original"]["determinant"],
            payload["sample_Mpl2_4_v_1"]["transformed"]["determinant"],
        )
        self.assertEqual(payload["sample_Mpl2_4_v_1"]["transformed"]["determinant"], "-4736")
        self.assertFalse(payload["verdict"]["proposed_basis_change_closes_no_ghost"])

    def test_proposed_shift_is_not_the_exact_diagonalizing_shift(self) -> None:
        payload = build_payload()

        self.assertIn("4*Mpl2 + 3*v^4", payload["exact_diagonalizing_shift"])
        self.assertNotEqual(
            payload["exact_diagonalizing_shift"],
            "-1/(2*Mpl2*sqrt(v))",
        )

    def test_constraint_projection_is_positive_but_conditional(self) -> None:
        payload = build_payload()
        projection = payload["cartan_constraint_projection"]

        self.assertEqual(projection["constraint"], "chi = 2*sqrt(v)*Mpl2*psi_p")
        self.assertEqual(projection["sample_Mpl2_4_v_1_alpha"], "5392")
        self.assertTrue(projection["conditional_positive_on_sample"])
        self.assertTrue(payload["verdict"]["constraint_projection_is_new_axiom_until_derived"])
        self.assertFalse(payload["verdict"]["prediction_ready"])

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_scalar_canonical_basis_check")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
