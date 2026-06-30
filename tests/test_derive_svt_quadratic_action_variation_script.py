from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_quadratic_action_variation import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_quadratic_action_variation.py"


class DeriveSVTQuadraticActionVariationScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_quadratic_action_variation.json")
                .read_text(encoding="utf-8")
            )

    def test_quadratic_variation_extracts_expected_coefficients(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["quadratic_variation_closed"])
        self.assertTrue(payload["all_expected_matches"])
        self.assertTrue(all(payload["matches_expected_coefficient_map"].values()))
        self.assertEqual(
            payload["derived_coefficients"]["vector_alpha"],
            "v*(Mpl2 - aetherKineticScale)",
        )
        self.assertEqual(
            payload["derived_coefficients"]["scalar_alpha"],
            "v*(Mpl2 - aetherKineticScale + 2*lambdaPhi*v)",
        )

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_quadratic_action_variation")
        self.assertEqual(payload["status"], "quadratic_action_variation_closed")
        self.assertIn("d^2 L2 / d qdot^2", payload["extraction_rule"]["alpha"])

    def test_no_fit_and_boundary_are_explicit(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["fit_used"])
        self.assertEqual(payload["free_parameters_fitted_to_data"], [])
        self.assertFalse(payload["full_nonlinear_tensor_variation_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertIn(
            "already-reduced SVT quadratic action density",
            payload["reason_full_nonlinear_tensor_variation_not_closed"],
        )

    def test_sample_witness_matches_existing_values(self) -> None:
        witness = build_payload()["sample_witness"]["coefficients"]

        self.assertEqual(witness["vector_alpha"], "3")
        self.assertEqual(witness["vector_beta"], "4")
        self.assertEqual(witness["vector_speed2"], "4/3")
        self.assertEqual(witness["scalar_alpha"], "5")
        self.assertEqual(witness["scalar_beta"], "62")
        self.assertEqual(witness["scalar_speed2"], "62/5")

    def test_terms_include_required_physics_blocks(self) -> None:
        payload = build_payload()
        sources = " ".join(row["source"] for row in payload["terms"])

        self.assertIn("Cartan EH", sources)
        self.assertIn("Aether", sources)
        self.assertIn("Hassan-Rosen", sources)
        self.assertIn("membrane", sources)


if __name__ == "__main__":
    unittest.main()
