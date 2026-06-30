from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_from_tetrad_connection_blocks import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_from_tetrad_connection_blocks.py"


class DeriveSVTFromTetradConnectionBlocksScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_tetrad_connection_block_derivation.json")
                .read_text(encoding="utf-8")
            )

    def test_primitive_block_expansion_matches_expected_coefficients(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["tetrad_connection_block_expansion_closed"])
        self.assertTrue(payload["linear_terms_cancel"])
        self.assertTrue(payload["all_expected_matches"])
        self.assertEqual(
            payload["derived_coefficients"]["vector_alpha"],
            "v*(Mpl2 - aetherKineticScale)",
        )
        self.assertEqual(
            payload["derived_coefficients"]["scalar_alpha"],
            "v*(Mpl2 - aetherKineticScale + 2*lambdaPhi*v)",
        )

    def test_script_writes_json_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_tetrad_connection_block_derivation")
        self.assertEqual(payload["status"], "primitive_block_eps2_expansion_closed")
        self.assertIn("quadratic_action_density", payload)

    def test_blocks_include_tetrad_connection_aether_hr_and_membrane(self) -> None:
        payload = build_payload()
        text = " ".join(
            f"{row['name']} {row['source']} {row['primitive']}"
            for row in payload["blocks"]
        )

        self.assertIn("spin-connection", text)
        self.assertIn("Aether", text)
        self.assertIn("Hassan-Rosen", text)
        self.assertIn("membrane", text)
        self.assertIn("Phi", text)

    def test_sample_witness_matches_prior_chain(self) -> None:
        witness = build_payload()["sample_witness"]["coefficients"]

        self.assertEqual(witness["vector_alpha"], "3")
        self.assertEqual(witness["vector_speed2"], "4/3")
        self.assertEqual(witness["scalar_alpha"], "5")
        self.assertEqual(witness["scalar_beta"], "62")
        self.assertEqual(witness["scalar_speed2"], "62/5")

    def test_full_nonlinear_expansion_boundary_is_explicit(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["fit_used"])
        self.assertEqual(payload["free_parameters_fitted_to_data"], [])
        self.assertFalse(payload["full_eh_hr_tensor_expansion_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertIn("full nonlinear Cartan", payload["reason_full_expansion_not_closed"])
        self.assertIn("HR square-root", payload["next_step"])


if __name__ == "__main__":
    unittest.main()
