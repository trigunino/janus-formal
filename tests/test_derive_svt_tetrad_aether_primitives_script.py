from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_tetrad_aether_primitives import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_tetrad_aether_primitives.py"


class DeriveSVTTetradAetherPrimitivesScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_tetrad_aether_primitive_derivation.json")
                .read_text(encoding="utf-8")
            )

    def test_tetrad_measure_is_linear_temporal_leg_not_phi_fourth(self) -> None:
        payload = build_payload()
        tetrad = payload["tetrad"]

        self.assertEqual(tetrad["background_measure"], "v")
        self.assertTrue(tetrad["linear_temporal_leg"])
        self.assertFalse(tetrad["conformal_phi_fourth_shortcut_used"])
        self.assertIn("eps*tau + v", tetrad["determinant"])

    def test_primitive_kinetic_coefficients_match_expected(self) -> None:
        payload = build_payload()
        coeffs = payload["derived_kinetic_coefficients"]

        self.assertTrue(payload["all_expected_matches"])
        self.assertTrue(all(payload["matches_expected"].values()))
        self.assertEqual(coeffs["vector_alpha_gravity"], "Mpl2*v")
        self.assertEqual(coeffs["vector_alpha_aether"], "-aetherKineticScale*v")
        self.assertEqual(coeffs["vector_alpha_cartan_aether"], "v*(Mpl2 - aetherKineticScale)")
        self.assertEqual(coeffs["scalar_alpha_cartan_aether"], "v*(Mpl2 - aetherKineticScale)")

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_tetrad_aether_primitive_derivation")
        self.assertEqual(
            payload["status"],
            "tetrad_measure_and_aether_kinetic_primitives_closed",
        )

    def test_remaining_primitives_are_explicit(self) -> None:
        payload = build_payload()
        remaining = " ".join(payload["still_open_primitives"])

        self.assertFalse(payload["prediction_ready"])
        self.assertIn("Hassan-Rosen", remaining)
        self.assertIn("GHY/Israel", remaining)
        self.assertIn("spatial curvature", remaining)


if __name__ == "__main__":
    unittest.main()
