from __future__ import annotations

from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "build_p0_modified_friedmann_minisuperspace.py"


class P0ModifiedFriedmannMinisuperspaceScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "p0_modified_friedmann_minisuperspace.json")
                .read_text(encoding="utf-8")
            )

    def test_hr_polynomials_are_encoded(self) -> None:
        payload = self.run_script_payload()
        polys = payload["hr_polynomials"]

        self.assertEqual(polys["x0"], "v*N_minus/N_plus")
        self.assertEqual(polys["r"], "a_minus/a_plus")
        self.assertEqual(polys["e1"], "x0 + 3*r")
        self.assertEqual(polys["e2"], "3*x0*r + 3*r^2")
        self.assertEqual(polys["e3"], "3*x0*r^2 + r^3")
        self.assertIn("3*x0", polys["U_HR_expanded"])

    def test_friedmann_gate_is_closed_but_observables_are_not(self) -> None:
        payload = self.run_script_payload()

        self.assertTrue(payload["micro_theory_ready"])
        self.assertTrue(payload["flrw_gate_closed"])
        self.assertFalse(payload["observable_prediction_ready"])
        self.assertEqual(
            payload["next_gate"],
            "derive_effective_dark_sector_map_from_flrw_sources",
        )

    def test_sample_witness_matches_full_hr_potential(self) -> None:
        payload = self.run_script_payload()
        witness = payload["sample_witness"]

        self.assertEqual(witness["values"]["T_memb"], 30)
        self.assertEqual(witness["computed"]["U_HR"], "35")
        self.assertEqual(witness["computed"]["Lambda_eff_numerator"], "170")
        self.assertEqual(witness["computed"]["H_plus_squared"], "85/6")
        self.assertEqual(witness["computed"]["H_minus_squared"], "85/6")


if __name__ == "__main__":
    unittest.main()
