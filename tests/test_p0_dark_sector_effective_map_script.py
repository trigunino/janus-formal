from __future__ import annotations

from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "build_p0_dark_sector_effective_map.py"


class P0DarkSectorEffectiveMapScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "p0_dark_sector_effective_map.json")
                .read_text(encoding="utf-8")
            )

    def test_effective_dark_sector_formulas_are_encoded(self) -> None:
        payload = self.run_script_payload()
        formulas = payload["formulas"]

        self.assertEqual(formulas["volume_ratio"], "(a_minus/a_plus)^3")
        self.assertEqual(formulas["rho_dm_app"], "volume_ratio*rho_minus")
        self.assertEqual(formulas["rho_de_app"], "Lambda_eff_numerator")
        self.assertEqual(formulas["rho_dark_total"], "rho_dm_app + rho_de_app")

    def test_dark_sector_gate_closes_but_observables_do_not(self) -> None:
        payload = self.run_script_payload()

        self.assertTrue(payload["micro_theory_ready"])
        self.assertTrue(payload["flrw_gate_closed"])
        self.assertTrue(payload["dark_sector_gate_closed"])
        self.assertFalse(payload["observable_prediction_ready"])
        self.assertEqual(payload["next_gate"], "derive_redshift_dependent_H0_map")

    def test_sample_witness_computes_volume_weighted_density(self) -> None:
        payload = self.run_script_payload()
        witness = payload["sample_witness"]

        self.assertEqual(witness["computed"]["volume_ratio"], "8")
        self.assertEqual(witness["computed"]["rho_dm_app"], "40")
        self.assertEqual(witness["computed"]["rho_de_app"], "170")
        self.assertEqual(witness["computed"]["rho_dark_total"], "210")
        self.assertEqual(witness["computed"]["H_plus_eff_squared"], "53/3")


if __name__ == "__main__":
    unittest.main()
