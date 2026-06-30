from __future__ import annotations

from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "build_p0_hubble_tension_effective_map.py"


class P0HubbleTensionEffectiveMapScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "p0_hubble_tension_effective_map.json")
                .read_text(encoding="utf-8")
            )

    def test_h0_formulas_are_encoded(self) -> None:
        payload = self.run_script_payload()
        formulas = payload["formulas"]

        self.assertEqual(
            formulas["H0_app_squared"], "H_J_squared/E_ref_squared"
        )
        self.assertEqual(
            formulas["H0_split_squared"],
            "H0_late_like_squared - H0_CMB_like_squared",
        )
        self.assertEqual(
            formulas["H0_ratio_squared"],
            "H0_late_like_squared/H0_CMB_like_squared",
        )

    def test_hubble_gate_closes_but_observables_do_not(self) -> None:
        payload = self.run_script_payload()

        self.assertTrue(payload["flrw_gate_closed"])
        self.assertTrue(payload["dark_sector_gate_closed"])
        self.assertTrue(payload["hubble_gate_closed"])
        self.assertFalse(payload["observable_prediction_ready"])
        self.assertEqual(
            payload["next_gate"],
            "derive_linear_growth_and_early_structure_map",
        )

    def test_sample_witness_computes_split_without_fit(self) -> None:
        payload = self.run_script_payload()
        computed = payload["sample_witness"]["computed"]

        self.assertEqual(computed["H_J_cmb_like_squared"], "85/6")
        self.assertEqual(computed["H_J_late_like_squared"], "53/3")
        self.assertEqual(computed["H0_CMB_like_squared"], "85/12")
        self.assertEqual(computed["H0_late_like_squared"], "53/3")
        self.assertEqual(computed["H0_split_squared"], "127/12")
        self.assertEqual(computed["H0_ratio_squared"], "212/85")
        self.assertIn("same candidate-action", payload["no_ad_hoc_fit_rule"])


if __name__ == "__main__":
    unittest.main()
