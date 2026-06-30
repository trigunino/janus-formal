from __future__ import annotations

from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "build_p0_linear_growth_early_structure_map.py"


class P0LinearGrowthEarlyStructureMapScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "p0_linear_growth_early_structure_map.json")
                .read_text(encoding="utf-8")
            )

    def test_structure_gate_closed_but_observable_not_ready(self) -> None:
        payload = self.run_script_payload()

        self.assertTrue(payload["flrw_gate_closed"])
        self.assertTrue(payload["dark_sector_gate_closed"])
        self.assertTrue(payload["structure_gate_closed"])
        self.assertFalse(payload["hubble_gate_closed"])
        self.assertFalse(payload["observable_prediction_ready"])
        self.assertIn(
            "negative-lensing divergence signature",
            payload["falsifiable_signatures_open"],
        )

    def test_growth_boost_witness_is_consistent(self) -> None:
        payload = self.run_script_payload()
        formulas = payload["sample_witness"]["formulas"]

        self.assertEqual(formulas["rho_DM_app"], "40")
        self.assertEqual(formulas["S_eff"], "42")
        self.assertEqual(formulas["growth_boost"], "21")
        self.assertEqual(formulas["collapse_time_index"], "1/21")

    def test_next_gate_and_remaining_blocks(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(
            payload["next_gate"], "derive_negative_lensing_and_primordial_gw_signatures"
        )
        self.assertEqual(payload["status"], "linear_growth_gate_closed_conditionally")


if __name__ == "__main__":
    unittest.main()
