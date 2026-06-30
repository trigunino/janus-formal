from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_curved_branch_desitter_seed import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_curved_branch_desitter_seed.py"


class DeriveSVTCurvedBranchDesitterSeedScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_curved_branch_desitter_seed.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_background_residual_maps_to_h2(self) -> None:
        payload = build_payload()
        background = payload["background"]

        self.assertEqual(background["T30_v1_m1_Mpl4_H2"], "1/2")
        self.assertEqual(background["T6_v1_m1_Mpl4_H2"], "0")
        self.assertEqual(payload["replacements"]["measure"], "a^3")
        self.assertEqual(payload["replacements"]["k_phys2"], "k^2/a^2")

    def test_desitter_lapse_has_hubble_friction(self) -> None:
        payload = build_payload()

        self.assertIn("H*a^2*dpsi_p", payload["lapse_plus_desitter_constraint"])
        self.assertIn("a^2", payload["phi_p_minus_phi_m_from_lapse_plus"])
        self.assertFalse(payload["prediction_ready"])

    def test_script_writes_report(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_curved_branch_desitter_seed")
        self.assertFalse(payload["fit_used"])


if __name__ == "__main__":
    unittest.main()
