from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.derive_svt_front_closure_checks import build_payload


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_svt_front_closure_checks.py"


class DeriveSVTFrontClosureChecksScriptTests(unittest.TestCase):
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
                (Path(tmpdir) / "svt_front_closure_checks.json").read_text(
                    encoding="utf-8"
                )
            )

    def test_hr_non_diagonal_sqrt_map_is_closed_but_componentwise(self) -> None:
        payload = build_payload()
        hr = payload["hr_non_diagonal"]
        loads = hr["componentwise_projector_loads"]

        self.assertTrue(hr["sqrt_frechet_closed"])
        self.assertEqual(loads["temporal_diagonal_load"], "3*(2*v + 1)/(2*v)")
        self.assertEqual(loads["time_space_offdiag_load"], "3*(v + 2)/(v + 1)")
        self.assertEqual(loads["spatial_offdiag_load"], "9/2")
        self.assertEqual(hr["scalar_projector_weight"], "3*v^2 + 3*v + 1")
        self.assertFalse(hr["scalar_weight_valid_for_all_components"])
        self.assertTrue(hr["requires_componentwise_svt_projection"])

    def test_israel_jump_algebra_is_closed(self) -> None:
        payload = build_payload()
        israel = payload["israel_jump"]

        self.assertEqual(israel["trace_jump"], "-S_trace/(2*Mpl2)")
        self.assertEqual(israel["pure_tension_jump_component"], "T_memb*h_ab/(2*Mpl2)")
        self.assertTrue(israel["algebraic_jump_closed"])
        self.assertFalse(israel["boundary_source_selection_closed"])

    def test_radion_normalization_options_are_explicit(self) -> None:
        payload = build_payload()
        radion = payload["radion_normalization"]

        self.assertEqual(radion["double_well_prefactor_1_mass2"], "8*lambdaPhi*v^2")
        self.assertEqual(radion["double_well_prefactor_1_over_4_mass2"], "2*lambdaPhi*v^2")
        self.assertEqual(
            radion["canonical_rescale_chi_equals_2_delta_phi_mass2"],
            "2*lambdaPhi*v^2",
        )
        self.assertFalse(radion["prefactor_1_matches_current"])
        self.assertTrue(radion["prefactor_1_over_4_matches_current"])
        self.assertTrue(radion["rescale_2_matches_current"])

    def test_script_writes_report_and_keeps_prediction_false(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(payload["artifact"], "svt_front_closure_checks")
        self.assertFalse(payload["fit_used"])
        self.assertFalse(payload["prediction_ready"])


if __name__ == "__main__":
    unittest.main()
