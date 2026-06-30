from __future__ import annotations

from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "build_p0_cosmology_observable_program.py"


class P0CosmologyObservableProgramScriptTests(unittest.TestCase):
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
            json_path = Path(tmpdir) / "p0_cosmology_observable_program.json"
            return json.loads(json_path.read_text(encoding="utf-8"))

    def test_observable_program_is_not_overclaimed(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(
            payload["micro_theory_status"],
            "prediction_ready_true_under_source_certificate",
        )
        self.assertFalse(payload["observable_prediction_ready"])
        self.assertIn("flat FLRW minisuperspace", payload["reason_not_ready"])
        self.assertIn("no claim of resolving H0 tension yet", payload["no_claims"])

    def test_flrw_is_first_next_step(self) -> None:
        payload = self.run_script_payload()
        flrw = payload["axes"]["flrw_background"]

        self.assertEqual(
            payload["first_next_step"],
            "derive_likelihood_pipeline",
        )
        self.assertEqual(flrw["priority"], 1)
        self.assertEqual(flrw["status"], "closed_conditionally_in_minisuperspace")
        self.assertIn("Lambda_eff(T_memb,mHR2,v)", flrw["required_outputs"])

    def test_observable_axes_are_present(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(
            set(payload["axes"]),
            {
                "flrw_background",
                "dark_sector_replacement",
                "hubble_tension",
                "early_structure_jwst",
                "falsifiable_signatures",
            },
        )
        self.assertIn(
            "negative-lensing divergence signature",
            payload["axes"]["falsifiable_signatures"]["required_outputs"],
        )
        self.assertEqual(
            payload["axes"]["dark_sector_replacement"]["status"],
            "closed_conditionally_in_flrw_effective_map",
        )
        self.assertEqual(
            payload["axes"]["hubble_tension"]["status"],
            "closed_conditionally_as_inference_map",
        )
        self.assertEqual(
            payload["axes"]["early_structure_jwst"]["status"],
            "closed_conditionally_as_growth_map",
        )
        self.assertEqual(
            payload["axes"]["falsifiable_signatures"]["status"],
            "closed_conditionally_as_signature_map",
        )


if __name__ == "__main__":
    unittest.main()
