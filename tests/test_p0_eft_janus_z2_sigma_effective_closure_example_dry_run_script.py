import json
import tempfile
import unittest
from pathlib import Path

from scripts.run_p0_eft_janus_z2_sigma_effective_closure_example_dry_run import (
    build_payload,
)


class JanusZ2SigmaEffectiveClosureExampleDryRunScriptTest(unittest.TestCase):
    def test_dry_run_writes_diagnostic_not_active_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            partial = tmpdir / "partial.json"
            occupation = tmpdir / "example_occupation.json"
            diagnostic = tmpdir / "diagnostic.json"
            active = tmpdir / "active_should_not_exist.json"
            partial.write_text(
                json.dumps(
                    {
                        "derived_effective_initial_data": {
                            "R_Sigma_over_ell_collar_Z2Sigma": 1.0,
                        }
                    }
                ),
                encoding="utf-8",
            )
            occupation.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "explicit_state_initial_data",
                        "full_no_fit_prediction_ready": False,
                        "N_occ_Z2Sigma": 1.0,
                        "N_occ_provenance": "example_declared_superselection_state_initial_data_not_active",
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(
                partial_path=partial,
                example_occupation_path=occupation,
                diagnostic_output_path=diagnostic,
            )
            written = json.loads(diagnostic.read_text(encoding="utf-8"))

        self.assertTrue(payload["diagnostic_effective_closure_ready"])
        self.assertFalse(payload["writes_active_manifest"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertFalse(payload["example_N_occ_is_physical_derivation"])
        self.assertFalse(active.exists())
        self.assertEqual(
            written["effective_initial_data"][
                "projected_baryon_number_charge_Z2Sigma"
            ],
            1.0,
        )


if __name__ == "__main__":
    unittest.main()
