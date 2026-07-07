import json
import tempfile
import unittest
from pathlib import Path

from scripts.write_p0_eft_janus_z2_sigma_effective_initial_state_input import (
    build_payload,
    write_outputs,
)


class EffectiveInitialStateInputScriptTests(unittest.TestCase):
    def test_valid_effective_initial_state_writes_occupation_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "projected_occupation_state_inputs.json"
            payload = build_payload(
                n_occ=7.0,
                provenance="declared_superselection_state_initial_data",
            )
            write_outputs(payload, output_path=output)
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertEqual(payload["branch"], "effective_initial_state")
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertFalse(payload["no_fit_branch_closed"])
        self.assertEqual(written["N_occ_Z2Sigma"], 7.0)

    def test_fit_or_planck_provenance_is_rejected(self):
        with self.assertRaises(ValueError):
            build_payload(n_occ=7.0, provenance="Planck fit")


if __name__ == "__main__":
    unittest.main()
