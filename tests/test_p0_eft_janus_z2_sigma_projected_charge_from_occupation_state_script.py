import json
import tempfile
import unittest
from pathlib import Path

from scripts.write_p0_eft_janus_z2_sigma_projected_charge_from_occupation_state import (
    build_payload,
)


def _occupation_payload():
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "explicit_state_initial_data",
        "full_no_fit_prediction_ready": False,
        "N_occ_Z2Sigma": 3.0,
        "N_occ_provenance": "declared_superselection_state_initial_data",
    }


class ProjectedChargeFromOccupationStateScriptTest(unittest.TestCase):
    def test_missing_occupation_blocks_without_writing_charge(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                occupation_path=root / "missing.json",
                source_path=root / "source.json",
                charge_path=root / "charge.json",
            )

            self.assertFalse(payload["gate_passed"])
            self.assertEqual(payload["primary_blocker"], "projected_occupation_state_inputs_json")
            self.assertFalse((root / "charge.json").exists())

    def test_valid_occupation_writes_projected_charge(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            occupation = root / "occupation.json"
            source = root / "source.json"
            charge = root / "charge.json"
            occupation.write_text(json.dumps(_occupation_payload()), encoding="utf-8")

            payload = build_payload(
                occupation_path=occupation,
                source_path=source,
                charge_path=charge,
            )

            self.assertTrue(payload["gate_passed"])
            self.assertTrue(payload["source_manifest_written"])
            self.assertTrue(payload["charge_manifest_written"])
            written = json.loads(charge.read_text(encoding="utf-8"))
            self.assertEqual(
                written["normalizations"]["projected_baryon_number_charge_Z2Sigma"],
                3.0,
            )
            self.assertFalse(written["observational_baryon_fit_used"])


if __name__ == "__main__":
    unittest.main()
