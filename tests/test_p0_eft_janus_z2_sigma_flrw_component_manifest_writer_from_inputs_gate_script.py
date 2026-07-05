import json
import tempfile
import unittest
from pathlib import Path

from janus_lab.z2_sigma_flrw_component_manifest import (
    FLRW_COMPONENT_FIELDS,
    load_active_z2sigma_flrw_component_manifest,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_component_manifest_writer_from_inputs_gate import (
    build_payload,
)


def _input_payload() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": [0.5, 1.0],
        "flrw_components_over_rho_crit0": {field: [0.0, 0.0] for field in FLRW_COMPONENT_FIELDS},
        "component_provenance": {
            field: f"active_flrw_component_derivation::{field}" for field in FLRW_COMPONENT_FIELDS
        },
    }


class P0EFTJanusZ2SigmaFLRWComponentManifestWriterFromInputsGateTests(unittest.TestCase):
    def test_missing_input_blocks_manifest_write(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                input_path=Path(tmp) / "missing.json",
                manifest_path=Path(tmp) / "flrw_components.json",
            )

        self.assertFalse(payload["input_exists"])
        self.assertFalse(payload["manifest_written"])
        self.assertFalse(payload["gate_passed"])

    def test_valid_active_inputs_write_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "flrw_component_inputs.json"
            output_path = tmpdir / "flrw_components.json"
            input_path.write_text(json.dumps(_input_payload()), encoding="utf-8")

            payload = build_payload(input_path=input_path, manifest_path=output_path)
            manifest = load_active_z2sigma_flrw_component_manifest(output_path)

        self.assertTrue(payload["input_valid"])
        self.assertTrue(payload["manifest_written"])
        self.assertTrue(payload["gate_passed"])
        self.assertIn("counterterm_p", manifest["flrw_components_over_rho_crit0"])
        self.assertFalse(manifest["archived_z4_reuse_used"])


if __name__ == "__main__":
    unittest.main()

