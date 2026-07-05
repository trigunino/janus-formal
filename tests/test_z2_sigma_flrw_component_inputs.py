import json
import tempfile
import unittest
from pathlib import Path

from janus_lab.z2_sigma_flrw_component_inputs import (
    load_active_z2sigma_flrw_component_input_manifest,
)
from janus_lab.z2_sigma_flrw_component_manifest import FLRW_COMPONENT_FIELDS


def _payload() -> dict:
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


class Z2SigmaFLRWComponentInputManifestTests(unittest.TestCase):
    def test_loader_accepts_strict_active_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "flrw_component_inputs.json"
            path.write_text(json.dumps(_payload()), encoding="utf-8")

            payload = load_active_z2sigma_flrw_component_input_manifest(path)

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertIn("cartan_ghy_rho", payload["flrw_components_over_rho_crit0"])

    def test_loader_rejects_forbidden_provenance(self):
        payload = _payload()
        payload["component_provenance"]["cartan_ghy_rho"] = "Planck LCDM"
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "flrw_component_inputs.json"
            path.write_text(json.dumps(payload), encoding="utf-8")

            with self.assertRaises(ValueError):
                load_active_z2sigma_flrw_component_input_manifest(path)

    def test_loader_rejects_misaligned_component(self):
        payload = _payload()
        payload["flrw_components_over_rho_crit0"]["matter_flux_rho"] = [0.0]
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "flrw_component_inputs.json"
            path.write_text(json.dumps(payload), encoding="utf-8")

            with self.assertRaises(ValueError):
                load_active_z2sigma_flrw_component_input_manifest(path)


if __name__ == "__main__":
    unittest.main()

