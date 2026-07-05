import json
import hashlib
import tempfile
import unittest
from pathlib import Path

import numpy as np

from scripts.build_p0_eft_janus_z2_sigma_bao_active_manifest_pipeline_gate import build_payload
from janus_lab.z2_sigma_active_inputs import load_active_z2sigma_bao_inputs


def _component_manifest(path: Path) -> None:
    a = np.geomspace(1.0e-5, 1.0, 512)
    z = np.geomspace(1.0, 1.0e5, 256) - 1.0
    zero_a = np.zeros_like(a)
    h_grid = 70.0 * np.sqrt(0.3 * (1.0 + z) ** 3 + 0.7)
    gamma = h_grid * (z / 1000.0)
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "H0_Z2Sigma_km_s_Mpc": 70.0,
        "omega_k_Z2Sigma": 0.01,
        "a_grid": a.tolist(),
        "z_grid": z.tolist(),
        "z_d_bracket": [100.0, 2000.0],
        "z_max": float(z[-1]),
        "flrw_components_over_rho_crit0": {
            "cartan_ghy_rho": (0.3 / a**3).tolist(),
            "cartan_ghy_p": zero_a.tolist(),
            "holst_nieh_yan_rho": zero_a.tolist(),
            "holst_nieh_yan_p": zero_a.tolist(),
            "matter_flux_rho": zero_a.tolist(),
            "matter_flux_p": zero_a.tolist(),
            "counterterm_rho": np.full_like(a, 0.7).tolist(),
            "counterterm_p": np.full_like(a, -0.7).tolist(),
        },
        "early_plasma": {
            "rho_baryon_Z2Sigma": (0.05 * (1.0 + z) ** 3).tolist(),
            "rho_photon_Z2Sigma": (5.0e-5 * (1.0 + z) ** 4).tolist(),
            "Gamma_drag_Z2Sigma": gamma.tolist(),
        },
        "component_provenance": {
            "cartan_ghy_rho": "active_Cartan_GHY_FLRW_component_gate",
            "cartan_ghy_p": "active_Cartan_GHY_FLRW_component_gate",
            "holst_nieh_yan_rho": "active_Holst_Nieh_Yan_FLRW_component_gate",
            "holst_nieh_yan_p": "active_Holst_Nieh_Yan_FLRW_component_gate",
            "matter_flux_rho": "active_matter_flux_transparency_or_flux_gate",
            "matter_flux_p": "active_matter_flux_transparency_or_flux_gate",
            "counterterm_rho": "active_counterterm_FLRW_component_gate",
            "counterterm_p": "active_counterterm_FLRW_component_gate",
            "rho_baryon_Z2Sigma": "active_photon_baryon_plasma_gate",
            "rho_photon_Z2Sigma": "active_photon_baryon_plasma_gate",
            "Gamma_drag_Z2Sigma": "active_drag_epoch_rate_gate",
        },
        "scalar_provenance": {
            "H0_Z2Sigma": "active_background_scale_gate",
            "omega_k_Z2Sigma": "active_projective_curvature_gate",
            "G_Z2Sigma": "active_low_energy_gravity_convention",
        },
    }
    path.write_text(json.dumps(payload), encoding="utf-8")


class P0EFTJanusZ2SigmaBAOActiveManifestPipelineGateTests(unittest.TestCase):
    def test_pipeline_blocks_without_component_manifest(self):
        payload = build_payload(Path("missing/component.json"), Path("missing/out.json"))

        self.assertFalse(payload["component_manifest_available"])
        self.assertFalse(payload["pipeline_executed"])
        self.assertFalse(payload["bao_input_manifest_written"])

    def test_pipeline_writes_valid_official_manifest_from_active_components(self):
        with tempfile.TemporaryDirectory() as tmp:
            component_path = Path(tmp) / "components.json"
            output_path = Path(tmp) / "bao_inputs.json"
            _component_manifest(component_path)

            payload = build_payload(component_path, output_path)
            loaded = load_active_z2sigma_bao_inputs(output_path)
            output_payload = json.loads(output_path.read_text(encoding="utf-8"))
            expected_hash = hashlib.sha256(component_path.read_bytes()).hexdigest()

        self.assertTrue(payload["pipeline_executed"])
        self.assertTrue(payload["bao_input_manifest_written"])
        self.assertEqual(payload["source_component_manifest_sha256"], expected_hash)
        self.assertEqual(loaded.omega_k_z2sigma, 0.01)
        self.assertEqual(output_payload["source_component_manifest_sha256"], expected_hash)
        self.assertGreater(loaded.z_d, 0.0)
        self.assertGreater(loaded.rd_mpc(), 0.0)

    def test_pipeline_can_derive_drag_epoch_bracket_from_active_grid(self):
        with tempfile.TemporaryDirectory() as tmp:
            component_path = Path(tmp) / "components.json"
            output_path = Path(tmp) / "bao_inputs.json"
            _component_manifest(component_path)
            payload_in = json.loads(component_path.read_text(encoding="utf-8"))
            del payload_in["z_d_bracket"]
            component_path.write_text(json.dumps(payload_in), encoding="utf-8")

            payload = build_payload(component_path, output_path)
            loaded = load_active_z2sigma_bao_inputs(output_path)

        self.assertTrue(payload["pipeline_executed"])
        self.assertGreater(loaded.z_d, 0.0)
        self.assertGreater(loaded.rd_mpc(), 0.0)

    def test_pipeline_rejects_missing_component_provenance(self):
        with tempfile.TemporaryDirectory() as tmp:
            component_path = Path(tmp) / "components.json"
            output_path = Path(tmp) / "bao_inputs.json"
            _component_manifest(component_path)
            payload = json.loads(component_path.read_text(encoding="utf-8"))
            del payload["component_provenance"]
            component_path.write_text(json.dumps(payload), encoding="utf-8")

            with self.assertRaises(ValueError):
                build_payload(component_path, output_path)


if __name__ == "__main__":
    unittest.main()
