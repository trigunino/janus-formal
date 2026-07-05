import unittest
import json
import tempfile
from pathlib import Path

import numpy as np

from scripts.build_p0_eft_janus_z2_sigma_bao_scale_free_minimal_contract_gate import (
    build_payload,
)


def _component_manifest(path: Path) -> None:
    a = np.geomspace(1.0e-5, 1.0, 32)
    z = np.geomspace(1.0, 1.0e4, 32) - 1.0
    zero_a = np.zeros_like(a)
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "H0_Z2Sigma_km_s_Mpc": 70.0,
        "omega_k_Z2Sigma": 0.0,
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
            "Gamma_drag_Z2Sigma": (70.0 * (z / 1000.0)).tolist(),
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


class P0EFTJanusZ2SigmaBAOScaleFreeMinimalContractGateTests(unittest.TestCase):
    def test_minimal_contract_lists_primitive_inputs_and_blocks_until_derived(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertFalse(payload["component_manifest_available"])
        self.assertFalse(payload["component_manifest_valid"])
        self.assertTrue(payload["bibliography_checked"])
        self.assertTrue(payload["standard_distance_definitions_available"])
        self.assertTrue(payload["standard_sound_horizon_context_available"])
        self.assertTrue(payload["local_z2_sigma_derivation_required"])
        self.assertIn("E_Z2Sigma_of_z", payload["primitive_physical_inputs"])
        self.assertIn("cs_over_c_Z2Sigma_of_z", payload["primitive_physical_inputs"])
        self.assertIn("Gamma_drag_over_H0_Z2Sigma_of_z", payload["primitive_physical_inputs"])
        self.assertIn("omega_k_Z2Sigma", payload["primitive_physical_inputs"])
        self.assertTrue(payload["primitive_physical_inputs"]["E_Z2Sigma_of_z"]["builder_ready"])
        self.assertFalse(payload["primitive_physical_inputs"]["E_Z2Sigma_of_z"]["values_available"])
        self.assertTrue(payload["primitive_physical_inputs"]["cs_over_c_Z2Sigma_of_z"]["builder_ready"])
        self.assertFalse(payload["primitive_physical_inputs"]["cs_over_c_Z2Sigma_of_z"]["values_available"])
        self.assertTrue(
            payload["primitive_physical_inputs"]["Gamma_drag_over_H0_Z2Sigma_of_z"]["builder_ready"]
        )
        self.assertFalse(
            payload["primitive_physical_inputs"]["Gamma_drag_over_H0_Z2Sigma_of_z"]["values_available"]
        )
        self.assertTrue(payload["primitive_physical_inputs"]["omega_k_Z2Sigma"]["builder_ready"])
        self.assertFalse(payload["primitive_physical_inputs"]["omega_k_Z2Sigma"]["values_available"])
        self.assertFalse(payload["primitive_physical_inputs_available"])
        self.assertFalse(payload["scale_free_chi2_contract_ready"])
        self.assertFalse(payload["gate_passed"])

    def test_minimal_contract_passes_when_strict_component_manifest_exists(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "bao_component_inputs.json"
            _component_manifest(path)

            payload = build_payload(component_manifest_path=path)

        self.assertTrue(payload["component_manifest_available"])
        self.assertTrue(payload["component_manifest_valid"])
        self.assertTrue(payload["primitive_physical_inputs_available"])
        self.assertTrue(payload["scale_free_chi2_contract_ready"])
        self.assertTrue(payload["gate_passed"])

    def test_minimal_contract_forbids_compressed_or_archived_inputs(self):
        payload = build_payload()

        self.assertFalse(payload["observational_H0_fit_used"])
        self.assertFalse(payload["compressed_planck_lcdm_rd_used"])
        self.assertFalse(payload["archived_z4_reuse_used"])
        self.assertFalse(payload["phenomenological_holst_bao_scan_used"])


if __name__ == "__main__":
    unittest.main()
