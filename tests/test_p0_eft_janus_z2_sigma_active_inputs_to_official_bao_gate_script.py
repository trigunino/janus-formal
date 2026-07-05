import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_active_inputs_to_official_bao_gate import build_payload


def _background_inputs() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "scalars": {
            "H0_Z2Sigma_km_s_Mpc": 70.0,
            "omega_k_Z2Sigma": 0.0,
            "gravitational_constant_si_Z2Sigma": 6.67430e-11,
        },
        "scalar_provenance": {
            "H0_Z2Sigma": "active_background_scale_gate",
            "omega_k_Z2Sigma": "active_projective_curvature_gate",
            "G_Z2Sigma": "active_low_energy_gravity_convention",
        },
    }


def _flrw_inputs() -> dict:
    fields = [
        "cartan_ghy_rho",
        "cartan_ghy_p",
        "holst_nieh_yan_rho",
        "holst_nieh_yan_p",
        "matter_flux_rho",
        "matter_flux_p",
        "counterterm_rho",
        "counterterm_p",
    ]
    components = {field: [0.0, 0.0, 0.0] for field in fields}
    components["cartan_ghy_rho"] = [1.0, 1.0, 1.0]
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": [1.0e-5, 1.0e-3, 1.0],
        "flrw_components_over_rho_crit0": components,
        "component_provenance": {
            field: f"active_flrw_component_derivation::{field}" for field in fields
        },
    }


def _early_inputs() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "z_grid": [100.0, 1000.0, 100000.0],
        "normalizations": {
            "rho_baryon0_Z2Sigma": 2.0,
            "photon_temperature0_Z2Sigma": 3.0,
            "radiation_constant_J_m3_K4": 4.0,
            "baryon_mass_kg": 2.0,
            "baryon_number_density0_m3_Z2Sigma": 1.0,
            "ionization_fraction_Z2Sigma": 0.5,
            "electrons_per_baryon": 0.8,
            "sigma_thomson_m2": 1.0e-40,
        },
        "normalization_provenance": {
            "rho_baryon0_Z2Sigma": "active_baryon_density_gate",
            "photon_temperature0_Z2Sigma": "active_temperature_gate",
            "radiation_constant_J_m3_K4": "explicit_radiation_constant_convention",
            "baryon_mass_kg": "explicit_baryon_mass_convention",
            "baryon_number_density0_m3_Z2Sigma": "active_baryon_number_gate",
            "ionization_fraction_Z2Sigma": "active_ionization_gate",
            "electrons_per_baryon": "active_charge_convention",
            "sigma_thomson_m2": "explicit_thomson_cross_section_convention",
        },
    }


class P0EFTJanusZ2SigmaActiveInputsToOfficialBAOGateTests(unittest.TestCase):
    def test_missing_inputs_block_official_bao(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            payload = build_payload(
                background_input_path=tmpdir / "missing_background.json",
                flrw_input_path=tmpdir / "missing_flrw.json",
                early_input_path=tmpdir / "missing_early.json",
                background_manifest_path=tmpdir / "background_scalars.json",
                flrw_manifest_path=tmpdir / "flrw_components.json",
                early_manifest_path=tmpdir / "early_plasma.json",
                component_manifest_path=tmpdir / "bao_component_inputs.json",
                bao_input_path=tmpdir / "bao_inputs.json",
            )

        self.assertFalse(payload["official_bao_evaluation"])
        self.assertFalse(payload["gate_passed"])

    def test_partial_inputs_do_not_write_intermediate_manifests(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            background = tmpdir / "background_scalar_inputs.json"
            background.write_text(json.dumps(_background_inputs()), encoding="utf-8")
            background_out = tmpdir / "background_scalars.json"
            payload = build_payload(
                background_input_path=background,
                flrw_input_path=tmpdir / "missing_flrw.json",
                early_input_path=tmpdir / "missing_early.json",
                background_manifest_path=background_out,
                flrw_manifest_path=tmpdir / "flrw_components.json",
                early_manifest_path=tmpdir / "early_plasma.json",
                component_manifest_path=tmpdir / "bao_component_inputs.json",
                bao_input_path=tmpdir / "bao_inputs.json",
            )

        self.assertFalse(payload["required_input_manifests_available"])
        self.assertFalse(payload["atomic_preflight_passed"])
        self.assertFalse(payload["background_scalar_manifest_written"])
        self.assertFalse(background_out.exists())

    def test_strict_active_inputs_block_until_counterterm_is_derived(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            background = tmpdir / "background_scalar_inputs.json"
            flrw = tmpdir / "flrw_component_inputs.json"
            early = tmpdir / "early_plasma_inputs.json"
            background.write_text(json.dumps(_background_inputs()), encoding="utf-8")
            flrw.write_text(json.dumps(_flrw_inputs()), encoding="utf-8")
            early.write_text(json.dumps(_early_inputs()), encoding="utf-8")

            payload = build_payload(
                background_input_path=background,
                flrw_input_path=flrw,
                early_input_path=early,
                background_manifest_path=tmpdir / "background_scalars.json",
                flrw_manifest_path=tmpdir / "flrw_components.json",
                early_manifest_path=tmpdir / "early_plasma.json",
                component_manifest_path=tmpdir / "bao_component_inputs.json",
                bao_input_path=tmpdir / "bao_inputs.json",
            )

        self.assertTrue(payload["required_input_manifests_available"])
        self.assertFalse(payload["counterterm_radial_reduction_ready"])
        self.assertFalse(payload["atomic_preflight_passed"])
        self.assertFalse(payload["background_scalar_manifest_written"])
        self.assertFalse(payload["flrw_component_manifest_written"])
        self.assertFalse(payload["early_plasma_manifest_written"])
        self.assertFalse(payload["bao_component_manifest_written"])
        self.assertFalse(payload["bao_input_manifest_written"])
        self.assertFalse(payload["official_bao_evaluation"])
        self.assertFalse(payload["bao_chi2_evaluated"])
        self.assertFalse(payload["gate_passed"])
        self.assertIsNone(payload["chi2_DESI_DR2_BAO"])
        self.assertEqual(
            payload["blocker"],
            "counterterm density/rho_p not derived from active Sigma radial reduction",
        )


if __name__ == "__main__":
    unittest.main()
