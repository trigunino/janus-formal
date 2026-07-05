import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

from janus_lab.z2_sigma_active_pipeline import REQUIRED_COMPONENT_PROVENANCE, _require_active_payload
from janus_lab.z2_sigma_component_manifest import (
    Z2SigmaBAOComponentFunctions,
    Z2SigmaFLRWComponentFunctions,
    write_active_z2sigma_bao_component_manifest,
    write_active_z2sigma_bao_component_manifest_from_background_flrw_component_and_early_plasma_manifests,
    write_active_z2sigma_bao_component_manifest_from_background_flrw_and_early_plasma_manifest,
    write_active_z2sigma_bao_component_manifest_from_flrw_and_early_plasma_manifest,
)
from janus_lab.z2_sigma_background_manifest import write_active_z2sigma_background_scalar_manifest
from janus_lab.z2_sigma_early_plasma_manifest import (
    Z2SigmaEarlyPlasmaComponentFunctions,
    write_active_z2sigma_early_plasma_manifest,
)
from janus_lab.z2_sigma_flrw_component_manifest import (
    FLRW_COMPONENT_FIELDS,
    write_active_z2sigma_flrw_component_manifest,
)


def _components() -> Z2SigmaBAOComponentFunctions:
    zero = lambda x: np.zeros_like(x)
    one = lambda x: np.ones_like(x)
    return Z2SigmaBAOComponentFunctions(
        cartan_ghy_rho=zero,
        cartan_ghy_p=zero,
        holst_nieh_yan_rho=zero,
        holst_nieh_yan_p=zero,
        matter_flux_rho=zero,
        matter_flux_p=zero,
        counterterm_rho=one,
        counterterm_p=lambda x: -np.ones_like(x),
        rho_baryon_z2sigma=one,
        rho_photon_z2sigma=lambda z: 2.0 * np.ones_like(z),
        gamma_drag_z2sigma=lambda z: 100.0 * np.ones_like(z),
    )


def _provenance() -> dict[str, str]:
    return {field: f"active_gate::{field}" for field in REQUIRED_COMPONENT_PROVENANCE}


def _scalar_provenance() -> dict[str, str]:
    return {
        "H0_Z2Sigma": "active_background_scale_gate",
        "omega_k_Z2Sigma": "active_projective_curvature_gate",
        "G_Z2Sigma": "active_low_energy_gravity_convention",
    }


def _flrw_components() -> Z2SigmaFLRWComponentFunctions:
    zero = lambda x: np.zeros_like(x)
    one = lambda x: np.ones_like(x)
    return Z2SigmaFLRWComponentFunctions(
        cartan_ghy_rho=zero,
        cartan_ghy_p=zero,
        holst_nieh_yan_rho=zero,
        holst_nieh_yan_p=zero,
        matter_flux_rho=zero,
        matter_flux_p=zero,
        counterterm_rho=one,
        counterterm_p=lambda x: -np.ones_like(x),
    )


class Z2SigmaComponentManifestTests(unittest.TestCase):
    def test_writer_outputs_pipeline_compatible_active_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "bao_component_inputs.json"
            write_active_z2sigma_bao_component_manifest(
                path,
                a_grid=[0.5, 1.0],
                z_grid=[0.0, 1.0, 2.0],
                h0_z2sigma_km_s_mpc=70.0,
                omega_k_z2sigma=0.0,
                z_d_bracket=(0.5, 1.5),
                z_max=2.0,
                components=_components(),
                component_provenance=_provenance(),
                scalar_provenance=_scalar_provenance(),
            )

            payload = json.loads(path.read_text(encoding="utf-8"))
            self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
            self.assertEqual(payload["source"], "active_derived")
            self.assertFalse(payload["compressed_planck_lcdm_rd_used"])
            self.assertFalse(payload["archived_z4_reuse_used"])
            self.assertIn("counterterm_rho", payload["flrw_components_over_rho_crit0"])
            self.assertIn("Gamma_drag_Z2Sigma", payload["early_plasma"])
            self.assertIn("kappa_rho_crit0_Z2Sigma_SI", payload["critical_normalization"])
            self.assertEqual(_require_active_payload(path)["active_core"], "Z2_tunnel_Sigma")

    def test_writer_allows_pipeline_derived_drag_epoch_bracket(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "bao_component_inputs.json"
            write_active_z2sigma_bao_component_manifest(
                path,
                a_grid=[0.5, 1.0],
                z_grid=[0.0, 1.0, 2.0],
                h0_z2sigma_km_s_mpc=70.0,
                omega_k_z2sigma=0.0,
                z_d_bracket=None,
                z_max=2.0,
                components=_components(),
                component_provenance=_provenance(),
                scalar_provenance=_scalar_provenance(),
            )

            payload = json.loads(path.read_text(encoding="utf-8"))

        self.assertIsNone(payload["z_d_bracket"])

    def test_writer_can_merge_valid_early_plasma_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            early_path = tmpdir / "early.json"
            component_path = tmpdir / "bao_component_inputs.json"
            write_active_z2sigma_early_plasma_manifest(
                early_path,
                [0.0, 1.0, 2.0],
                Z2SigmaEarlyPlasmaComponentFunctions(
                    rho_baryon_z2sigma=lambda z: np.ones_like(z),
                    rho_photon_z2sigma=lambda z: 2.0 * np.ones_like(z),
                    gamma_drag_z2sigma=lambda z: 100.0 * np.ones_like(z),
                ),
                {
                    "rho_baryon_Z2Sigma": "active_baryon_density_gate",
                    "rho_photon_Z2Sigma": "active_photon_density_gate",
                    "Gamma_drag_Z2Sigma": "active_thomson_drag_gate",
                },
            )
            flrw_provenance = {
                field: f"active_flrw_gate::{field}"
                for field in REQUIRED_COMPONENT_PROVENANCE
                if field not in {"rho_baryon_Z2Sigma", "rho_photon_Z2Sigma", "Gamma_drag_Z2Sigma"}
            }

            write_active_z2sigma_bao_component_manifest_from_flrw_and_early_plasma_manifest(
                component_path,
                a_grid=[0.5, 1.0],
                h0_z2sigma_km_s_mpc=70.0,
                omega_k_z2sigma=0.0,
                z_max=2.0,
                flrw_components=_flrw_components(),
                flrw_component_provenance=flrw_provenance,
                scalar_provenance=_scalar_provenance(),
                early_plasma_manifest_path=early_path,
            )

            payload = _require_active_payload(component_path)

        self.assertEqual(payload["early_plasma"]["Gamma_drag_Z2Sigma"], [100.0, 100.0, 100.0])
        self.assertEqual(payload["component_provenance"]["Gamma_drag_Z2Sigma"], "active_thomson_drag_gate")

    def test_writer_can_consume_background_and_early_plasma_manifests(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            background_path = tmpdir / "background.json"
            early_path = tmpdir / "early.json"
            component_path = tmpdir / "bao_component_inputs.json"
            write_active_z2sigma_background_scalar_manifest(
                background_path,
                h0_z2sigma_km_s_mpc=70.0,
                omega_k_z2sigma=0.02,
                gravitational_constant_si_z2sigma=1.0,
                scalar_provenance={
                    "H0_Z2Sigma": "active_background_scale_gate",
                    "omega_k_Z2Sigma": "active_projective_curvature_gate",
                    "G_Z2Sigma": "active_low_energy_gravity_convention",
                },
            )
            write_active_z2sigma_early_plasma_manifest(
                early_path,
                [0.0, 1.0],
                Z2SigmaEarlyPlasmaComponentFunctions(
                    rho_baryon_z2sigma=lambda z: np.ones_like(z),
                    rho_photon_z2sigma=lambda z: 2.0 * np.ones_like(z),
                    gamma_drag_z2sigma=lambda z: 100.0 * np.ones_like(z),
                ),
                {
                    "rho_baryon_Z2Sigma": "active_baryon_density_gate",
                    "rho_photon_Z2Sigma": "active_photon_density_gate",
                    "Gamma_drag_Z2Sigma": "active_thomson_drag_gate",
                },
            )
            flrw_provenance = {
                field: f"active_flrw_gate::{field}"
                for field in REQUIRED_COMPONENT_PROVENANCE
                if field not in {"rho_baryon_Z2Sigma", "rho_photon_Z2Sigma", "Gamma_drag_Z2Sigma"}
            }

            write_active_z2sigma_bao_component_manifest_from_background_flrw_and_early_plasma_manifest(
                component_path,
                background_scalar_manifest_path=background_path,
                a_grid=[0.5, 1.0],
                z_max=2.0,
                flrw_components=_flrw_components(),
                flrw_component_provenance=flrw_provenance,
                early_plasma_manifest_path=early_path,
            )

            payload = _require_active_payload(component_path)

        self.assertEqual(payload["omega_k_Z2Sigma"], 0.02)
        self.assertIn("kappa_Z2Sigma_SI", payload["critical_normalization"])

    def test_writer_can_consume_background_flrw_component_and_early_manifests(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            background_path = tmpdir / "background.json"
            flrw_path = tmpdir / "flrw.json"
            early_path = tmpdir / "early.json"
            component_path = tmpdir / "bao_component_inputs.json"
            write_active_z2sigma_background_scalar_manifest(
                background_path,
                h0_z2sigma_km_s_mpc=70.0,
                omega_k_z2sigma=0.02,
                gravitational_constant_si_z2sigma=1.0,
                scalar_provenance=_scalar_provenance(),
            )
            write_active_z2sigma_flrw_component_manifest(
                flrw_path,
                a_grid=[0.5, 1.0],
                flrw_components_over_rho_crit0={
                    field: [0.0, 0.0] for field in FLRW_COMPONENT_FIELDS
                },
                component_provenance={
                    field: f"active_flrw_gate::{field}" for field in FLRW_COMPONENT_FIELDS
                },
            )
            write_active_z2sigma_early_plasma_manifest(
                early_path,
                [0.0, 1.0],
                Z2SigmaEarlyPlasmaComponentFunctions(
                    rho_baryon_z2sigma=lambda z: np.ones_like(z),
                    rho_photon_z2sigma=lambda z: 2.0 * np.ones_like(z),
                    gamma_drag_z2sigma=lambda z: 100.0 * np.ones_like(z),
                ),
                {
                    "rho_baryon_Z2Sigma": "active_baryon_density_gate",
                    "rho_photon_Z2Sigma": "active_photon_density_gate",
                    "Gamma_drag_Z2Sigma": "active_thomson_drag_gate",
                },
            )

            write_active_z2sigma_bao_component_manifest_from_background_flrw_component_and_early_plasma_manifests(
                component_path,
                background_scalar_manifest_path=background_path,
                flrw_component_manifest_path=flrw_path,
                early_plasma_manifest_path=early_path,
                z_max=2.0,
            )

            payload = _require_active_payload(component_path)

        self.assertEqual(payload["omega_k_Z2Sigma"], 0.02)
        self.assertEqual(payload["component_provenance"]["cartan_ghy_rho"], "active_flrw_gate::cartan_ghy_rho")
        self.assertEqual(payload["component_provenance"]["Gamma_drag_Z2Sigma"], "active_thomson_drag_gate")

    def test_writer_rejects_bad_grid_and_forbidden_provenance(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "bad.json"
            with self.assertRaises(ValueError):
                write_active_z2sigma_bao_component_manifest(
                    path,
                    a_grid=[1.0, 0.5],
                    z_grid=[0.0, 1.0],
                    h0_z2sigma_km_s_mpc=70.0,
                    omega_k_z2sigma=0.0,
                    z_d_bracket=(0.2, 0.8),
                    z_max=1.0,
                    components=_components(),
                    component_provenance=_provenance(),
                    scalar_provenance=_scalar_provenance(),
                )

            bad_provenance = _provenance()
            bad_provenance["cartan_ghy_rho"] = "Planck LCDM"
            with self.assertRaises(ValueError):
                write_active_z2sigma_bao_component_manifest(
                    path,
                    a_grid=[0.5, 1.0],
                    z_grid=[0.0, 1.0],
                    h0_z2sigma_km_s_mpc=70.0,
                    omega_k_z2sigma=0.0,
                    z_d_bracket=(0.2, 0.8),
                    z_max=1.0,
                    components=_components(),
                    component_provenance=bad_provenance,
                    scalar_provenance=_scalar_provenance(),
                )


if __name__ == "__main__":
    unittest.main()
