from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from janus_lab.data import load_desi_bao
from janus_lab.z2_sigma_active_inputs import load_active_z2sigma_bao_inputs
from janus_lab.z2_sigma_active_pipeline import write_bao_manifest_from_active_component_manifest
from janus_lab.z2_sigma_bao import chi2_against_desi
from janus_lab.z2_sigma_bao_schema import REQUIRED_COMPONENT_PROVENANCE
from janus_lab.z2_sigma_background_manifest import write_active_z2sigma_background_scalar_manifest
from janus_lab.z2_sigma_component_manifest import (
    Z2SigmaBAOComponentFunctions,
    write_active_z2sigma_bao_component_manifest_from_background_flrw_component_and_early_plasma_manifests,
    Z2SigmaFLRWComponentFunctions,
)
from janus_lab.z2_sigma_early_plasma_manifest import (
    Z2SigmaEarlyPlasmaComponentFunctions,
    write_active_z2sigma_early_plasma_manifest,
)
from janus_lab.z2_sigma_flrw_component_manifest import write_active_z2sigma_flrw_component_manifest


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_component_to_chi2_dry_run.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_component_to_chi2_dry_run.json")


def _dry_components() -> Z2SigmaBAOComponentFunctions:
    zero_a = lambda a: np.zeros_like(a)
    return Z2SigmaBAOComponentFunctions(
        cartan_ghy_rho=lambda a: 0.3 / (a**3),
        cartan_ghy_p=zero_a,
        holst_nieh_yan_rho=zero_a,
        holst_nieh_yan_p=zero_a,
        matter_flux_rho=zero_a,
        matter_flux_p=zero_a,
        counterterm_rho=lambda a: 0.7 * np.ones_like(a),
        counterterm_p=lambda a: -0.7 * np.ones_like(a),
        rho_baryon_z2sigma=lambda z: (1.0 + z) ** 3,
        rho_photon_z2sigma=lambda z: 1.0e5 * (1.0 + z) ** 4,
        gamma_drag_z2sigma=lambda z: 3430.0 * ((1.0 + z) / 1000.0),
    )


def _dry_flrw_components() -> Z2SigmaFLRWComponentFunctions:
    direct = _dry_components()
    return Z2SigmaFLRWComponentFunctions(
        cartan_ghy_rho=direct.cartan_ghy_rho,
        cartan_ghy_p=direct.cartan_ghy_p,
        holst_nieh_yan_rho=direct.holst_nieh_yan_rho,
        holst_nieh_yan_p=direct.holst_nieh_yan_p,
        matter_flux_rho=direct.matter_flux_rho,
        matter_flux_p=direct.matter_flux_p,
        counterterm_rho=direct.counterterm_rho,
        counterterm_p=direct.counterterm_p,
    )


def _dry_early_plasma_components() -> Z2SigmaEarlyPlasmaComponentFunctions:
    direct = _dry_components()
    return Z2SigmaEarlyPlasmaComponentFunctions(
        rho_baryon_z2sigma=direct.rho_baryon_z2sigma,
        rho_photon_z2sigma=direct.rho_photon_z2sigma,
        gamma_drag_z2sigma=direct.gamma_drag_z2sigma,
    )


def build_payload() -> dict:
    provenance = {field: f"active_integration_dry_run::{field}" for field in REQUIRED_COMPONENT_PROVENANCE}
    scalar_provenance = {
        "H0_Z2Sigma": "active_integration_dry_run::H0_Z2Sigma",
        "omega_k_Z2Sigma": "active_integration_dry_run::omega_k_Z2Sigma",
        "G_Z2Sigma": "active_integration_dry_run::G_Z2Sigma",
    }
    with tempfile.TemporaryDirectory() as tmp:
        tmpdir = Path(tmp)
        background_manifest = tmpdir / "background_scalars.json"
        flrw_manifest = tmpdir / "flrw_components.json"
        early_plasma_manifest = tmpdir / "early_plasma.json"
        component_manifest = tmpdir / "bao_component_inputs.json"
        bao_manifest = tmpdir / "bao_inputs.json"
        a_grid = np.linspace(0.05, 1.0, 128)
        z_grid = np.linspace(0.0, 2000.0, 256)
        write_active_z2sigma_background_scalar_manifest(
            background_manifest,
            h0_z2sigma_km_s_mpc=70.0,
            omega_k_z2sigma=0.0,
            gravitational_constant_si_z2sigma=6.67430e-11,
            scalar_provenance=scalar_provenance,
        )
        flrw = _dry_flrw_components()
        write_active_z2sigma_flrw_component_manifest(
            flrw_manifest,
            a_grid=a_grid,
            flrw_components_over_rho_crit0={
                "cartan_ghy_rho": flrw.cartan_ghy_rho(a_grid),
                "cartan_ghy_p": flrw.cartan_ghy_p(a_grid),
                "holst_nieh_yan_rho": flrw.holst_nieh_yan_rho(a_grid),
                "holst_nieh_yan_p": flrw.holst_nieh_yan_p(a_grid),
                "matter_flux_rho": flrw.matter_flux_rho(a_grid),
                "matter_flux_p": flrw.matter_flux_p(a_grid),
                "counterterm_rho": flrw.counterterm_rho(a_grid),
                "counterterm_p": flrw.counterterm_p(a_grid),
            },
            component_provenance={
                field: source
                for field, source in provenance.items()
                if field not in {"rho_baryon_Z2Sigma", "rho_photon_Z2Sigma", "Gamma_drag_Z2Sigma"}
            },
        )
        write_active_z2sigma_early_plasma_manifest(
            early_plasma_manifest,
            z_grid,
            _dry_early_plasma_components(),
            {
                "rho_baryon_Z2Sigma": provenance["rho_baryon_Z2Sigma"],
                "rho_photon_Z2Sigma": provenance["rho_photon_Z2Sigma"],
                "Gamma_drag_Z2Sigma": provenance["Gamma_drag_Z2Sigma"],
            },
            z_d_bracket=(900.0, 1200.0),
        )
        write_active_z2sigma_bao_component_manifest_from_background_flrw_component_and_early_plasma_manifests(
            component_manifest,
            background_scalar_manifest_path=background_manifest,
            flrw_component_manifest_path=flrw_manifest,
            z_max=2000.0,
            early_plasma_manifest_path=early_plasma_manifest,
        )
        write_bao_manifest_from_active_component_manifest(component_manifest, bao_manifest)
        inputs = load_active_z2sigma_bao_inputs(bao_manifest)
        rd = inputs.rd_mpc()
        dataset = load_desi_bao()
        result = chi2_against_desi(
            dataset,
            inputs.h_z2sigma,
            rd,
            omega_k_z2sigma=inputs.omega_k_z2sigma,
        )

    return {
        "status": "janus-z2-sigma-bao-component-to-chi2-dry-run",
        "active_core": "Z2_tunnel_Sigma",
        "dry_run_only": True,
        "official_bao_evaluation": False,
        "component_manifest_writer_exercised": True,
        "strict_background_manifest_exercised": True,
        "strict_flrw_manifest_exercised": True,
        "strict_early_plasma_manifest_exercised": True,
        "strict_three_manifest_merge_exercised": True,
        "active_manifest_pipeline_exercised": True,
        "official_chi2_calculator_exercised": True,
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "temporary_outputs_only": True,
        "data_points": int(dataset.value.size),
        "rd_Z2Sigma_mpc": float(rd),
        "chi2_DESI_DR2_BAO_dry_run": float(result.chi2),
        "gate_passed": True,
        "next_required": [
            "replace_dry_components_with_active_derived_component_functions",
            "write_outputs_active_z2_sigma_bao_component_inputs_json",
            "run_active_manifest_pipeline_gate",
            "run_official_chi2_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Component-to-Chi2 Dry Run",
        "",
        f"Dry run only: `{payload['dry_run_only']}`",
        f"Official BAO evaluation: `{payload['official_bao_evaluation']}`",
        f"Component writer exercised: `{payload['component_manifest_writer_exercised']}`",
        f"Active manifest pipeline exercised: `{payload['active_manifest_pipeline_exercised']}`",
        f"Official chi2 calculator exercised: `{payload['official_chi2_calculator_exercised']}`",
        f"Dry-run chi2: `{payload['chi2_DESI_DR2_BAO_dry_run']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
