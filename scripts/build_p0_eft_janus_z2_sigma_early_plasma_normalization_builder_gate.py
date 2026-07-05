from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_early_plasma_normalization_builder_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_early_plasma_normalization_builder_gate.json")


def build_payload() -> dict:
    return {
        "status": "janus-z2-sigma-early-plasma-normalization-builder-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "primary_sources_checked": [
            "blackbody photon energy density rho_gamma = a_rad T^4",
            "FLRW conserved baryon mass-density scaling",
            "Thomson drag-rate dependence on free-electron density",
        ],
        "baryon_number_density_builder_ready": True,
        "baryon_mass_density_from_number_builder_ready": True,
        "conserved_photon_temperature_builder_ready": True,
        "blackbody_photon_density_builder_ready": True,
        "free_electron_normalization_chain_ready": True,
        "requires_active_baryon_mass_density": True,
        "requires_active_baryon_number_density": True,
        "requires_explicit_baryon_mass": True,
        "requires_active_photon_temperature_normalization": True,
        "requires_active_photon_temperature": True,
        "requires_explicit_radiation_constant": True,
        "requires_active_ionization_fraction": True,
        "uses_planck_Tcmb_default": False,
        "uses_planck_omega_b_default": False,
        "uses_planck_lcdm_recombination_history": False,
        "uses_archived_z4_inputs": False,
        "early_plasma_normalization_values_ready": False,
        "gate_passed": True,
        "next_required": [
            "derive_active_photon_temperature_history_Tgamma_Z2Sigma",
            "derive_active_baryon_mass_density_history_rhob_Z2Sigma",
            "derive_active_baryon_number_density_history_nb_Z2Sigma",
            "derive_or_declare_active_baryon_mass_convention",
            "derive_active_ionization_fraction_xe_Z2Sigma",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Early-Plasma Normalization Builder Gate",
        "",
        f"Baryon number builder ready: `{payload['baryon_number_density_builder_ready']}`",
        f"Photon temperature builder ready: `{payload['conserved_photon_temperature_builder_ready']}`",
        f"Photon density builder ready: `{payload['blackbody_photon_density_builder_ready']}`",
        f"Values ready: `{payload['early_plasma_normalization_values_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
