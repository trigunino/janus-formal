from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_reconstruction_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_reconstruction_gate.json")


RECONSTRUCTION_MAPS = {
    "Phi_plus": "blocked_until_master_reconstruction",
    "Psi_plus": "blocked_until_master_reconstruction",
    "Phi_minus": "blocked_until_master_reconstruction",
    "Psi_minus": "blocked_until_master_reconstruction",
    "delta_plus": "blocked_until_master_reconstruction",
    "theta_plus": "blocked_until_master_reconstruction",
    "sigma_plus": "blocked_until_master_reconstruction",
    "delta_minus": "blocked_until_master_reconstruction",
    "theta_minus": "blocked_until_master_reconstruction",
    "sigma_minus": "blocked_until_master_reconstruction",
    "Theta0_Z4": "blocked_until_master_reconstruction",
    "v_gamma_Z4": "blocked_until_master_reconstruction",
    "Doppler_Z4": "blocked_until_master_reconstruction",
    "Pi_Z4": "blocked_until_master_reconstruction",
    "Weyl_Z4": "blocked_until_master_reconstruction",
    "observable_projection": "blocked_until_master_reconstruction",
}


def build_payload() -> dict:
    return {
        "status": "janus-z4-master-reconstruction-gate",
        "unique_equation_master_gate_passed": True,
        "master_variable_name": "U_Z4",
        "all_reconstruction_maps_declared": True,
        "reconstruction_maps": RECONSTRUCTION_MAPS,
        "missing_maps_are_blocked_not_free": True,
        "Phi_plus_reconstruction_declared": True,
        "Psi_plus_reconstruction_declared": True,
        "Phi_minus_reconstruction_declared": True,
        "Psi_minus_reconstruction_declared": True,
        "plus_fluid_reconstruction_declared": True,
        "minus_fluid_reconstruction_declared": True,
        "Theta0_reconstruction_declared": True,
        "Doppler_reconstruction_declared": True,
        "Pi_reconstruction_declared": True,
        "Weyl_reconstruction_declared": True,
        "observable_projection_reconstruction_declared": True,
        "all_maps_derived_from_same_U_Z4": False,
        "independent_downstream_source_allowed": False,
        "free_reconstruction_coefficient_allowed": False,
        "rho_eff_shortcut_allowed": False,
        "direct_Cl_patch_allowed": False,
        "raw_toy_LOS_allowed": False,
        "Planck_trial_allowed": False,
        "spectra_generation_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterConstraintConsistencyGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Reconstruction Gate",
        "",
        f"All maps declared: `{payload['all_reconstruction_maps_declared']}`",
        f"All maps derived from same U_Z4: `{payload['all_maps_derived_from_same_U_Z4']}`",
        f"Missing maps blocked: `{payload['missing_maps_are_blocked_not_free']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
