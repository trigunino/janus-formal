from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_two_sector_boltzmann_variables_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_two_sector_boltzmann_variables_gate.json")


PLUS_VARIABLES = [
    "delta_plus",
    "theta_plus",
    "sigma_plus",
    "pressure_plus",
    "sound_speed_plus",
]
MINUS_VARIABLES = [
    "delta_minus",
    "theta_minus",
    "sigma_minus",
    "pressure_minus",
    "sound_speed_minus",
]
METRIC_VARIABLES = [
    "Phi_plus",
    "Psi_plus",
    "Phi_minus",
    "Psi_minus",
]
PROJECTION_VARIABLES = [
    "P_Z4_plus_obs",
    "coupling_matrix_M_pm",
    "sector_sign_convention",
]


def build_payload() -> dict:
    return {
        "status": "janus-z4-two-sector-boltzmann-variables-gate",
        "closed_previous_branches": {
            "early_ISW_closed_Boltzmann_no_slip_candidate": "archived_carrier_degenerate",
            "full_derived_slip_source": "archived_A_s_carrier_tangent",
            "derived_slip_surface_SW_branch": "archived_weak_after_Doppler_closure",
        },
        "plus_sector_variables": PLUS_VARIABLES,
        "minus_sector_variables": MINUS_VARIABLES,
        "metric_variables": METRIC_VARIABLES,
        "projection_variables": PROJECTION_VARIABLES,
        "plus_sector_declared": True,
        "minus_sector_declared": True,
        "metric_plus_minus_declared": True,
        "z4_projection_declared": True,
        "coupling_matrix_declared": True,
        "sign_convention_declared": True,
        "rho_eff_shortcut_forbidden": True,
        "direct_Cl_patch_forbidden": True,
        "raw_toy_LOS_forbidden": True,
        "Planck_trial_allowed": False,
        "spectra_generation_allowed": False,
        "carrier_tangent_projection_required_before_promotion": True,
        "next_required_gate": "P0EFTJanusZ4TwoSectorConservationBianchiGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Two-Sector Boltzmann Variables Gate",
        "",
        f"Plus sector declared: `{payload['plus_sector_declared']}`",
        f"Minus sector declared: `{payload['minus_sector_declared']}`",
        f"rho_eff shortcut forbidden: `{payload['rho_eff_shortcut_forbidden']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
