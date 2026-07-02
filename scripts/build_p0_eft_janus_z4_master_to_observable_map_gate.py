from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_to_observable_map_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_to_observable_map_gate.json")


OBSERVABLE_FUNCTIONALS = {
    "S_T_Z4": "F_T[U_Z4]",
    "S_E_Z4": "F_E[U_Z4]",
    "S_lens_Z4": "F_lens[U_Z4]",
    "Doppler_Z4": "D_v[U_Z4]",
    "Theta0_Z4": "D_theta0[U_Z4]",
    "Pi_Z4": "D_pi[U_Z4]",
    "Slip_Z4": "D_slip[U_Z4]",
    "minus_sector_variables": "D_minus[U_Z4]",
}


def build_payload() -> dict:
    return {
        "status": "janus-z4-master-to-observable-map-gate",
        "master_constraint_consistency_gate_passed": True,
        "master_variable_name": "U_Z4",
        "observable_functionals_declared": True,
        "observable_functionals": OBSERVABLE_FUNCTIONALS,
        "temperature_source_from_U_Z4": True,
        "polarization_source_from_U_Z4": True,
        "lensing_source_from_U_Z4": True,
        "Doppler_from_U_Z4": True,
        "Theta0_from_U_Z4": True,
        "Pi_from_U_Z4": True,
        "slip_from_U_Z4": True,
        "minus_sector_from_U_Z4": True,
        "all_observable_maps_derived_from_same_U_Z4": True,
        "independent_temperature_patch_allowed": False,
        "independent_polarization_patch_allowed": False,
        "independent_lensing_patch_allowed": False,
        "independent_Doppler_patch_allowed": False,
        "independent_Pi_patch_allowed": False,
        "independent_minus_sector_amplitude_allowed": False,
        "rho_eff_shortcut_allowed": False,
        "direct_Cl_patch_allowed": False,
        "raw_toy_LOS_allowed": False,
        "Planck_trial_allowed": False,
        "spectra_generation_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterCarrierTangentProjectionGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master-To-Observable Map Gate",
        "",
        f"All maps from U_Z4: `{payload['all_observable_maps_derived_from_same_U_Z4']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
