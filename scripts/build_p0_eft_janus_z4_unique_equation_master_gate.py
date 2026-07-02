from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_unique_equation_master_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_unique_equation_master_gate.json")


def build_payload() -> dict:
    return {
        "status": "janus-z4-unique-equation-master-gate",
        "frozen_patchwork_branches_acknowledged": True,
        "master_variable_declared": True,
        "master_variable_name": "U_Z4",
        "master_operator_declared": True,
        "master_operator_name": "L_Z4",
        "master_source_declared": True,
        "master_source_name": "J_Z4",
        "master_equation_form": "L_Z4[U_Z4] = J_Z4",
        "Z4_parity_declared": True,
        "Z4_parity": "odd_master_mode",
        "boundary_or_orbifold_conditions_declared": True,
        "boundary_condition_policy": "orbifold_boundary_conditions_required_before_solution",
        "GR_limit_declared": True,
        "GR_limit_policy": "U_Z4_to_zero_recovers_GR",
        "plus_minus_reconstruction_declared": True,
        "observable_projection_declared": True,
        "master_equation_solved": False,
        "master_solution_available": False,
        "independent_deltaSlip_allowed": False,
        "independent_Doppler_allowed": False,
        "independent_Pi_allowed": False,
        "independent_minus_sector_amplitude_allowed": False,
        "rho_eff_shortcut_allowed": False,
        "direct_Cl_patch_allowed": False,
        "raw_toy_LOS_allowed": False,
        "Planck_trial_allowed": False,
        "spectra_generation_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterReconstructionGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Unique Equation Master Gate",
        "",
        f"Master equation: `{payload['master_equation_form']}`",
        f"Master variable: `{payload['master_variable_name']}`",
        f"Solved: `{payload['master_equation_solved']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
