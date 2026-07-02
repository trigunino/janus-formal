from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_minus_sector_decoupling_law_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_minus_sector_decoupling_law_gate.json")


def build_payload() -> dict:
    return {
        "status": "janus-z4-minus-sector-decoupling-law-gate",
        "thermal_ratio_gate_completed": True,
        "thermal_ratio_diagnostic_only": True,
        "minus_decoupling_law_declared": False,
        "minus_visibility_function_declared": False,
        "minus_drag_epoch_declared": False,
        "minus_opacity_history_declared": False,
        "minus_recombination_solver_required": True,
        "conservation_bianchi_required": True,
        "full_action_or_microphysical_derivation_required": True,
        "free_decoupling_shift_allowed": False,
        "free_visibility_patch_allowed": False,
        "rho_eff_shortcut_allowed": False,
        "direct_Cl_patch_allowed": False,
        "raw_toy_LOS_allowed": False,
        "Planck_trial_allowed": False,
        "spectra_generation_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "derive_minus_sector_decoupling_or_archive_two_sector_CMB_route",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Minus-Sector Decoupling Law Gate",
        "",
        f"Minus decoupling law declared: `{payload['minus_decoupling_law_declared']}`",
        f"Minus recombination solver required: `{payload['minus_recombination_solver_required']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
