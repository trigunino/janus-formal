from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_constraint_consistency_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_constraint_consistency_gate.json")


def build_payload() -> dict:
    checks = {
        "Bianchi_consistency": "blocked_until_master_reconstruction",
        "plus_conservation": "blocked_until_master_reconstruction",
        "minus_conservation": "blocked_until_master_reconstruction",
        "trace_free_slip_consistency": "blocked_until_master_reconstruction",
        "Doppler_continuity_consistency": "blocked_until_master_reconstruction",
        "Pi_from_multipoles": "blocked_until_master_reconstruction",
        "projection_Z4_compatibility": "blocked_until_master_reconstruction",
        "GR_limit": "blocked_until_master_reconstruction",
    }
    return {
        "status": "janus-z4-master-constraint-consistency-gate",
        "master_reconstruction_gate_passed": True,
        "constraint_checks_declared": True,
        "constraint_checks": checks,
        "all_constraints_passed": False,
        "blocked_until_master_reconstruction": True,
        "Bianchi_consistency_required": True,
        "plus_minus_conservation_required": True,
        "trace_free_slip_consistency_required": True,
        "Doppler_continuity_consistency_required": True,
        "Pi_from_multipoles_required": True,
        "projection_Z4_compatibility_required": True,
        "GR_limit_required": True,
        "independent_downstream_source_allowed": False,
        "rho_eff_shortcut_allowed": False,
        "direct_Cl_patch_allowed": False,
        "raw_toy_LOS_allowed": False,
        "Planck_trial_allowed": False,
        "spectra_generation_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterToObservableMapGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Constraint Consistency Gate",
        "",
        f"All constraints passed: `{payload['all_constraints_passed']}`",
        f"Blocked until reconstruction: `{payload['blocked_until_master_reconstruction']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
