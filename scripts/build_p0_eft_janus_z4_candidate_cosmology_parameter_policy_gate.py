from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_candidate_cosmology_parameter_policy_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_candidate_cosmology_parameter_policy_gate.json")
TRIAL_JSON = Path("outputs/reports/p0_eft_janus_z4_closed_boltzmann_candidate_highl_decomposition_trial.json")
BOUNDARY_JSON = Path("outputs/reports/p0_eft_janus_z4_boundary_safe_nuisance_profiling_gate.json")

COSMOLOGY_PARAMETERS = ("omega_b", "omega_cdm", "theta_s_or_H0", "tau", "A_s", "n_s")


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload() -> dict:
    trial = _load(TRIAL_JSON)
    boundary = _load(BOUNDARY_JSON)
    cosmology_fixed = {name: True for name in COSMOLOGY_PARAMETERS}
    return {
        "status": "janus-z4-candidate-cosmology-parameter-policy-gate",
        "source_trial": str(TRIAL_JSON),
        "source_boundary_safe": str(BOUNDARY_JSON),
        "backend": trial.get("backend"),
        "backend_uses_static_spectra_tables": True,
        "cosmological_transfer_regeneration_available": False,
        "cosmology_parameters_fixed": cosmology_fixed,
        "standard_cosmology_profiled": False,
        "nuisance_foreground_profiled_locally": bool(boundary.get("boundary_safe_local_profiled_candidate")),
        "lambda_T": trial.get("lambda_T"),
        "lambda_E": trial.get("lambda_E"),
        "lambda_policy": "frozen_from_candidate_spec_after_internal_trials",
        "lambda_frozen": trial.get("lambda_T") == -8.0e-3 and trial.get("lambda_E") == -2.0e-2,
        "no_new_physics": bool(trial.get("no_new_z4_physics")),
        "no_lambda_retuning": bool(trial.get("no_parameter_retuning")),
        "boundary_safe_local_profiled_candidate": bool(boundary.get("boundary_safe_local_profiled_candidate")),
        "joint_cosmology_nuisance_z4_fit_performed": False,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
        "policy_gate_passed": bool(
            boundary.get("boundary_safe_local_profiled_candidate")
            and trial.get("lambda_T") == -8.0e-3
            and trial.get("lambda_E") == -2.0e-2
            and trial.get("no_new_z4_physics")
            and trial.get("no_parameter_retuning")
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Candidate Cosmology Parameter Policy Gate",
        "",
        f"Gate passed: `{payload['policy_gate_passed']}`",
        f"Backend uses static spectra tables: `{payload['backend_uses_static_spectra_tables']}`",
        f"Cosmological transfer regeneration available: `{payload['cosmological_transfer_regeneration_available']}`",
        f"Lambda policy: `{payload['lambda_policy']}`",
        f"Profiled Planck candidate: `{payload['profiled_planck_candidate']}`",
        f"Full Planck validation: `{payload['full_planck_validation']}`",
        "",
        "Standard cosmological parameters are fixed in the current spectra-table backend.",
        "A local cosmology profiling trial is blocked until a regenerating CAMB/Z4 backend exists.",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
