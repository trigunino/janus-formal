from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_camb_z4_backend_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_camb_z4_backend_gate.json")
POLICY_JSON = Path("outputs/reports/p0_eft_janus_z4_candidate_cosmology_parameter_policy_gate.json")
TRIAL_JSON = Path("outputs/reports/p0_eft_janus_z4_closed_boltzmann_candidate_highl_decomposition_trial.json")

REQUIRED_INPUTS = (
    "omega_b",
    "omega_cdm",
    "H0_or_theta_s",
    "tau",
    "A_s",
    "n_s",
    "nuisance_vector",
    "lambda_T",
    "lambda_E",
)

REQUIRED_OUTPUTS = (
    "TT",
    "TE",
    "EE",
    "C_phi_phi",
    "lensed_TT",
    "lensed_TE",
    "lensed_EE",
)

REQUIRED_CACHE_KEYS = (
    "theory_vector_hash",
    "cosmology_hash",
    "nuisance_hash",
    "lambda_hash",
    "backend_version",
    "CAMB_version",
    "Z4_delta_version",
)


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload() -> dict:
    policy = _load(POLICY_JSON)
    trial = _load(TRIAL_JSON)
    backend_regenerative = False
    z4_deltas_regenerated_per_cosmology = False
    source_of_spectra = "csv_fixed"
    no_stale_csv_reuse = source_of_spectra == "regenerated"
    return {
        "status": "janus-z4-regenerative-camb-z4-backend-gate",
        "source_policy": str(POLICY_JSON),
        "source_trial": str(TRIAL_JSON),
        "current_backend": trial.get("backend"),
        "source_of_spectra": source_of_spectra,
        "required_inputs": list(REQUIRED_INPUTS),
        "required_outputs": list(REQUIRED_OUTPUTS),
        "required_cache_keys": list(REQUIRED_CACHE_KEYS),
        "backend_regenerative": backend_regenerative,
        "camb_gr_regenerated_per_cosmology": backend_regenerative,
        "z4_deltas_regenerated_per_cosmology": z4_deltas_regenerated_per_cosmology,
        "z4_fixed_delta_transport_declared": False,
        "no_stale_csv_reuse": no_stale_csv_reuse,
        "cache_keys_include_cosmology": False,
        "cache_keys_include_nuisance": False,
        "cache_keys_include_lambdas": False,
        "cache_keys_include_backend_versions": False,
        "lambda_T": trial.get("lambda_T"),
        "lambda_E": trial.get("lambda_E"),
        "lambda_frozen_initially": trial.get("lambda_T") == -8.0e-3 and trial.get("lambda_E") == -2.0e-2,
        "no_new_physics": bool(trial.get("no_new_z4_physics")),
        "candidate_cosmology_policy_gate_passed": bool(policy.get("policy_gate_passed")),
        "local_cosmology_profiling_allowed": False,
        "regenerative_gr_handshake_allowed": backend_regenerative,
        "frozen_candidate_replay_allowed": backend_regenerative and z4_deltas_regenerated_per_cosmology,
        "full_planck_validation": False,
        "gate_passed": bool(
            backend_regenerative
            and z4_deltas_regenerated_per_cosmology
            and no_stale_csv_reuse
            and trial.get("lambda_T") == -8.0e-3
            and trial.get("lambda_E") == -2.0e-2
            and trial.get("no_new_z4_physics")
        ),
        "blocked_reason": "current backend consumes fixed CSV spectra; it does not regenerate CAMB-GR or Z4 deltas under cosmology changes",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Regenerative CAMB/Z4 Backend Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Current backend: `{payload['current_backend']}`",
        f"Source of spectra: `{payload['source_of_spectra']}`",
        f"Backend regenerative: `{payload['backend_regenerative']}`",
        f"Z4 deltas regenerated per cosmology: `{payload['z4_deltas_regenerated_per_cosmology']}`",
        f"No stale CSV reuse: `{payload['no_stale_csv_reuse']}`",
        f"Local cosmology profiling allowed: `{payload['local_cosmology_profiling_allowed']}`",
        f"Blocked reason: `{payload['blocked_reason']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
