from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_candidate_local_cosmology_profiling_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_candidate_local_cosmology_profiling_gate.json")
POLICY_JSON = Path("outputs/reports/p0_eft_janus_z4_candidate_cosmology_parameter_policy_gate.json")


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload() -> dict:
    policy = _load(POLICY_JSON)
    regeneration_available = bool(policy.get("cosmological_transfer_regeneration_available"))
    runnable = bool(policy.get("policy_gate_passed") and regeneration_available)
    return {
        "status": "janus-z4-candidate-local-cosmology-profiling-gate",
        "source_policy": str(POLICY_JSON),
        "policy_gate_passed": bool(policy.get("policy_gate_passed")),
        "same_cosmology_space_for_GR_and_candidate": True,
        "same_priors_bounds_optimizer_for_GR_and_candidate": True,
        "lambda_policy": policy.get("lambda_policy"),
        "lambda_frozen": bool(policy.get("lambda_frozen")),
        "no_new_physics": bool(policy.get("no_new_physics")),
        "cosmological_transfer_regeneration_available": regeneration_available,
        "local_cosmology_profiling_runnable": runnable,
        "local_cosmology_profiling_executed": False,
        "blocked_reason": None
        if runnable
        else "current backend consumes fixed spectra tables; it cannot regenerate spectra under omega_b/omega_cdm/H0/tau/As/ns shifts",
        "cosmology_profiled_gain": None,
        "local_cosmology_profiled_candidate": False,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
        "gate_passed": bool(runnable),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Candidate Local Cosmology Profiling Gate",
        "",
        f"Runnable: `{payload['local_cosmology_profiling_runnable']}`",
        f"Executed: `{payload['local_cosmology_profiling_executed']}`",
        f"Blocked reason: `{payload['blocked_reason']}`",
        f"Profiled Planck candidate: `{payload['profiled_planck_candidate']}`",
        f"Full Planck validation: `{payload['full_planck_validation']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
