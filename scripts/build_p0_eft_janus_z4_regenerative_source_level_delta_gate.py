from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_source_level_delta_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_source_level_delta_gate.json")
Z4_DELTA_JSON = Path("outputs/reports/p0_eft_janus_z4_regenerative_z4_delta_per_cosmology_gate.json")


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _hash_payload(payload: object) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def build_payload() -> dict:
    z4_delta = _load(Z4_DELTA_JSON)
    mutation_rows = {}
    for name, row in z4_delta.get("mutation_rows", {}).items():
        source_contract = {
            "parameter": name,
            "delta_S_T_Z4": "not_derived",
            "Pi_source_Z4": "not_derived",
            "photon_polarization_hierarchy_source": "effective_only",
            "lambda_T": z4_delta.get("lambda_T"),
            "lambda_E": z4_delta.get("lambda_E"),
            "cosmology_hash_changed": row.get("cosmology_hash_changed"),
        }
        mutation_rows[name] = {
            "cosmology_hash_changed": bool(row.get("cosmology_hash_changed")),
            "effective_spectrum_delta_hash_changed": bool(row.get("z4_delta_hash_changed")),
            "source_delta_cache_key_includes_cosmology_hash": True,
            "source_delta_cache_key_includes_lambda_hash": True,
            "source_contract_hash": _hash_payload(source_contract),
            "delta_S_T_Z4_hash_changed": False,
            "Pi_source_hash_changed": False,
            "hierarchy_source_hash_changed": False,
            "source_level_delta_changed": False,
        }
    return {
        "status": "janus-z4-regenerative-source-level-delta-gate",
        "source_z4_delta_gate": str(Z4_DELTA_JSON),
        "lambda_T": z4_delta.get("lambda_T"),
        "lambda_E": z4_delta.get("lambda_E"),
        "lambda_frozen": z4_delta.get("lambda_T") == -8.0e-3 and z4_delta.get("lambda_E") == -2.0e-2,
        "no_new_physics": True,
        "no_lambda_retuning": True,
        "effective_gate_passed": bool(z4_delta.get("effective_gate_passed")),
        "mutation_rows": mutation_rows,
        "delta_S_T_Z4_regenerated_per_cosmology": False,
        "Pi_source_regenerated_per_cosmology": False,
        "photon_polarization_hierarchy_source_regenerated_per_cosmology": False,
        "source_delta_cache_key_includes_cosmology_hash": True,
        "source_delta_cache_key_includes_lambda_hash": True,
        "no_stale_source_delta_reuse": False,
        "full_source_level_z4_delta_regeneration": False,
        "local_cosmology_profiling_allowed": False,
        "strict_source_level_gate_passed": False,
        "blocked_reason": "source equations for delta_S_T_Z4 and Pi_source_Z4 are not implemented; only effective spectral deltas regenerate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Regenerative Source-Level Delta Gate",
        "",
        f"Strict source-level gate passed: `{payload['strict_source_level_gate_passed']}`",
        f"delta_S_T_Z4 regenerated: `{payload['delta_S_T_Z4_regenerated_per_cosmology']}`",
        f"Pi source regenerated: `{payload['Pi_source_regenerated_per_cosmology']}`",
        f"Local cosmology profiling allowed: `{payload['local_cosmology_profiling_allowed']}`",
        f"Blocked reason: `{payload['blocked_reason']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
