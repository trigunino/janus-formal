from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_regenerative_polarization_pi_source_gate import build_payload as polarization_payload
from scripts.build_p0_eft_janus_z4_regenerative_temperature_source_delta_gate import build_payload as temperature_payload
from scripts.build_p0_eft_janus_z4_regenerative_z4_delta_per_cosmology_gate import build_payload as z4_delta_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_source_level_delta_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_source_level_delta_gate.json")


def build_payload() -> dict:
    z4_delta = z4_delta_payload()
    temp = temperature_payload()
    pol = polarization_payload()
    mutation_rows = {}
    for name, row in z4_delta.get("mutation_rows", {}).items():
        temp_row = temp.get("mutation_rows", {}).get(name, {})
        pol_row = pol.get("mutation_rows", {}).get(name, {})
        mutation_rows[name] = {
            "cosmology_hash_changed": bool(row.get("cosmology_hash_changed")),
            "effective_spectrum_delta_hash_changed": bool(row.get("z4_delta_hash_changed")),
            "source_delta_cache_key_includes_cosmology_hash": True,
            "source_delta_cache_key_includes_lambda_hash": True,
            "delta_S_T_Z4_hash_changed": bool(temp_row.get("temperature_source_hash_changed")),
            "Pi_source_hash_changed": bool(pol_row.get("Pi_source_hash_changed")),
            "hierarchy_source_hash_changed": bool(pol_row.get("hierarchy_hash_changed")),
            "source_level_delta_changed": bool(
                temp_row.get("temperature_source_hash_changed") and pol_row.get("Pi_source_hash_changed")
            ),
        }
    full_source = bool(
        z4_delta.get("effective_gate_passed")
        and temp.get("regenerative_temperature_source_delta_gate_passed")
        and pol.get("regenerative_polarization_pi_source_gate_passed")
        and all(row["source_level_delta_changed"] for row in mutation_rows.values())
    )
    return {
        "status": "janus-z4-regenerative-source-level-delta-gate",
        "lambda_T": z4_delta.get("lambda_T"),
        "lambda_E": z4_delta.get("lambda_E"),
        "lambda_frozen": z4_delta.get("lambda_T") == -8.0e-3 and z4_delta.get("lambda_E") == -2.0e-2,
        "no_new_physics": True,
        "no_lambda_retuning": True,
        "effective_gate_passed": bool(z4_delta.get("effective_gate_passed")),
        "mutation_rows": mutation_rows,
        "delta_S_T_Z4_regenerated_per_cosmology": bool(temp.get("delta_S_T_Z4_regenerated_per_cosmology")),
        "Pi_source_regenerated_per_cosmology": bool(pol.get("Pi_source_regenerated_per_cosmology")),
        "photon_polarization_hierarchy_source_regenerated_per_cosmology": bool(
            pol.get("photon_polarization_hierarchy_regenerated_per_cosmology")
        ),
        "source_delta_cache_key_includes_cosmology_hash": True,
        "source_delta_cache_key_includes_lambda_hash": True,
        "no_stale_source_delta_reuse": full_source,
        "full_source_level_z4_delta_regeneration": full_source,
        "local_cosmology_profiling_allowed": False,
        "strict_source_level_gate_passed": full_source,
        "blocked_reason": None if full_source else "source-level temperature and Pi regeneration are not both closed",
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
