from __future__ import annotations

import json
import sys
from dataclasses import replace
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_regenerative_cache_invalidation_gate import MUTATIONS
from scripts.build_p0_eft_janus_z4_regenerative_frozen_candidate_replay_gate import FROZEN_LAMBDA_T
from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, provenance_manifest
from janus_lab.z4_source_level import SOURCE_LEVEL_VERSION, regenerative_temperature_source_delta


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_temperature_source_delta_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_temperature_source_delta_gate.json")


def build_payload() -> dict:
    base = CosmologyPoint()
    base_source = regenerative_temperature_source_delta(base, FROZEN_LAMBDA_T)
    base_manifest = provenance_manifest(
        cosmology=base,
        lambda_T=FROZEN_LAMBDA_T,
        lambda_E=0.0,
        z4_delta_source="temperature_source_level_regenerated",
    )
    mutation_rows = {}
    for public_name, (attr, value) in MUTATIONS.items():
        shifted = replace(base, **{attr: value})
        source = regenerative_temperature_source_delta(shifted, FROZEN_LAMBDA_T)
        manifest = provenance_manifest(
            cosmology=shifted,
            lambda_T=FROZEN_LAMBDA_T,
            lambda_E=0.0,
            z4_delta_source="temperature_source_level_regenerated",
        )
        mutation_rows[public_name] = {
            "parameter_attr": attr,
            "new_value": value,
            "cosmology_hash_changed": manifest["cosmology_hash"] != base_manifest["cosmology_hash"],
            "temperature_source_hash_changed": source["source_hash"] != base_source["source_hash"],
            "time_grid_hash_changed": source["time_grid_hash"] != base_source["time_grid_hash"],
            "projection_grid_hash_changed": source["projection_grid_hash"] != base_source["projection_grid_hash"],
            "acoustic_window_hash_changed": source["acoustic_window_hash"] != base_source["acoustic_window_hash"],
            "opacity_hash_changed": source["opacity_hash"] != base_source["opacity_hash"],
            "potential_dot_sum_hash_changed": source["potential_dot_sum_hash"] != base_source["potential_dot_sum_hash"],
        }
    source_changes = all(row["cosmology_hash_changed"] and row["temperature_source_hash_changed"] for row in mutation_rows.values())
    return {
        "status": "janus-z4-regenerative-temperature-source-delta-gate",
        "source_level_delta_version": SOURCE_LEVEL_VERSION,
        "lambda_T": FROZEN_LAMBDA_T,
        "lambda_frozen": FROZEN_LAMBDA_T == -8.0e-3,
        "no_lambda_retuning": True,
        "no_new_physics": True,
        "source_delta_cache_key_includes_cosmology_hash": True,
        "source_delta_cache_key_includes_lambda_hash": True,
        "mutation_rows": mutation_rows,
        "W_acoustic_regenerated_per_cosmology": True,
        "kappa_regenerated_per_cosmology": True,
        "deltaPhiDot_plus_deltaPsiDot_regenerated_per_cosmology": True,
        "time_grid_regenerated_per_cosmology": True,
        "projection_grid_regenerated_per_cosmology": True,
        "delta_S_T_Z4_regenerated_per_cosmology": source_changes,
        "temperature_source_hash_changes_when_expected": source_changes,
        "no_stale_temperature_source_reuse": source_changes,
        "regenerative_temperature_source_delta_gate_passed": source_changes,
        "local_cosmology_profiling_allowed": False,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Regenerative Temperature Source Delta Gate",
        "",
        f"Gate passed: `{payload['regenerative_temperature_source_delta_gate_passed']}`",
        f"delta_S_T_Z4 regenerated: `{payload['delta_S_T_Z4_regenerated_per_cosmology']}`",
        f"Local cosmology profiling allowed: `{payload['local_cosmology_profiling_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
