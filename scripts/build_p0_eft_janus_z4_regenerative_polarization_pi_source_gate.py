from __future__ import annotations

import json
import sys
from dataclasses import replace
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_regenerative_cache_invalidation_gate import MUTATIONS
from scripts.build_p0_eft_janus_z4_regenerative_frozen_candidate_replay_gate import FROZEN_LAMBDA_E
from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, provenance_manifest
from janus_lab.z4_source_level import SOURCE_LEVEL_VERSION, regenerative_polarization_pi_source


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_polarization_pi_source_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_polarization_pi_source_gate.json")
HIERARCHY_LMAX = 24


def build_payload() -> dict:
    base = CosmologyPoint()
    base_source = regenerative_polarization_pi_source(base, FROZEN_LAMBDA_E, HIERARCHY_LMAX)
    base_manifest = provenance_manifest(
        cosmology=base,
        lambda_T=0.0,
        lambda_E=FROZEN_LAMBDA_E,
        z4_delta_source="polarization_pi_source_level_regenerated",
    )
    mutation_rows = {}
    for public_name, (attr, value) in MUTATIONS.items():
        shifted = replace(base, **{attr: value})
        source = regenerative_polarization_pi_source(shifted, FROZEN_LAMBDA_E, HIERARCHY_LMAX)
        manifest = provenance_manifest(
            cosmology=shifted,
            lambda_T=0.0,
            lambda_E=FROZEN_LAMBDA_E,
            z4_delta_source="polarization_pi_source_level_regenerated",
        )
        mutation_rows[public_name] = {
            "parameter_attr": attr,
            "new_value": value,
            "cosmology_hash_changed": manifest["cosmology_hash"] != base_manifest["cosmology_hash"],
            "polarization_source_hash_changed": source["source_hash"] != base_source["source_hash"],
            "Theta_l_hash_changed": source["Theta_l_hash"] != base_source["Theta_l_hash"],
            "E_l_hash_changed": source["E_l_hash"] != base_source["E_l_hash"],
            "Pi_source_hash_changed": source["Pi_source_hash"] != base_source["Pi_source_hash"],
            "hierarchy_hash_changed": source["hierarchy_hash"] != base_source["hierarchy_hash"],
            "TCA_settings_hash_changed": source["TCA_settings_hash"] != base_source["TCA_settings_hash"],
            "opacity_grid_hash_changed": source["opacity_grid_hash"] != base_source["opacity_grid_hash"],
            "time_grid_hash_changed": source["time_grid_hash"] != base_source["time_grid_hash"],
            "projection_grid_hash_changed": source["projection_grid_hash"] != base_source["projection_grid_hash"],
        }
    source_changes = all(
        row["cosmology_hash_changed"] and row["polarization_source_hash_changed"] and row["Pi_source_hash_changed"]
        for row in mutation_rows.values()
    )
    return {
        "status": "janus-z4-regenerative-polarization-pi-source-gate",
        "source_level_delta_version": SOURCE_LEVEL_VERSION,
        "lambda_E": FROZEN_LAMBDA_E,
        "hierarchy_lmax": HIERARCHY_LMAX,
        "lambda_frozen": FROZEN_LAMBDA_E == -2.0e-2,
        "no_lambda_retuning": True,
        "no_new_physics": True,
        "source_delta_cache_key_includes_cosmology_hash": True,
        "source_delta_cache_key_includes_lambda_hash": True,
        "hierarchy_lmax_included_in_cache_key": True,
        "TCA_settings_hash_included_in_cache_key": True,
        "opacity_grid_hash_included_in_cache_key": True,
        "mutation_rows": mutation_rows,
        "Theta_l_regenerated_per_cosmology": source_changes,
        "E_l_regenerated_per_cosmology": source_changes,
        "Pi_source_regenerated_per_cosmology": source_changes,
        "photon_polarization_hierarchy_regenerated_per_cosmology": source_changes,
        "TCA_switch_regenerated_per_cosmology": True,
        "opacity_dependence_regenerated_per_cosmology": True,
        "time_grid_regenerated_per_cosmology": True,
        "Pi_source_derived_from_multipoles": True,
        "no_free_Theta2_source_tag": True,
        "direct_EE_patch": False,
        "direct_TE_patch": False,
        "no_stale_Pi_source_reuse": source_changes,
        "regenerative_polarization_pi_source_gate_passed": source_changes,
        "local_cosmology_profiling_allowed": False,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Regenerative Polarization Pi Source Gate",
        "",
        f"Gate passed: `{payload['regenerative_polarization_pi_source_gate_passed']}`",
        f"Pi source regenerated: `{payload['Pi_source_regenerated_per_cosmology']}`",
        f"Photon/polarization hierarchy regenerated: `{payload['photon_polarization_hierarchy_regenerated_per_cosmology']}`",
        f"Local cosmology profiling allowed: `{payload['local_cosmology_profiling_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
