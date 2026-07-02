from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path

import numpy as np

from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, FIELDS, generate_camb_gr_rows, provenance_manifest


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_cache_invalidation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_cache_invalidation_gate.json")

MUTATIONS = {
    "omega_b": ("ombh2", 0.02247),
    "omega_cdm": ("omch2", 0.1205),
    "H0_or_theta_s": ("H0", 67.9),
    "tau": ("tau", 0.059),
    "A_s": ("As", 2.142e-9),
    "n_s": ("ns", 0.970),
}


def _max_delta(base: list[dict[str, float]], mutated: list[dict[str, float]], field: str) -> float:
    return float(max(abs(float(a[field]) - float(b[field])) for a, b in zip(base, mutated)))


def build_payload() -> dict:
    base = CosmologyPoint()
    base_rows = generate_camb_gr_rows(base)
    base_manifest = provenance_manifest(cosmology=base)
    mutation_rows = {}
    for public_name, (attr, value) in MUTATIONS.items():
        shifted = replace(base, **{attr: value})
        rows = generate_camb_gr_rows(shifted)
        manifest = provenance_manifest(cosmology=shifted)
        deltas = {field: _max_delta(base_rows, rows, field) for field in FIELDS if field != "ell"}
        mutation_rows[public_name] = {
            "parameter_attr": attr,
            "new_value": value,
            "cosmology_hash_changed": manifest["cosmology_hash"] != base_manifest["cosmology_hash"],
            "theory_vector_hash_changed": manifest["theory_vector_hash"] != base_manifest["theory_vector_hash"],
            "source_of_spectra": manifest["source_of_spectra"],
            "max_abs_delta_by_field": deltas,
            "spectra_changed": bool(any(np.isfinite(v) and v > 0.0 for v in deltas.values())),
        }
    all_hashes_changed = all(row["cosmology_hash_changed"] and row["theory_vector_hash_changed"] for row in mutation_rows.values())
    all_spectra_changed = all(row["spectra_changed"] for row in mutation_rows.values())
    all_regenerated = all(row["source_of_spectra"] == "regenerated" for row in mutation_rows.values())
    return {
        "status": "janus-z4-regenerative-cache-invalidation-gate",
        "source_of_spectra": "regenerated",
        "base_cosmology_hash": base_manifest["cosmology_hash"],
        "base_theory_vector_hash": base_manifest["theory_vector_hash"],
        "mutation_rows": mutation_rows,
        "cosmology_hash_changes_for_all_mutations": all_hashes_changed,
        "spectra_change_for_all_mutations": all_spectra_changed,
        "no_stale_csv_reuse": all_regenerated,
        "cache_key_contains_all_cosmology_params": all_hashes_changed,
        "gate_passed": bool(all_hashes_changed and all_spectra_changed and all_regenerated),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Regenerative Cache Invalidation Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"All cosmology hashes changed: `{payload['cosmology_hash_changes_for_all_mutations']}`",
        f"All spectra changed: `{payload['spectra_change_for_all_mutations']}`",
        f"No stale CSV reuse: `{payload['no_stale_csv_reuse']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
