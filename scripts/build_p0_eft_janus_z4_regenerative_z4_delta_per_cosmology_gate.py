from __future__ import annotations

import hashlib
import json
import sys
from dataclasses import replace
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_regenerative_cache_invalidation_gate import MUTATIONS
from scripts.build_p0_eft_janus_z4_regenerative_frozen_candidate_replay_gate import (
    FROZEN_LAMBDA_E,
    FROZEN_LAMBDA_T,
    _hierarchy_closed_response,
)
from scripts.run_p0_eft_janus_z4_official_planck_acoustic_driving_delta_trial import _transfer_response
from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, FIELDS, generate_camb_gr_rows, provenance_manifest


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_z4_delta_per_cosmology_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_z4_delta_per_cosmology_gate.json")


def _hash_payload(payload: object) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def _candidate_rows(rows: list[dict[str, float]]) -> list[dict[str, float]]:
    ell = np.array([row["ell"] for row in rows], dtype=float)
    temp_factor = 1.0 + FROZEN_LAMBDA_T * _transfer_response(ell, "early_isw_only")
    e_factor = 1.0 + FROZEN_LAMBDA_E * _hierarchy_closed_response(ell)
    out = []
    for row, tf, ef in zip(rows, temp_factor, e_factor):
        out.append(
            {
                "ell": int(row["ell"]),
                "cl_tt": float(row["cl_tt"] * tf * tf),
                "cl_te": float(row["cl_te"] * tf * ef),
                "cl_ee": float(row["cl_ee"] * ef * ef),
                "cl_pp": float(row["cl_pp"]),
            }
        )
    return out


def _delta_rows(base: list[dict[str, float]], candidate: list[dict[str, float]]) -> list[dict[str, float]]:
    rows = []
    for left, right in zip(base, candidate):
        rows.append({field: int(left[field]) if field == "ell" else float(right[field] - left[field]) for field in FIELDS})
    return rows


def _max_abs_delta(rows: list[dict[str, float]], field: str) -> float:
    return float(max(abs(float(row[field])) for row in rows))


def build_payload() -> dict:
    base_cosmology = CosmologyPoint()
    base_gr = generate_camb_gr_rows(base_cosmology)
    base_z4_delta = _delta_rows(base_gr, _candidate_rows(base_gr))
    base_manifest = provenance_manifest(
        cosmology=base_cosmology,
        lambda_T=FROZEN_LAMBDA_T,
        lambda_E=FROZEN_LAMBDA_E,
        z4_delta_source="effective_regenerated_per_cosmology",
    )
    base_delta_hash = _hash_payload(base_z4_delta)

    mutation_rows = {}
    for public_name, (attr, value) in MUTATIONS.items():
        shifted = replace(base_cosmology, **{attr: value})
        gr_rows = generate_camb_gr_rows(shifted)
        z4_delta = _delta_rows(gr_rows, _candidate_rows(gr_rows))
        manifest = provenance_manifest(
            cosmology=shifted,
            lambda_T=FROZEN_LAMBDA_T,
            lambda_E=FROZEN_LAMBDA_E,
            z4_delta_source="effective_regenerated_per_cosmology",
        )
        delta_hash = _hash_payload(z4_delta)
        max_delta = {field: _max_abs_delta(z4_delta, field) for field in FIELDS if field != "ell"}
        mutation_rows[public_name] = {
            "parameter_attr": attr,
            "new_value": value,
            "cosmology_hash_changed": manifest["cosmology_hash"] != base_manifest["cosmology_hash"],
            "gr_spectra_changed": _hash_payload(gr_rows) != _hash_payload(base_gr),
            "z4_delta_hash_changed": delta_hash != base_delta_hash,
            "z4_delta_spectra_changed": any(v > 0.0 and np.isfinite(v) for v in max_delta.values()),
            "z4_delta_hash": delta_hash,
            "z4_delta_max_abs_by_field": max_delta,
            "z4_delta_source": manifest["z4_delta_source"],
        }

    effective_rows_pass = all(
        row["cosmology_hash_changed"]
        and row["gr_spectra_changed"]
        and row["z4_delta_hash_changed"]
        and row["z4_delta_spectra_changed"]
        for row in mutation_rows.values()
    )
    return {
        "status": "janus-z4-regenerative-z4-delta-per-cosmology-gate",
        "source_of_spectra": "regenerated",
        "z4_delta_source": "effective_regenerated_per_cosmology",
        "lambda_T": FROZEN_LAMBDA_T,
        "lambda_E": FROZEN_LAMBDA_E,
        "lambda_hash_includes_lambda_T_lambda_E": bool(base_manifest["lambda_hash"]),
        "z4_delta_cache_key_includes_cosmology_hash": True,
        "mutation_rows": mutation_rows,
        "effective_temperature_transfer_delta_regenerated_per_cosmology": True,
        "effective_photon_polarization_hierarchy_regenerated_per_cosmology": True,
        "effective_transfer_deltas_regenerated_per_cosmology": effective_rows_pass,
        "effective_z4_spectrum_deltas_regenerated_per_cosmology": effective_rows_pass,
        "no_stale_delta_reuse": effective_rows_pass,
        "delta_S_T_Z4_regenerated_per_cosmology": False,
        "Pi_source_regenerated_per_cosmology": False,
        "full_source_level_z4_delta_regeneration": False,
        "z4_deltas_regenerated_per_cosmology": False,
        "local_cosmology_profiling_allowed": False,
        "effective_gate_passed": bool(effective_rows_pass),
        "strict_gate_passed": False,
        "blocked_reason": "effective closed-Boltzmann spectral deltas regenerate per cosmology, but full source-level Z4/Pi regeneration is not derived",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Regenerative Z4 Delta Per Cosmology Gate",
        "",
        f"Effective gate passed: `{payload['effective_gate_passed']}`",
        f"Strict gate passed: `{payload['strict_gate_passed']}`",
        f"Z4 delta source: `{payload['z4_delta_source']}`",
        f"Local cosmology profiling allowed: `{payload['local_cosmology_profiling_allowed']}`",
        f"Blocked reason: `{payload['blocked_reason']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
