from __future__ import annotations

import csv
import json
import sys
from dataclasses import replace
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_candidate_local_cosmology_profiling_gate import (
    COMBINED_CHANNELS,
    DECOMPOSED_CHANNELS,
    _total,
)
from scripts.build_p0_eft_janus_z4_regenerative_frozen_candidate_replay_gate import (
    FROZEN_LAMBDA_E,
    FROZEN_LAMBDA_T,
    _write_candidate,
)
from scripts.run_p0_eft_janus_z4_official_planck_closed_boltzmann_acoustic_polarization_trial import _run_likelihood_set
from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, FIELDS, generate_camb_gr_rows, write_spectra


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_carrier_tangent_projection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_carrier_tangent_projection_gate.json")
SPECTRA_DIR = Path("outputs/reports/z4_carrier_tangent_projection_spectra")
CHANNELS = ("cl_tt", "cl_te", "cl_ee")
PARAMETER_STEPS = {
    "omega_cdm": ("omch2", 5.0e-4),
    "omega_b": ("ombh2", 1.0e-4),
    "H0": ("H0", 0.5),
    "A_s": ("As", 4.2e-11),
    "n_s": ("ns", 5.0e-3),
    "tau": ("tau", 5.0e-3),
}


def _rows_to_arrays(rows: list[dict[str, float]]) -> dict[str, np.ndarray]:
    return {field: np.array([float(row[field]) for row in rows], dtype=float) for field in FIELDS}


def _flatten(arrays: dict[str, np.ndarray], scales: dict[str, float]) -> np.ndarray:
    return np.concatenate([arrays[channel] / scales[channel] for channel in CHANNELS])


def _unflatten(vector: np.ndarray, reference: list[dict[str, float]], scales: dict[str, float]) -> list[dict[str, float]]:
    n = len(reference)
    chunks = {}
    start = 0
    for channel in CHANNELS:
        chunks[channel] = vector[start : start + n] * scales[channel]
        start += n
    rows = []
    for i, row in enumerate(reference):
        rows.append(
            {
                "ell": int(row["ell"]),
                "cl_tt": float(row["cl_tt"] + chunks["cl_tt"][i]),
                "cl_te": float(row["cl_te"] + chunks["cl_te"][i]),
                "cl_ee": float(row["cl_ee"] + chunks["cl_ee"][i]),
                "cl_pp": float(row["cl_pp"]),
            }
        )
    return rows


def _basis_totals(like: dict) -> dict[str, float | None]:
    return {
        "combined_highl": _total(like, COMBINED_CHANNELS),
        "decomposed_highl": _total(like, DECOMPOSED_CHANNELS),
    }


def _central_tangent(parameter: str, field: str, step: float) -> tuple[list[dict[str, float]], list[dict[str, float]]]:
    base = CosmologyPoint()
    minus = replace(base, **{field: getattr(base, field) - step})
    plus = replace(base, **{field: getattr(base, field) + step})
    return generate_camb_gr_rows(minus), generate_camb_gr_rows(plus)


def build_payload(run_official: bool = False) -> dict:
    reference = generate_camb_gr_rows(CosmologyPoint())
    candidate_path = SPECTRA_DIR / "reference_z4.csv"
    baseline_path = SPECTRA_DIR / "reference_gr.csv"
    write_spectra(baseline_path, reference)
    _write_candidate(reference, FROZEN_LAMBDA_T, FROZEN_LAMBDA_E, candidate_path)

    with candidate_path.open(newline="", encoding="utf-8") as handle:
        candidate = [
            {key: (int(value) if key == "ell" else float(value)) for key, value in row.items()}
            for row in csv.DictReader(handle)
        ]

    ref_arrays = _rows_to_arrays(reference)
    cand_arrays = _rows_to_arrays(candidate)
    scales = {channel: float(np.sqrt(np.mean(np.square(ref_arrays[channel]))) or 1.0) for channel in CHANNELS}
    z4_vector = _flatten({channel: cand_arrays[channel] - ref_arrays[channel] for channel in CHANNELS}, scales)

    tangent_columns = []
    tangent_norms = {}
    for name, (field, step) in PARAMETER_STEPS.items():
        minus_rows, plus_rows = _central_tangent(name, field, step)
        minus_arrays = _rows_to_arrays(minus_rows)
        plus_arrays = _rows_to_arrays(plus_rows)
        derivative = {
            channel: (plus_arrays[channel] - minus_arrays[channel]) / (2.0 * step)
            for channel in CHANNELS
        }
        column = _flatten(derivative, scales)
        tangent_columns.append(column)
        tangent_norms[name] = float(np.linalg.norm(column))

    matrix = np.column_stack(tangent_columns)
    coefficients, *_ = np.linalg.lstsq(matrix, z4_vector, rcond=None)
    projected = matrix @ coefficients
    perpendicular = z4_vector - projected
    z4_norm_sq = float(np.dot(z4_vector, z4_vector))
    parallel_fraction = float(np.dot(projected, projected) / z4_norm_sq) if z4_norm_sq else 0.0
    perpendicular_fraction = float(np.dot(perpendicular, perpendicular) / z4_norm_sq) if z4_norm_sq else 0.0
    contributions = {
        name: float(abs(coefficients[i]) * tangent_norms[name])
        for i, name in enumerate(PARAMETER_STEPS)
    }
    dominant = max(contributions, key=contributions.get)

    orthogonal_rows = _unflatten(perpendicular, reference, scales)
    orthogonal_path = SPECTRA_DIR / "reference_z4_orthogonal_residual.csv"
    write_spectra(orthogonal_path, orthogonal_rows)

    baseline_like = _run_likelihood_set(baseline_path, run_official)
    orthogonal_like = _run_likelihood_set(orthogonal_path, run_official)
    baseline_totals = _basis_totals(baseline_like)
    orthogonal_totals = _basis_totals(orthogonal_like)
    residual_gains = {
        key: (
            float(orthogonal_totals[key] - baseline_totals[key])
            if orthogonal_totals[key] is not None and baseline_totals[key] is not None
            else None
        )
        for key in baseline_totals
    }
    residual_improves = bool(
        run_official
        and residual_gains["combined_highl"] is not None
        and residual_gains["decomposed_highl"] is not None
        and residual_gains["combined_highl"] < 0.0
        and residual_gains["decomposed_highl"] < 0.0
    )

    return {
        "status": "janus-z4-carrier-tangent-projection-gate",
        "run_official_requested": run_official,
        "lambda_T": FROZEN_LAMBDA_T,
        "lambda_E": FROZEN_LAMBDA_E,
        "lambda_frozen": True,
        "no_lambda_retuning": True,
        "no_new_physics": True,
        "channels_projected": list(CHANNELS),
        "parameter_steps": PARAMETER_STEPS,
        "baseline_spectra_path": str(baseline_path),
        "candidate_spectra_path": str(candidate_path),
        "orthogonal_residual_spectra_path": str(orthogonal_path),
        "z4_parallel_fraction_to_carrier_tangent": parallel_fraction,
        "z4_perpendicular_fraction_to_carrier_tangent": perpendicular_fraction,
        "dominant_parallel_direction": dominant,
        "tangent_coefficients": {
            name: float(coefficients[i]) for i, name in enumerate(PARAMETER_STEPS)
        },
        "tangent_contribution_scores": contributions,
        "orthogonal_residual_gain": residual_gains,
        "orthogonal_residual_improves_nonoverlap": residual_improves,
        "carrier_tangent_projection_gate_passed": True,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Carrier Tangent Projection Gate",
        "",
        f"Dominant tangent direction: `{payload['dominant_parallel_direction']}`",
        f"Parallel fraction: `{payload['z4_parallel_fraction_to_carrier_tangent']}`",
        f"Perpendicular fraction: `{payload['z4_perpendicular_fraction_to_carrier_tangent']}`",
        f"Orthogonal residual improves non-overlap: `{payload['orthogonal_residual_improves_nonoverlap']}`",
        f"Full Planck validation: `{payload['full_planck_validation']}`",
        "",
    ]
    for key, value in payload["orthogonal_residual_gain"].items():
        lines.append(f"- `{key}` orthogonal residual gain: `{value}`")
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_official=True), indent=2))
