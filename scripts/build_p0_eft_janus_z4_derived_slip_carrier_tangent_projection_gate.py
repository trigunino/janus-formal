from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_carrier_tangent_projection_gate import (
    CHANNELS,
    PARAMETER_STEPS,
    _central_tangent,
    _flatten,
    _rows_to_arrays,
)
from scripts.build_p0_eft_janus_z4_derived_slip_source_level_regeneration_gate import (
    NORMAL_ORIENTATION_SIGN,
    _slip_sources,
    build_payload as source_regeneration_payload,
)
from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, generate_camb_gr_rows


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_derived_slip_carrier_tangent_projection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_derived_slip_carrier_tangent_projection_gate.json")
OLD_NO_SLIP_PARALLEL_FRACTION = 0.9040080775
OLD_NO_SLIP_PERPENDICULAR_FRACTION = 0.0959918908


def _unit(values: np.ndarray) -> np.ndarray:
    scale = float(np.max(np.abs(values))) or 1.0
    return values / scale


def _interp_to_ells(source: dict, key: str, ells: np.ndarray) -> np.ndarray:
    payload = source["source_payload"]
    x = np.linspace(float(ells[0]), float(ells[-1]), len(payload[key]))
    return np.interp(ells, x, np.asarray(payload[key], dtype=float))


def _source_channel_delta(source: dict, reference: list[dict[str, float]], subchannel: str) -> dict[str, np.ndarray]:
    arrays = _rows_to_arrays(reference)
    ells = arrays["ell"]
    zero = np.zeros_like(ells, dtype=float)
    if subchannel == "surface_term":
        shape = _unit(_interp_to_ells(source, "temperature_surface_term", ells))
        return {"cl_tt": arrays["cl_tt"] * shape, "cl_te": 0.5 * arrays["cl_te"] * shape, "cl_ee": zero}
    if subchannel == "early_isw_term":
        shape = _unit(_interp_to_ells(source, "temperature_early_ISW_term", ells))
        return {"cl_tt": arrays["cl_tt"] * shape, "cl_te": arrays["cl_te"] * shape, "cl_ee": zero}
    if subchannel == "polarization_Pi_term":
        shape = _unit(_interp_to_ells(source, "Pi_source_Z4_with_slip", ells))
        return {"cl_tt": zero, "cl_te": 0.5 * arrays["cl_te"] * shape, "cl_ee": arrays["cl_ee"] * shape}
    if subchannel == "full_slip_source":
        surface = _source_channel_delta(source, reference, "surface_term")
        isw = _source_channel_delta(source, reference, "early_isw_term")
        pi = _source_channel_delta(source, reference, "polarization_Pi_term")
        return {channel: surface[channel] + isw[channel] + pi[channel] for channel in CHANNELS}
    raise ValueError(f"unknown subchannel {subchannel}")


def _tangent_matrix(reference: list[dict[str, float]], scales: dict[str, float]) -> tuple[np.ndarray, dict[str, float]]:
    columns = []
    norms = {}
    for name, (field, step) in PARAMETER_STEPS.items():
        minus_rows, plus_rows = _central_tangent(name, field, step)
        minus_arrays = _rows_to_arrays(minus_rows)
        plus_arrays = _rows_to_arrays(plus_rows)
        derivative = {channel: (plus_arrays[channel] - minus_arrays[channel]) / (2.0 * step) for channel in CHANNELS}
        column = _flatten(derivative, scales)
        columns.append(column)
        norms[name] = float(np.linalg.norm(column))
    return np.column_stack(columns), norms


def _projection_stats(vector: np.ndarray, matrix: np.ndarray, tangent_norms: dict[str, float]) -> dict:
    try:
        coefficients, *_ = np.linalg.lstsq(matrix, vector, rcond=None)
        solver = "lstsq"
    except np.linalg.LinAlgError:
        coefficients = np.linalg.pinv(matrix) @ vector
        solver = "pinv_fallback"
    projected = matrix @ coefficients
    perpendicular = vector - projected
    norm_sq = float(np.dot(vector, vector))
    parallel_fraction = float(np.dot(projected, projected) / norm_sq) if norm_sq else 0.0
    perpendicular_fraction = float(np.dot(perpendicular, perpendicular) / norm_sq) if norm_sq else 0.0
    contributions = {name: float(abs(coefficients[i]) * tangent_norms[name]) for i, name in enumerate(PARAMETER_STEPS)}
    return {
        "parallel_fraction": parallel_fraction,
        "perpendicular_fraction": perpendicular_fraction,
        "dominant_tangent_direction": max(contributions, key=contributions.get),
        "tangent_contribution_scores": contributions,
        "orthogonal_residual_norm": float(np.linalg.norm(perpendicular)),
        "projection_solver": solver,
    }


def _classify(parallel_fraction: float) -> str:
    if parallel_fraction >= 0.85:
        return "carrier_tangent_archive_fast"
    if parallel_fraction >= 0.70:
        return "weak_improvement_audit_projection"
    if parallel_fraction >= 0.50:
        return "interesting_derived_slip_candidate"
    return "strong_z4_orthogonal_signature"


def _evaluate_orientation(orientation: float, matrix: np.ndarray, tangent_norms: dict[str, float], reference: list[dict[str, float]], scales: dict[str, float]) -> dict:
    source = _slip_sources(CosmologyPoint(), normal_orientation_sign=orientation)
    subchannels = {}
    for subchannel in ("surface_term", "early_isw_term", "polarization_Pi_term", "full_slip_source"):
        delta = _source_channel_delta(source, reference, subchannel)
        stats = _projection_stats(_flatten(delta, scales), matrix, tangent_norms)
        subchannels[subchannel] = stats
    full = subchannels["full_slip_source"]
    return {
        "normal_orientation_sign": orientation,
        "derived_slip_parallel_fraction": full["parallel_fraction"],
        "derived_slip_perpendicular_fraction": full["perpendicular_fraction"],
        "dominant_tangent_direction": full["dominant_tangent_direction"],
        "orthogonal_residual_norm": full["orthogonal_residual_norm"],
        "classification": _classify(full["parallel_fraction"]),
        "subchannels": subchannels,
    }


def build_payload() -> dict:
    source_gate = source_regeneration_payload()
    reference = generate_camb_gr_rows(CosmologyPoint())
    arrays = _rows_to_arrays(reference)
    scales = {channel: float(np.sqrt(np.mean(np.square(arrays[channel]))) or 1.0) for channel in CHANNELS}
    matrix, tangent_norms = _tangent_matrix(reference, scales)
    active = _evaluate_orientation(NORMAL_ORIENTATION_SIGN, matrix, tangent_norms, reference, scales)
    flipped = _evaluate_orientation(-NORMAL_ORIENTATION_SIGN, matrix, tangent_norms, reference, scales)
    parallel = active["derived_slip_parallel_fraction"]
    improves = parallel < OLD_NO_SLIP_PARALLEL_FRACTION
    favorable = parallel < 0.70
    return {
        "status": "janus-z4-derived-slip-carrier-tangent-projection-gate",
        "source_level_regeneration_gate_passed": bool(source_gate["derived_slip_source_level_regeneration_gate_passed"]),
        "visible_slip_projection": "boundary_normal_derivative",
        "orientation_sign_policy": "fixed_by_Z4_boundary_convention",
        "normal_orientation_sign": NORMAL_ORIENTATION_SIGN,
        "orientation_flip_diagnostic_only": True,
        "active_orientation": active,
        "orientation_flip_diagnostic": flipped,
        "old_no_slip_parallel_fraction": OLD_NO_SLIP_PARALLEL_FRACTION,
        "old_no_slip_perpendicular_fraction": OLD_NO_SLIP_PERPENDICULAR_FRACTION,
        "derived_slip_parallel_fraction": parallel,
        "derived_slip_perpendicular_fraction": active["derived_slip_perpendicular_fraction"],
        "dominant_tangent_direction": active["dominant_tangent_direction"],
        "orthogonal_residual_norm": active["orthogonal_residual_norm"],
        "derived_slip_less_carrier_tangent_than_no_slip": improves,
        "derived_slip_tangent_projection_favorable": favorable,
        "interpretation_band": active["classification"],
        "subchannel_projection": active["subchannels"],
        "carrier_tangent_projection_gate_passed": True,
        "Planck_trial_allowed": False,
        "candidate_promotion_allowed": False,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Derived Slip Carrier Tangent Projection Gate",
        "",
        f"Parallel fraction: `{payload['derived_slip_parallel_fraction']}`",
        f"Perpendicular fraction: `{payload['derived_slip_perpendicular_fraction']}`",
        f"Old no-slip parallel fraction: `{payload['old_no_slip_parallel_fraction']}`",
        f"Improves vs no-slip: `{payload['derived_slip_less_carrier_tangent_than_no_slip']}`",
        f"Interpretation: `{payload['interpretation_band']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
