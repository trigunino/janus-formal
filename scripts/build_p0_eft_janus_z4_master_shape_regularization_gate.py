from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, generate_camb_gr_rows
from janus_lab.z4_source_level import hash_payload
from scripts.build_p0_eft_janus_z4_carrier_tangent_projection_gate import _flatten, _rows_to_arrays
from scripts.build_p0_eft_janus_z4_derived_slip_carrier_tangent_projection_gate import CHANNELS, _projection_stats, _tangent_matrix
from scripts.build_p0_eft_janus_z4_master_diagnostic_shape_report_gate import _peak_ell, _zero_count
from scripts.build_p0_eft_janus_z4_master_diagnostic_spectra_generation_gate import _interp
from scripts.build_p0_eft_janus_z4_master_pre_likelihood_lock_gate import build_payload as lock_payload
from scripts.build_p0_eft_janus_z4_master_source_level_regeneration_gate import _source_payload
from scripts.build_p0_eft_janus_z4_two_sector_source_construction_audit_gate import _unit


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_shape_regularization_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_shape_regularization_gate.json")
REGULARIZATION_LIMIT = 2.0 / 3.0


def _regularize(shape: np.ndarray, limit: float = REGULARIZATION_LIMIT) -> np.ndarray:
    return limit * np.tanh(shape / limit)


def _ratio_stats(base: np.ndarray, delta: np.ndarray) -> dict:
    ratio = 1.0 + delta / base
    return {
        "ratio_min": float(np.min(ratio)),
        "ratio_max": float(np.max(ratio)),
        "ratio_mean": float(np.mean(ratio)),
        "max_abs_fractional_deviation": float(np.max(np.abs(ratio - 1.0))),
    }


def build_payload() -> dict:
    lock = lock_payload()
    source = _source_payload()
    reference = generate_camb_gr_rows(CosmologyPoint())
    arrays = _rows_to_arrays(reference)
    ell = arrays["ell"]

    s_t = _unit(_interp(source["S_T_Z4"], ell))
    s_e = _unit(_interp(source["S_E_Z4"], ell))
    doppler = _unit(_interp(source["Doppler_Z4"], ell))
    pi = _unit(_interp(source["Pi_Z4"], ell))
    raw_shape = {
        "cl_tt": s_t + 0.15 * doppler,
        "cl_te": 0.5 * s_t + 0.5 * s_e,
        "cl_ee": s_e + 0.2 * pi,
    }
    regularized_shape = {channel: _regularize(shape) for channel, shape in raw_shape.items()}
    delta = {channel: arrays[channel] * regularized_shape[channel] for channel in CHANNELS}
    candidate = {channel: arrays[channel] + delta[channel] for channel in CHANNELS}

    shape_rows = {}
    for channel in CHANNELS:
        shape_rows[channel] = {
            **_ratio_stats(arrays[channel], delta[channel]),
            "baseline_peak_ell": _peak_ell(ell, arrays[channel]),
            "candidate_peak_ell": _peak_ell(ell, candidate[channel]),
            "peak_shift": _peak_ell(ell, candidate[channel]) - _peak_ell(ell, arrays[channel]),
            "baseline_zero_count": _zero_count(arrays[channel]),
            "candidate_zero_count": _zero_count(candidate[channel]),
            "zero_count_delta": _zero_count(candidate[channel]) - _zero_count(arrays[channel]),
        }

    scales = {channel: float(np.sqrt(np.mean(np.square(arrays[channel]))) or 1.0) for channel in CHANNELS}
    matrix, tangent_norms = _tangent_matrix(reference, scales)
    stats = _projection_stats(_flatten(delta, scales), matrix, tangent_norms)
    zero_artifacts_after = {
        channel: row["zero_count_delta"]
        for channel, row in shape_rows.items()
        if row["zero_count_delta"] != 0
    }
    max_dev = max(row["max_abs_fractional_deviation"] for row in shape_rows.values())
    max_peak_shift = max(abs(row["peak_shift"]) for row in shape_rows.values())
    lock_cleared = not zero_artifacts_after and max_dev <= 1.0

    return {
        "status": "janus-z4-master-shape-regularization-gate",
        "pre_likelihood_lock_was_active": lock["pre_likelihood_lock_active"],
        "raw_lock_reason": lock["lock_reason"],
        "source_payload_hash": hash_payload(source),
        "regularization_route": "orbifold_membrane_bounded_tanh_master_shape",
        "regularization_limit": REGULARIZATION_LIMIT,
        "is_action_derived": False,
        "shape_regularization_evaluated": True,
        "shape_rows_after_regularization": shape_rows,
        "zero_crossing_artifacts_before": lock["zero_crossing_artifacts"],
        "zero_crossing_artifacts_after": zero_artifacts_after,
        "max_abs_fractional_deviation_after": max_dev,
        "max_abs_peak_shift_after": max_peak_shift,
        "phase_guard_passed_after": max_peak_shift <= 200,
        "amplitude_guard_passed_after": max_dev <= 1.0,
        "shape_regularization_clears_pre_likelihood_lock": lock_cleared,
        "carrier_parallel_fraction_after_regularization": stats["parallel_fraction"],
        "carrier_perpendicular_fraction_after_regularization": stats["perpendicular_fraction"],
        "dominant_tangent_direction_after_regularization": stats["dominant_tangent_direction"],
        "passes_carrier_threshold_after_regularization": stats["parallel_fraction"] < 0.7,
        "passes_strong_carrier_threshold_after_regularization": stats["parallel_fraction"] < 0.5,
        "diagnostic_regularized_spectra_allowed": lock_cleared and stats["parallel_fraction"] < 0.7,
        "official_planck_trial_allowed": False,
        "likelihood_evaluation_allowed": False,
        "candidate_promotion_allowed": False,
        "lambda_retuning_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterRegularizedDiagnosticSpectraGenerationGate"
        if lock_cleared and stats["parallel_fraction"] < 0.7
        else "revise_master_shape_regularization",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Shape Regularization Gate",
        "",
        f"Route: `{payload['regularization_route']}`",
        f"Limit: `{payload['regularization_limit']}`",
        f"Lock cleared: `{payload['shape_regularization_clears_pre_likelihood_lock']}`",
        f"Parallel fraction: `{payload['carrier_parallel_fraction_after_regularization']}`",
        f"Official Planck allowed: `{payload['official_planck_trial_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
