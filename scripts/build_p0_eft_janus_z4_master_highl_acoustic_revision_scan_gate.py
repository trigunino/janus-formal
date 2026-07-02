from __future__ import annotations

import json
import sys
import csv
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_carrier_tangent_projection_gate import _flatten, _rows_to_arrays
from scripts.build_p0_eft_janus_z4_derived_slip_carrier_tangent_projection_gate import CHANNELS, _projection_stats, _tangent_matrix
from scripts.build_p0_eft_janus_z4_master_diagnostic_spectra_generation_gate import _interp
from scripts.build_p0_eft_janus_z4_master_observed_failure_map_gate import build_payload as failure_payload
from scripts.build_p0_eft_janus_z4_master_shape_regularization_gate import _regularize
from scripts.build_p0_eft_janus_z4_master_source_level_regeneration_gate import _source_payload
from scripts.build_p0_eft_janus_z4_two_sector_source_construction_audit_gate import _unit


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_highl_acoustic_revision_scan_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_highl_acoustic_revision_scan_gate.json")
REFERENCE_GR_CSV = Path("outputs/reports/z4_master_regularized_diagnostic_spectra/reference_gr.csv")


def _read_reference_rows() -> list[dict[str, float]]:
    if not REFERENCE_GR_CSV.exists():
        raise FileNotFoundError(f"Missing reference spectra: {REFERENCE_GR_CSV}")
    with REFERENCE_GR_CSV.open(newline="", encoding="utf-8") as handle:
        return [
            {key: (int(value) if key == "ell" else float(value)) for key, value in row.items()}
            for row in csv.DictReader(handle)
        ]


def _delta_for_shapes(arrays: dict[str, np.ndarray], shapes: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    return {channel: arrays[channel] * shapes[channel] for channel in CHANNELS}


def _metrics(
    rows: list[dict[str, float]],
    delta: dict[str, np.ndarray],
    matrix: np.ndarray,
    tangent_norms: dict,
) -> dict:
    arrays = _rows_to_arrays(rows)
    ell = arrays["ell"]
    scales = {channel: float(np.sqrt(np.mean(np.square(arrays[channel]))) or 1.0) for channel in CHANNELS}
    stats = _projection_stats(_flatten(delta, scales), matrix, tangent_norms)
    high = (ell >= 600.0) & (ell <= 1800.0)
    high_terms = [
        delta[channel][high] / np.maximum(np.abs(arrays[channel][high]), 1.0e-30)
        for channel in CHANNELS
    ]
    return {
        "parallel_fraction": stats["parallel_fraction"],
        "perpendicular_fraction": stats["perpendicular_fraction"],
        "dominant_tangent_direction": stats["dominant_tangent_direction"],
        "highl_fractional_rms": float(np.sqrt(np.mean(np.square(np.concatenate(high_terms))))),
        "max_abs_fractional_delta": max(
            float(np.max(np.abs(delta[channel] / np.maximum(np.abs(arrays[channel]), 1.0e-30))))
            for channel in CHANNELS
        ),
    }


def _baseline_shapes(source: dict, ell: np.ndarray) -> dict[str, np.ndarray]:
    s_t = _unit(_interp(source["S_T_Z4"], ell))
    s_e = _unit(_interp(source["S_E_Z4"], ell))
    doppler = _unit(_interp(source["Doppler_Z4"], ell))
    pi = _unit(_interp(source["Pi_Z4"], ell))
    return {
        "cl_tt": _regularize(s_t + 0.15 * doppler),
        "cl_te": _regularize(0.5 * s_t + 0.5 * s_e),
        "cl_ee": _regularize(s_e + 0.2 * pi),
    }


def _revised_shapes(source: dict, ell: np.ndarray, strength: float, center: float) -> dict[str, np.ndarray]:
    u = _interp(source["U_Z4"], ell)
    scale = max(float(np.max(np.abs(u))), 1.0e-30)
    guard = 1.0 - strength / (1.0 + np.exp(-(ell - center) / 120.0))
    s_t = _interp(source["S_T_Z4"], ell) * guard / scale
    s_e = _interp(source["S_E_Z4"], ell) * guard / scale
    doppler = _interp(source["Doppler_Z4"], ell) * guard / scale
    pi = _interp(source["Pi_Z4"], ell) * guard / scale
    return {
        "cl_tt": _regularize(s_t + 0.15 * doppler),
        "cl_te": _regularize(0.5 * s_t + 0.5 * s_e),
        "cl_ee": _regularize(s_e + 0.2 * pi),
    }


def build_payload() -> dict:
    failure = failure_payload()
    source = _source_payload()
    rows = _read_reference_rows()
    arrays = _rows_to_arrays(rows)
    ell = arrays["ell"]
    scales = {channel: float(np.sqrt(np.mean(np.square(arrays[channel]))) or 1.0) for channel in CHANNELS}
    matrix, tangent_norms = _tangent_matrix(rows, scales)
    baseline_delta = _delta_for_shapes(arrays, _baseline_shapes(source, ell))
    baseline = _metrics(rows, baseline_delta, matrix, tangent_norms)
    scan_rows = []
    for strength in (0.3, 0.5, 0.7, 0.9):
        for center in (700.0, 900.0, 1100.0, 1300.0):
            delta = _delta_for_shapes(arrays, _revised_shapes(source, ell, strength, center))
            row = {
                "revision": "shared_U_norm_silk_guard",
                "silk_guard_strength": strength,
                "silk_guard_center_ell": center,
                **_metrics(rows, delta, matrix, tangent_norms),
            }
            row["highl_reduction_factor"] = row["highl_fractional_rms"] / baseline["highl_fractional_rms"]
            row["passes_carrier_threshold"] = row["parallel_fraction"] < 0.7
            row["keeps_nontrivial_signal"] = row["max_abs_fractional_delta"] > 0.05
            scan_rows.append(row)
    viable = [
        row
        for row in scan_rows
        if row["passes_carrier_threshold"]
        and row["keeps_nontrivial_signal"]
        and row["highl_reduction_factor"] < 0.5
    ]
    best = min(viable, key=lambda row: row["highl_fractional_rms"]) if viable else None
    return {
        "status": "janus-z4-master-highl-acoustic-revision-scan-gate",
        "observed_failure_class": failure["failure_class"],
        "failure_map_highl_dominates": failure["highl_failure_dominates"],
        "revision_principle": "replace_channelwise_unit_normalization_with_shared_U_Z4_normalization_and_silk_guard",
        "baseline_metrics": baseline,
        "scan_rows": scan_rows,
        "best_revision": best,
        "revision_found": best is not None,
        "selected_revision_is_upstream_master": bool(best is not None),
        "downstream_patch_allowed": False,
        "observed_planck_rerun_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterRevisedSourceLevelRegenerationGate"
        if best
        else "derive_new_master_highl_acoustic_shape",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    best = payload["best_revision"] or {}
    lines = [
        "# Janus Z4 Master High-L Acoustic Revision Scan Gate",
        "",
        f"Revision found: `{payload['revision_found']}`",
        f"Best strength: `{best.get('silk_guard_strength')}`",
        f"Best center ell: `{best.get('silk_guard_center_ell')}`",
        f"Best high-l reduction: `{best.get('highl_reduction_factor')}`",
        f"Best parallel fraction: `{best.get('parallel_fraction')}`",
        f"Observed Planck rerun allowed: `{payload['observed_planck_rerun_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
