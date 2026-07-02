from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_carrier_tangent_projection_gate import _rows_to_arrays
from scripts.build_p0_eft_janus_z4_derived_slip_carrier_tangent_projection_gate import CHANNELS, _tangent_matrix
from scripts.build_p0_eft_janus_z4_master_diagnostic_spectra_generation_gate import _interp
from scripts.build_p0_eft_janus_z4_master_highl_acoustic_revision_scan_gate import (
    _delta_for_shapes,
    _metrics,
    _read_reference_rows,
)
from scripts.build_p0_eft_janus_z4_master_revised_source_level_regeneration_gate import (
    build_payload as revised_source_payload,
    build_revised_source_payload,
)
from scripts.build_p0_eft_janus_z4_master_shape_regularization_gate import _regularize


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_revised_carrier_tangent_projection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_revised_carrier_tangent_projection_gate.json")


def _revised_source_shapes(source: dict, ell: np.ndarray) -> dict[str, np.ndarray]:
    s_t = _interp(source["S_T_Z4"], ell)
    s_e = _interp(source["S_E_Z4"], ell)
    doppler = _interp(source["Doppler_Z4"], ell)
    pi = _interp(source["Pi_Z4"], ell)
    return {
        "cl_tt": _regularize(s_t + 0.15 * doppler),
        "cl_te": _regularize(0.5 * s_t + 0.5 * s_e),
        "cl_ee": _regularize(s_e + 0.2 * pi),
    }


def build_payload() -> dict:
    source_gate = revised_source_payload()
    source = build_revised_source_payload()
    rows = _read_reference_rows()
    arrays = _rows_to_arrays(rows)
    ell = arrays["ell"]
    scales = {channel: float(np.sqrt(np.mean(np.square(arrays[channel]))) or 1.0) for channel in CHANNELS}
    matrix, tangent_norms = _tangent_matrix(rows, scales)
    delta = _delta_for_shapes(arrays, _revised_source_shapes(source, ell))
    metrics = _metrics(rows, delta, matrix, tangent_norms)
    carrier_threshold_passed = metrics["parallel_fraction"] < 0.7
    strong_orthogonal_candidate = metrics["parallel_fraction"] < 0.5
    return {
        "status": "janus-z4-master-revised-carrier-tangent-projection-gate",
        "source_level_v2_passed": source_gate["revision_scan_passed"],
        "source_level_version": source_gate["source_level_version"],
        "parallel_fraction": metrics["parallel_fraction"],
        "perpendicular_fraction": metrics["perpendicular_fraction"],
        "dominant_tangent_direction": metrics["dominant_tangent_direction"],
        "highl_fractional_rms": metrics["highl_fractional_rms"],
        "max_abs_fractional_delta": metrics["max_abs_fractional_delta"],
        "carrier_threshold_passed": carrier_threshold_passed,
        "strong_orthogonal_candidate": strong_orthogonal_candidate,
        "nontrivial_signal_preserved": metrics["max_abs_fractional_delta"] > 0.05,
        "downstream_patch_allowed": False,
        "lambda_retuning_allowed": False,
        "spectra_generation_allowed": False,
        "observed_Planck_rerun_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterRegularizedDiagnosticSpectraV2Gate"
        if carrier_threshold_passed
        else "derive_new_master_highl_acoustic_shape",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Revised Carrier-Tangent Projection Gate",
        "",
        f"Source v2 passed: `{payload['source_level_v2_passed']}`",
        f"Parallel fraction: `{payload['parallel_fraction']}`",
        f"Perpendicular fraction: `{payload['perpendicular_fraction']}`",
        f"Dominant tangent direction: `{payload['dominant_tangent_direction']}`",
        f"Carrier threshold passed: `{payload['carrier_threshold_passed']}`",
        f"Observed Planck rerun allowed: `{payload['observed_Planck_rerun_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
