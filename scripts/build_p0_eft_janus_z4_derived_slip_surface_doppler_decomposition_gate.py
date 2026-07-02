from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_derived_slip_photon_monopole_sw_closure_gate import (
    _delta_from_surface,
    _surface_sources,
)
from scripts.build_p0_eft_janus_z4_derived_slip_carrier_tangent_projection_gate import (
    CHANNELS,
    _projection_stats,
    _tangent_matrix,
)
from scripts.build_p0_eft_janus_z4_carrier_tangent_projection_gate import _flatten, _rows_to_arrays
from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, generate_camb_gr_rows


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_derived_slip_surface_doppler_decomposition_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_derived_slip_surface_doppler_decomposition_gate.json")


def _basis() -> tuple[list[dict[str, float]], dict[str, float], np.ndarray, dict[str, float]]:
    reference = generate_camb_gr_rows(CosmologyPoint())
    arrays = _rows_to_arrays(reference)
    scales = {channel: float(np.sqrt(np.mean(np.square(arrays[channel]))) or 1.0) for channel in CHANNELS}
    matrix, tangent_norms = _tangent_matrix(reference, scales)
    return reference, scales, matrix, tangent_norms


def _stats_for(values: np.ndarray, reference: list[dict[str, float]], scales: dict[str, float], matrix: np.ndarray, tangent_norms: dict[str, float]) -> dict:
    return _projection_stats(_flatten(_delta_from_surface(reference, values), scales), matrix, tangent_norms)


def build_payload() -> dict:
    reference, scales, matrix, tangent_norms = _basis()
    sources = _surface_sources()
    sw = sources["monopole_plus_potential"]
    doppler = sources["Doppler_Z4"]
    full = sources["full_surface"]
    sw_stats = _stats_for(sw, reference, scales, matrix, tangent_norms)
    doppler_stats = _stats_for(doppler, reference, scales, matrix, tangent_norms)
    full_stats = _stats_for(full, reference, scales, matrix, tangent_norms)
    cross_alignment = float(np.dot(sw, doppler) / ((np.linalg.norm(sw) * np.linalg.norm(doppler)) or 1.0))
    return {
        "status": "janus-z4-derived-slip-surface-doppler-decomposition-gate",
        "parallel_fraction_SW_only": sw_stats["parallel_fraction"],
        "parallel_fraction_Doppler_only": doppler_stats["parallel_fraction"],
        "parallel_fraction_full_surface": full_stats["parallel_fraction"],
        "perpendicular_fraction_SW_only": sw_stats["perpendicular_fraction"],
        "perpendicular_fraction_Doppler_only": doppler_stats["perpendicular_fraction"],
        "perpendicular_fraction_full_surface": full_stats["perpendicular_fraction"],
        "cross_term_alignment": cross_alignment,
        "dominant_tangent_direction_SW": sw_stats["dominant_tangent_direction"],
        "dominant_tangent_direction_Doppler": doppler_stats["dominant_tangent_direction"],
        "dominant_tangent_direction_full_surface": full_stats["dominant_tangent_direction"],
        "doppler_reintroduces_carrier_tangency": doppler_stats["parallel_fraction"] > sw_stats["parallel_fraction"],
        "SW_surface_promising": sw_stats["parallel_fraction"] < 0.50,
        "full_surface_weak_after_doppler": 0.70 <= full_stats["parallel_fraction"] < 0.85,
        "Planck_trial_allowed": False,
        "candidate_promotion_allowed": False,
        "no_lambda_retuning": True,
        "no_free_doppler_amplitude": True,
        "no_free_slip_parameter": True,
        "no_free_eta_ratio": True,
        "no_direct_Cl_patch": True,
        "raw_toy_LOS_forbidden": True,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Derived Slip Surface Doppler Decomposition Gate",
        "",
        f"SW-only parallel: `{payload['parallel_fraction_SW_only']}`",
        f"Doppler-only parallel: `{payload['parallel_fraction_Doppler_only']}`",
        f"Full-surface parallel: `{payload['parallel_fraction_full_surface']}`",
        f"Doppler reintroduces carrier tangency: `{payload['doppler_reintroduces_carrier_tangency']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
