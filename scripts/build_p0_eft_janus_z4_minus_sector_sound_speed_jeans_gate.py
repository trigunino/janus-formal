from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, generate_camb_gr_rows
from scripts.build_p0_eft_janus_z4_carrier_tangent_projection_gate import _flatten, _rows_to_arrays
from scripts.build_p0_eft_janus_z4_derived_slip_carrier_tangent_projection_gate import (
    CHANNELS,
    _projection_stats,
    _tangent_matrix,
)
from scripts.build_p0_eft_janus_z4_minus_sector_independent_transfer_gate import _best_rescale, _rank_stats
from scripts.build_p0_eft_janus_z4_two_sector_source_construction_audit_gate import _delta, _unit
from scripts.build_p0_eft_janus_z4_two_sector_source_level_regeneration_gate import _source_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_minus_sector_sound_speed_jeans_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_minus_sector_sound_speed_jeans_gate.json")
INDEPENDENCE_THRESHOLD = 0.20
ORTHOGONAL_THRESHOLD = 0.70


def _interp(values: np.ndarray, x: np.ndarray) -> np.ndarray:
    src = np.linspace(float(x[0]), float(x[-1]), len(values))
    return np.interp(x, src, values)


def _jeans_filter(ell: np.ndarray) -> np.ndarray:
    k = ell / float(np.max(ell))
    k_j_minus = 0.37
    return 1.0 / (1.0 + np.square(k / k_j_minus))


def _score(plus: np.ndarray, minus: np.ndarray, reference: list[dict[str, float]], scales, matrix, tangent_norms) -> dict:
    coeff, residual = _best_rescale(plus, minus)
    ranks = _rank_stats(plus, minus)
    anti = minus - plus
    stats = _projection_stats(_flatten(_delta(reference, _unit(anti), "temperature"), scales), matrix, tangent_norms)
    independent = residual > INDEPENDENCE_THRESHOLD and ranks["effective_transfer_rank"] == 2
    return {
        "minus_over_plus_amplitude_fit": coeff,
        "residual_after_best_amplitude_fit": residual,
        "effective_transfer_rank": ranks["effective_transfer_rank"],
        "rank1_explained_variance": ranks["rank1_explained_variance"],
        "rank2_residual_variance": ranks["rank2_residual_variance"],
        "parallel_fraction": stats["parallel_fraction"],
        "perpendicular_fraction": stats["perpendicular_fraction"],
        "dominant_tangent_direction": stats["dominant_tangent_direction"],
        "minus_sector_independent_transfer": independent,
        "carrier_tangent_after_microphysics": stats["parallel_fraction"] >= ORTHOGONAL_THRESHOLD,
        "survives_transfer_and_projection": independent and stats["parallel_fraction"] < ORTHOGONAL_THRESHOLD,
    }


def build_payload() -> dict:
    source = _source_payload()
    reference = generate_camb_gr_rows(CosmologyPoint())
    arrays = _rows_to_arrays(reference)
    ell = arrays["ell"]
    scales = {channel: float(np.sqrt(np.mean(np.square(arrays[channel]))) or 1.0) for channel in CHANNELS}
    matrix, tangent_norms = _tangent_matrix(reference, scales)

    plus_base = _interp(np.asarray(source["plus_drive"], dtype=float), ell)
    minus_base = _interp(np.asarray(source["minus_drive"], dtype=float), ell)
    filt = _jeans_filter(ell)
    d_filt = np.gradient(filt, ell)
    rows = {
        "density": _score(plus_base, minus_base * filt, reference, scales, matrix, tangent_norms),
        "velocity": _score(np.gradient(plus_base, ell), np.gradient(minus_base * filt, ell), reference, scales, matrix, tangent_norms),
        "shear": _score(np.gradient(np.gradient(plus_base, ell), ell), np.gradient(np.gradient(minus_base * filt, ell), ell), reference, scales, matrix, tangent_norms),
        "Weyl": _score(plus_base, minus_base * filt, reference, scales, matrix, tangent_norms),
        "Theta0": _score(plus_base, plus_base + 0.5 * minus_base * filt, reference, scales, matrix, tangent_norms),
        "Pi": _score(0.15 * plus_base, 0.35 * (plus_base - minus_base * filt) + 0.15 * plus_base, reference, scales, matrix, tangent_norms),
        "projection_source": _score(plus_base, minus_base * (filt + 0.1 * d_filt), reference, scales, matrix, tangent_norms),
    }
    survivors = [name for name, row in rows.items() if row["survives_transfer_and_projection"]]
    return {
        "status": "janus-z4-minus-sector-sound-speed-jeans-gate",
        "microphysics_route": "sound_speed_jeans",
        "is_derived_from_full_action": False,
        "fixed_jeans_profile_used": True,
        "free_minus_amplitude_allowed": False,
        "minus_sound_speed_differs_from_plus": True,
        "minus_pressure_differs_from_plus": True,
        "minus_shear_differs_from_plus": any(rows[name]["minus_sector_independent_transfer"] for name in ("shear", "Pi")),
        "transfer_rows": rows,
        "surviving_components_parallel_lt_0p7": survivors,
        "any_component_survives": bool(survivors),
        "independent_transfer_rank_obtained": any(row["minus_sector_independent_transfer"] for row in rows.values()),
        "carrier_tangent_projection_required_before_observation": True,
        "rho_eff_shortcut_allowed": False,
        "projection_only_fix_allowed": False,
        "direct_Cl_patch_allowed": False,
        "raw_toy_LOS_allowed": False,
        "Planck_trial_allowed": False,
        "spectra_generation_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MinusIndependentComponentGate" if survivors else "P0EFTJanusZ4MinusSectorShearFreeStreamingGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Minus-Sector Sound-Speed/Jeans Gate",
        "",
        f"Derived from full action: `{payload['is_derived_from_full_action']}`",
        f"Independent transfer rank obtained: `{payload['independent_transfer_rank_obtained']}`",
        f"Survivors <0.7: `{payload['surviving_components_parallel_lt_0p7']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
