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
from scripts.build_p0_eft_janus_z4_two_sector_source_level_regeneration_gate import _source_payload
from scripts.build_p0_eft_janus_z4_two_sector_source_construction_audit_gate import _delta, _unit


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_projection_parity_preservation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_projection_parity_preservation_gate.json")
SURVIVAL_THRESHOLD = 0.10
ORTHOGONAL_THRESHOLD = 0.70


def _norm(v: np.ndarray) -> float:
    return float(np.linalg.norm(v))


def _to_ell_grid(values: np.ndarray, ell: np.ndarray) -> np.ndarray:
    x = np.linspace(float(ell[0]), float(ell[-1]), len(values))
    return np.interp(ell, x, values)


def _rows() -> dict[str, dict[str, float | bool | str]]:
    source = _source_payload()
    tau = np.asarray(source["time_grid"], dtype=float)
    plus = np.asarray(source["plus_drive"], dtype=float)
    minus = np.asarray(source["minus_drive"], dtype=float)
    window = np.asarray(source["projection_window"], dtype=float)
    symmetric = 0.5 * (plus + minus)
    antisymmetric = 0.5 * (plus - minus)
    d_symmetric = np.gradient(symmetric, tau)
    d_antisymmetric = np.gradient(antisymmetric, tau)

    projections = {
        "value_projection": (window * symmetric, window * antisymmetric),
        "normal_derivative_projection": (window * d_symmetric, window * d_antisymmetric),
        "jump_projection": (window * symmetric, window * (plus - minus)),
        "membrane_weighted_projection": (window * symmetric, np.gradient(window) * antisymmetric),
        "mixed_value_derivative_projection": (
            window * (symmetric + 0.25 * d_symmetric),
            window * (antisymmetric + 0.25 * d_antisymmetric),
        ),
    }

    reference = generate_camb_gr_rows(CosmologyPoint())
    arrays = _rows_to_arrays(reference)
    ell = arrays["ell"]
    scales = {channel: float(np.sqrt(np.mean(np.square(arrays[channel]))) or 1.0) for channel in CHANNELS}
    matrix, tangent_norms = _tangent_matrix(reference, scales)

    rows = {}
    for name, (sym, anti) in projections.items():
        sym_norm = _norm(sym)
        anti_norm = _norm(anti)
        ratio = anti_norm / (sym_norm or 1.0)
        anti_ell = _to_ell_grid(anti, ell)
        stats = _projection_stats(_flatten(_delta(reference, _unit(anti_ell), "temperature"), scales), matrix, tangent_norms)
        rows[name] = {
            "projection_norm_symmetric": sym_norm,
            "projection_norm_antisymmetric": anti_norm,
            "antisymmetric_survival_ratio": ratio,
            "projection_nulls_Z4_odd_mode": ratio < SURVIVAL_THRESHOLD,
            "projected_antisymmetric_parallel_fraction": stats["parallel_fraction"],
            "projected_antisymmetric_parallel_to_carrier": stats["parallel_fraction"] >= ORTHOGONAL_THRESHOLD,
            "dominant_tangent_direction": stats["dominant_tangent_direction"],
            "preserves_antisymmetry": ratio >= SURVIVAL_THRESHOLD and stats["parallel_fraction"] < ORTHOGONAL_THRESHOLD,
        }
    return rows


def build_payload() -> dict:
    rows = _rows()
    preserving = [name for name, row in rows.items() if row["preserves_antisymmetry"]]
    best = min(rows, key=lambda name: rows[name]["projected_antisymmetric_parallel_fraction"])
    return {
        "status": "janus-z4-projection-parity-preservation-gate",
        "projection_rows": rows,
        "which_projection_preserves_antisymmetry": preserving,
        "any_projection_preserves_antisymmetry": bool(preserving),
        "best_projection_by_carrier_orthogonality": best,
        "best_projection_parallel_fraction": rows[best]["projected_antisymmetric_parallel_fraction"],
        "value_projection_nulls_Z4_odd_mode": rows["value_projection"]["projection_nulls_Z4_odd_mode"],
        "normal_derivative_projection_tested": True,
        "jump_projection_tested": True,
        "membrane_weighted_projection_tested": True,
        "mixed_value_derivative_projection_tested": True,
        "free_projection_coefficient_allowed": False,
        "Planck_trial_allowed": False,
        "spectra_generation_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4ObservableProjectionRevisionGate" if preserving else "P0EFTJanusZ4MinusSectorIndependentTransferGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Projection Parity Preservation Gate",
        "",
        f"Any projection preserves antisymmetry: `{payload['any_projection_preserves_antisymmetry']}`",
        f"Preserving projections: `{payload['which_projection_preserves_antisymmetry']}`",
        f"Best projection: `{payload['best_projection_by_carrier_orthogonality']}`",
        f"Best parallel fraction: `{payload['best_projection_parallel_fraction']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
