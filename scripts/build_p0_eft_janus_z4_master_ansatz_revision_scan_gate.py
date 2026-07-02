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
from scripts.build_p0_eft_janus_z4_derived_slip_carrier_tangent_projection_gate import CHANNELS, _projection_stats, _tangent_matrix
from scripts.build_p0_eft_janus_z4_two_sector_source_construction_audit_gate import _unit


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_ansatz_revision_scan_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_ansatz_revision_scan_gate.json")
SUCCESS_THRESHOLD = 0.70
STRONG_THRESHOLD = 0.50


def _basis(ell: np.ndarray) -> dict[str, np.ndarray]:
    x = ell / float(np.max(ell))
    return {
        "odd_low_frequency": np.sin(6.0 * x + 0.2) * np.exp(-0.7 * x),
        "odd_high_frequency": np.sin(19.0 * x + 0.5) * np.exp(-1.2 * x),
        "node_locked": np.sin(11.0 * x) * (1.0 - 2.0 * x) * np.exp(-0.9 * x),
        "localized_transition": np.exp(-np.square((x - 0.42) / 0.13)) * np.sign(0.42 - x),
        "curvature_mode": (x - np.mean(x)) * (1.0 - x) * np.exp(-0.8 * x),
    }


def _delta_from_u(arrays: dict[str, np.ndarray], ell: np.ndarray, u: np.ndarray) -> dict[str, np.ndarray]:
    du = np.gradient(u, ell)
    ddu = np.gradient(du, ell)
    return {
        "cl_tt": arrays["cl_tt"] * u,
        "cl_te": arrays["cl_te"] * (0.62 * u + 0.28 * du),
        "cl_ee": arrays["cl_ee"] * (0.36 * u - 0.18 * du + 0.05 * ddu),
    }


def build_payload() -> dict:
    reference = generate_camb_gr_rows(CosmologyPoint())
    arrays = _rows_to_arrays(reference)
    ell = arrays["ell"]
    scales = {channel: float(np.sqrt(np.mean(np.square(arrays[channel]))) or 1.0) for channel in CHANNELS}
    matrix, tangent_norms = _tangent_matrix(reference, scales)

    rows = {}
    for name, raw in _basis(ell).items():
        u = _unit(raw)
        stats = _projection_stats(_flatten(_delta_from_u(arrays, ell, u), scales), matrix, tangent_norms)
        rows[name] = {
            "parallel_fraction": stats["parallel_fraction"],
            "perpendicular_fraction": stats["perpendicular_fraction"],
            "dominant_tangent_direction": stats["dominant_tangent_direction"],
            "passes_success_threshold_lt_0p7": stats["parallel_fraction"] < SUCCESS_THRESHOLD,
            "passes_strong_threshold_lt_0p5": stats["parallel_fraction"] < STRONG_THRESHOLD,
        }
    best = min(rows, key=lambda key: rows[key]["parallel_fraction"])
    return {
        "status": "janus-z4-master-ansatz-revision-scan-gate",
        "previous_master_parallel_fraction": 0.9972684620305592,
        "ansatz_rows": rows,
        "best_ansatz": best,
        "best_parallel_fraction": rows[best]["parallel_fraction"],
        "best_dominant_tangent_direction": rows[best]["dominant_tangent_direction"],
        "any_ansatz_passes_lt_0p7": any(row["passes_success_threshold_lt_0p7"] for row in rows.values()),
        "any_ansatz_passes_lt_0p5": any(row["passes_strong_threshold_lt_0p5"] for row in rows.values()),
        "scan_is_internal_not_observational_fit": True,
        "lambda_retuning_allowed": False,
        "Planck_trial_allowed": False,
        "spectra_generation_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterSourceLevelRegenerationGate" if rows[best]["parallel_fraction"] < SUCCESS_THRESHOLD else "revise_unique_Z4_master_operator",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Ansatz Revision Scan Gate",
        "",
        f"Best ansatz: `{payload['best_ansatz']}`",
        f"Best parallel fraction: `{payload['best_parallel_fraction']}`",
        f"Any <0.7: `{payload['any_ansatz_passes_lt_0p7']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
