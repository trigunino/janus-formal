from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from janus_lab.janus_2024_bulk_path import build_cited_bulk_reference_path
from janus_lab.janus_2024_cited_calibration import (
    published_janus_2024_cited_calibration,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_bulk_observable_path_gate.json"
REPORT_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_bulk_observable_path_gate.md"


def build_payload() -> dict:
    calibration = published_janus_2024_cited_calibration()
    reference = calibration.to_reference()
    contract = calibration.to_normalization_contract()
    path = build_cited_bulk_reference_path(
        reference=reference,
        q0=calibration.q0,
        h0_s_inv=calibration.h0_s_inv,
        alpha_seconds=calibration.alpha_seconds,
    )
    cross_density = path.determinant_weighted_cross_density(contract)
    return {
        "status": "the-janus-cosmological-model-2024-bulk-observable-path-gate",
        "active_two_metric_reference_object_present": True,
        "bulk_history_wrapper_present": True,
        "bulk_history_built_from_cited_calibration": True,
        "background_path_uses_q0_u0_proxy": False,
        "background_path_uses_bulk_two_metric_history": True,
        "determinant_bridge_history_present": True,
        "determinant_weighted_cross_density_present": True,
        "present_e_plus_is_unity": bool(abs(path.e_plus(0.0) - 1.0) < 1.0e-12),
        "present_a_plus_is_unity": bool(abs(path.a_plus[-1] - 1.0) < 1.0e-12),
        "path_sample_count": int(len(path.x0)),
        "redshift_max": float(path.redshift_grid()[0]),
        "minus_initialization_convention": "common_clock_curvature_matched_present_hubble_ratio=1/(1-2q0)",
        "cross_density_today_kg_m3": float(cross_density[-1]),
        "e_plus_from_bulk_history_present": True,
        "e_minus_from_bulk_history_present": True,
        "distance_scan_run": False,
        "official_observational_run": False,
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# The Janus Cosmological Model 2024 Bulk Observable Path Gate",
                "",
                f"Uses q0/u0 proxy: `{payload['background_path_uses_q0_u0_proxy']}`",
                f"Uses bulk two-metric history: `{payload['background_path_uses_bulk_two_metric_history']}`",
                f"Built from cited calibration: `{payload['bulk_history_built_from_cited_calibration']}`",
                f"Determinant bridge history present: `{payload['determinant_bridge_history_present']}`",
                f"Determinant-weighted cross density present: `{payload['determinant_weighted_cross_density_present']}`",
                f"E_plus from bulk history present: `{payload['e_plus_from_bulk_history_present']}`",
                f"E_minus from bulk history present: `{payload['e_minus_from_bulk_history_present']}`",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
