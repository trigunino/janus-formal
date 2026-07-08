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
from janus_lab.janus_2024_cited_calibration import published_janus_2024_cited_calibration
from janus_lab.janus_2024_reference import Janus2024PublishedDustBackground


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_paper_native_materialization_audit.json"
REPORT_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_paper_native_materialization_audit.md"


def build_payload() -> dict:
    paper = Janus2024PublishedDustBackground()
    calibration = published_janus_2024_cited_calibration()
    reference = calibration.to_reference()
    path = build_cited_bulk_reference_path(
        reference=reference,
        q0=calibration.q0,
        h0_s_inv=calibration.h0_s_inv,
        alpha_seconds=calibration.alpha_seconds,
    )
    return {
        "status": "the-janus-cosmological-model-2024-paper-native-materialization-audit",
        "paper_equation_layer_present": True,
        "common_time_coordinate": paper.common_time_coordinate,
        "paper_curvature_branch_present": bool(paper.k_plus == -1 and paper.k_minus == -1),
        "two_metric_bulk_reference_object_present": True,
        "bulk_history_wrapper_present": True,
        "bulk_history_uses_two_metric_history": True,
        "paper_only_layer_closed": False,
        "paper_plus_cited_calibration_layer_closed_up_to_minus_init": True,
        "plus_history_materialized": True,
        "minus_history_materialized": True,
        "plus_history_source_kind": "cited_q0_h0_exact_shape",
        "minus_history_source_kind": "repo_convention_from_cited_calibration",
        "absolute_normalization_source_kind": "cited_q0_h0_ratio_not_strict_paper_only",
        "plus_history_fixed_by_cited_sources": True,
        "absolute_normalization_fixed_by_cited_sources_and_ratio": True,
        "minus_initialization_fixed_by_sources": False,
        "present_a_plus_unity": bool(abs(path.a_plus[-1] - 1.0) < 1.0e-12),
        "present_e_plus_unity": bool(abs(path.e_plus(0.0) - 1.0) < 1.0e-12),
        "history_sample_count": int(len(path.x0)),
        "history_redshift_max": float(path.redshift_grid()[0]),
        "minus_initialization_convention": "h_minus0_ratio=1/(1-2*q0)",
        "strict_paper_only_background_materialization_closed": False,
        "remaining_blockers": [
            "paper_native_absolute_density_normalization_not_materialized_from_2024_text_alone",
            "minus_history_initialization_not_fixed_explicitly_by_2024_text",
            "bulk_history_still_uses_cited_calibration_layer",
        ],
        "verdict": {
            "bulk_materialization_exists": True,
            "bulk_materialization_is_strict_paper_only": False,
            "bulk_materialization_is_usable_for_next_improvement_branch": True,
        },
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# The Janus Cosmological Model 2024 Paper-Native Materialization Audit",
                "",
                f"Bulk materialization exists: `{payload['verdict']['bulk_materialization_exists']}`",
                f"Strict paper-only bulk materialization closed: `{payload['strict_paper_only_background_materialization_closed']}`",
                f"Paper-plus-cited layer closed up to minus init: `{payload['paper_plus_cited_calibration_layer_closed_up_to_minus_init']}`",
                f"Plus history source kind: `{payload['plus_history_source_kind']}`",
                f"Minus history source kind: `{payload['minus_history_source_kind']}`",
                f"Absolute normalization source kind: `{payload['absolute_normalization_source_kind']}`",
                "",
                "## Remaining blockers",
                "",
                *[f"- `{item}`" for item in payload["remaining_blockers"]],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
