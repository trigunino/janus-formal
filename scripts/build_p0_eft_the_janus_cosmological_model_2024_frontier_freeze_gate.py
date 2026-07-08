from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_the_janus_cosmological_model_2024_frontier_status import (
    build_payload as build_frontier_status_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_frontier_freeze_gate.json"
REPORT_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_frontier_freeze_gate.md"


def build_payload() -> dict:
    frontier = build_frontier_status_payload()
    return {
        "status": "the-janus-cosmological-model-2024-frontier-freeze-gate",
        "frontier_status_gate": frontier["status"],
        "the_janus_cosmological_model_2024_frontier_branch_frozen": True,
        "current_source_set_exploration_exhausted": True,
        "full_prediction_closed_with_current_source_set": False,
        "no_more_progress_without_enlarging_allowed_source_set": True,
        "freeze_scope": {
            "paper_only": True,
            "paper_plus_cited_comparison": True,
            "source_boundary_frontier": True,
        },
        "source_boundary_summary": {
            "step1_sn_pipeline_reached_boundary": frontier["step1_sn_pipeline"]["source_boundary_reached"],
            "step2_strict_paper_only_closed": frontier["step2_two_metric_background"]["strict_paper_only_closed"],
            "step3_strict_paper_only_closed": frontier["step3_absolute_normalization"]["strict_paper_only_closed"],
            "step4_native_bao_ruler_closed": frontier["step4_native_bao_contract"]["native_bao_ruler_closed"],
            "step5_absolute_background_input_ready": frontier["step5_sector_split_operationality"]["absolute_background_input_ready"],
            "step6_native_cmb_opened": frontier["step6_native_cmb_branch"]["opened"],
        },
        "current_branch_verdict": {
            "prediction_space_explored_to_current_source_boundary": True,
            "observational_closure_requires_new_theoretical_input": True,
            "acceptable_next_move": "start_new_branch_with_enlarged_theoretical_source_set",
        },
        "forbidden_next_move_inside_frozen_branch": [
            "pretend_step2_is_closed_from_same_texts",
            "pretend_step3_absolute_normalization_is_source_closed",
            "pretend_step4_native_bao_ruler_exists",
            "open_native_cmb_on_unclosed_background",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# The Janus Cosmological Model 2024 Frontier Freeze Gate",
                "",
                f"Frontier branch frozen: `{payload['the_janus_cosmological_model_2024_frontier_branch_frozen']}`",
                f"Current source-set exploration exhausted: `{payload['current_source_set_exploration_exhausted']}`",
                f"Full prediction closed with current source set: `{payload['full_prediction_closed_with_current_source_set']}`",
                f"No more progress without enlarging allowed source set: `{payload['no_more_progress_without_enlarging_allowed_source_set']}`",
                f"Next move: `{payload['current_branch_verdict']['acceptable_next_move']}`",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
