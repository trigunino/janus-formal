from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_the_janus_cosmological_model_2024_bao_contract_audit import (
    build_payload as build_bao_payload,
)
from scripts.build_p0_eft_the_janus_cosmological_model_2024_minus_sector_initialization_audit import (
    build_payload as build_minus_init_payload,
)
from scripts.build_p0_eft_the_janus_cosmological_model_2024_normalization_contract_gate import (
    build_payload as build_norm_payload,
)
from scripts.build_p0_eft_the_janus_cosmological_model_2024_paper_native_materialization_audit import (
    build_payload as build_bulk_payload,
)
from scripts.build_p0_eft_the_janus_cosmological_model_2024_paper_native_sn_fit_audit import (
    build_payload as build_sn_payload,
)
from scripts.build_p0_eft_the_janus_cosmological_model_2024_sector_split_operational_audit import (
    build_payload as build_split_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_frontier_status.json"
REPORT_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_frontier_status.md"


def build_payload() -> dict:
    sn = build_sn_payload()
    bulk = build_bulk_payload()
    minus_init = build_minus_init_payload()
    norm = build_norm_payload()
    bao = build_bao_payload()
    split = build_split_payload()
    return {
        "status": "the-janus-cosmological-model-2024-frontier-status",
        "step1_sn_pipeline": {
            "source_boundary_reached": True,
            "official_pipeline_recovers_published_q0": sn["verdict"]["official_jla_pipeline_recovers_published_q0"],
            "paper_like_pipeline_recovers_published_q0": sn["verdict"]["paper_like_pipeline_recovers_published_q0"],
            "exact_q0_and_chi2_simultaneous_closure": sn["verdict"]["exact_published_q0_and_chi2_simultaneous_reproduction_closed"],
        },
        "step2_two_metric_background": {
            "strict_paper_only_closed": bulk["strict_paper_only_background_materialization_closed"],
            "cited_assisted_layer_closed_up_to_minus_init": bulk["paper_plus_cited_calibration_layer_closed_up_to_minus_init"],
            "minus_initialization_source_underdetermined": minus_init["minus_sector_initialization_is_source_underdetermined"],
        },
        "step3_absolute_normalization": {
            "strict_paper_only_closed": norm["strict_paper_only_contract_ready"],
            "cited_assisted_closed": norm["cited_assisted_contract_ready"],
            "source_boundary_reached": norm["step3_source_boundary_reached"],
        },
        "step4_native_bao_contract": {
            "native_bao_geometry_basis_present": bao["native_bao_geometry_basis_present"],
            "native_bao_ruler_closed": bao["native_bao_ruler_closed"],
            "source_boundary_reached": bao["step4_source_boundary_reached"],
        },
        "step5_sector_split_operationality": {
            "relative_split_present": split["relative_sector_split_present"],
            "absolute_background_input_ready": split["operational_absolute_background_input_ready"],
            "cited_assisted_background_input_ready": split["operational_cited_assisted_background_input_ready"],
            "source_boundary_reached": split["step5_source_boundary_reached"],
        },
        "step6_native_cmb_branch": {
            "opened": False,
            "blocked_by_steps_2_to_5": True,
        },
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# The Janus Cosmological Model 2024 Frontier Status",
                "",
                f"Step 1 source boundary reached: `{payload['step1_sn_pipeline']['source_boundary_reached']}`",
                f"Step 2 strict paper-only closed: `{payload['step2_two_metric_background']['strict_paper_only_closed']}`",
                f"Step 3 strict paper-only closed: `{payload['step3_absolute_normalization']['strict_paper_only_closed']}`",
                f"Step 4 native BAO ruler closed: `{payload['step4_native_bao_contract']['native_bao_ruler_closed']}`",
                f"Step 5 absolute background input ready: `{payload['step5_sector_split_operationality']['absolute_background_input_ready']}`",
                f"Step 6 opened: `{payload['step6_native_cmb_branch']['opened']}`",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
