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

from janus_lab import published_janus_extended2026_core
from scripts.build_p0_eft_janus_z2_background_observational_endpoint import (
    build_payload as build_background_endpoint_payload,
)
from scripts.build_p0_eft_the_janus_cosmological_model_2024_bulk_observable_path_gate import (
    build_payload as build_bulk_path_payload,
)
from scripts.build_p0_eft_the_janus_cosmological_model_2024_normalization_contract_gate import (
    build_payload as build_normalization_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_extended2026_core_status.json"
REPORT_PATH = REPORTS / "p0_eft_janus_extended2026_core_status.md"


def build_payload() -> dict:
    core = published_janus_extended2026_core()
    bulk_path = build_bulk_path_payload()
    normalization = build_normalization_payload()
    endpoint = build_background_endpoint_payload()
    eq40 = core.variable_constants_eq40_exponents()

    return {
        "status": "janus-extended2026-core-status",
        "source_bundle_ready": True,
        "core_source_ids": list(core.source_ids),
        "verified_equation_anchors": list(core.verified_equation_anchors),
        "verified_source_claims": list(core.verified_source_claims),
        "variable_constants_eq40_exponents": eq40,
        "executable_components": {
            "cited_calibration_present": True,
            "bulk_two_metric_path_present": bool(
                bulk_path["background_path_uses_bulk_two_metric_history"]
            ),
            "absolute_normalization_contract_present": bool(
                normalization["absolute_normalization_contract_instantiated"]
            ),
            "background_observational_endpoint_present": True,
        },
        "background_observational_endpoint": {
            "verdict": endpoint["verdict"],
            "best_baseline_family": endpoint["best_baseline_family"],
            "delta_chi2_janus_minus_best_baseline": endpoint[
                "delta_chi2_janus_minus_best_baseline"
            ],
            "gr_limit_edge_preferred": endpoint["gr_limit_edge_preferred"],
            "continuation_to_branch_3_recommended": endpoint[
                "continuation_to_branch_3_recommended"
            ],
        },
        "native_2026_bao_ruler_executable": False,
        "native_2026_cmb_path_executable": False,
        "observational_closure_ready": False,
        "current_blockers": list(core.current_blockers()),
        "next_required": [
            "derive_native_bao_ruler_from_M18_plus_X2026_variable_constants",
            "separate_paper_native_background_from_cited_SN_calibration",
            "add_extended2026_background_runner_before_CMB_claims",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Extended2026 Core Status",
                "",
                f"Source bundle ready: `{payload['source_bundle_ready']}`",
                f"Bulk two-metric path present: `{payload['executable_components']['bulk_two_metric_path_present']}`",
                f"Absolute normalization contract present: `{payload['executable_components']['absolute_normalization_contract_present']}`",
                f"Background observational endpoint verdict: `{payload['background_observational_endpoint']['verdict']}`",
                f"GR-limit edge preferred: `{payload['background_observational_endpoint']['gr_limit_edge_preferred']}`",
                f"Native 2026 BAO ruler executable: `{payload['native_2026_bao_ruler_executable']}`",
                f"Native 2026 CMB path executable: `{payload['native_2026_cmb_path_executable']}`",
                f"Observational closure ready: `{payload['observational_closure_ready']}`",
                "",
                "## Core sources",
                "",
                *[f"- `{item}`" for item in payload["core_source_ids"]],
                "",
                "## Current blockers",
                "",
                *[f"- `{item}`" for item in payload["current_blockers"]],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
