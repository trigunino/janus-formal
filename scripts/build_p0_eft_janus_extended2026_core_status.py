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
from scripts.build_p0_eft_janus_extended2026_published_background_status import (
    build_payload as build_published_background_payload,
)
from scripts.build_p0_eft_janus_extended2026_observational_claim_map import (
    build_payload as build_claim_map_payload,
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
    published_background = build_published_background_payload()
    claim_map = build_claim_map_payload()
    eq40 = core.variable_constants_eq40_exponents()
    layers = core.branch_layers()

    return {
        "status": "janus-extended2026-core-status",
        "source_bundle_ready": True,
        "core_source_ids": list(core.source_ids),
        "supporting_cosmology_source_ids": list(core.supporting_cosmology_source_ids),
        "supporting_math_source_ids": list(core.supporting_math_source_ids),
        "adjacent_noncore_source_ids": list(core.adjacent_noncore_source_ids),
        "branch_layers": {key: list(value) for key, value in layers.items()},
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
            "strict_published_plus_branch_present": bool(
                published_background["published_plus_branch_executable"]
            ),
            "strict_published_sn_proxy_present": bool(
                published_background["published_sn_proxy_executable"]
            ),
            "background_observational_endpoint_present": bool(
                published_background["full_background_observational_endpoint_closed"]
            ),
        },
        "published_background_status": {
            "source_policy": published_background["source_policy"],
            "strict_minus_sector_history_closed": published_background[
                "strict_minus_sector_history_closed"
            ],
            "native_bao_ruler_closed": published_background[
                "native_bao_ruler_closed"
            ],
            "sn_full_covariance_chi2": published_background["sn_full_covariance"][
                "chi2"
            ],
            "full_background_observational_endpoint_closed": published_background[
                "full_background_observational_endpoint_closed"
            ],
        },
        "observational_claim_map": {
            "strictly_reproducible_claim_count": claim_map[
                "strictly_reproducible_claim_count"
            ],
            "non_executable_claim_count": claim_map["non_executable_claim_count"],
            "next_allowed_execution_scope": claim_map["next_allowed_execution_scope"],
            "forbidden_scope_without_new_paper_level_derivation": claim_map[
                "forbidden_scope_without_new_paper_level_derivation"
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
                f"Strict published plus branch present: `{payload['executable_components']['strict_published_plus_branch_present']}`",
                f"Strict published SN proxy present: `{payload['executable_components']['strict_published_sn_proxy_present']}`",
                f"Strictly reproducible observational claims: `{payload['observational_claim_map']['strictly_reproducible_claim_count']}`",
                f"Native 2026 BAO ruler executable: `{payload['native_2026_bao_ruler_executable']}`",
                f"Native 2026 CMB path executable: `{payload['native_2026_cmb_path_executable']}`",
                f"Observational closure ready: `{payload['observational_closure_ready']}`",
                "",
                "## Core sources",
                "",
                *[f"- `{item}`" for item in payload["core_source_ids"]],
                "",
                "## Supporting cosmology sources",
                "",
                *[
                    f"- `{item}`"
                    for item in payload["supporting_cosmology_source_ids"]
                ],
                "",
                "## Supporting math sources",
                "",
                *[f"- `{item}`" for item in payload["supporting_math_source_ids"]],
                "",
                "## Adjacent non-core sources",
                "",
                *[f"- `{item}`" for item in payload["adjacent_noncore_source_ids"]],
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
