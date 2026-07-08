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


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_minus_sector_initialization_audit.json"
REPORT_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_minus_sector_initialization_audit.md"


def build_payload() -> dict:
    return {
        "status": "the-janus-cosmological-model-2024-minus-sector-initialization-audit",
        "source_set_checked": [
            "EPJC2024_the-janus-cosmological-model",
            "M18_constraints-on-janus-cosmological-model-from-recent-observations-of-supernovae-t",
            "X2022-hal-acceleration-cosmic-expansion",
            "M20_the-janus-cosmological-model-and-the-fluctuations-of-the-cmb",
            "M30_a-bimetric-cosmological-model-based-on-andrei-sakharov-s-twin-universe-approach",
        ],
        "source_fixed_items_found": [
            "common_time_coordinate_x0",
            "k_plus_equals_k_minus_equals_minus_one_branch",
            "global_signed_energy_conservation_shape",
            "plus_branch_exact_shape_a_plus_u",
            "published_q0_anchor",
            "relative_sector_content_claim",
            "order_of_magnitude_a_minus_over_a_plus_from_cmb_imprint",
        ],
        "source_missing_items": [
            "explicit_present_day_a_minus_normalization",
            "explicit_present_day_H_minus_normalization",
            "explicit_minus_initial_value_rule_equivalent_to_h_minus0_ratio",
        ],
        "repo_current_minus_initialization_convention": "h_minus0_ratio=1/(1-2*q0)",
        "source_derives_repo_current_minus_initialization_convention": False,
        "minus_sector_initialization_is_source_underdetermined": True,
        "allowed_conclusion": "paper_plus_cited_calibration_layer_may_use_repo_minus_initialization_as_helper_only_not_as_source_closed_bulk_law",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# The Janus Cosmological Model 2024 Minus-Sector Initialization Audit",
                "",
                f"Source-derives current minus initialization convention: `{payload['source_derives_repo_current_minus_initialization_convention']}`",
                f"Minus-sector initialization source-underdetermined: `{payload['minus_sector_initialization_is_source_underdetermined']}`",
                f"Repo convention: `{payload['repo_current_minus_initialization_convention']}`",
                "",
                "## Source-missing items",
                "",
                *[f"- `{item}`" for item in payload["source_missing_items"]],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
