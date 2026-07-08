from __future__ import annotations

import json
from pathlib import Path


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_bao_contract_audit.json"
REPORT_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_bao_contract_audit.md"


def build_payload() -> dict:
    return {
        "status": "the-janus-cosmological-model-2024-bao-contract-audit",
        "source_set_checked": [
            "EPJC2024_the-janus-cosmological-model",
            "M18_constraints-on-janus-cosmological-model-from-recent-observations-of-supernovae-t",
            "X2022-hal-acceleration-cosmic-expansion",
            "X2026-variable-constants",
            "X2026-expansion-desi",
        ],
        "source_fixed_items_found": [
            "plus_branch_open_distance_basis",
            "published_q0_anchor",
            "published_open_geometry_distance_relations",
            "published_variable_constants_eq40_exponents",
        ],
        "source_missing_items": [
            "native_sound_horizon_or_ruler_definition",
            "native_mapping_from_open_distance_basis_to_DESI_compressed_BAO_vector",
            "source_derived_D_M_over_r_d_contract",
            "source_derived_D_H_over_r_d_contract",
            "source_derived_D_V_over_r_d_contract",
        ],
        "native_bao_geometry_basis_present": True,
        "native_bao_ruler_closed": False,
        "native_bao_observable_contract_closed": False,
        "variable_constants_supply_bao_clue_only": True,
        "step4_source_boundary_reached": True,
        "allowed_conclusion": "BAO_continuation_requires_new_paper_level_derivation_or_explicit_post_paper_rule_not_present_in_current_source_boundary",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# The Janus Cosmological Model 2024 BAO Contract Audit",
                "",
                f"Native BAO geometry basis present: `{payload['native_bao_geometry_basis_present']}`",
                f"Native BAO ruler closed: `{payload['native_bao_ruler_closed']}`",
                f"Native BAO observable contract closed: `{payload['native_bao_observable_contract_closed']}`",
                f"Step-4 source boundary reached: `{payload['step4_source_boundary_reached']}`",
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
