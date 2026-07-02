from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_hard_external_theorem_target_registry.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_hard_external_theorem_target_registry.json")


def build_payload() -> dict:
    targets = {
        "aps_pin_global_index": {
            "external_or_local_target_declared": True,
            "can_be_replaced_by_import": True,
            "accepted_import_must_prove": [
                "pin_minus_lift_squared_minus_one",
                "aps_boundary_projector_fredholm",
                "eta_zero_mode_cancellation_global",
                "no_parity_anomaly_global",
                "trace_regularization_standard_global",
            ],
            "closed": False,
        },
        "orbifold_cover_ratio_2_to_1": {
            "external_or_local_target_declared": True,
            "can_be_replaced_by_import": False,
            "accepted_import_must_prove": [
                "global_euler_holonomy_class_computed",
                "volume_cover_ratio_two_to_one",
                "global_volume_ratio_unique_two_to_one",
            ],
            "closed": False,
        },
        "unique_action_to_equations": {
            "external_or_local_target_declared": True,
            "can_be_replaced_by_import": False,
            "accepted_import_must_prove": [
                "full_nonlinear_boundary_variation_closed",
                "common_obstruction_vanishes",
                "ward_closure_ready",
                "gauge_fixed_boundary_variation_unique",
            ],
            "closed": False,
        },
    }
    registry_ready = all(row["external_or_local_target_declared"] for row in targets.values())
    return {
        "status": "janus-z4-hard-external-theorem-target-registry",
        "targets": targets,
        "registry_complete": registry_ready,
        "imported_theorem_may_replace_only_matching_target": True,
        "no_fit_promotion_requires_all_targets_closed": True,
        "all_hard_targets_closed": all(row["closed"] for row in targets.values()),
        "pure_math_model_closed_without_axioms": False,
        "full_cosmology_prediction_ready_no_fit": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Hard External Theorem Target Registry",
        "",
        f"Registry complete: `{payload['registry_complete']}`",
        f"All hard targets closed: `{payload['all_hard_targets_closed']}`",
        f"No-fit promotion requires all targets closed: `{payload['no_fit_promotion_requires_all_targets_closed']}`",
        "",
    ]
    for name, row in payload["targets"].items():
        lines.extend([
            f"## `{name}`",
            f"- can be replaced by import: `{row['can_be_replaced_by_import']}`",
            f"- closed: `{row['closed']}`",
            "- accepted import/proof must prove:",
        ])
        lines.extend(f"  - `{item}`" for item in row["accepted_import_must_prove"])
        lines.append("")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
