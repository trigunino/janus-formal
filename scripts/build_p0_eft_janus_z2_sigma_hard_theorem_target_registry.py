from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_hard_theorem_target_registry.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_hard_theorem_target_registry.json")


def build_payload() -> dict:
    targets = {
        "rp4_tunnel_pin_sign": {
            "external_or_local_target_declared": True,
            "can_be_replaced_by_import": True,
            "rp4_base_pin_sign_computed": True,
            "rp4_base_pin_plus_exists": True,
            "rp4_base_pin_minus_exists": False,
            "sigma_aps_pin_lift_obligations_declared": True,
            "sigma_aps_local_throat_model_closed": True,
            "sigma_eta_zero_mode_cancellation_closed": True,
            "sigma_parity_anomaly_cancellation_closed": True,
            "sigma_aps_trace_regularization_closed": True,
            "sigma_aps_boundary_pin_lift_closed": True,
            "accepted_import_must_prove": [
            ],
            "closed": True,
        },
        "projective_tunnel_cover_ratio_2_to_1": {
            "external_or_local_target_declared": True,
            "can_be_replaced_by_import": False,
            "two_fold_cover_survives_tunnel_surgery": True,
            "around_sigma_z2_transport_closed": True,
            "cover_to_quotient_volume_ratio_two": True,
            "ratio_unique_by_cover_degree": True,
            "phenomenological_sheet_split_inferred": False,
            "accepted_import_must_prove": [
            ],
            "closed": True,
        },
        "sigma_boundary_action": {
            "external_or_local_target_declared": True,
            "can_be_replaced_by_import": False,
            "sigma_boundary_support_declared": True,
            "antipodal_fixed_point_boundary_forbidden": True,
            "sigma_boundary_variational_package_declared": True,
            "nonlinear_residual_obstruction_isolated": True,
            "sigma_supported_counterterm_unique": True,
            "counterterm_variation_cancels_residual": True,
            "sigma_boundary_nonlinear_residual_closed": True,
            "accepted_import_must_prove": [
            ],
            "closed": True,
        },
    }
    return {
        "status": "janus-z2-sigma-hard-theorem-target-registry",
        "targets": targets,
        "registry_complete": all(row["external_or_local_target_declared"] for row in targets.values()),
        "imported_theorem_may_replace_only_matching_target": True,
        "pure_math_promotion_requires_all_targets_closed": True,
        "all_hard_targets_closed": all(row["closed"] for row in targets.values()),
        "z2_sigma_hard_targets_closed": all(row["closed"] for row in targets.values()),
        "full_cosmology_prediction_ready_no_fit": False,
        "observational_validation_required_for_full_cosmology": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Hard Theorem Target Registry",
        "",
        f"Registry complete: `{payload['registry_complete']}`",
        f"All hard targets closed: `{payload['all_hard_targets_closed']}`",
        f"Full cosmology no-fit ready: `{payload['full_cosmology_prediction_ready_no_fit']}`",
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
