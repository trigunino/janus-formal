from __future__ import annotations

import json
from pathlib import Path


OUTPUT_PATH = Path("outputs/active_z2_sigma/linear_k_partition_audit.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_linear_k_partition_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_linear_k_partition_audit.json")


def build_payload(*, output_path: Path = OUTPUT_PATH) -> dict:
    comparison = {
        "required_from_mixed_trace_match": "L_required_linear = (4/kappa_Z2Sigma) K",
        "canonical_Cartan_GHY_density": "L_CartanGHY = (epsilon_Z2/kappa_Z2Sigma) K",
        "ratio_required_to_canonical_single_oriented_side": "4*epsilon_Z2",
        "same_operator": "sqrt(|h|) K",
        "independent_counterterm_allowed": False,
    }
    decision = {
        "linear_K_piece_already_in_known_boundary_operator_class": True,
        "must_be_partitioned_into_Cartan_GHY_or_junction_sector": True,
        "counterterm_linear_K_residual_allowed": False,
        "counterterm_remaining_density_must_be_non_GHY": True,
        "R_Sigma_solution_certificate_still_blocked": True,
    }
    payload = {
        "status": "janus-z2-sigma-linear-k-partition-audit",
        "active_core": "Z2_tunnel_Sigma",
        "source": "symbolic_partition_audit",
        "comparison": comparison,
        "decision": decision,
        "interpretation": (
            "The only minimal mixed h,K term that matches the finite-throat trace "
            "is proportional to sqrt(|h|)K, the same operator class as Cartan-GHY. "
            "It may indicate a partition/normalization issue in the existing "
            "Cartan-GHY+junction blocks, but it cannot be introduced again as an "
            "independent Sigma counterterm."
        ),
        "next_required": [
            "audit_CartanGHY_plus_junction_normalization_against_finite_throat_trace",
            "subtract_known_linear_K_operator_from_counterterm_basis",
            "derive_remaining_non_GHY_density_or_show_remaining_counterterm_zero",
        ],
        "forbidden_shortcuts": [
            "do_not_duplicate_sqrt_h_K_operator_in_L_ct",
            "do_not_absorb_partition_mismatch_into_fitted_counterterm",
            "do_not_promote_RSigma_certificate_before_partition_audit",
        ],
        "output_manifest": str(output_path),
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Linear K Partition Audit",
        "",
        payload["interpretation"],
        "",
        "## Comparison",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["comparison"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
