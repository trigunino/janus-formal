from __future__ import annotations

import json
from pathlib import Path


OUTPUT_PATH = Path("outputs/active_z2_sigma/mixed_hk_trace_solution_obstruction.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_mixed_hk_trace_solution_obstruction.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_mixed_hk_trace_solution_obstruction.json")


def build_payload(*, output_path: Path = OUTPUT_PATH) -> dict:
    solution_family = {
        "target": "h_trace_R_h = 12/(kappa_Z2Sigma R)",
        "minimal_basis_h_trace": "3*c1*epsilon_Z2/R + (18*c2+6*c3)/R^2",
        "coefficient_conditions": {
            "c1": "4*epsilon_Z2/kappa_Z2Sigma",
            "c3": "-3*c2",
            "c2": "free unless extra curvature-sector condition is derived",
        },
        "R_K_trace_family": (
            "R_K_q = -12/(kappa_Z2Sigma R^2) - 18*c2/R^3"
        ),
    }
    obstruction = {
        "dirichlet_h_only_minimal_counterterm_closes": False,
        "dirichlet_h_only_reason": (
            "after imposing no independent K variation, the remaining minimal "
            "constant basis scales as 1/R^2 and cannot match the finite Israel "
            "trace target scaling 1/R for all R"
        ),
        "linear_K_required": True,
        "linear_K_term": "c1*epsilon_Z2*K",
        "cartan_GHY_like": True,
        "counterterm_non_duplication_policy_satisfied": False,
        "minimal_mixed_hK_counterterm_closes": False,
    }
    payload = {
        "status": "janus-z2-sigma-mixed-hk-trace-solution-obstruction",
        "active_core": "Z2_tunnel_Sigma",
        "source": "symbolic_derivation",
        "input_result": "resolved_throat_trace_equations",
        "solution_family": solution_family,
        "obstruction": obstruction,
        "interpretation": (
            "Allowing mixed h,K variation lets the minimal basis match the finite "
            "Israel throat trace only by turning on the linear epsilon_Z2*K term. "
            "That term is Cartan-GHY-like, so it cannot be promoted as an independent "
            "Sigma counterterm under the active non-duplication policy."
        ),
        "decision": {
            "dirichlet_h_only_selected": False,
            "mixed_hK_minimal_counterterm_selected": False,
            "do_not_promote_minimal_mixed_hK_counterterm": True,
            "do_not_claim_E_counterterm_closed": True,
            "redirect_linear_K_piece_to_Cartan_GHY_or_junction_partition": True,
            "active_counterterm_must_be_non_GHY_density": True,
            "selected_remaining_route": (
                "derive_non_GHY_tunnel_density_or_repartition_radius_blocks"
            ),
        },
        "next_required": [
            "audit_whether_linear_K_trace_belongs_to_existing_Cartan_GHY_or_junction_block",
            "derive_non_GHY_local_density_from_tunnel_resolution_if_counterterm_still_needed",
            "or_repartition_E_RSigma_blocks_to_avoid_duplicate_linear_K_counterterm",
        ],
        "forbidden_shortcuts": [
            "do_not_keep_c1_epsilon_K_as_new_counterterm",
            "do_not_fit_c2",
            "do_not_hide_GHY_duplicate_inside_L_ct",
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
        "# Janus Z2/Sigma Mixed hK Trace Solution Obstruction",
        "",
        payload["interpretation"],
        "",
        f"Minimal mixed hK counterterm closes: `{payload['obstruction']['minimal_mixed_hK_counterterm_closes']}`",
        f"Cartan-GHY-like duplicate: `{payload['obstruction']['cartan_GHY_like']}`",
        "",
        "## Coefficient Conditions",
    ]
    lines.extend(
        f"- `{key}`: `{value}`"
        for key, value in payload["solution_family"]["coefficient_conditions"].items()
    )
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
