from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_global_regular_freg_data_frontier_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_global_regular_freg_data_frontier_gate.json")


def build_payload() -> dict:
    frontier = {
        "normal_frame_holonomy_defect": {
            "needed_primitives": [
                "lambda_grid",
                "collar_coordinate_u_grid",
                "normal_connection_omega_perp_lambda_u",
                "deck_frame_map_lambda",
                "closed_collar_cycle_ordering",
            ],
            "formula_target": "||D_Z2 P exp(int omega_perp du) - Id||^2",
            "ready": False,
        },
        "collar_endpoint_mismatch": {
            "needed_primitives": [
                "h_plus_endpoint_lambda",
                "h_minus_endpoint_lambda",
                "tau_Z2_pullback_matrix_on_endpoint_tangents",
                "endpoint_metric_norm",
            ],
            "formula_target": "||tau_Z2^* h_minus - h_plus||^2",
            "ready": False,
        },
        "junction_bianchi_defect": {
            "needed_primitives": [
                "S_Sigma_ab_lambda",
                "D_a_Sigma_connection_lambda",
                "bulk_normal_flux_jump_lambda",
                "surface_vector_norm",
            ],
            "formula_target": "||D_a S_Sigma^{ab} + [T_n^b]_Z2||^2",
            "ready": False,
        },
    }
    return {
        "status": "janus-z2-sigma-global-regular-freg-data-frontier-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_symbolic_audit",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "torus_replacement_used": False,
        "full_no_fit_prediction_ready": False,
        "frontier": frontier,
        "all_primitives_ready": all(item["ready"] for item in frontier.values()),
        "gate_passed": True,
        "primary_blocker": "active_freg_primitives_not_materialized",
        "next_required": [
            "materialize normal_connection_omega_perp_lambda_u",
            "materialize endpoint collar metrics and tau_Z2 pullback matrix",
            "materialize Sigma stress divergence and bulk normal flux jump",
            "then write outputs/active_z2_sigma/global_regular_freg_components.json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Global Regular F_reg Data Frontier Gate",
        "",
        f"All primitives ready: `{payload['all_primitives_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Frontier",
    ]
    for name, item in payload["frontier"].items():
        lines.append(f"- `{name}` ready=`{item['ready']}` target=`{item['formula_target']}`")
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
