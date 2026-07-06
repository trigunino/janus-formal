from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_alpha_res_z2_anti_invariance_obligation_gate import (
    build_payload as build_alpha_res_route,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_point_collapse_limit_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_point_collapse_limit_gate.json"
)


def build_payload() -> dict:
    alpha = build_alpha_res_route()
    scaling_channels = {
        "linear_K_slot": {
            "model": "sqrt_h ~ R_Sigma^3, K ~ R_Sigma^-1",
            "integrated_scaling": "O(R_Sigma^2)",
            "vanishes_if_bound_uniform": True,
        },
        "quadratic_K_slot": {
            "model": "sqrt_h * K^2",
            "integrated_scaling": "O(R_Sigma)",
            "vanishes_if_bound_uniform": True,
        },
        "cubic_or_delta_slot": {
            "model": "sqrt_h * K^3 or point-supported defect",
            "integrated_scaling": "O(1) or worse",
            "vanishes_if_bound_uniform": False,
        },
    }
    declared = {
        "point_collapse_route_declared": True,
        "singular_limit_not_smooth_sigma_declared": True,
        "active_pipeline_replacement_forbidden": True,
        "fitted_counterterm_coefficient_forbidden": True,
        "density_ansatz_bypass_forbidden_without_limit_certificate": True,
    }
    closure = {
        "alpha_res_route_available": alpha["route_status"] in {"credible_but_blocked", "closed"},
        "volume_collapse_rate_declared": True,
        "alpha_res_growth_bound_declared": False,
        "distributional_defect_control_declared": False,
        "z2_limit_compatibility_declared": False,
        "integrated_alpha_res_vanishes_proved": False,
        "L_ct_bypass_ready": False,
    }
    gate_passed = all(declared.values()) and all(closure.values())
    blockers = [key for key, value in closure.items() if not value]
    return {
        "status": "janus-z2-sigma-point-collapse-limit-gate",
        "active_core": "Z2_tunnel_Sigma",
        "route": "SigmaPointCollapseLimitGate",
        "source": "exploratory_branch_only",
        "declared": declared,
        "limit_formula": {
            "target": "lim_{R_Sigma -> 0} integral_Sigma(R_Sigma) alpha_res = 0",
            "controlled_bound": "|alpha_res| <= C * R_Sigma^-p with p < 3",
            "danger": "p >= 3 or delta_point defects can leave a finite/divergent residue",
            "consequence_if_proved": "E_counterterm can be zero without explicit L_ct",
        },
        "scaling_channels": scaling_channels,
        "closure": closure,
        "upstream_alpha_res_route": {
            "status": alpha["status"],
            "route_status": alpha["route_status"],
            "primary_blocker": alpha["primary_blocker"],
            "component_values_available": alpha["closure"]["alpha_res_component_values_available"],
        },
        "route_status": "credible_but_blocked" if not gate_passed else "closed",
        "gate_passed": gate_passed,
        "primary_blocker": "none" if gate_passed else blockers[0],
        "blockers": blockers,
        "interpretation": (
            "The point-collapse limit is a valid isolated question, but it is not a "
            "drop-in replacement for the smooth Sigma pipeline. It would need a "
            "uniform alpha_res growth bound, control of point-supported defects, "
            "and a proof that the Z2 geometry survives the singular limit."
        ),
        "next_required": []
        if gate_passed
        else [
            "emit_alpha_res_component_scaling_exponents_in_R_Sigma",
            "prove_uniform_bound_p_less_than_3_for_all_components",
            "exclude_delta_point_distributional_residue",
            "prove_Z2_pairing_survives_R_Sigma_to_zero_limit",
            "then_reassess_L_ct_bypass_without_polluting_active_pipeline",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Point Collapse Limit Gate",
        "",
        f"Route status: `{payload['route_status']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Limit Formula",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["limit_formula"].items())
    lines.extend(["", "## Scaling Channels"])
    for name, item in payload["scaling_channels"].items():
        lines.append(
            f"- `{name}`: scaling=`{item['integrated_scaling']}`, "
            f"safe_if_uniform=`{item['vanishes_if_bound_uniform']}`"
        )
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
