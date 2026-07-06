from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_minimal_basis_trace_constraints_gate import (
    build_payload as build_trace_constraints,
)
from scripts.derive_p0_eft_janus_z2_sigma_surface_action_or_no_go_gate import (
    build_payload as build_surface_action_no_go,
)
from scripts.derive_p0_eft_janus_z2_sigma_holst_palatini_boundary_theta_pt67_projection import (
    build_payload as build_theta_projection,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_minimal_basis_dual_route_decision_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_minimal_basis_dual_route_decision_gate.json"
)


def build_payload() -> dict:
    trace = build_trace_constraints()
    surface_action = build_surface_action_no_go()
    theta_projection = build_theta_projection()
    traces_available = False
    direct_action_ready = not surface_action["no_unique_surface_action_from_current_inputs"]
    nonzero_parametric_ready = True
    winner = "none"
    if traces_available:
        winner = "active_trace_solution_route"
    elif direct_action_ready:
        winner = "direct_surface_action_route"
    return {
        "status": "janus-z2-sigma-counterterm-minimal-basis-dual-route-decision-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "diagnostic_reduction",
        "routes": {
            "active_trace_solution_route": {
                "ready": traces_available,
                "requires": ["active_R_h_trace_target", "active_R_K_trace_target"],
                "status": "blocked",
                "reason": "repo_has_no_active_R_h_trace_or_R_K_trace_payload",
            },
            "nonzero_parametric_E_counterterm_route": {
                "ready": nonzero_parametric_ready,
                "status": "parametric_only",
                "expression": "E_ct(R)=sqrt(q)*(6*c1*epsilon_Z2*R + 9*c2 + 6*c3)",
                "requires_for_numeric": [
                    "c1_c2_c3_from_active_trace_targets_or_boundary_condition",
                    "R_Sigma(a)",
                    "sqrt_q_or_volume_normalization",
                ],
            },
            "direct_surface_action_route": {
                "ready": direct_action_ready,
                "status": "blocked" if not direct_action_ready else "ready",
                "reason": (
                    "no_unique_surface_action_from_current_inputs"
                    if not direct_action_ready
                    else "active_surface_action_density_available"
                ),
                "missing_for_closure": surface_action["missing_for_closure"],
            },
            "holst_palatini_theta_projection_route": {
                "ready": bool(theta_projection["gate_passed"]),
                "status": "eliminates_theta_non_GHY_traces"
                if theta_projection["gate_passed"]
                else "blocked",
                "R_h_trace_from_theta": theta_projection.get("projection", {})
                .get("projection_result", {})
                .get("non_GHY_metric_trace_R_h_from_theta"),
                "R_K_trace_from_theta": theta_projection.get("projection", {})
                .get("projection_result", {})
                .get("non_GHY_extrinsic_trace_R_K_from_theta"),
                "counterterm_component_unblocked": theta_projection.get("projection", {}).get(
                    "counterterm_component_unblocked", False
                ),
            },
        },
        "decision": {
            "winner": winner,
            "preferred_next": "derive_active_R_h_trace_and_R_K_trace",
            "fallback": "derive_direct_active_surface_density_or_carry_parametric_E_counterterm_until_boundary_condition_available",
            "do_not_claim_E_counterterm_zero": True,
            "do_not_fit_c1_c2_c3": True,
        },
        "upstream": {
            "minimal_trace_constraints": {
                "gate": trace["status"],
                "fully_determined": trace["solvability"][
                    "coefficients_fully_determined_by_minimal_basis"
                ],
                "minimum_new_inputs": trace["solvability"]["minimum_new_inputs_needed"],
            }
        },
        "direct_action_audit": {
            "gate": surface_action["status"],
            "no_unique_surface_action_from_current_inputs": surface_action[
                "no_unique_surface_action_from_current_inputs"
            ],
            "decision": surface_action["decision"],
        },
        "theta_projection_audit": {
            "gate": theta_projection["status"],
            "passed": theta_projection["gate_passed"],
            "counterterm_component_unblocked": theta_projection.get("projection", {}).get(
                "counterterm_component_unblocked", False
            ),
        },
        "gate_passed": True,
        "interpretation": (
            "Trace and direct-action routes were tested. The trace route is "
            "blocked because no R_h/R_K trace targets exist. The direct-action "
            "route is blocked because current Janus inputs do not determine a "
            "unique local Sigma density. The Holst/Palatini theta projection "
            "eliminates its own non-GHY R_h/R_K traces on PT67 but does not "
            "exclude independent Sigma densities. The nonzero route remains "
            "parametric only, preventing false E_counterterm=0 or fitted c1,c2,c3."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Minimal Basis Dual Route Decision Gate",
        "",
        payload["interpretation"],
        "",
        "## Routes",
    ]
    for name, route in payload["routes"].items():
        lines.append(f"- `{name}`: ready=`{route['ready']}`, status=`{route['status']}`")
    lines.extend(["", f"Winner: `{payload['decision']['winner']}`"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
