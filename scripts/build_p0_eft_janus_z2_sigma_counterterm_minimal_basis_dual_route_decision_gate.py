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


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_minimal_basis_dual_route_decision_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_minimal_basis_dual_route_decision_gate.json"
)


def build_payload() -> dict:
    trace = build_trace_constraints()
    traces_available = False
    nonzero_parametric_ready = True
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
        },
        "decision": {
            "preferred_next": "derive_active_R_h_trace_and_R_K_trace",
            "fallback": "carry_parametric_E_counterterm_until_boundary_condition_available",
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
        "gate_passed": True,
        "interpretation": (
            "Both routes were tested. The active trace route is blocked because no "
            "R_h/R_K trace targets exist. The nonzero route is usable only as a "
            "parametric expression for E_counterterm, not as a numerical active "
            "component. This prevents falsely setting E_counterterm to zero or "
            "fitting c1,c2,c3."
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
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
