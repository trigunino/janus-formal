from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_weak_congruence_map_equation.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_weak_congruence_map_equation.json")


def build_payload() -> dict:
    equations = [
        {
            "sector": "plus",
            "weak_condition": "C_plus-minus^mu_{alpha beta} u_-to+^alpha u_-to+^beta = 0",
            "equivalent_form": "u_-to+^nu D_plus_nu u_-to+^mu = 0 when u_minus is source-geodesic",
            "full_isometry_required": False,
        },
        {
            "sector": "minus",
            "weak_condition": "C_minus-plus^a_{mu nu} u_+to-^mu u_+to-^nu = 0",
            "equivalent_form": "u_+to-^b D_minus_b u_+to-^a = 0 when u_plus is source-geodesic",
            "full_isometry_required": False,
        },
    ]
    why_weaker = [
        "It constrains only the connection projection along the physical dust velocity.",
        "It does not impose C^mu_{alpha beta}=0 for transverse vectors.",
        "It does not impose Phi^* g_plus = g_minus.",
        "It preserves room for distinct a_plus/a_minus and non-isometric two-metric geometry.",
    ]
    closure_obligations = [
        {
            "name": "action_origin",
            "obligation": "derive the weak congruence equation from E_phi/E_L or S_couple",
            "closed": False,
        },
        {
            "name": "mirror_inverse_consistency",
            "obligation": "prove plus and minus equations are inverse-map mirrors, not two independent gauges",
            "closed": False,
        },
        {
            "name": "curl_integrability",
            "obligation": "prove D_[mu](C u u)_{nu]} obstruction cancels on the dust image distribution",
            "closed": False,
        },
        {
            "name": "same_L_K_Qcross",
            "obligation": "use the same L for dust K transport and optical Q_cross",
            "closed": False,
        },
    ]
    decision = {
        "connection_residual_cancelled_for_dust": "conditional",
        "overconstraint_reduced_vs_isometry": True,
        "generic_janus_not_excluded": True,
        "accepted_as_final_closure": False,
        "reason": (
            "The weak congruence equation is the correct target shape: it cancels the "
            "dust connection force without collapsing the two metrics into a local "
            "isometry. It is still an imposed map equation until derived from the "
            "Janus/Stueckelberg action and its integrability conditions."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_weak_congruence_map_equation",
        "status": "best-current-weak-target-conditional-open",
        "fit_used": False,
        "free_parameters": [],
        "source_derived": False,
        "new_axiom_if_imposed": True,
        "physics_closed": False,
        "prediction_ready": False,
        "equations": equations,
        "why_weaker_than_isometry": why_weaker,
        "closure_obligations": closure_obligations,
        "decision": decision,
        "next_step": (
            "Try to obtain this projected equation as an Euler-Lagrange consequence of "
            "the Stueckelberg map variables, not as a hand-imposed constraint."
        ),
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Weak Congruence Map Equation",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Source derived: {payload['source_derived']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Weak Equations",
    ]
    for row in payload["equations"]:
        lines.append(f"- {row['sector']}: `{row['weak_condition']}`")
        lines.append(f"  - equivalent form: `{row['equivalent_form']}`")
        lines.append(f"  - full isometry required: {row['full_isometry_required']}")
    lines.extend(["", "## Why This Is Weaker Than Isometry"])
    lines.extend(f"- {item}" for item in payload["why_weaker_than_isometry"])
    lines.extend(["", "## Closure Obligations"])
    for row in payload["closure_obligations"]:
        lines.append(f"- {row['name']}: {row['obligation']} (closed={row['closed']})")
    lines.extend(
        [
            "",
            "## Decision",
            f"Connection residual cancelled for dust: {decision['connection_residual_cancelled_for_dust']}",
            f"Overconstraint reduced vs isometry: {decision['overconstraint_reduced_vs_isometry']}",
            f"Generic Janus not excluded: {decision['generic_janus_not_excluded']}",
            f"Accepted as final closure: {decision['accepted_as_final_closure']}",
            f"Reason: {decision['reason']}",
            "",
            f"Next step: {payload['next_step']}",
            "",
        ]
    )
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
