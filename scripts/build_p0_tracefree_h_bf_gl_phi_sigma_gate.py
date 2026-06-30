from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_bf_gl_phi_sigma_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_bf_gl_phi_sigma_gate.json")


def build_payload() -> dict:
    candidate_sources = [
        {
            "name": "Phi_Sigma",
            "role": "source term for symmetric GL strain",
            "janus_equation_supplied": False,
            "selects_h_tf_q_tf": False,
            "blocker": "must be derived from the Janus action, not inserted as fitted data",
        },
        {
            "name": "N_alpha",
            "role": "Cartan/relative-connection source equation",
            "janus_equation_supplied": False,
            "selects_h_tf_q_tf": False,
            "blocker": "must source symmetric strain through an Euler-Lagrange equation",
        },
    ]
    rejected_routes = [
        {
            "route": "pure_bf_topological_constraint",
            "accepted": False,
            "reason": "topological BF constraints do not select local H_TF dynamics",
        },
        {
            "route": "fitted_phi_sigma",
            "accepted": False,
            "reason": "fitted Phi_Sigma is not a Janus source equation",
        },
        {
            "route": "residual_cancellation",
            "accepted": False,
            "reason": "post-hoc residual cancellation is not source selection",
        },
    ]
    acceptance_gate = [
        {
            "check": "janus_phi_sigma_or_n_alpha_equation",
            "passed": False,
            "requirement": "derive Phi_Sigma/N_alpha from the Janus action",
        },
        {
            "check": "bianchi_curvature_integrability",
            "passed": False,
            "requirement": "prove Bianchi residuals and relative curvature integrability close",
        },
        {
            "check": "gauge_fixing",
            "passed": False,
            "requirement": "fix GL/Cartan gauge without hiding H_TF modes",
        },
        {
            "check": "mirror_inverse",
            "passed": False,
            "requirement": "prove plus/minus inverse transport closes both branches",
        },
        {
            "check": "same_l_transport",
            "passed": False,
            "requirement": "use the same L for K_plus/K_minus and Q_cross",
        },
        {
            "check": "ghost_stability_if_propagating",
            "passed": False,
            "requirement": "prove ghost/tachyon stability for propagating GL strain",
        },
    ]
    return {
        "description": (
            "Bounded P0 gate for BF/GL Phi_Sigma as a trace-free H/Q_TF "
            "source candidate."
        ),
        "status": "tracefree-h-bf-gl-phi-sigma-gate-open",
        "candidate": "bf_gl_phi_sigma",
        "connection_route": "BF/GL or Cartan relative connection",
        "qtf_channel": "trace-free H / Q_TF symmetric strain",
        "candidate_sources": candidate_sources,
        "rejected_routes": rejected_routes,
        "acceptance_gate": acceptance_gate,
        "janus_phi_sigma_source_equation_supplied": False,
        "janus_n_alpha_source_equation_supplied": False,
        "pure_bf_selects_local_h_tf_dynamics": False,
        "fitted_phi_sigma_allowed": False,
        "residual_cancellation_allowed": False,
        "all_acceptance_checks_passed": False,
        "source_selection_closed": False,
        "physics_closed": False,
        "prediction": False,
        "prediction_ready": False,
        "guardrails": [
            "do not treat pure BF/topological constraints as local H_TF dynamics",
            "do not fit Phi_Sigma to cancel trace-free residuals",
            "do not use residual cancellation as a source equation",
            "require Bianchi/curvature integrability, gauge fixing, mirror inverse, same-L transport, and stability gates",
        ],
        "verdict": (
            "BF/GL or Cartan relative connection can source symmetric strain only "
            "after Janus supplies a Phi_Sigma/N_alpha source equation. Pure BF "
            "constraint data alone do not select local H_TF/Q_TF dynamics."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H BF/GL Phi_Sigma Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Candidate: {payload['candidate']}",
        f"Connection route: {payload['connection_route']}",
        f"Q_TF channel: {payload['qtf_channel']}",
        f"Janus Phi_Sigma source equation supplied: {payload['janus_phi_sigma_source_equation_supplied']}",
        f"Janus N_alpha source equation supplied: {payload['janus_n_alpha_source_equation_supplied']}",
        f"Pure BF selects local H_TF dynamics: {payload['pure_bf_selects_local_h_tf_dynamics']}",
        f"Fitted Phi_Sigma allowed: {payload['fitted_phi_sigma_allowed']}",
        f"Residual cancellation allowed: {payload['residual_cancellation_allowed']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Candidate Sources",
        "",
        "| name | role | Janus equation supplied | selects H_TF/Q_TF | blocker |",
        "|---|---|---:|---:|---|",
    ]
    for row in payload["candidate_sources"]:
        lines.append(
            f"| {row['name']} | {row['role']} | {row['janus_equation_supplied']} | "
            f"{row['selects_h_tf_q_tf']} | {row['blocker']} |"
        )
    lines.extend(
        [
            "",
            "## Rejected Routes",
            "",
            "| route | accepted | reason |",
            "|---|---:|---|",
        ]
    )
    for row in payload["rejected_routes"]:
        lines.append(f"| {row['route']} | {row['accepted']} | {row['reason']} |")
    lines.extend(
        [
            "",
            "## Acceptance Gate",
            "",
            "| check | passed | requirement |",
            "|---|---:|---|",
        ]
    )
    for row in payload["acceptance_gate"]:
        lines.append(f"| {row['check']} | {row['passed']} | {row['requirement']} |")
    lines.extend(["", "## Guardrails", ""])
    lines.extend(f"- {item}" for item in payload["guardrails"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
