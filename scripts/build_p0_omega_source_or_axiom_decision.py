from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_omega_source_or_axiom_decision.md")
JSON_PATH = Path("outputs/reports/p0_omega_source_or_axiom_decision.json")


def build_payload() -> dict:
    decision_rows = [
        {
            "route": "janus_source_trace",
            "status": "pending-audit",
            "needed": "published/source-local derivation of FW/comoving or congruence law giving Omega_u u=0",
        },
        {
            "route": "transport_axiom",
            "status": "available-not-adopted",
            "needed": "explicit no-fit axiom for shared L/Omega, mirror, K/Q_cross, rank-one dust scope",
        },
        {
            "route": "projection_annihilation",
            "status": "available-open",
            "needed": "source-derived P with P R_Omega P^T=0 shared by observables",
        },
    ]
    return {
        "description": "Decision gate for closing Omega via Janus source derivation or explicit transport axiom.",
        "status": "omega-source-or-axiom-open",
        "decision_rows": decision_rows,
        "janus_source_trace_required": True,
        "janus_source_omega_traceability_audit_available": True,
        "janus_source_trace_closed": False,
        "transport_axiom_route_available": True,
        "transport_axiom_acceptance_gate_available": True,
        "transport_axiom_adopted": False,
        "projection_route_available": True,
        "omega_next_decision_matrix_available": True,
        "omega_residual_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Omega closure is reduced to a source traceability question. If no Janus "
            "source derives the transport law, only an explicit no-fit transport axiom can move it forward."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Omega Source Or Axiom Decision",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Janus source trace required: {payload['janus_source_trace_required']}",
        f"Janus source omega traceability audit available: {payload['janus_source_omega_traceability_audit_available']}",
        f"Janus source trace closed: {payload['janus_source_trace_closed']}",
        f"Transport axiom route available: {payload['transport_axiom_route_available']}",
        f"Transport axiom acceptance gate available: {payload['transport_axiom_acceptance_gate_available']}",
        f"Transport axiom adopted: {payload['transport_axiom_adopted']}",
        f"Projection route available: {payload['projection_route_available']}",
        f"Omega next decision matrix available: {payload['omega_next_decision_matrix_available']}",
        f"Omega residual closed: {payload['omega_residual_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Decision Rows",
        "",
    ]
    for row in payload["decision_rows"]:
        lines.append(f"- {row['route']}: {row['status']} | needed: {row['needed']}")
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
