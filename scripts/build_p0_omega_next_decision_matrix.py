from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_omega_next_decision_matrix.md")
JSON_PATH = Path("outputs/reports/p0_omega_next_decision_matrix.json")


def build_payload() -> dict:
    decisions = [
        {
            "decision": "search_external_source_first",
            "rule": "look for published/source evidence for D_u L, FW/comoving tetrad, congruence/cross-force, or S_couple",
            "selected": True,
        },
        {
            "decision": "write_axiom_candidate",
            "rule": "write a complete no-fit transport axiom candidate but keep adopted=false",
            "selected": True,
        },
        {
            "decision": "use_axiom_in_prediction",
            "rule": "forbidden until source search exhausted, axiom accepted, mirror/K/Q_cross tests pass",
            "selected": False,
        },
    ]
    return {
        "description": "Next decision matrix for Omega closure: external source search versus transport axiom candidate.",
        "status": "omega-next-decision-open",
        "decisions": decisions,
        "external_source_search_required": True,
        "external_janus_omega_source_search_gate_available": True,
        "axiom_candidate_allowed": True,
        "axiom_candidate_adopted": False,
        "prediction_use_allowed": False,
        "omega_residual_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Proceed on both documentation branches: search for a source-derived law and "
            "write the axiom candidate. Do not use the axiom for predictions."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Omega Next Decision Matrix",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"External source search required: {payload['external_source_search_required']}",
        f"External Janus omega source search gate available: {payload['external_janus_omega_source_search_gate_available']}",
        f"Axiom candidate allowed: {payload['axiom_candidate_allowed']}",
        f"Axiom candidate adopted: {payload['axiom_candidate_adopted']}",
        f"Prediction use allowed: {payload['prediction_use_allowed']}",
        f"Omega residual closed: {payload['omega_residual_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Decisions",
        "",
    ]
    for row in payload["decisions"]:
        lines.append(f"- {row['decision']}: {row['rule']} (selected: {row['selected']})")
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
