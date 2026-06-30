from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_d_source_derived_stf_operator_escape_gate import (
    build_payload as build_escape,
)
from scripts.build_p0_tracefree_h_derivative_branch_stability_gate import (
    build_payload as build_stability,
)
from scripts.build_p0_tracefree_h_source_action_provenance_chain_gate import (
    build_payload as build_provenance,
)


REPORT_PATH = Path("outputs/reports/p0_route_d_stf_operator_construction_obstruction.md")
JSON_PATH = Path("outputs/reports/p0_route_d_stf_operator_construction_obstruction.json")


def build_payload() -> dict:
    escape = build_escape()
    provenance = build_provenance()
    stability = build_stability()
    candidates = [
        {
            "candidate": "relative_H_action",
            "formal_stf_operator": True,
            "janus_action_provenance": False,
            "accepted": False,
        },
        {
            "candidate": "bf_gl_constraint_action",
            "formal_stf_operator": "conditional",
            "janus_action_provenance": False,
            "accepted": False,
        },
        {
            "candidate": "vlasov_quadrupole_moment",
            "formal_stf_operator": "moment source",
            "janus_action_provenance": False,
            "accepted": False,
        },
        {
            "candidate": "matter_pi_tf_variation",
            "formal_stf_operator": "conditional",
            "janus_action_provenance": False,
            "accepted": False,
        },
        {
            "candidate": "curvature_stf_operator",
            "formal_stf_operator": "conditional",
            "janus_action_provenance": False,
            "accepted": False,
        },
    ]
    missing_chain = [
        "accepted Janus action/source for the STF channel",
        "declared variation domain",
        "deltaS/deltaH or deltaS/deltaQ_TF",
        "P_STF projection after variation",
        "same-bridge identification",
        "same-L Noether closure",
        "stability/principal-symbol closure",
    ]
    return {
        "description": (
            "Route D construction obstruction: try the remaining STF operator "
            "families and record exactly why none is accepted as Janus-derived."
        ),
        "status": "stf-operator-construction-obstruction-open",
        "escape_status": escape["status"],
        "provenance_status": provenance["status"],
        "stability_status": stability["status"],
        "candidates": candidates,
        "missing_chain": missing_chain,
        "candidate_count": len(candidates),
        "accepted_candidate_count": sum(1 for row in candidates if row["accepted"]),
        "formal_stf_operators_exist": True,
        "accepted_janus_derived_stf_operator_exists": False,
        "source_action_provenance_closed": bool(provenance["source_action_provenance_closed"]),
        "stability_requirements_closed": bool(stability["requirements_closed"]),
        "residual_operator_allowed": False,
        "determinant_trace_allowed": False,
        "escape_hatch_still_open": True,
        "full_no_go_proved": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Formal STF operators can be written, but none is accepted because the "
            "Janus source-action provenance and same-L/stability chain is unclosed. "
            "This narrows the escape hatch without proving the full no-go."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route D STF Operator Construction Obstruction",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Candidate count: {payload['candidate_count']}",
        f"Accepted candidate count: {payload['accepted_candidate_count']}",
        f"Formal STF operators exist: {payload['formal_stf_operators_exist']}",
        f"Accepted Janus-derived STF operator exists: {payload['accepted_janus_derived_stf_operator_exists']}",
        f"Source-action provenance closed: {payload['source_action_provenance_closed']}",
        f"Stability requirements closed: {payload['stability_requirements_closed']}",
        f"Residual operator allowed: {payload['residual_operator_allowed']}",
        f"Determinant trace allowed: {payload['determinant_trace_allowed']}",
        f"Escape hatch still open: {payload['escape_hatch_still_open']}",
        f"Full no-go proved: {payload['full_no_go_proved']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| candidate | formal STF operator | Janus action provenance | accepted |",
        "|---|---|---:|---:|",
    ]
    for row in payload["candidates"]:
        lines.append(
            f"| {row['candidate']} | {row['formal_stf_operator']} | "
            f"{row['janus_action_provenance']} | {row['accepted']} |"
        )
    lines.extend(["", "## Missing Chain", ""])
    lines.extend(f"- {item}" for item in payload["missing_chain"])
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
