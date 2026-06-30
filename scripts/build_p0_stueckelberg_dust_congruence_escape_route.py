from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_dust_congruence_escape_route.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_dust_congruence_escape_route.json")


def build_payload() -> dict:
    route = {
        "name": "dust_congruence_only",
        "idea": "require receiver-geodesic transport only along the physical dust congruence, not all tangent vectors",
        "unknown_reduction": "constraints apply to u_to^nu D_self_nu u_to^mu rather than full connection matching",
        "overconstraint_reduced": True,
        "tensor_proof_complete": False,
    }
    equations = [
        {
            "sector": "plus",
            "condition": "u_-to+^nu D_plus_nu u_-to+^mu = 0",
            "scope": "dust-flow contraction only",
            "closed": "conditional",
        },
        {
            "sector": "minus",
            "condition": "u_+to-^nu D_minus_nu u_+to-^mu = 0",
            "scope": "mirror dust-flow contraction only",
            "closed": "conditional",
        },
    ]
    risks = [
        "may close dust residuals but not pressure/Pi extensions",
        "may not control lensing rays outside dust congruence",
        "still needs E_phi/E_L to produce the congruence equations",
    ]
    return {
        "description": "Dust-congruence escape route for Stueckelberg connection integrability.",
        "status": "dust-congruence-route-conditional",
        "route": route,
        "equations": equations,
        "overconstraint_reduced": True,
        "dust_residual_closure_possible": True,
        "full_tensor_closure": False,
        "physics_closed": False,
        "prediction_ready": False,
        "risks": risks,
        "verdict": (
            "This is the best mathematical escape from overconstraint: require the map "
            "to preserve the physical dust congruence, not the whole connection. It may "
            "close dust residuals conditionally, but it is not a full tensor/matter proof."
        ),
    }


def render_markdown(payload: dict) -> str:
    route = payload["route"]
    lines = [
        "# P0 Stueckelberg Dust-Congruence Escape Route",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Overconstraint reduced: {payload['overconstraint_reduced']}",
        f"Dust residual closure possible: {payload['dust_residual_closure_possible']}",
        f"Full tensor closure: {payload['full_tensor_closure']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        f"Route: {route['name']}",
        f"Idea: {route['idea']}",
        f"Unknown reduction: {route['unknown_reduction']}",
        "",
        "## Equations",
        "",
    ]
    for row in payload["equations"]:
        lines.append(f"- {row['sector']}: `{row['condition']}` ({row['scope']}, closed={row['closed']})")
    lines.extend(["", "## Risks", ""])
    lines.extend(f"- {item}" for item in payload["risks"])
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
