from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_phi_j_l_boundary_selector_probe.md")
JSON_PATH = Path("outputs/reports/p0_phi_j_l_boundary_selector_probe.json")


def build_payload() -> dict:
    eps, x = sp.symbols("epsilon x")
    phi = x + eps * sp.sin(x)
    jacobian = sp.diff(phi, x)
    selectors = [
        {
            "selector": "identity_at_quarter_turn",
            "condition": "phi(pi/2)=pi/2",
            "equation": str(sp.simplify(phi.subs(x, sp.pi / 2) - sp.pi / 2)),
            "solutions": str(sp.solve([sp.simplify(phi.subs(x, sp.pi / 2) - sp.pi / 2)], [eps], dict=True)),
            "fixes_epsilon": True,
            "source_supplied": False,
        },
        {
            "selector": "unit_jacobian_at_origin",
            "condition": "J(0)=1",
            "equation": str(sp.simplify(jacobian.subs(x, 0) - 1)),
            "solutions": str(sp.solve([sp.simplify(jacobian.subs(x, 0) - 1)], [eps], dict=True)),
            "fixes_epsilon": True,
            "source_supplied": False,
        },
        {
            "selector": "periodic_endpoints",
            "condition": "phi(2pi)-phi(0)=2pi",
            "equation": str(sp.simplify(phi.subs(x, 2 * sp.pi) - phi.subs(x, 0) - 2 * sp.pi)),
            "solutions": "all epsilon",
            "fixes_epsilon": False,
            "source_supplied": True,
        },
        {
            "selector": "mirror_inverse_only",
            "condition": "inverse map exists and orientation is preserved",
            "equation": "|epsilon| < 1",
            "solutions": "open family",
            "fixes_epsilon": False,
            "source_supplied": True,
        },
    ]
    source_grade = [
        "M15/M30 support periodic/topological/mirror compatibility at the structural level",
        "M15/M30 do not supply pointwise identity gauge phi(pi/2)=pi/2 or J(0)=1",
        "strong selectors can fix epsilon mathematically but would be new boundary axioms unless sourced",
    ]
    return {
        "description": "Boundary selector probe for the phi/J/L underselection family.",
        "status": "boundary-selectors-can-fix-family-but-not-source-supplied",
        "candidate_family": "phi=x+epsilon sin(x)",
        "selectors": selectors,
        "source_grade": source_grade,
        "strong_selectors_exist": True,
        "strong_selectors_source_supplied": False,
        "mirror_topology_alone_fixes_unique_map": False,
        "periodic_boundary_alone_fixes_unique_map": False,
        "new_boundary_axiom_required_if_adopted": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "A boundary condition can fix the toy underselection, but only strong pointwise "
            "selectors do so. The structural Janus mirror/periodic conditions leave the family open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Phi/J/L Boundary Selector Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Candidate family: `{payload['candidate_family']}`",
        f"Strong selectors exist: {payload['strong_selectors_exist']}",
        f"Strong selectors source supplied: {payload['strong_selectors_source_supplied']}",
        f"Mirror/topology alone fixes unique map: {payload['mirror_topology_alone_fixes_unique_map']}",
        f"Periodic boundary alone fixes unique map: {payload['periodic_boundary_alone_fixes_unique_map']}",
        f"New boundary axiom required if adopted: {payload['new_boundary_axiom_required_if_adopted']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Selectors",
        "",
        "| selector | condition | equation | solutions | fixes epsilon | source supplied |",
        "|---|---|---|---|---:|---:|",
    ]
    for row in payload["selectors"]:
        lines.append(
            f"| {row['selector']} | `{row['condition']}` | `{row['equation']}` | "
            f"`{row['solutions']}` | {row['fixes_epsilon']} | {row['source_supplied']} |"
        )
    lines.extend(["", "## Source Grade", ""])
    lines.extend(f"- {item}" for item in payload["source_grade"])
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
