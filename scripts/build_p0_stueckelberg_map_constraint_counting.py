from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_map_constraint_counting.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_map_constraint_counting.json")


def build_payload() -> dict:
    unknowns = [
        {
            "field": "phi",
            "degree_of_freedom": 4,
            "role": "diffeomorphism/Stueckelberg map between plus and minus sectors",
        },
        {
            "field": "L",
            "degree_of_freedom": 6,
            "role": "local Lorentz map shared by transport, K, and Q_cross",
        },
    ]
    constraints = [
        {
            "name": "receiver geodesic conditions",
            "count": "up to 4 vector conditions per sector",
            "risk": "can consume phi freedom before residual cancellation is imposed",
        },
        {
            "name": "E_phi map equations",
            "count": "4 plus/mirror components before integrability reduction",
            "risk": "may overdetermine the 4 phi components once receiver conditions are kept",
        },
        {
            "name": "E_L Lorentz equations",
            "count": "6 antisymmetric Lorentz components before gauge reduction",
            "risk": "may overdetermine L when same L must also serve K and Q_cross",
        },
        {
            "name": "mirror inverse consistency",
            "count": "phi^{-1} and L^{-1} are not independent unknowns",
            "risk": "minus equations cannot be counted as fresh adjustable freedom",
        },
        {
            "name": "same L for K/Q_cross",
            "count": "one shared 6-dof Lorentz field",
            "risk": "forbids separate optical, transport, and interaction Lorentz fits",
        },
        {
            "name": "residual closures",
            "count": "R_plus=0 and R_minus=0 after map substitution",
            "risk": "closure conditions stack on already-used phi/L freedom",
        },
    ]
    escape_routes = [
        {
            "route": "symmetry",
            "mechanism": "mirror symmetry or isotropy reduces independent equations",
            "status": "possible-not-proved",
        },
        {
            "route": "FLRW",
            "mechanism": "homogeneity/isotropy collapses phi and L to few scalar functions",
            "status": "toy-sector-only",
        },
        {
            "route": "dust congruence only",
            "mechanism": "impose receiver geodesic transport only along the physical dust flow",
            "status": "narrowed-domain",
        },
        {
            "route": "gauge freedom",
            "mechanism": "use diffeomorphism and Lorentz gauge redundancy to remove dependent equations",
            "status": "requires-rank-proof",
        },
    ]
    total_unknown_dof = sum(row["degree_of_freedom"] for row in unknowns)
    return {
        "description": (
            "Bounded P0 artifact for Stueckelberg map-equation degree-of-freedom "
            "versus constraint counting."
        ),
        "artifact": "stueckelberg-map-constraint-counting",
        "status": "bounded-counting-overconstraint-risk",
        "source_derived": False,
        "physics_closed": False,
        "prediction_ready": False,
        "fit_to_observations": False,
        "unknowns": unknowns,
        "total_unknown_dof": total_unknown_dof,
        "constraints": constraints,
        "overconstraint_risks": [
            "receiver geodesic conditions plus E_phi can exceed the 4 phi degrees of freedom",
            "E_L plus same-L K/Q_cross obligations can exceed the 6 Lorentz degrees of freedom",
            "mirror inverse consistency means minus-sector equations are checks, not new knobs",
            "residual closures may be independent unless symmetry or gauge identities reduce rank",
        ],
        "escape_routes": escape_routes,
        "verdict": (
            "The branch has 10 local map unknowns before gauge/rank reductions: phi(4) and "
            "L(6). The listed constraints plausibly overdetermine those unknowns unless "
            "symmetry, FLRW specialization, dust-congruence restriction, or gauge identities "
            "make the equations dependent. This is not prediction ready."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Stueckelberg Map Constraint Counting",
        "",
        payload["description"],
        "",
        f"Artifact: {payload['artifact']}",
        f"Status: {payload['status']}",
        f"Source derived: {payload['source_derived']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Fit to observations: {payload['fit_to_observations']}",
        f"Total unknown dof: {payload['total_unknown_dof']}",
        "",
        "## Unknowns",
        "",
        "| field | dof | role |",
        "|---|---:|---|",
    ]
    for row in payload["unknowns"]:
        lines.append(f"| {row['field']} | {row['degree_of_freedom']} | {row['role']} |")
    lines.extend(["", "## Constraints", "", "| name | count | risk |", "|---|---|---|"])
    for row in payload["constraints"]:
        lines.append(f"| {row['name']} | {row['count']} | {row['risk']} |")
    lines.extend(["", "## Overconstraint Risks", ""])
    lines.extend(f"- {item}" for item in payload["overconstraint_risks"])
    lines.extend(["", "## Escape Routes", "", "| route | mechanism | status |", "|---|---|---|"])
    for row in payload["escape_routes"]:
        lines.append(f"| {row['route']} | {row['mechanism']} | {row['status']} |")
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
