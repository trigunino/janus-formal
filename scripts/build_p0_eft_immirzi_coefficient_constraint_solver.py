from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_immirzi_coefficient_constraint_solver.md")
JSON_PATH = Path("outputs/reports/p0_eft_immirzi_coefficient_constraint_solver.json")


def solve_constraints() -> dict:
    c_q, c_pi, c_slip = sp.symbols("c_q c_pi c_slip")
    equations = [
        sp.Eq(c_q + c_pi, 1),
        sp.Eq(c_slip - c_q, 0),
    ]
    solution = sp.solve(equations, [c_q, c_pi, c_slip], dict=True)
    rank = sp.linear_eq_to_matrix([eq.lhs - eq.rhs for eq in equations], [c_q, c_pi, c_slip])[0].rank()
    return {
        "equations": [str(eq) for eq in equations],
        "solution": [{str(k): str(v) for k, v in row.items()} for row in solution],
        "rank": int(rank),
        "unknowns": 3,
        "underdetermined": rank < 3,
        "free_parameter": "c_pi" if rank < 3 else None,
    }


def build_payload() -> dict:
    solved = solve_constraints()
    return {
        "description": "Symbolic constraint solver for Immirzi perturbation coefficients.",
        "status": "immirzi-coefficient-constraint-solver-run",
        "constraints": solved["equations"],
        "solution_family": solved["solution"],
        "rank": solved["rank"],
        "unknowns": solved["unknowns"],
        "underdetermined": solved["underdetermined"],
        "free_parameter": solved["free_parameter"],
        "unique_coefficients_derived": not solved["underdetermined"],
        "cambridge_safe_to_patch": False,
        "next_required": (
            "Add one independent physical constraint from the linearized Holst stress tensor "
            "or impose a derived gauge choice for the remaining free parameter."
        ),
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT Immirzi Coefficient Constraint Solver",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Unique coefficients derived: {payload['unique_coefficients_derived']}",
            f"CAMB safe to patch: {payload['cambridge_safe_to_patch']}",
            f"Rank: {payload['rank']} / {payload['unknowns']}",
            f"Free parameter: `{payload['free_parameter']}`",
            "",
            "## Constraints",
            "",
            *[f"- `{eq}`" for eq in payload["constraints"]],
            "",
            "## Solution Family",
            "",
            f"```json\n{json.dumps(payload['solution_family'], indent=2)}\n```",
            "",
            "## Next",
            "",
            payload["next_required"],
            "",
        ]
    )


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
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
