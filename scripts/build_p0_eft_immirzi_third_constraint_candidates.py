from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_immirzi_third_constraint_candidates.md")
JSON_PATH = Path("outputs/reports/p0_eft_immirzi_third_constraint_candidates.json")


def solve_case(name: str, third_equation: sp.Equality) -> dict:
    c_q, c_pi, c_slip = sp.symbols("c_q c_pi c_slip")
    equations = [
        sp.Eq(c_q + c_pi, 1),
        sp.Eq(c_slip - c_q, 0),
        third_equation,
    ]
    solution = sp.solve(equations, [c_q, c_pi, c_slip], dict=True)
    sol = solution[0] if solution else {}
    bounded = all(value.is_number for value in sol.values()) and all(abs(float(value)) <= 1.0 for value in sol.values())
    slip_active = bool(sol and sol.get(c_slip, 0) != 0)
    return {
        "name": name,
        "third_constraint": str(third_equation),
        "solution": {str(k): str(v) for k, v in sol.items()},
        "unique": len(solution) == 1 and len(sol) == 3,
        "bounded": bounded,
        "slip_active": slip_active,
        "preferred": bool(len(solution) == 1 and len(sol) == 3 and bounded and slip_active),
    }


def build_payload() -> dict:
    c_q, c_pi, c_slip = sp.symbols("c_q c_pi c_slip")
    cases = [
        solve_case("traceless_holst_stress", sp.Eq(c_pi, 0)),
        solve_case("no_free_slip_gauge", sp.Eq(c_slip, sp.Rational(1, 2))),
    ]
    preferred = next((case for case in cases if case["preferred"]), None)
    return {
        "description": "Candidate third constraints for closing Immirzi perturbation coefficients.",
        "status": "immirzi-third-constraint-candidates-scored",
        "base_constraints": ["c_q + c_pi = 1", "c_slip = c_q"],
        "cases": cases,
        "preferred_case": preferred,
        "unique_candidate_found": preferred is not None,
        "cambridge_safe_to_patch": False,
        "next_required": (
            "Derive the preferred third constraint from the linearized Holst stress tensor before "
            "using its coefficients in CAMB."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Immirzi Third Constraint Candidates",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Unique candidate found: {payload['unique_candidate_found']}",
        f"CAMB safe to patch: {payload['cambridge_safe_to_patch']}",
        "",
        "| case | third constraint | solution | preferred |",
        "|---|---|---|---:|",
    ]
    for case in payload["cases"]:
        lines.append(
            f"| {case['name']} | `{case['third_constraint']}` | `{case['solution']}` | {case['preferred']} |"
        )
    lines.extend(["", "## Next", "", payload["next_required"], ""])
    return "\n".join(lines)


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
