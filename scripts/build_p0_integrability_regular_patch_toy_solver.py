from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_integrability_regular_patch_toy_solver.md")
JSON_PATH = Path("outputs/reports/p0_integrability_regular_patch_toy_solver.json")


def build_payload() -> dict:
    x, y = sp.symbols("x y")
    a, b, c, d = sp.symbols("a b c d")
    theta = sp.symbols("theta")
    xi = sp.Matrix([a * x + b * y, c * x + d * y])
    jac = sp.Matrix([[sp.diff(xi[0], x), sp.diff(xi[0], y)], [sp.diff(xi[1], x), sp.diff(xi[1], y)]])
    curl_xi = sp.diff(xi[1], x) - sp.diff(xi[0], y)
    volume_trace = sp.trace(jac)
    omega = sp.Matrix([[0, theta], [-theta, 0]])
    lorentz_residual = sp.simplify(omega + omega.T)
    equations = [
        {"name": "curl_free_xi", "equation": str(curl_xi), "constraint": "c-b=0"},
        {"name": "volume_preserving_linearized", "equation": str(volume_trace), "constraint": "a+d=0"},
        {"name": "lorentz_generator", "equation": str(lorentz_residual), "constraint": "omega+omega.T=0"},
    ]
    solution_family = sp.solve([curl_xi, volume_trace], [c, d], dict=True)
    free_modes = ["a", "b", "theta"]
    gauge_boundary_conditions = [
        {"condition": "a=0", "role": "fix linear stretch/shear boundary mode"},
        {"condition": "b=0", "role": "fix off-diagonal potential/gauge mode"},
        {"condition": "theta=0", "role": "fix residual local Lorentz rotation"},
    ]
    gauge_fixed_solution = {"a": "0", "b": "0", "c": "0", "d": "0", "theta": "0"}
    return {
        "description": "Linearized regular-patch toy solver for integrability-first phi/L selection.",
        "status": "toy-solver-free-modes-remain",
        "ansatz": {
            "phi": "id + xi, xi=(a x + b y, c x + d y)",
            "L": "I + omega, omega antisymmetric with parameter theta",
            "patch": "2D regular single-stream toy patch",
        },
        "equations": equations,
        "solution_family": [dict((str(k), str(v)) for k, v in row.items()) for row in solution_family],
        "free_modes": free_modes,
        "gauge_boundary_conditions": gauge_boundary_conditions,
        "gauge_fixed_solution": gauge_fixed_solution,
        "regularity_condition": "det(I + Dxi) != 0",
        "forces_unique_phi_l": False,
        "gauge_fixed_unique_phi_l": True,
        "gauge_fixed_unique_is_derived": False,
        "requires_boundary_data": True,
        "requires_gauge_fixing": True,
        "caustic_control_needed": True,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "In this linearized regular patch, curl-free and volume constraints reduce the map "
            "but leave free modes. Integrability-first does not select unique phi/L without "
            "boundary data, gauge fixing, and caustic control. A trivial unique branch appears "
            "only after imposing boundary/gauge conditions by hand."
        ),
    }


def render_markdown(payload: dict) -> str:
    ansatz = payload["ansatz"]
    lines = [
        "# P0 Integrability Regular Patch Toy Solver",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Forces unique phi/L: {payload['forces_unique_phi_l']}",
        f"Requires boundary data: {payload['requires_boundary_data']}",
        f"Requires gauge fixing: {payload['requires_gauge_fixing']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Ansatz",
        "",
        f"- phi: `{ansatz['phi']}`",
        f"- L: `{ansatz['L']}`",
        f"- patch: {ansatz['patch']}",
        "",
        "## Equations",
        "",
    ]
    for row in payload["equations"]:
        lines.append(f"- {row['name']}: `{row['equation']}` -> {row['constraint']}")
    lines.extend(["", "## Solution Family", ""])
    lines.extend(f"- {row}" for row in payload["solution_family"])
    lines.extend(["", "## Free Modes", ""])
    lines.extend(f"- `{item}`" for item in payload["free_modes"])
    lines.extend(["", "## Gauge/Boundary Conditions", ""])
    for row in payload["gauge_boundary_conditions"]:
        lines.append(f"- `{row['condition']}`: {row['role']}")
    lines.extend(["", f"Gauge-fixed solution: `{payload['gauge_fixed_solution']}`"])
    lines.append(f"Gauge-fixed unique phi/L: {payload['gauge_fixed_unique_phi_l']}")
    lines.append(f"Gauge-fixed uniqueness derived: {payload['gauge_fixed_unique_is_derived']}")
    lines.extend(["", f"Regularity condition: `{payload['regularity_condition']}`"])
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
