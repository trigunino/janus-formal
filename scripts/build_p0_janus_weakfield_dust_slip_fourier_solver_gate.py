from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_janus_weakfield_dust_slip_fourier_solver_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_weakfield_dust_slip_fourier_solver_gate.json")


def fourier_matrix() -> sp.Matrix:
    k2, chi, rho_m_to_p, rho_p_to_m = sp.symbols("k2 chi rho0_minus_to_plus rho0_plus_to_minus")
    return sp.Matrix(
        [
            [-2 * k2 - 2 * chi * rho_m_to_p, 2 * chi * rho_m_to_p],
            [-2 * chi * rho_p_to_m, -2 * k2 + 2 * chi * rho_p_to_m],
        ]
    )


def determinant_factor() -> sp.Expr:
    k2, chi, rho_m_to_p, rho_p_to_m = sp.symbols("k2 chi rho0_minus_to_plus rho0_plus_to_minus")
    return sp.factor(fourier_matrix().det() - 4 * k2 * (k2 + chi * (rho_m_to_p - rho_p_to_m)))


def build_payload() -> dict:
    k2, chi, source_plus, source_minus = sp.symbols("k2 chi S_plus S_minus")
    rho_m_to_p, rho_p_to_m = sp.symbols("rho0_minus_to_plus rho0_plus_to_minus")
    matrix = fourier_matrix()
    rhs = sp.Matrix([chi * source_plus, -chi * source_minus])
    solution = sp.simplify(matrix.inv() * rhs)
    det = sp.factor(matrix.det())
    return {
        "description": (
            "Fourier-space invertibility gate for the conditional dust/slip coupled "
            "Janus weak-field Poisson target."
        ),
        "status": "dust-slip-fourier-solver-gate-open",
        "depends_on": ["p0_janus_weakfield_dust_slip_poisson_target"],
        "laplacian_convention": "Lap(Psi)(k) = -k2 Psi(k)",
        "matrix": [[sp.sstr(item) for item in row] for row in matrix.tolist()],
        "rhs": [sp.sstr(item) for item in rhs],
        "determinant": sp.sstr(det),
        "solution_psi_plus": sp.sstr(sp.factor(solution[0])),
        "solution_psi_minus": sp.sstr(sp.factor(solution[1])),
        "invertibility_conditions": [
            "k2 != 0 after boundary/mean-mode gauge is fixed",
            "k2 + chi(rho0_minus_to_plus - rho0_plus_to_minus) != 0",
        ],
        "zero_mode_requires_boundary_gauge": True,
        "mass_gap_resonance_requires_source_branch": True,
        "fourier_solver_written": True,
        "background_branch_selected": False,
        "boundary_conditions_source_derived": False,
        "qdet_convention_selected_from_source": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The conditional dust/slip operator is algebraically invertible away from "
            "the listed modes. This is still not a prediction because the background, "
            "boundary/gauge, and Q_det source convention remain open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Weak-Field Dust Slip Fourier Solver Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Laplacian convention: `{payload['laplacian_convention']}`",
        f"Determinant: `{payload['determinant']}`",
        f"Zero mode requires boundary/gauge: {payload['zero_mode_requires_boundary_gauge']}",
        f"Mass-gap resonance requires source branch: {payload['mass_gap_resonance_requires_source_branch']}",
        f"Background branch selected: {payload['background_branch_selected']}",
        f"Boundary conditions source-derived: {payload['boundary_conditions_source_derived']}",
        f"Q_det convention selected from source: {payload['qdet_convention_selected_from_source']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Matrix",
        "",
        f"- row 1: `{payload['matrix'][0]}`",
        f"- row 2: `{payload['matrix'][1]}`",
        f"- rhs: `{payload['rhs']}`",
        "",
        "## Solution",
        "",
        f"- Psi_plus(k): `{payload['solution_psi_plus']}`",
        f"- Psi_minus(k): `{payload['solution_psi_minus']}`",
        "",
        "## Invertibility Conditions",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["invertibility_conditions"])
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
