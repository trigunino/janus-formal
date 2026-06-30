from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_janus_weakfield_zero_mode_background_gauge_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_weakfield_zero_mode_background_gauge_gate.json")


def zero_mode_matrix() -> sp.Matrix:
    chi, rho_m_to_p, rho_p_to_m = sp.symbols("chi rho0_minus_to_plus rho0_plus_to_minus")
    return sp.Matrix(
        [
            [-2 * chi * rho_m_to_p, 2 * chi * rho_m_to_p],
            [-2 * chi * rho_p_to_m, 2 * chi * rho_p_to_m],
        ]
    )


def common_mode_kernel_residual() -> sp.Matrix:
    return sp.simplify(zero_mode_matrix() * sp.Matrix([1, 1]))


def source_compatibility_expression() -> sp.Expr:
    source_plus, source_minus = sp.symbols("S_plus S_minus")
    rho_m_to_p, rho_p_to_m = sp.symbols("rho0_minus_to_plus rho0_plus_to_minus")
    left_null = sp.Matrix([rho_p_to_m, -rho_m_to_p])
    rhs = sp.Matrix([source_plus, -source_minus])
    return sp.factor((left_null.T * rhs)[0])


def build_payload() -> dict:
    return {
        "description": (
            "Zero-mode/background-gauge gate for the conditional dust/slip Fourier "
            "solver. It separates source compatibility from the arbitrary common "
            "potential gauge."
        ),
        "status": "zero-mode-background-gauge-gate-open",
        "depends_on": ["p0_janus_weakfield_dust_slip_fourier_solver_gate"],
        "zero_mode_matrix": [[sp.sstr(item) for item in row] for row in zero_mode_matrix().tolist()],
        "common_mode_kernel_residual": [sp.sstr(item) for item in common_mode_kernel_residual()],
        "source_compatibility_condition": sp.sstr(source_compatibility_expression()),
        "gauge_choices_allowed": [
            "set mean(Psi_plus + Psi_minus)=0 after source compatibility is proved",
            "fix common additive potential by boundary convention, not by data fitting",
        ],
        "not_allowed": [
            "use the common zero mode to tune lensing amplitude",
            "hide a failed source-compatibility condition inside Q_det or Q_cross",
            "set Phi=Psi outside the dust/zero-Pi branch",
        ],
        "zero_mode_kernel_identified": True,
        "source_compatibility_written": True,
        "common_mode_gauge_is_not_physics": True,
        "background_branch_selected": False,
        "boundary_conditions_source_derived": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The k=0 blocker is now explicit: solve source compatibility first, then "
            "fix the common potential as gauge. This does not close the physical branch."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Weak-Field Zero-Mode Background Gauge Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source compatibility condition: `{payload['source_compatibility_condition']} = 0`",
        f"Zero-mode kernel identified: {payload['zero_mode_kernel_identified']}",
        f"Common mode gauge is not physics: {payload['common_mode_gauge_is_not_physics']}",
        f"Background branch selected: {payload['background_branch_selected']}",
        f"Boundary conditions source-derived: {payload['boundary_conditions_source_derived']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Gauge Choices Allowed",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["gauge_choices_allowed"])
    lines.extend(["", "## Not Allowed", ""])
    lines.extend(f"- {item}" for item in payload["not_allowed"])
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
