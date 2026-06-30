from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_action_ghost_stability_gate.md")
JSON_PATH = Path("outputs/reports/p0_action_ghost_stability_gate.json")


def quadratic_gate(kinetic_matrix: sp.Matrix, mass_matrix: sp.Matrix) -> dict:
    kinetic_eigen = [sp.simplify(value) for value in kinetic_matrix.eigenvals().keys()]
    mass_eigen = [sp.simplify(value) for value in mass_matrix.eigenvals().keys()]
    return {
        "kinetic_eigenvalues": [str(value) for value in kinetic_eigen],
        "mass_eigenvalues": [str(value) for value in mass_eigen],
        "ghost_free_symbolic_condition": "all kinetic eigenvalues > 0",
        "tachyon_free_symbolic_condition": "all mass eigenvalues >= 0",
    }


def build_payload() -> dict:
    k_plus, k_minus, k_cross = sp.symbols("k_plus k_minus k_cross", real=True)
    m_plus, m_minus, m_cross = sp.symbols("m_plus m_minus m_cross", real=True)
    kinetic = sp.Matrix([[k_plus, k_cross], [k_cross, k_minus]])
    mass = sp.Matrix([[m_plus, m_cross], [m_cross, m_minus]])
    determinant_conditions = {
        "kinetic_positive_definite": [
            "k_plus > 0",
            "k_minus > 0",
            "k_plus*k_minus - k_cross^2 > 0",
        ],
        "mass_positive_semidefinite": [
            "m_plus >= 0",
            "m_minus >= 0",
            "m_plus*m_minus - m_cross^2 >= 0",
        ],
    }
    return {
        "description": "P0 gate for rejecting candidate Janus S_cross actions with quadratic ghost or tachyon instabilities.",
        "status": "gate-ready-candidate-actions-missing",
        "symbolic_quadratic_gate": quadratic_gate(kinetic, mass),
        "determinant_conditions": determinant_conditions,
        "accepted_action_supplied": False,
        "janus_candidate_tested": False,
        "prediction_ready": False,
        "required_before_acceptance": [
            "derive the candidate quadratic action from the same S_cross/Phi_R source",
            "extract kinetic and mass matrices around the declared Janus background",
            "prove kinetic matrix positive definite after gauge constraints are removed",
            "prove no tachyonic physical branch on the chosen background",
            "check constraints remove gauge modes rather than hiding negative-norm modes",
        ],
        "verdict": (
            "This gate does not close Janus. It prevents accepting a mathematically "
            "convenient S_cross if its linearized physical modes contain ghosts or "
            "unbounded instabilities."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Action Ghost Stability Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Accepted action supplied: {payload['accepted_action_supplied']}",
        f"Janus candidate tested: {payload['janus_candidate_tested']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Symbolic Quadratic Gate",
        "",
    ]
    gate = payload["symbolic_quadratic_gate"]
    lines.append(f"- kinetic eigenvalues: `{gate['kinetic_eigenvalues']}`")
    lines.append(f"- mass eigenvalues: `{gate['mass_eigenvalues']}`")
    lines.append(f"- ghost-free condition: `{gate['ghost_free_symbolic_condition']}`")
    lines.append(f"- tachyon-free condition: `{gate['tachyon_free_symbolic_condition']}`")
    lines.extend(["", "## Determinant Conditions", ""])
    for key, values in payload["determinant_conditions"].items():
        lines.append(f"{key}:")
        lines.extend(f"- `{value}`" for value in values)
    lines.extend(["", "## Required Before Acceptance", ""])
    lines.extend(f"- {item}" for item in payload["required_before_acceptance"])
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
