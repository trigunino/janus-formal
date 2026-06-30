from __future__ import annotations

from pathlib import Path
import json
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_action_ghost_stability_gate import build_payload as build_ghost_gate


REPORT_PATH = Path("outputs/reports/p0_h_strain_action_variation_gate.md")
JSON_PATH = Path("outputs/reports/p0_h_strain_action_variation_gate.json")


def euler_lagrange(lagrangian: sp.Expr, field: sp.Expr, coordinate: sp.Symbol) -> sp.Expr:
    dfield = sp.diff(field, coordinate)
    return sp.simplify(
        sp.diff(sp.diff(lagrangian, dfield), coordinate)
        - sp.diff(lagrangian, field)
    )


def build_payload() -> dict:
    ghost = build_ghost_gate()
    x = sp.symbols("x")
    c1, c2, c3, k = sp.symbols("c1 c2 c3 k")
    q = sp.Function("q")(x)
    dq = sp.diff(q, x)
    potential = c1 * q + c2 * q**2 / 2 + c3 * q**3 / 3
    ultralocal_lagrangian = -potential
    derivative_lagrangian = k * dq**2 / 2 - potential
    ultralocal_el = euler_lagrange(ultralocal_lagrangian, q, x)
    derivative_el = euler_lagrange(derivative_lagrangian, q, x)
    return {
        "description": "Variation gate for H/Sigma strain actions: ultralocal V(H) versus derivative D H dynamics.",
        "status": "h-strain-action-variation-gate-open",
        "depends_on": ["p0_action_ghost_stability_gate"],
        "ghost_symbolic_gate": "p0_h_strain_ghost_symbolic_gate",
        "toy_field": "q represents one trace-free component of H or Q_TF",
        "ultralocal_lagrangian": str(ultralocal_lagrangian),
        "ultralocal_euler_lagrange": str(ultralocal_el),
        "derivative_lagrangian": str(derivative_lagrangian),
        "derivative_euler_lagrange": str(derivative_el),
        "classification": [
            {
                "action_class": "ultralocal_potential_V_H",
                "can_select_h_branch": "algebraic only",
                "can_select_dh_or_sigma": False,
                "reason": "EL contains no derivative of q, so it cannot source N_alpha=D_alpha H",
            },
            {
                "action_class": "derivative_strain_kinetic_DH2",
                "can_select_h_branch": "PDE",
                "can_select_dh_or_sigma": "conditional",
                "reason": "EL contains second derivatives and can define a strain PDE only if source-derived",
            },
            {
                "action_class": "bf_multiplier_target_N",
                "can_select_h_branch": "constraint",
                "can_select_dh_or_sigma": "conditional",
                "reason": "valid only if the target N_alpha/Phi_Sigma is source-derived, not inserted",
            },
        ],
        "ultralocal_el_contains_derivative": False,
        "derivative_el_contains_second_derivative": True,
        "ghost_gate_status": ghost["status"],
        "source_derived_kinetic_supplied": False,
        "source_derived_potential_supplied": False,
        "source_derived_target_n_supplied": False,
        "source_selection_closed": False,
        "prediction_ready": False,
        "verdict": (
            "An ultralocal V(H) can at most select an algebraic strain branch. "
            "A real Sigma/DH selector needs derivative H dynamics or a BF target, "
            "and both remain source-open plus ghost/stability gated."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 H Strain Action Variation Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Toy field: {payload['toy_field']}",
        f"Ultralocal EL contains derivative: {payload['ultralocal_el_contains_derivative']}",
        f"Derivative EL contains second derivative: {payload['derivative_el_contains_second_derivative']}",
        f"Ghost gate status: {payload['ghost_gate_status']}",
        f"Ghost symbolic gate: `{payload['ghost_symbolic_gate']}`",
        f"Source selection closed: {payload['source_selection_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Toy Variations",
        "",
        f"- ultralocal L: `{payload['ultralocal_lagrangian']}`",
        f"- ultralocal EL: `{payload['ultralocal_euler_lagrange']}`",
        f"- derivative L: `{payload['derivative_lagrangian']}`",
        f"- derivative EL: `{payload['derivative_euler_lagrange']}`",
        "",
        "## Classification",
        "",
        "| action class | can select H branch | can select DH/Sigma | reason |",
        "|---|---|---|---|",
    ]
    for row in payload["classification"]:
        lines.append(
            f"| {row['action_class']} | {row['can_select_h_branch']} | "
            f"{row['can_select_dh_or_sigma']} | {row['reason']} |"
        )
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
