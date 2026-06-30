from __future__ import annotations

from pathlib import Path
import json
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_action_ghost_stability_gate import build_payload as build_ghost_gate
from scripts.build_p0_h_strain_action_variation_gate import (
    build_payload as build_variation_gate,
)


REPORT_PATH = Path("outputs/reports/p0_h_strain_ghost_symbolic_gate.md")
JSON_PATH = Path("outputs/reports/p0_h_strain_ghost_symbolic_gate.json")


def derivative_strain_gate() -> dict:
    t, x = sp.symbols("t x")
    k_t, k_x = sp.symbols("k_t k_x", real=True)
    m_sq = sp.Symbol("m^2", real=True)
    q = sp.Function("q")(t, x)
    q_t = sp.diff(q, t)
    q_x = sp.diff(q, x)
    lagrangian = k_t * q_t**2 / 2 - k_x * q_x**2 / 2 - m_sq * q**2 / 2
    momentum = sp.diff(lagrangian, q_t)
    hamiltonian = sp.simplify(momentum * q_t - lagrangian)
    euler_lagrange = sp.simplify(
        sp.diff(sp.diff(lagrangian, q_t), t)
        + sp.diff(sp.diff(lagrangian, q_x), x)
        - sp.diff(lagrangian, q)
    )
    return {
        "toy_lagrangian": str(lagrangian),
        "canonical_momentum": str(momentum),
        "hamiltonian_density": str(hamiltonian),
        "euler_lagrange": str(euler_lagrange),
        "boundedness_conditions": ["k_t > 0", "k_x > 0", "m^2 >= 0"],
    }


def build_payload() -> dict:
    variation = build_variation_gate()
    ghost = build_ghost_gate()
    gate = derivative_strain_gate()
    return {
        "description": (
            "Bounded P0 ghost/stability artifact for a derivative H/Q_TF strain "
            "mode after gauge/constraint reduction."
        ),
        "status": "h-strain-ghost-symbolic-gate-open",
        "depends_on": [
            "p0_h_strain_action_variation_gate",
            "p0_action_ghost_stability_gate",
        ],
        "variation_gate_status": variation["status"],
        "ghost_gate_status": ghost["status"],
        "toy_model": (
            "L = 1/2 k_t q_t^2 - 1/2 k_x q_x^2 - 1/2 m^2 q^2; "
            "q is one physical H/Q_TF strain component."
        ),
        "symbolic_derivation": gate,
        "boundedness_conditions": gate["boundedness_conditions"],
        "instability_flags": [
            {
                "flag": "wrong_sign_kinetic",
                "condition": "k_t <= 0",
                "meaning": "ghost or degenerate kinetic energy for the strain mode",
            },
            {
                "flag": "wrong_sign_gradient",
                "condition": "k_x <= 0",
                "meaning": "gradient instability or missing spatial stiffness",
            },
            {
                "flag": "tachyon",
                "condition": "m^2 < 0",
                "meaning": "homogeneous strain mode has tachyonic mass",
            },
        ],
        "source_derived_action_supplied": False,
        "source_derived_action_missing": True,
        "prediction_ready": False,
        "verdict": (
            "The toy derivative strain action is bounded only for k_t>0, k_x>0 "
            "and m^2>=0. A source-derived H/Q_TF action is still missing, so this "
            "gate rejects sign-unstable candidates but makes no prediction."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 H Strain Ghost Symbolic Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Depends on: {', '.join(payload['depends_on'])}",
        f"Variation gate status: {payload['variation_gate_status']}",
        f"Ghost gate status: {payload['ghost_gate_status']}",
        f"Source-derived action supplied: {payload['source_derived_action_supplied']}",
        f"Source-derived action missing: {payload['source_derived_action_missing']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Toy Derivative Strain Action",
        "",
        payload["toy_model"],
        "",
    ]
    derivation = payload["symbolic_derivation"]
    lines.append(f"- L: `{derivation['toy_lagrangian']}`")
    lines.append(f"- pi: `{derivation['canonical_momentum']}`")
    lines.append(f"- Hamiltonian density: `{derivation['hamiltonian_density']}`")
    lines.append(f"- Euler-Lagrange: `{derivation['euler_lagrange']}`")
    lines.extend(["", "## Boundedness Conditions", ""])
    lines.extend(f"- `{item}`" for item in payload["boundedness_conditions"])
    lines.extend(["", "## Instability Flags", ""])
    for row in payload["instability_flags"]:
        lines.append(f"- `{row['flag']}` if `{row['condition']}`: {row['meaning']}")
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
