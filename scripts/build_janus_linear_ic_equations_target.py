from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/janus_linear_ic_equations_target.md")
JSON_PATH = Path("outputs/reports/janus_linear_ic_equations_target.json")


def build_payload() -> dict:
    variables = [
        "delta_plus(k,a)",
        "delta_minus_eff(k,a)",
        "theta_plus(k,a)=div(v_plus)",
        "theta_minus(k,a)=div(v_minus)",
        "Phi_plus(k,a)",
    ]
    equations = [
        {
            "name": "positive_effective_poisson",
            "equation": "nabla_x^2 Phi_plus = 4 pi G a^2 (rho_bar_plus delta_plus - rho_bar_minus delta_minus_eff)",
            "status": "weak-field target",
        },
        {
            "name": "negative_potential",
            "equation": "nabla_x^2 Phi_minus = -nabla_x^2 Phi_plus",
            "status": "weak-field sign target",
        },
        {
            "name": "continuity_plus",
            "equation": "dot(delta_plus) + a^-1 div(u_plus) = 0",
            "status": "linear target",
        },
        {
            "name": "continuity_minus",
            "equation": "dot(delta_minus_eff) + a^-1 div(u_minus) = 0",
            "status": "linear target",
        },
        {
            "name": "euler_plus",
            "equation": "dot(u_plus) + H u_plus = -a^-1 grad(Phi_plus)",
            "status": "sign target from g_plus motion",
        },
        {
            "name": "euler_minus",
            "equation": "dot(u_minus) + H u_minus = -a^-1 grad(Phi_minus)",
            "status": "sign target from g_minus=-g_plus weak-field motion",
        },
    ]
    growth_targets = [
        "delta_plus'' + A(a) delta_plus' = +(3/2)(Omega_plus delta_plus - Omega_minus delta_minus)",
        "delta_minus'' + A(a) delta_minus' = -(3/2)(Omega_plus delta_plus - Omega_minus delta_minus)",
        "A(a) = 2 + d ln(H) / d ln(a)",
        "H(a) = H0 E_J(a)",
    ]
    velocity_targets = [
        "u_s(k,a) = i a H(a) [k/k^2] delta_s'(k,a) for irrotational modes",
        "theta_s(k,a) = -a H(a) delta_s'(k,a)",
    ]
    transfer_boundary = [
        "delta_s(k,a_ic) = A_J T_s(k,a_ic) xi(k)",
        "delta(k,a) = G_J(a,a_ic) delta(k,a_ic)",
    ]
    derived_targets = [
        {
            "target": "transfer",
            "symbol": "T_J^plus(k,a_i), T_J^minus(k,a_i)",
            "rule": "eigenmodes or Green functions of the linear two-sector operator",
        },
        {
            "target": "growth",
            "symbol": "D_plus(k,a), D_minus(k,a)",
            "rule": "propagator from a_i to a under Janus expansion E(a)",
        },
        {
            "target": "velocity",
            "symbol": "theta_s(k,a), v_s(k,a)",
            "rule": "from continuity/euler, not arbitrary displacement scaling",
        },
        {
            "target": "amplitude",
            "symbol": "A_J",
            "rule": "source-backed normalization or explicit no-fit comparison target; not sigma8 rescaling",
        },
    ]
    numerical_controls = [
        "fixed-total mass normalization is required for grid convergence diagnostics",
        "analytic-multimode IC is a convergence control, not a physical Janus transfer function",
        "bounded/lognormal/Gaussian IC families remain scaffolds until T_J and A_J are derived",
    ]
    blockers = [
        "derive source_scale(a) and drag(a) from full Janus linear perturbation equations",
        "decide whether delta_minus is positive-effective or negative-proper before coupling to Q_det",
        "connect the velocity field to Q_cross only after the L_minus_to_plus four-velocity cross-map is defined",
        "derive amplitude A_J without fitting sigma8 or survey lensing data",
        "verify sign conventions against the PM signed-sector kernel",
    ]
    return {
        "description": "Linear weak-field target for source-derived Janus initial conditions.",
        "source_anchors": [
            "M15/M30 Newtonian sign kernel",
            "M18 Janus expansion E(a)",
            "local PM H0^-1 time calibration",
        ],
        "physics_closed": False,
        "variables": variables,
        "equations": equations,
        "growth_targets": growth_targets,
        "velocity_targets": velocity_targets,
        "transfer_boundary": transfer_boundary,
        "derived_targets": derived_targets,
        "numerical_controls": numerical_controls,
        "blockers": blockers,
        "verdict": (
            "This makes the IC scaffold actionable: transfer, growth and velocity "
            "must come from the same linear two-sector operator. It is not yet a "
            "source-derived production IC."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Linear IC Equations Target",
        "",
        payload["description"],
        "",
        f"Physics closed: {payload['physics_closed']}",
        "",
        "## Variables",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["variables"])
    lines.extend(
        [
            "",
            "## Equations",
            "",
            "| name | equation | status |",
            "|---|---|---|",
        ]
    )
    for row in payload["equations"]:
        lines.append(f"| {row['name']} | `{row['equation']}` | {row['status']} |")
    lines.extend(["", "## Growth Targets", ""])
    lines.extend(f"- `{item}`" for item in payload["growth_targets"])
    lines.extend(["", "## Velocity Targets", ""])
    lines.extend(f"- `{item}`" for item in payload["velocity_targets"])
    lines.extend(["", "## Transfer Boundary", ""])
    lines.extend(f"- `{item}`" for item in payload["transfer_boundary"])
    lines.extend(
        [
            "",
            "## Derived Targets",
            "",
            "| target | symbol | rule |",
            "|---|---|---|",
        ]
    )
    for row in payload["derived_targets"]:
        lines.append(f"| {row['target']} | `{row['symbol']}` | {row['rule']} |")
    lines.extend(["", "## Numerical Controls", ""])
    lines.extend(f"- {item}" for item in payload["numerical_controls"])
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
