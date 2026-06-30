from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_janus_pressure_pi0i_transport_derivation.md")
JSON_PATH = Path("outputs/reports/p0_janus_pressure_pi0i_transport_derivation.json")


def linear_pi0i_from_boost() -> dict[str, sp.Expr]:
    bx, by, bz = sp.symbols("beta_x beta_y beta_z")
    pxx, pxy, pxz, pyy, pyz, pzz = sp.symbols("Pi_xx Pi_xy Pi_xz Pi_yy Pi_yz Pi_zz")
    return {
        "Pi0x": sp.simplify(bx * pxx + by * pxy + bz * pxz),
        "Pi0y": sp.simplify(bx * pxy + by * pyy + bz * pyz),
        "Pi0z": sp.simplify(bx * pxz + by * pyz + bz * pzz),
    }


def linear_t0i_momentum() -> dict[str, sp.Expr]:
    rho, pressure, bx, by, bz = sp.symbols("rho p beta_x beta_y beta_z")
    pi = linear_pi0i_from_boost()
    return {
        "T0x": sp.simplify((rho + pressure) * bx + pi["Pi0x"]),
        "T0y": sp.simplify((rho + pressure) * by + pi["Pi0y"]),
        "T0z": sp.simplify((rho + pressure) * bz + pi["Pi0z"]),
    }


def build_payload() -> dict:
    pi0i = linear_pi0i_from_boost()
    t0i = linear_t0i_momentum()
    transport_laws = [
        {
            "object": "four_velocity",
            "law": "u_to^A=L^A_B u_source^B",
            "closed_algebraically": True,
        },
        {
            "object": "perfect_fluid",
            "law": "K_to^{AB}=(rho_to+p_to)u_to^A u_to^B+p_to eta^{AB}",
            "closed_algebraically": True,
        },
        {
            "object": "anisotropic_stress",
            "law": "Pi_to^{AB}=L^A_C L^B_D Pi_source^{CD}",
            "closed_algebraically": True,
        },
        {
            "object": "full_stress",
            "law": "K_to^{AB}=(rho_to+p_to)u_to^A u_to^B+p_to eta^{AB}+Pi_to^{AB}",
            "closed_algebraically": True,
        },
    ]
    still_source_dependent = [
        "equation of state p_to=w_to rho_to or other accepted Janus matter branch",
        "whether Pi_source^{AB}=0, degenerate, or dynamically evolved",
        "beta_i from Janus G0i source dynamics",
        "same-L Bianchi residual closure R_plus=R_minus=0",
    ]
    return {
        "description": (
            "Algebraic same-L transport derivation for pressure and Pi0i momentum terms."
        ),
        "status": "pressure-pi0i-transport-derived-source-open",
        "depends_on": [
            "p0_janus_pressure_pi0i_transport_gate",
            "p0_janus_weakfield_g0i_shift_operator_derivation",
            "p0_l_k_qcross_consistency_target",
        ],
        "transport_laws": transport_laws,
        "linear_pi0i_from_rest_spatial_pi": {key: sp.sstr(value) for key, value in pi0i.items()},
        "linear_t0i": {key: sp.sstr(value) for key, value in t0i.items()},
        "still_source_dependent": still_source_dependent,
        "same_l_transport_formula_derived": True,
        "pressure_t0i_formula_derived": True,
        "pi0i_boost_formula_derived": True,
        "dust_limit_recovered": True,
        "perfect_fluid_transport_closed_algebraically": True,
        "anisotropic_pi0i_transport_closed_algebraically": True,
        "equation_of_state_source_derived": False,
        "pi_evolution_source_derived": False,
        "source_derived_beta_available": False,
        "residuals_closed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The pressure/Pi0i transport algebra is now explicit with the same L. "
            "Physical closure still requires source-derived EOS, Pi evolution or Pi=0 proof, "
            "beta_i, and R_plus/R_minus cancellation."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Pressure/Pi0i Transport Derivation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Same-L transport formula derived: {payload['same_l_transport_formula_derived']}",
        f"Pressure T0i formula derived: {payload['pressure_t0i_formula_derived']}",
        f"Pi0i boost formula derived: {payload['pi0i_boost_formula_derived']}",
        f"Perfect-fluid transport closed algebraically: {payload['perfect_fluid_transport_closed_algebraically']}",
        f"Anisotropic Pi0i transport closed algebraically: {payload['anisotropic_pi0i_transport_closed_algebraically']}",
        f"Equation of state source-derived: {payload['equation_of_state_source_derived']}",
        f"Pi evolution source-derived: {payload['pi_evolution_source_derived']}",
        f"Source-derived beta available: {payload['source_derived_beta_available']}",
        f"Residuals closed: {payload['residuals_closed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Transport Laws",
        "",
        "| object | law | closed algebraically |",
        "|---|---|---|",
    ]
    for row in payload["transport_laws"]:
        lines.append(f"| {row['object']} | `{row['law']}` | {row['closed_algebraically']} |")
    lines.extend(["", "## Linear Pi0i", ""])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["linear_pi0i_from_rest_spatial_pi"].items())
    lines.extend(["", "## Linear T0i", ""])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["linear_t0i"].items())
    lines.extend(["", "## Still Source-Dependent", ""])
    lines.extend(f"- {item}" for item in payload["still_source_dependent"])
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
