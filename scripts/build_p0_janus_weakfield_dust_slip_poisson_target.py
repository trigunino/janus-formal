from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_janus_weakfield_dust_slip_poisson_target.md")
JSON_PATH = Path("outputs/reports/p0_janus_weakfield_dust_slip_poisson_target.json")


def dust_delta_b4vol_plus_from_minus() -> sp.Expr:
    psi_plus, psi_minus = sp.symbols("Psi_plus Psi_minus")
    return sp.simplify(2 * (psi_plus - psi_minus))


def dust_delta_b4vol_minus_from_plus() -> sp.Expr:
    return sp.simplify(-dust_delta_b4vol_plus_from_minus())


def coupled_poisson_residuals() -> dict[str, sp.Expr]:
    lap_plus, lap_minus, psi_plus, psi_minus = sp.symbols("Lap_Psi_plus Lap_Psi_minus Psi_plus Psi_minus")
    chi, rho_m_to_p, rho_p_to_m, source_plus, source_minus = sp.symbols(
        "chi rho0_minus_to_plus rho0_plus_to_minus S_plus S_minus"
    )
    relative = psi_plus - psi_minus
    return {
        "plus": sp.simplify(2 * lap_plus - 2 * chi * rho_m_to_p * relative - chi * source_plus),
        "minus": sp.simplify(2 * lap_minus - 2 * chi * rho_p_to_m * relative + chi * source_minus),
        "relative": sp.simplify(
            2 * (lap_plus - lap_minus)
            - 2 * chi * (rho_m_to_p - rho_p_to_m) * relative
            - chi * (source_plus + source_minus)
        ),
    }


def build_payload() -> dict:
    residuals = coupled_poisson_residuals()
    return {
        "description": (
            "Conditional dust/slip weak-field target reducing the Janus source rows "
            "to coupled Poisson equations for Psi_plus and Psi_minus."
        ),
        "status": "dust-slip-coupled-poisson-target-open",
        "depends_on": [
            "p0_janus_weakfield_source_potential_system",
            "p0_janus_weakfield_phi_psi_qdet_source_closure_attempt",
        ],
        "assumptions": [
            "weak-field Newtonian gauge",
            "dust or zero effective anisotropic stress in both sectors",
            "boundary/gauge condition allows Phi_plus=Psi_plus and Phi_minus=Psi_minus",
            "no observational fit or sigma8/S8 normalization",
        ],
        "delta_b4vol_plus_from_minus_dust": sp.sstr(dust_delta_b4vol_plus_from_minus()),
        "delta_b4vol_minus_from_plus_dust": sp.sstr(dust_delta_b4vol_minus_from_plus()),
        "operator_rows": [
            {
                "name": "plus",
                "residual_zero_form": sp.sstr(residuals["plus"]),
                "meaning": (
                    "2 Lap(Psi_plus) - 2 chi rho0_minus_to_plus(Psi_plus-Psi_minus) "
                    "= chi S_plus"
                ),
            },
            {
                "name": "minus",
                "residual_zero_form": sp.sstr(residuals["minus"]),
                "meaning": (
                    "2 Lap(Psi_minus) - 2 chi rho0_plus_to_minus(Psi_plus-Psi_minus) "
                    "= -chi S_minus"
                ),
            },
            {
                "name": "relative",
                "residual_zero_form": sp.sstr(residuals["relative"]),
                "meaning": (
                    "relative mode equation for Psi_plus-Psi_minus after subtracting "
                    "the two sector rows"
                ),
            },
        ],
        "source_symbols": {
            "S_plus": "delta_rho_plus + delta_rho_minus_to_plus",
            "S_minus": "delta_rho_minus + delta_rho_plus_to_minus",
        },
        "dust_slip_condition_applied_conditionally": True,
        "coupled_operator_written": True,
        "background_branch_selected": False,
        "boundary_conditions_source_derived": False,
        "qdet_convention_selected_from_source": False,
        "same_l_qcross_selected": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This is a calculable dust/slip target, not a closure proof. It exposes "
            "the coupled determinant feedback and leaves background, boundary, Q_det, "
            "and same-L transport selection open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Weak-Field Dust Slip Poisson Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Delta B plus_from_minus dust: `{payload['delta_b4vol_plus_from_minus_dust']}`",
        f"Delta B minus_from_plus dust: `{payload['delta_b4vol_minus_from_plus_dust']}`",
        f"Coupled operator written: {payload['coupled_operator_written']}",
        f"Background branch selected: {payload['background_branch_selected']}",
        f"Boundary conditions source-derived: {payload['boundary_conditions_source_derived']}",
        f"Q_det convention selected from source: {payload['qdet_convention_selected_from_source']}",
        f"Same-L Q_cross selected: {payload['same_l_qcross_selected']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Assumptions",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["assumptions"])
    lines.extend(["", "## Operator Rows", "", "| name | residual zero form | meaning |", "|---|---|---|"])
    for row in payload["operator_rows"]:
        lines.append(f"| {row['name']} | `{row['residual_zero_form']}` | {row['meaning']} |")
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
