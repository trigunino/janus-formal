from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_janus_weakfield_source_potential_system.md")
JSON_PATH = Path("outputs/reports/p0_janus_weakfield_source_potential_system.json")


def determinant_log_density_factor(phi: sp.Symbol, psi: sp.Symbol) -> sp.Expr:
    return sp.simplify(phi - 3 * psi)


def b4vol_linearized(source_phi: sp.Symbol, source_psi: sp.Symbol, receiver_phi: sp.Symbol, receiver_psi: sp.Symbol) -> sp.Expr:
    return sp.simplify(
        1
        + determinant_log_density_factor(source_phi, source_psi)
        - determinant_log_density_factor(receiver_phi, receiver_psi)
    )


def build_payload() -> dict:
    phi_plus, phi_minus, psi_plus, psi_minus = sp.symbols("Phi_plus Phi_minus Psi_plus Psi_minus")
    b_plus = b4vol_linearized(phi_minus, psi_minus, phi_plus, psi_plus)
    b_minus = b4vol_linearized(phi_plus, psi_plus, phi_minus, psi_minus)
    poisson_rows = [
        {
            "sector": "plus",
            "row": "2 Lap(Psi_plus) = chi(rho_plus + B_4vol_plus_from_minus rho_minus_to_plus)",
            "source_slot": "G_plus = chi(T_plus + B_4vol_plus_from_minus T_minus_to_plus)",
            "status": "target-written-source-coefficients-open",
        },
        {
            "sector": "minus",
            "row": "2 Lap(Psi_minus) = -chi(B_4vol_minus_from_plus rho_plus_to_minus + rho_minus)",
            "source_slot": "G_minus = -chi(B_4vol_minus_from_plus T_plus_to_minus + T_minus)",
            "status": "target-written-source-coefficients-open",
        },
    ]
    slip_rows = [
        {
            "sector": "plus",
            "row": "D_i D_j(Phi_plus - Psi_plus) = chi Pi_plus_effective_ij",
            "dust_limit": "dust limit: Phi_plus - Psi_plus is harmonic/gauge-fixed to zero when Pi_plus_effective_ij=0",
        },
        {
            "sector": "minus",
            "row": "D_i D_j(Phi_minus - Psi_minus) = -chi Pi_minus_effective_ij",
            "dust_limit": "dust limit: Phi_minus - Psi_minus is harmonic/gauge-fixed to zero when Pi_minus_effective_ij=0",
        },
    ]
    determinant_rows = [
        {
            "branch": "plus_from_minus",
            "definition": "sqrt(-g_minus)/sqrt(-g_plus)",
            "linearized": sp.sstr(b_plus),
            "delta_log": sp.sstr(sp.simplify(b_plus - 1)),
        },
        {
            "branch": "minus_from_plus",
            "definition": "sqrt(-g_plus)/sqrt(-g_minus)",
            "linearized": sp.sstr(b_minus),
            "delta_log": sp.sstr(sp.simplify(b_minus - 1)),
        },
    ]
    return {
        "description": (
            "P0 weak-field source-potential system target from Janus cross-source slots, "
            "with the linearized B_4vol determinant ratio made explicit."
        ),
        "status": "weakfield-source-potential-system-open",
        "depends_on": [
            "p0_janus_equations_to_dlogb4vol_closure_attempt",
            "p0_janus_weakfield_metric_tetrad_bridge",
        ],
        "feeds": [
            "p0_janus_weakfield_metric_tetrad_bridge",
            "p0_weakfield_relative_curvature_rows_target",
            "p0_weakfield_tetrad_pipeline_probe",
        ],
        "metric_convention": "ds^2=-(1+2 Phi)dt^2+(1-2 Psi)delta_ij dx^i dx^j",
        "sqrt_minus_g_linearized": "1 + Phi - 3 Psi",
        "poisson_rows": poisson_rows,
        "slip_rows": slip_rows,
        "determinant_rows": determinant_rows,
        "poisson_rows_written": True,
        "slip_rows_written": True,
        "linearized_determinant_density_ratio_derived": True,
        "janus_cross_source_slots_preserved": True,
        "determinant_not_lensing_amplitude": True,
        "qdet_qcross_absorption_forbidden": True,
        "uses_observational_fit": False,
        "janus_source_potentials_solved": False,
        "boundary_conditions_source_derived": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This fixes the linear determinant bookkeeping and records the source-potential rows. "
            "It still does not solve Phi/Psi or close boundary/gauge/source identities."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Weak-Field Source Potential System",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Metric convention: `{payload['metric_convention']}`",
        f"sqrt(-g) linearized: `{payload['sqrt_minus_g_linearized']}`",
        f"Linearized determinant density ratio derived: {payload['linearized_determinant_density_ratio_derived']}",
        f"Janus source potentials solved: {payload['janus_source_potentials_solved']}",
        f"Boundary conditions source-derived: {payload['boundary_conditions_source_derived']}",
        f"Q_det/Q_cross absorption forbidden: {payload['qdet_qcross_absorption_forbidden']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Poisson Rows",
        "",
        "| sector | row | source slot | status |",
        "|---|---|---|---|",
    ]
    for row in payload["poisson_rows"]:
        lines.append(f"| {row['sector']} | `{row['row']}` | `{row['source_slot']}` | {row['status']} |")
    lines.extend(["", "## Slip Rows", "", "| sector | row | dust limit |", "|---|---|---|"])
    for row in payload["slip_rows"]:
        lines.append(f"| {row['sector']} | `{row['row']}` | {row['dust_limit']} |")
    lines.extend(["", "## Determinant Rows", "", "| branch | definition | linearized | delta log |", "|---|---|---|---|"])
    for row in payload["determinant_rows"]:
        lines.append(
            f"| {row['branch']} | `{row['definition']}` | `{row['linearized']}` | `{row['delta_log']}` |"
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
