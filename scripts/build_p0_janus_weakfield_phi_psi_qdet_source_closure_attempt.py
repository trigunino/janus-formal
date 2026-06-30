from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_janus_weakfield_phi_psi_qdet_source_closure_attempt.md")
JSON_PATH = Path("outputs/reports/p0_janus_weakfield_phi_psi_qdet_source_closure_attempt.json")


def delta_b4vol_plus_from_minus() -> sp.Expr:
    phi_plus, phi_minus, psi_plus, psi_minus = sp.symbols("Phi_plus Phi_minus Psi_plus Psi_minus")
    return sp.simplify(phi_minus - phi_plus - 3 * psi_minus + 3 * psi_plus)


def delta_b4vol_minus_from_plus() -> sp.Expr:
    return sp.simplify(-delta_b4vol_plus_from_minus())


def build_payload() -> dict:
    delta_b_plus = sp.sstr(delta_b4vol_plus_from_minus())
    delta_b_minus = sp.sstr(delta_b4vol_minus_from_plus())
    source_rows = [
        {
            "sector": "plus",
            "delta_b": delta_b_plus,
            "effective_source": (
                "delta_S00_plus = delta_rho_plus + delta_rho_minus_to_plus + "
                "rho0_minus_to_plus delta_B_4vol_plus_from_minus"
            ),
            "potential_row": "2 Lap(Psi_plus) = chi delta_S00_plus",
            "closed": False,
        },
        {
            "sector": "minus",
            "delta_b": delta_b_minus,
            "effective_source": (
                "delta_S00_minus = -(delta_rho_minus + delta_rho_plus_to_minus + "
                "rho0_plus_to_minus delta_B_4vol_minus_from_plus)"
            ),
            "potential_row": "2 Lap(Psi_minus) = chi delta_S00_minus",
            "closed": False,
        },
    ]
    qdet_options = [
        {
            "name": "positive_effective_density",
            "rho_used": "rho_minus_eff = B_4vol_plus_from_minus rho_minus_proper",
            "q_det": "1",
            "allowed_if": "B_4vol has already weighted the active source",
        },
        {
            "name": "negative_proper_density",
            "rho_used": "rho_minus_proper",
            "q_det": "B_4vol_plus_from_minus",
            "allowed_if": "the source was not already converted to positive-effective density",
        },
    ]
    open_requirements = [
        "derive background subtraction or background branch for rho0 terms",
        "derive boundary/gauge conditions for additive Phi/Psi modes without observational fit",
        "derive slip/anisotropic-stress source rows before setting Phi=Psi outside dust",
        "select exactly one Q_det density convention from source bookkeeping",
        "keep the same L for K transport and Q_cross after Phi/Psi are solved",
    ]
    return {
        "description": "Bounded weak-field Phi/Psi/Q_det closure attempt from Janus source slots.",
        "status": "phi-psi-qdet-source-closure-attempt-open",
        "depends_on": [
            "p0_janus_weakfield_source_potential_system",
            "p0_janus_equations_to_dlogb4vol_closure_attempt",
            "qdet_density_measure_target",
        ],
        "source_rows": source_rows,
        "qdet_options": qdet_options,
        "open_requirements": open_requirements,
        "linearized_b4vol_feedback_written": True,
        "reciprocal_determinant_linearized": True,
        "poisson_feedback_system_written": True,
        "qdet_convention_options_separated": True,
        "qdet_convention_selected_from_source": False,
        "phi_psi_source_equations_closed": False,
        "uses_observational_fit": False,
        "uses_scalar_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The determinant feedback term is explicit, so Q_det cannot be used as a patch. "
            "Closure still requires source-derived background, gauge, slip, and convention selection."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Weak-Field Phi/Psi/Qdet Source Closure Attempt",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Linearized B_4vol feedback written: {payload['linearized_b4vol_feedback_written']}",
        f"Reciprocal determinant linearized: {payload['reciprocal_determinant_linearized']}",
        f"Q_det convention selected from source: {payload['qdet_convention_selected_from_source']}",
        f"Phi/Psi source equations closed: {payload['phi_psi_source_equations_closed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses scalar absorption: {payload['uses_scalar_absorption']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Source Rows",
        "",
        "| sector | delta B | effective source | potential row | closed |",
        "|---|---|---|---|---|",
    ]
    for row in payload["source_rows"]:
        lines.append(
            f"| {row['sector']} | `{row['delta_b']}` | `{row['effective_source']}` | "
            f"`{row['potential_row']}` | {row['closed']} |"
        )
    lines.extend(["", "## Qdet Options", "", "| name | rho used | q_det | allowed if |", "|---|---|---|---|"])
    for row in payload["qdet_options"]:
        lines.append(f"| {row['name']} | `{row['rho_used']}` | `{row['q_det']}` | {row['allowed_if']} |")
    lines.extend(["", "## Open Requirements", ""])
    lines.extend(f"- {item}" for item in payload["open_requirements"])
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
