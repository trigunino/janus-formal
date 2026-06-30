from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_janus_weakfield_g0i_shift_operator_derivation.md")
JSON_PATH = Path("outputs/reports/p0_janus_weakfield_g0i_shift_operator_derivation.json")


def derive_g0i_operator() -> dict[str, sp.Expr]:
    psi_ti, div_shift_i, lap_shift_i = sp.symbols("Psi_ti divB_i lapB_i")
    return {
        "full": sp.simplify(2 * psi_ti + sp.Rational(1, 2) * (div_shift_i - lap_shift_i)),
        "transverse_quasistatic": sp.simplify(-sp.Rational(1, 2) * lap_shift_i),
    }


def build_payload() -> dict:
    operator = derive_g0i_operator()
    source_rows = [
        {
            "sector": "plus",
            "operator_row": (
                "2 partial_t partial_i Psi_plus + 1/2(partial_i partial_j B_plus_j - "
                "Lap B_plus_i)"
            ),
            "source_row": "chi(T0i_plus + B_4vol_plus_from_minus T0i_minus_to_plus)",
            "transverse_quasistatic": "-1/2 Lap B_plus_i",
            "closed": True,
        },
        {
            "sector": "minus",
            "operator_row": (
                "2 partial_t partial_i Psi_minus + 1/2(partial_i partial_j B_minus_j - "
                "Lap B_minus_i)"
            ),
            "source_row": "-chi(B_4vol_minus_from_plus T0i_plus_to_minus + T0i_minus)",
            "transverse_quasistatic": "-1/2 Lap B_minus_i",
            "closed": True,
        },
    ]
    return {
        "description": (
            "Linearized weak-field G0i shift operator derived from h00=-2Phi, "
            "h0i=B_i, hij=-2Psi delta_ij."
        ),
        "status": "g0i-shift-operator-derived-matter-open",
        "depends_on": [
            "p0_janus_weakfield_shift_boost_t0i_derivation",
            "p0_noncomoving_momentum_t0i_closure_target",
        ],
        "linearized_einstein_formula": (
            "G0i=1/2(partial_a partial_0 h^a_i + partial_a partial_i h^a_0 "
            "- box h0i - partial_0 partial_i h)"
        ),
        "operator_full_symbolic": sp.sstr(operator["full"]),
        "operator_transverse_quasistatic_symbolic": sp.sstr(operator["transverse_quasistatic"]),
        "source_rows": source_rows,
        "g0i_operator_derived": True,
        "shift_poisson_operator_transverse_closed": True,
        "psi_time_derivative_retained": True,
        "t0i_source_transport_closed": False,
        "pressure_pi0i_transport_closed": False,
        "source_derived_beta_available": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The geometric G0i operator is closed at linear weak-field order. "
            "The physical closure now sits in the transported T0i source: beta, pressure, "
            "and Pi0i must be source-derived before the non-comoving same-L branch can close."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Weak-Field G0i Shift Operator Derivation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Linearized formula: `{payload['linearized_einstein_formula']}`",
        f"Operator full symbolic: `{payload['operator_full_symbolic']}`",
        f"Operator transverse quasistatic symbolic: `{payload['operator_transverse_quasistatic_symbolic']}`",
        f"G0i operator derived: {payload['g0i_operator_derived']}",
        f"Shift Poisson operator transverse closed: {payload['shift_poisson_operator_transverse_closed']}",
        f"Psi time derivative retained: {payload['psi_time_derivative_retained']}",
        f"T0i source transport closed: {payload['t0i_source_transport_closed']}",
        f"Pressure/Pi0i transport closed: {payload['pressure_pi0i_transport_closed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Source Rows",
        "",
        "| sector | operator row | source row | transverse quasistatic | closed |",
        "|---|---|---|---|---|",
    ]
    for row in payload["source_rows"]:
        lines.append(
            f"| {row['sector']} | `{row['operator_row']}` | `{row['source_row']}` | "
            f"`{row['transverse_quasistatic']}` | {row['closed']} |"
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
