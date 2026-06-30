from __future__ import annotations

from pathlib import Path
import json
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_janus_weakfield_phi_psi_qdet_source_closure_attempt import (
    delta_b4vol_minus_from_plus,
    delta_b4vol_plus_from_minus,
)


REPORT_PATH = Path("outputs/reports/p0_janus_weakfield_delta_s00_source_expansion_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_weakfield_delta_s00_source_expansion_gate.json")


def symbols() -> dict[str, sp.Symbol]:
    names = [
        "Delta_Phi",
        "Delta_Psi",
        "delta_rho_plus",
        "delta_rho_minus",
        "delta_rho_minus_to_plus",
        "delta_rho_plus_to_minus",
        "rho0_minus_to_plus",
        "rho0_plus_to_minus",
    ]
    return {name: sp.Symbol(name) for name in names}


def delta_b_plus_reduced() -> sp.Expr:
    s = symbols()
    return sp.simplify(s["Delta_Phi"] - 3 * s["Delta_Psi"])


def delta_b_minus_reduced() -> sp.Expr:
    return sp.simplify(-delta_b_plus_reduced())


def source_expansions() -> dict[str, sp.Expr]:
    s = symbols()
    delta_s_plus = sp.simplify(
        s["delta_rho_plus"]
        + s["delta_rho_minus_to_plus"]
        + s["rho0_minus_to_plus"] * delta_b_plus_reduced()
    )
    delta_s_minus = sp.simplify(
        -(
            s["delta_rho_minus"]
            + s["delta_rho_plus_to_minus"]
            + s["rho0_plus_to_minus"] * delta_b_minus_reduced()
        )
    )
    return {
        "delta_S00_plus": delta_s_plus,
        "delta_S00_minus": delta_s_minus,
        "delta_S00_minus_minus_plus": sp.factor(delta_s_minus - delta_s_plus),
    }


def dust_slip_relative_source() -> sp.Expr:
    s = symbols()
    expression = source_expansions()["delta_S00_minus_minus_plus"]
    return sp.factor(expression.subs(s["Delta_Phi"], s["Delta_Psi"]))


def build_payload() -> dict:
    expansions = source_expansions()
    source_rows = [
        {
            "name": name,
            "expression": sp.sstr(expression),
            "closed": True,
        }
        for name, expression in expansions.items()
    ]
    return {
        "description": "Algebraic weak-field expansion of Janus delta_S00 source rows with B4vol feedback.",
        "status": "delta-s00-source-expansion-algebra-closed-physics-open",
        "depends_on": [
            "p0_janus_weakfield_phi_psi_qdet_source_closure_attempt",
            "p0_janus_weakfield_delta_phi_psi_source_chain_gate",
        ],
        "delta_b4vol_full_source": {
            "plus_from_minus": sp.sstr(delta_b4vol_plus_from_minus()),
            "minus_from_plus": sp.sstr(delta_b4vol_minus_from_plus()),
        },
        "delta_b4vol_reduced": {
            "plus_from_minus": sp.sstr(delta_b_plus_reduced()),
            "minus_from_plus": sp.sstr(delta_b_minus_reduced()),
        },
        "source_rows": source_rows,
        "dust_slip_delta_s00_minus_minus_plus": sp.sstr(dust_slip_relative_source()),
        "delta_s00_expansion_closed": True,
        "relative_source_written": True,
        "dust_slip_reduction_written": True,
        "density_transport_closed": False,
        "background_subtraction_closed": False,
        "qdet_convention_selected_from_source": False,
        "slip_source_closed": False,
        "boundary_gauge_closed": False,
        "uses_observational_fit": False,
        "qdet_absorption_allowed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "delta_S00 is now expanded algebraically with B4vol feedback. This can feed "
            "the Delta_Psi equation, but physical closure still needs density transport, "
            "background subtraction, Q_det convention, slip source and boundary/gauge."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Weak-Field Delta S00 Source Expansion Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Delta S00 expansion closed: {payload['delta_s00_expansion_closed']}",
        f"Relative source written: {payload['relative_source_written']}",
        f"Dust/slip reduction written: {payload['dust_slip_reduction_written']}",
        f"Density transport closed: {payload['density_transport_closed']}",
        f"Background subtraction closed: {payload['background_subtraction_closed']}",
        f"Qdet convention selected from source: {payload['qdet_convention_selected_from_source']}",
        f"Slip source closed: {payload['slip_source_closed']}",
        f"Boundary/gauge closed: {payload['boundary_gauge_closed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Qdet absorption allowed: {payload['qdet_absorption_allowed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Delta B4vol Reduced",
        "",
    ]
    for name, expression in payload["delta_b4vol_reduced"].items():
        lines.append(f"- {name}: `{expression}`")
    lines.extend(["", "## Source Rows", "", "| name | expression | closed |", "|---|---|---:|"])
    for row in payload["source_rows"]:
        lines.append(f"| {row['name']} | `{row['expression']}` | {row['closed']} |")
    lines.extend(
        [
            "",
            f"Dust/slip relative source: `{payload['dust_slip_delta_s00_minus_minus_plus']}`",
            "",
            f"Verdict: {payload['verdict']}",
            "",
        ]
    )
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
