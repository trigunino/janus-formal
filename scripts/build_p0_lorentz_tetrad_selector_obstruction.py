from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_lorentz_tetrad_selector_obstruction.md")
JSON_PATH = Path("outputs/reports/p0_lorentz_tetrad_selector_obstruction.json")


def build_payload() -> dict:
    rapidity = sp.symbols("rapidity", real=True)
    eta = sp.Matrix([[-1, 0], [0, 1]])
    boost = sp.Matrix(
        [
            [sp.cosh(rapidity), sp.sinh(rapidity)],
            [sp.sinh(rapidity), sp.cosh(rapidity)],
        ]
    )
    lorentz_residual = sp.simplify(boost.T * eta * boost - eta)
    determinant = sp.simplify(boost.det())
    rows = [
        {
            "condition": "lorentz_admissibility",
            "formula": "L.T eta L = eta",
            "closed": bool(lorentz_residual == sp.zeros(2)),
            "selects_unique_l": False,
            "reason": "all rapidities satisfy the local Lorentz condition",
        },
        {
            "condition": "determinant",
            "formula": "det L = 1 for proper boosts",
            "closed": bool(determinant == 1),
            "selects_unique_l": False,
            "reason": "fixed Lorentz determinant cannot carry the B4vol/J_phi scalar factor",
        },
        {
            "condition": "same_l_qcross_k",
            "formula": "same L must feed K transport and Q_cross",
            "closed": False,
            "selects_unique_l": False,
            "reason": "local admissibility does not derive D L, rapidity transport, or source branch",
        },
    ]
    return {
        "description": "Local Lorentz/tetrad admissibility obstruction for selecting phi/J/L.",
        "status": "lorentz-tetrad-selector-obstruction-open",
        "eta": str(eta),
        "boost_matrix": str(boost),
        "lorentz_residual": str(lorentz_residual),
        "determinant": str(determinant),
        "rows": rows,
        "lorentz_condition_symbolically_closed": bool(lorentz_residual == sp.zeros(2)),
        "proper_boost_determinant_fixed": bool(determinant == 1),
        "rapidity_family_remains_free": True,
        "lorentz_admissibility_selects_unique_l": False,
        "lorentz_admissibility_selects_jphi": False,
        "requires_source_rapidity_transport": True,
        "requires_same_l_transport_proof": True,
        "uses_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "hidden_axiom_used": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Lorentz/tetrad admissibility is necessary but not selective. The local "
            "proper-boost family preserves eta and has det L=1 for arbitrary rapidity, "
            "so it cannot by itself select the spacetime Jacobian J_phi or the same-L "
            "transport branch."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Lorentz/Tetrad Selector Obstruction",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Lorentz condition symbolically closed: {payload['lorentz_condition_symbolically_closed']}",
        f"Proper boost determinant fixed: {payload['proper_boost_determinant_fixed']}",
        f"Rapidity family remains free: {payload['rapidity_family_remains_free']}",
        f"Lorentz admissibility selects unique L: {payload['lorentz_admissibility_selects_unique_l']}",
        f"Lorentz admissibility selects J_phi: {payload['lorentz_admissibility_selects_jphi']}",
        f"Requires source rapidity transport: {payload['requires_source_rapidity_transport']}",
        f"Requires same-L transport proof: {payload['requires_same_l_transport_proof']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Hidden axiom used: {payload['hidden_axiom_used']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Rows",
        "",
        "| condition | formula | closed | selects unique L | reason |",
        "|---|---|---:|---:|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['condition']} | `{row['formula']}` | {row['closed']} | "
            f"{row['selects_unique_l']} | {row['reason']} |"
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
