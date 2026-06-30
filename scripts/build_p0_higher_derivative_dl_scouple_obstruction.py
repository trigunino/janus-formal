from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_higher_derivative_dl_scouple_obstruction.md")
JSON_PATH = Path("outputs/reports/p0_higher_derivative_dl_scouple_obstruction.json")


def build_payload() -> dict:
    x = sp.symbols("x")
    kappa, mass = sp.symbols("kappa mass", positive=True)
    l_field = sp.Function("L")(x)
    dl = sp.diff(l_field, x)
    phi = sp.Function("phi")(x)
    d2phi = sp.diff(phi, x, 2)

    l_kinetic = sp.Rational(1, 2) * kappa * dl**2
    e_l_kinetic = sp.simplify(
        sp.diff(l_kinetic, l_field) - sp.diff(sp.diff(l_kinetic, dl), x)
    )
    l_massive = l_kinetic + sp.Rational(1, 2) * mass**2 * (l_field - 1) ** 2
    e_l_massive = sp.simplify(
        sp.diff(l_massive, l_field) - sp.diff(sp.diff(l_massive, dl), x)
    )
    phi_bending = sp.Rational(1, 2) * kappa * d2phi**2
    e_phi_bending = sp.simplify(sp.diff(sp.diff(phi_bending, d2phi), x, 2))

    rows = [
        {
            "route": "dl_kinetic",
            "lagrangian": "kappa/2 * (D L)^2",
            "euler_lagrange": str(e_l_kinetic),
            "produces_transport_pde": True,
            "selects_unique_map": False,
            "reason": "homogeneous L''=0 leaves integration constants without boundary/source data",
        },
        {
            "route": "massive_dl_kinetic",
            "lagrangian": "kappa/2 * (D L)^2 + mass^2/2 * (L-1)^2",
            "euler_lagrange": str(e_l_massive),
            "produces_transport_pde": True,
            "selects_unique_map": False,
            "reason": "adds a scale mass/kappa and boundary data not fixed by current Janus sources",
        },
        {
            "route": "phi_bending",
            "lagrangian": "kappa/2 * (D^2 phi)^2",
            "euler_lagrange": str(e_phi_bending),
            "produces_transport_pde": True,
            "selects_unique_map": False,
            "reason": "fourth-order homogeneous map equation needs four boundary/source conditions",
        },
    ]
    return {
        "description": "Obstruction for higher-derivative D L D L S_couple selector routes.",
        "status": "higher-derivative-dl-scouple-selector-open",
        "rows": rows,
        "dl_kinetic_el": str(e_l_kinetic),
        "massive_dl_kinetic_el": str(e_l_massive),
        "phi_bending_el": str(e_phi_bending),
        "higher_derivative_terms_produce_pde": True,
        "higher_derivative_terms_select_unique_phi_j_l": False,
        "requires_source_derived_coefficient": True,
        "requires_source_or_boundary_data": True,
        "requires_same_l_qcross_k_proof": True,
        "requires_split_noether_proof": True,
        "new_axiom_if_adopted_without_source": True,
        "uses_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "hidden_axiom_used": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Higher-derivative D L terms are a real non-rustine direction because "
            "they produce transport PDEs. In the tested local class they still do "
            "not select a unique phi/J/L: coefficients, boundary/source data, same-L "
            "compatibility, and split Noether closure remain source-derived obligations."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Higher-Derivative D L S_couple Obstruction",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"D L kinetic EL: `{payload['dl_kinetic_el']}`",
        f"Massive D L kinetic EL: `{payload['massive_dl_kinetic_el']}`",
        f"Phi bending EL: `{payload['phi_bending_el']}`",
        f"Higher-derivative terms produce PDE: {payload['higher_derivative_terms_produce_pde']}",
        (
            "Higher-derivative terms select unique phi/J/L: "
            f"{payload['higher_derivative_terms_select_unique_phi_j_l']}"
        ),
        f"Requires source-derived coefficient: {payload['requires_source_derived_coefficient']}",
        f"Requires source or boundary data: {payload['requires_source_or_boundary_data']}",
        f"Requires same-L/Qcross/K proof: {payload['requires_same_l_qcross_k_proof']}",
        f"Requires split Noether proof: {payload['requires_split_noether_proof']}",
        f"New axiom if adopted without source: {payload['new_axiom_if_adopted_without_source']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Hidden axiom used: {payload['hidden_axiom_used']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Rows",
        "",
        "| route | lagrangian | Euler-Lagrange | produces PDE | selects unique map | reason |",
        "|---|---|---|---:|---:|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['route']} | `{row['lagrangian']}` | `{row['euler_lagrange']}` | "
            f"{row['produces_transport_pde']} | {row['selects_unique_map']} | {row['reason']} |"
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
