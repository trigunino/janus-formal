from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_weakfield_relative_curvature_rows_target.md")
JSON_PATH = Path("outputs/reports/p0_weakfield_relative_curvature_rows_target.json")
SPATIAL_INDICES = ("x", "y", "z")


def potential_symbols() -> tuple[sp.Symbol, sp.Symbol, sp.Symbol, sp.Symbol]:
    return sp.symbols("Phi_plus Phi_minus Psi_plus Psi_minus")


def spatial_hessian_symbols() -> dict[str, dict[tuple[str, str], sp.Symbol]]:
    hessians: dict[str, dict[tuple[str, str], sp.Symbol]] = {}
    for field in ("Phi_plus", "Phi_minus", "Psi_plus", "Psi_minus"):
        entries: dict[tuple[str, str], sp.Symbol] = {}
        for i, left in enumerate(SPATIAL_INDICES):
            for right in SPATIAL_INDICES[i:]:
                symbol = sp.Symbol(f"H_{field}_{left}{right}")
                entries[(left, right)] = symbol
                entries[(right, left)] = symbol
        hessians[field] = entries
    return hessians


def potential_differences() -> dict[str, sp.Expr]:
    Phi_plus, Phi_minus, Psi_plus, Psi_minus = potential_symbols()
    return {
        "Delta_Phi": sp.simplify(Phi_minus - Phi_plus),
        "Delta_Psi": sp.simplify(Psi_minus - Psi_plus),
    }


def derive_relative_rows() -> dict[str, dict[str, sp.Expr]]:
    hessians = spatial_hessian_symbols()
    delta_phi = {
        pair: sp.simplify(hessians["Phi_minus"][pair] - hessians["Phi_plus"][pair])
        for pair in hessians["Phi_plus"]
    }
    delta_psi = {
        pair: sp.simplify(hessians["Psi_minus"][pair] - hessians["Psi_plus"][pair])
        for pair in hessians["Psi_plus"]
    }

    temporal_rows = {
        f"Delta_R_0{left}0{right}": delta_phi[(left, right)]
        for i, left in enumerate(SPATIAL_INDICES)
        for right in SPATIAL_INDICES[i:]
    }
    spatial_rows = {
        "Delta_R_xyxy": sp.simplify(delta_psi[("x", "x")] + delta_psi[("y", "y")]),
        "Delta_R_xzxz": sp.simplify(delta_psi[("x", "x")] + delta_psi[("z", "z")]),
        "Delta_R_yzyz": sp.simplify(delta_psi[("y", "y")] + delta_psi[("z", "z")]),
        "Delta_R_xyxz": delta_psi[("y", "z")],
        "Delta_R_xzyz": delta_psi[("x", "y")],
        "Delta_R_yxyz": delta_psi[("x", "z")],
    }
    return {
        "temporal_tidal_rows": temporal_rows,
        "spatial_tidal_rows": spatial_rows,
    }


def build_payload() -> dict:
    rows = derive_relative_rows()
    curvature_rows = []
    for row, expression in rows["temporal_tidal_rows"].items():
        curvature_rows.append(
            {
                "row": row,
                "definition": "Hessian(Phi_minus - Phi_plus)",
                "derived_expression": sp.sstr(expression),
                "role": "restricted weak-field temporal tidal row",
            }
        )
    for row, expression in rows["spatial_tidal_rows"].items():
        curvature_rows.append(
            {
                "row": row,
                "definition": "linearized spatial tidal row from Hessian(Psi_minus - Psi_plus)",
                "derived_expression": sp.sstr(expression),
                "role": "restricted weak-field spatial tidal row",
            }
        )

    return {
        "description": (
            "Symbolic Newtonian-gauge weak-field relative curvature target rows "
            "for curvature-integrability probes."
        ),
        "status": "restricted-weakfield-relative-curvature-target",
        "depends_on": "p0_bianchi_minimal_curvature_integrability_system",
        "feeds": [
            "p0_curvature_integrability_sparse_pde_probe",
            "p0_bianchi_minimal_curvature_numeric_probe",
        ],
        "scope": (
            "restricted Newtonian-gauge/weak-field target only; not full Janus "
            "perturbation or tetrad closure"
        ),
        "potential_symbols": [sp.sstr(symbol) for symbol in potential_symbols()],
        "potential_differences": {
            name: sp.sstr(expression) for name, expression in potential_differences().items()
        },
        "hessian_symbols": sorted(
            {sp.sstr(symbol) for sector in spatial_hessian_symbols().values() for symbol in sector.values()}
        ),
        "curvature_rows": curvature_rows,
        "source_rows_computable": True,
        "source_curvature_rows_computable": True,
        "full_physics_closed": False,
        "prediction_ready": False,
        "uses_observational_fit": False,
        "fit_parameters": [],
        "verdict": (
            "These weak-field rows provide source-computable symbolic targets for "
            "integrability probes, without closing full Janus perturbation/tetrad "
            "physics and without introducing a fit."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Weak-Field Relative Curvature Rows Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Depends on: {payload['depends_on']}",
        f"Feeds: {payload['feeds']}",
        f"Scope: {payload['scope']}",
        f"Potential symbols: {payload['potential_symbols']}",
        f"Potential differences: {payload['potential_differences']}",
        f"Source rows computable: {payload['source_rows_computable']}",
        f"Full physics closed: {payload['full_physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Fit parameters: {payload['fit_parameters']}",
        "",
        "## Curvature Rows",
        "",
        "| row | definition | derived expression | role |",
        "|---|---|---|---|",
    ]
    for row in payload["curvature_rows"]:
        lines.append(
            f"| {row['row']} | `{row['definition']}` | "
            f"`{row['derived_expression']}` | {row['role']} |"
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
