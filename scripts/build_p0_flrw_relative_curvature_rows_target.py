from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_flrw_relative_curvature_rows_target.md")
JSON_PATH = Path("outputs/reports/p0_flrw_relative_curvature_rows_target.json")


def curvature_symbols() -> tuple[sp.Symbol, sp.Symbol, sp.Symbol, sp.Symbol]:
    return sp.symbols("H_plus H_minus dH_plus dH_minus")


def derive_relative_rows() -> dict[str, sp.Expr]:
    H_plus, H_minus, dH_plus, dH_minus = curvature_symbols()
    temporal_plus = dH_plus + H_plus**2
    temporal_minus = dH_minus + H_minus**2
    spatial_plus = H_plus**2
    spatial_minus = H_minus**2
    return {
        "F_i0": sp.simplify(temporal_minus - temporal_plus),
        "F_ij": sp.simplify(spatial_minus - spatial_plus),
    }


def build_payload() -> dict:
    rows = derive_relative_rows()
    curvature_rows = [
        {
            "row": "F_i0",
            "definition": "(dH_minus + H_minus**2) - (dH_plus + H_plus**2)",
            "derived_expression": sp.sstr(rows["F_i0"]),
            "role": "orthonormal time-space FLRW relative curvature row",
        },
        {
            "row": "F_ij",
            "definition": "H_minus**2 - H_plus**2",
            "derived_expression": sp.sstr(rows["F_ij"]),
            "role": "orthonormal spatial FLRW relative curvature row",
        },
    ]
    return {
        "description": (
            "Symbolic homogeneous-FLRW target rows for relative spin-curvature inputs "
            "to the Bianchi-minimal curvature probe."
        ),
        "status": "homogeneous-flrw-relative-curvature-target",
        "depends_on": "p0_bianchi_minimal_curvature_integrability_system",
        "feeds": "p0_bianchi_minimal_curvature_numeric_probe",
        "scope": "homogeneous FLRW target only; not full Janus perturbation",
        "symbols": ["H_plus", "H_minus", "dH_plus", "dH_minus"],
        "curvature_rows": curvature_rows,
        "source_curvature_rows_computable": True,
        "full_physics_closed": False,
        "prediction_ready": False,
        "uses_observational_fit": False,
        "fit_parameters": [],
        "verdict": (
            "The orthonormal FLRW relative curvature rows are source-computable "
            "symbolic targets for the Bianchi-minimal probe. They do not close "
            "the full Janus perturbation problem and introduce no fit."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 FLRW Relative Curvature Rows Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Depends on: {payload['depends_on']}",
        f"Feeds: {payload['feeds']}",
        f"Scope: {payload['scope']}",
        f"Symbols: {payload['symbols']}",
        f"Source curvature rows computable: {payload['source_curvature_rows_computable']}",
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
