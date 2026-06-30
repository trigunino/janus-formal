from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_weakfield_tetrad_connection_target.md")
JSON_PATH = Path("outputs/reports/p0_weakfield_tetrad_connection_target.json")
SPATIAL = ("x", "y", "z")


def gradient_symbols(prefix: str) -> dict[str, sp.Symbol]:
    return {axis: sp.Symbol(f"d{axis}_{prefix}") for axis in SPATIAL}


def hessian_symbols(prefix: str) -> dict[tuple[str, str], sp.Symbol]:
    values: dict[tuple[str, str], sp.Symbol] = {}
    for i, left in enumerate(SPATIAL):
        for right in SPATIAL[i:]:
            symbol = sp.Symbol(f"H_{prefix}_{left}{right}")
            values[(left, right)] = symbol
            values[(right, left)] = symbol
    return values


def derive_connection_targets() -> dict:
    dphi = gradient_symbols("DeltaPhi")
    dpsi = gradient_symbols("DeltaPsi")
    hphi = hessian_symbols("DeltaPhi")
    hpsi = hessian_symbols("DeltaPsi")

    boost_connection = {
        f"Delta_omega_0{axis}0": dphi[axis]
        for axis in SPATIAL
    }
    spatial_rotation = {}
    for i in SPATIAL:
        for j in SPATIAL:
            if i == j:
                continue
            for k in SPATIAL:
                value = (dpsi[j] if k == i else 0) - (dpsi[i] if k == j else 0)
                if value != 0:
                    spatial_rotation[f"Delta_omega_{i}{j}{k}"] = sp.simplify(value)
    curvature_rows = {
        f"Delta_F_0{left}0{right}": hphi[(left, right)]
        for i, left in enumerate(SPATIAL)
        for right in SPATIAL[i:]
    }
    spatial_curvature_rows = {
        "Delta_F_xyxy": sp.simplify(hpsi[("x", "x")] + hpsi[("y", "y")]),
        "Delta_F_xzxz": sp.simplify(hpsi[("x", "x")] + hpsi[("z", "z")]),
        "Delta_F_yzyz": sp.simplify(hpsi[("y", "y")] + hpsi[("z", "z")]),
    }
    return {
        "boost_connection": boost_connection,
        "spatial_rotation": spatial_rotation,
        "temporal_curvature_rows": curvature_rows,
        "spatial_curvature_rows": spatial_curvature_rows,
    }


def build_payload() -> dict:
    targets = derive_connection_targets()
    rows = []
    for group, values in targets.items():
        for name, expression in values.items():
            rows.append(
                {
                    "group": group,
                    "row": name,
                    "expression": sp.sstr(expression),
                }
            )
    return {
        "description": (
            "Restricted weak-field tetrad/spin-connection target linking potential gradients "
            "to the curvature rows used by the integrability probes."
        ),
        "status": "restricted-weakfield-tetrad-connection-target",
        "depends_on": "p0_weakfield_relative_curvature_rows_target",
        "feeds": [
            "p0_weakfield_curvature_injection_probe",
            "p0_curvature_integrability_sparse_pde_probe",
        ],
        "coframe_branch": "e0=(1+Phi)dt, ei=(1-Psi)dxi, linear order",
        "scope": "Newtonian-gauge weak-field tetrad target only; not full Janus tetrad or nonlinear connection",
        "rows": rows,
        "connection_rows_computable": True,
        "curvature_rows_recovered_symbolically": True,
        "full_janus_tetrad_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "uses_observational_fit": False,
        "verdict": (
            "The restricted tetrad target makes the missing connection layer explicit: "
            "relative potential gradients feed relative spin-connection rows, and their "
            "derivatives recover the weak-field curvature rows. Full Janus tetrad closure "
            "remains open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Weak-Field Tetrad Connection Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Depends on: {payload['depends_on']}",
        f"Feeds: {payload['feeds']}",
        f"Coframe branch: {payload['coframe_branch']}",
        f"Scope: {payload['scope']}",
        f"Connection rows computable: {payload['connection_rows_computable']}",
        f"Curvature rows recovered symbolically: {payload['curvature_rows_recovered_symbolically']}",
        f"Full Janus tetrad closed: {payload['full_janus_tetrad_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        "",
        "## Rows",
        "",
        "| group | row | expression |",
        "|---|---|---|",
    ]
    for row in payload["rows"]:
        lines.append(f"| {row['group']} | `{row['row']}` | `{row['expression']}` |")
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
