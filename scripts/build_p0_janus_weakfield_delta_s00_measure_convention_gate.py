from __future__ import annotations

from pathlib import Path
import json
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_b_jphi_qdet_conditional_selection import (
    build_payload as build_conditional_selection,
)


REPORT_PATH = Path("outputs/reports/p0_janus_weakfield_delta_s00_measure_convention_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_weakfield_delta_s00_measure_convention_gate.json")


def symbols() -> dict[str, sp.Symbol]:
    names = [
        "delta_B",
        "rho0_other_to_self",
        "delta_rho_other_proper",
        "delta_rho_other_eff",
        "delta_rho_self",
    ]
    return {name: sp.Symbol(name) for name in names}


def convention_expressions() -> dict[str, sp.Expr]:
    s = symbols()
    proper_cross = sp.simplify(
        s["delta_rho_other_proper"] + s["rho0_other_to_self"] * s["delta_B"]
    )
    effective_definition = sp.simplify(proper_cross)
    effective_cross = s["delta_rho_other_eff"]
    double_counted_cross = sp.simplify(
        s["delta_rho_other_eff"] + s["rho0_other_to_self"] * s["delta_B"]
    )
    return {
        "proper_cross_delta": proper_cross,
        "effective_density_definition": effective_definition,
        "effective_cross_delta": effective_cross,
        "double_counted_cross_delta": double_counted_cross,
        "double_counting_residual": sp.simplify(double_counted_cross - effective_definition),
        "delta_s00_self_plus_proper_cross": sp.simplify(s["delta_rho_self"] + proper_cross),
        "delta_s00_self_plus_effective_cross": sp.simplify(s["delta_rho_self"] + effective_cross),
    }


def build_payload() -> dict:
    conditional_selection = build_conditional_selection()
    expressions = convention_expressions()
    selected_field_residual_convention = (
        "proper_density_input"
        if conditional_selection["selected_field_residual_branch"] == "field_equation_4volume_source"
        else None
    )
    convention_rows = [
        {
            "name": "proper_density_input",
            "cross_delta": sp.sstr(expressions["proper_cross_delta"]),
            "qdet": "B4vol",
            "rule": "use proper density and add rho0 delta_B once",
            "accepted_for_delta_s00_algebra": True,
        },
        {
            "name": "effective_density_input",
            "cross_delta": sp.sstr(expressions["effective_cross_delta"]),
            "qdet": "1",
            "rule": "delta_rho_other_eff already includes rho0 delta_B",
            "accepted_for_delta_s00_algebra": True,
        },
        {
            "name": "double_counted_effective_times_b4vol",
            "cross_delta": sp.sstr(expressions["double_counted_cross_delta"]),
            "qdet": "B4vol applied again",
            "rule": "forbidden because it adds rho0 delta_B twice",
            "accepted_for_delta_s00_algebra": False,
        },
    ]
    return {
        "description": "Weak-field delta_S00 density-measure convention gate preventing B4vol/Qdet double counting.",
        "status": "delta-s00-measure-convention-algebra-closed-selection-open",
        "depends_on": [
            "qdet_density_measure_target",
            "p0_source_measure_convention_matrix",
            "p0_b_jphi_qdet_conditional_selection",
            "p0_janus_weakfield_delta_s00_source_expansion_gate",
        ],
        "convention_rows": convention_rows,
        "effective_density_definition": sp.sstr(expressions["effective_density_definition"]),
        "double_counting_residual": sp.sstr(expressions["double_counting_residual"]),
        "proper_and_effective_equivalence_condition": (
            "delta_rho_other_eff = delta_rho_other_proper + rho0_other_to_self delta_B"
        ),
        "measure_convention_algebra_closed": True,
        "single_active_convention_required": True,
        "selected_field_residual_branch": conditional_selection["selected_field_residual_branch"],
        "selected_field_residual_convention": selected_field_residual_convention,
        "field_residual_convention_selected": selected_field_residual_convention is not None,
        "accepted_convention": None,
        "source_convention_selected": False,
        "double_counting_forbidden": True,
        "qdet_absorption_allowed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The delta_S00 source can be written with either proper density plus one B4vol "
            "factor, or with an already effective density and Qdet=1. Applying B4vol to "
            "the effective density is explicitly rejected."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Weak-Field Delta S00 Measure Convention Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Effective density definition: `{payload['effective_density_definition']}`",
        f"Double-counting residual: `{payload['double_counting_residual']}`",
        f"Measure convention algebra closed: {payload['measure_convention_algebra_closed']}",
        f"Single active convention required: {payload['single_active_convention_required']}",
        f"Selected field residual branch: `{payload['selected_field_residual_branch']}`",
        f"Selected field residual convention: `{payload['selected_field_residual_convention']}`",
        f"Field residual convention selected: {payload['field_residual_convention_selected']}",
        f"Accepted convention: {payload['accepted_convention']}",
        f"Source convention selected: {payload['source_convention_selected']}",
        f"Double counting forbidden: {payload['double_counting_forbidden']}",
        f"Qdet absorption allowed: {payload['qdet_absorption_allowed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Convention Rows",
        "",
        "| name | cross delta | qdet | rule | accepted |",
        "|---|---|---|---|---:|",
    ]
    for row in payload["convention_rows"]:
        lines.append(
            f"| {row['name']} | `{row['cross_delta']}` | `{row['qdet']}` | "
            f"{row['rule']} | {row['accepted_for_delta_s00_algebra']} |"
        )
    lines.extend(
        [
            "",
            f"Equivalence condition: `{payload['proper_and_effective_equivalence_condition']}`",
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
