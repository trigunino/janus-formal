from __future__ import annotations

from pathlib import Path
import json
import sys

import numpy as np
import sympy as sp
from scipy import linalg


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_pt_geometry_path_rule_audit import (
    build_payload as build_pt_audit,
)
from scripts.build_p0_route_c_small_loop_holonomy_numeric_probe import boost_generator
from scripts.build_p0_route_c_two_path_nonunique_l_probe import build_payload as build_two_path


REPORT_PATH = Path("outputs/reports/p0_route_c_pt_selector_derivation_attempt.md")
JSON_PATH = Path("outputs/reports/p0_route_c_pt_selector_derivation_attempt.json")
TOLERANCE = 1e-10


def pt_odd_residual(expr: sp.Expr, t: sp.Symbol, x: sp.Symbol) -> sp.Expr:
    return sp.expand(expr.subs({t: -t, x: -x}) + expr)


def build_payload() -> dict:
    pt_audit = build_pt_audit()
    two_path = build_two_path()
    t, x, eps = sp.symbols("t x eps")
    fixed_surface_a = t
    fixed_surface_b = t + eps * x**3
    surface_a_residual = pt_odd_residual(fixed_surface_a, t, x)
    surface_b_residual = pt_odd_residual(fixed_surface_b, t, x)

    area_x = two_path["area_x"]
    area_y = two_path["area_y"]
    generator_x = boost_generator("x")
    generator_y = boost_generator("y")
    path_xy = linalg.expm(area_y * generator_y) @ linalg.expm(area_x * generator_x)
    path_yx = linalg.expm(area_x * generator_x) @ linalg.expm(area_y * generator_y)
    identity_cost_xy = float(linalg.norm(path_xy - np.eye(4), ord="fro"))
    identity_cost_yx = float(linalg.norm(path_yx - np.eye(4), ord="fro"))
    identity_cost_difference = abs(identity_cost_xy - identity_cost_yx)

    candidate_rows = [
        {
            "candidate": "pt_fixed_surface",
            "tested_condition": "F(PT x) = -F(x)",
            "pt_condition_passes": True,
            "selector_derived": False,
            "counterexample": "F=t and F=t+eps*x^3 are both PT-odd but define different surfaces",
            "blocker": "PT parity leaves a functional family; Janus must fix eps or the boundary equation",
        },
        {
            "candidate": "pt_path_functional",
            "tested_condition": "PT-even local path cost treats reversed/pair paths equally",
            "pt_condition_passes": True,
            "selector_derived": False,
            "counterexample": "a symmetric local cost cannot distinguish x-then-y from y-then-x",
            "blocker": "an ordered Wilson/path term could select, but would be a new action unless source-derived",
        },
        {
            "candidate": "pt_holonomy_minimal_curvature",
            "tested_condition": "Lorentz holonomy and mirror admissibility are imposed before selection",
            "pt_condition_passes": True,
            "selector_derived": False,
            "counterexample": "two admissible noncommuting holonomies survive with different L",
            "blocker": "minimal/zero residual criteria need a source-fixed norm, boundary and ordering rule",
        },
    ]
    return {
        "description": (
            "Route C hard derivation attempt for a zero-axiom PT selector. It "
            "formalizes PT as an involutive geometry and tests three possible "
            "selector mechanisms against the same-L/noncommuting-holonomy lock."
        ),
        "status": "pt-selector-derivation-attempt-open",
        "depends_on": [
            "p0_route_c_pt_geometry_path_rule_audit",
            "p0_route_c_two_path_nonunique_l_probe",
        ],
        "pt_audit_status": pt_audit["status"],
        "candidate_rows": candidate_rows,
        "pt_geometry_formalized": True,
        "pt_involution_required": "P_T^2 = identity",
        "metric_compatibility_required": "P_T^* g_minus = g_plus or explicitly sourced defect",
        "tetrad_transport_required": "L = e_plus^{-1} dP_T e_minus only after P_T/path is selected",
        "same_l_required_for": ["K", "Q_cross", "Vlasov/matter", "mirror_inverse"],
        "surface_a": str(fixed_surface_a),
        "surface_b": str(fixed_surface_b),
        "surface_a_pt_odd_residual": str(surface_a_residual),
        "surface_b_pt_odd_residual": str(surface_b_residual),
        "pt_surface_family_underselected": surface_a_residual == 0 and surface_b_residual == 0,
        "pt_symmetric_path_cost_difference": 0.0,
        "identity_holonomy_cost_xy": identity_cost_xy,
        "identity_holonomy_cost_yx": identity_cost_yx,
        "identity_holonomy_cost_tie": identity_cost_difference < TOLERANCE,
        "two_path_l_residual": two_path["two_path_l_residual"],
        "two_path_counterexample_active": bool(two_path["two_paths_select_different_l"]),
        "zero_axiom_pt_selector_found": False,
        "pt_fixed_surface_closes": False,
        "pt_path_functional_closes": False,
        "pt_holonomy_minimal_curvature_closes": False,
        "requires_new_source_term_or_axiom": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The hard PT attempt still does not close Route C. PT can define "
            "admissibility constraints, but PT-odd surfaces are underselected, "
            "PT-symmetric local path costs do not resolve noncommuting order, and "
            "holonomy-minimal criteria need a Janus-supplied norm/boundary/action."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C PT Selector Derivation Attempt",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"PT geometry formalized: {payload['pt_geometry_formalized']}",
        f"PT involution required: `{payload['pt_involution_required']}`",
        f"Metric compatibility required: `{payload['metric_compatibility_required']}`",
        f"Tetrad transport required: `{payload['tetrad_transport_required']}`",
        f"Same L required for: `{payload['same_l_required_for']}`",
        f"Surface A PT-odd residual: `{payload['surface_a_pt_odd_residual']}`",
        f"Surface B PT-odd residual: `{payload['surface_b_pt_odd_residual']}`",
        f"PT surface family underselected: {payload['pt_surface_family_underselected']}",
        f"PT symmetric path cost difference: {payload['pt_symmetric_path_cost_difference']:.12g}",
        f"Identity holonomy cost tie: {payload['identity_holonomy_cost_tie']}",
        f"Two-path L residual: {payload['two_path_l_residual']:.12g}",
        f"Two-path counterexample active: {payload['two_path_counterexample_active']}",
        f"Zero-axiom PT selector found: {payload['zero_axiom_pt_selector_found']}",
        f"Requires new source term or axiom: {payload['requires_new_source_term_or_axiom']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| candidate | tested condition | PT condition passes | selector derived | blocker |",
        "|---|---|---:|---:|---|",
    ]
    for row in payload["candidate_rows"]:
        lines.append(
            f"| {row['candidate']} | {row['tested_condition']} | "
            f"{row['pt_condition_passes']} | {row['selector_derived']} | {row['blocker']} |"
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
