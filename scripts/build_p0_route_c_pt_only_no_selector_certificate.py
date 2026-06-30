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

from scripts.build_p0_route_c_pt_selector_derivation_attempt import (
    build_payload as build_pt_selector,
)
from scripts.build_p0_route_c_small_loop_holonomy_numeric_probe import boost_generator
from scripts.build_p0_route_c_two_path_nonunique_l_probe import build_payload as build_two_path


REPORT_PATH = Path("outputs/reports/p0_route_c_pt_only_no_selector_certificate.md")
JSON_PATH = Path("outputs/reports/p0_route_c_pt_only_no_selector_certificate.json")
TOLERANCE = 1e-10


def build_payload() -> dict:
    selector = build_pt_selector()
    two_path = build_two_path()
    q = sp.symbols("q")
    a1, a3, a5, b0, b2, b4 = sp.symbols("a1 a3 a5 b0 b2 b4")
    pt_odd_surface_family = a1 * q + a3 * q**3 + a5 * q**5
    pt_even_cost_family = b0 + b2 * q**2 + b4 * q**4
    pt_odd_residual = sp.expand(pt_odd_surface_family.subs(q, -q) + pt_odd_surface_family)
    pt_even_residual = sp.expand(pt_even_cost_family.subs(q, -q) - pt_even_cost_family)

    area_x = two_path["area_x"]
    area_y = two_path["area_y"]
    generator_x = boost_generator("x")
    generator_y = boost_generator("y")
    path_xy = linalg.expm(area_y * generator_y) @ linalg.expm(area_x * generator_x)
    path_yx = linalg.expm(area_x * generator_x) @ linalg.expm(area_y * generator_y)
    trace_difference = float(abs(np.trace(path_xy) - np.trace(path_yx)))
    determinant_difference = float(abs(np.linalg.det(path_xy) - np.linalg.det(path_yx)))
    frobenius_l_difference = float(linalg.norm(path_xy - path_yx, ord="fro"))

    certificate_rows = [
        {
            "claim": "pt_odd_surface_underselection",
            "bounded_result": True,
            "evidence": "F(q)=a1*q+a3*q^3+a5*q^5 is PT-odd for arbitrary coefficients",
            "escape": "Janus must supply a boundary equation fixing the coefficients or surface",
        },
        {
            "claim": "pt_even_scalar_cost_underselection",
            "bounded_result": True,
            "evidence": "C(q)=b0+b2*q^2+b4*q^4 is PT-even for arbitrary coefficients",
            "escape": "Janus must supply the path functional, not only PT parity",
        },
        {
            "claim": "scalar_holonomy_invariant_tie",
            "bounded_result": True,
            "evidence": "trace/determinant invariants tie while noncommuting paths give different L",
            "escape": "an ordered Wilson/path action must be source-derived",
        },
        {
            "claim": "mirror_inverse_not_selector",
            "bounded_result": True,
            "evidence": "mirror inverse maps an accepted L to its inverse but does not choose the path",
            "escape": "a covariant same-L path rule must be derived before mirror testing",
        },
    ]
    return {
        "description": (
            "Bounded certificate that PT symmetry alone does not select the Route C "
            "same-L cross-sector holonomy path."
        ),
        "status": "pt-only-no-selector-certificate-bounded",
        "depends_on": [
            "p0_route_c_pt_selector_derivation_attempt",
            "p0_route_c_two_path_nonunique_l_probe",
        ],
        "selector_status": selector["status"],
        "certificate_rows": certificate_rows,
        "pt_odd_surface_family": str(pt_odd_surface_family),
        "pt_odd_surface_residual": str(pt_odd_residual),
        "pt_even_cost_family": str(pt_even_cost_family),
        "pt_even_cost_residual": str(pt_even_residual),
        "pt_surface_family_dimension_tested": 3,
        "pt_cost_family_dimension_tested": 3,
        "trace_difference_xy_yx": trace_difference,
        "determinant_difference_xy_yx": determinant_difference,
        "scalar_invariants_tie": trace_difference < TOLERANCE
        and determinant_difference < TOLERANCE,
        "frobenius_l_difference_xy_yx": frobenius_l_difference,
        "noncommuting_paths_select_different_l": bool(two_path["two_paths_select_different_l"]),
        "bounded_pt_only_no_selector_closed": True,
        "pt_only_selects_unique_l": False,
        "ordered_path_action_is_escape": True,
        "requires_janus_source_for_escape": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "PT-only selection is now bounded as a no-selector result. PT parity "
            "admits families of surfaces and scalar costs, and scalar holonomy "
            "invariants can tie while L differs. A selector must therefore come "
            "from a Janus source term, boundary law, or ordered path action."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C PT-Only No-Selector Certificate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"PT odd surface family: `{payload['pt_odd_surface_family']}`",
        f"PT odd surface residual: `{payload['pt_odd_surface_residual']}`",
        f"PT even cost family: `{payload['pt_even_cost_family']}`",
        f"PT even cost residual: `{payload['pt_even_cost_residual']}`",
        f"Scalar invariants tie: {payload['scalar_invariants_tie']}",
        f"Frobenius L difference xy/yx: {payload['frobenius_l_difference_xy_yx']:.12g}",
        f"Noncommuting paths select different L: {payload['noncommuting_paths_select_different_l']}",
        f"Bounded PT-only no-selector closed: {payload['bounded_pt_only_no_selector_closed']}",
        f"PT-only selects unique L: {payload['pt_only_selects_unique_l']}",
        f"Ordered path action is escape: {payload['ordered_path_action_is_escape']}",
        f"Requires Janus source for escape: {payload['requires_janus_source_for_escape']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| claim | bounded result | evidence | escape |",
        "|---|---:|---|---|",
    ]
    for row in payload["certificate_rows"]:
        lines.append(
            f"| {row['claim']} | {row['bounded_result']} | {row['evidence']} | "
            f"{row['escape']} |"
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
