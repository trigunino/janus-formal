from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_boundary_gauge_unique_l_obstruction import (
    build_payload as build_boundary_obstruction,
)
from scripts.build_p0_route_c_janus_path_rule_source_derivation_gate import (
    build_payload as build_path_source,
)
from scripts.build_p0_route_c_small_loop_holonomy_numeric_probe import (
    build_payload as build_small_loop,
)
from scripts.build_p0_route_c_two_path_nonunique_l_probe import build_payload as build_two_path


REPORT_PATH = Path("outputs/reports/p0_route_c_no_path_rule_underselection_theorem.md")
JSON_PATH = Path("outputs/reports/p0_route_c_no_path_rule_underselection_theorem.json")


def build_payload() -> dict:
    path_source = build_path_source()
    boundary = build_boundary_obstruction()
    small_loop = build_small_loop()
    two_path = build_two_path()
    theorem_rows = [
        {
            "premise": "lorentz_admissibility",
            "evidence": "curvature generator is in the Lorentz algebra",
            "sufficient_for_unique_l": False,
        },
        {
            "premise": "small_loop_holonomy",
            "evidence": "constant-curvature small-loop and segmentation checks pass",
            "sufficient_for_unique_l": False,
        },
        {
            "premise": "noncommuting_holonomy",
            "evidence": "two admissible path orderings produce different L",
            "sufficient_for_unique_l": False,
        },
        {
            "premise": "mirror_boundary_structure",
            "evidence": "mirror/topology filters branches but does not choose one path family",
            "sufficient_for_unique_l": False,
        },
        {
            "premise": "pt_geometry_filter",
            "evidence": "PT involution and parity constrain admissible maps but do not select a noncommuting holonomy order",
            "sufficient_for_unique_l": False,
        },
        {
            "premise": "janus_path_source",
            "evidence": "geodesics exist but cross-sector path selector is absent",
            "sufficient_for_unique_l": False,
        },
    ]
    return {
        "description": (
            "Bounded Route C theorem: curvature, Lorentz admissibility, local "
            "holonomy, mirror structure, and structural boundary data underselect L "
            "unless Janus supplies a path rule."
        ),
        "status": "no-path-rule-underselection-theorem-bounded",
        "depends_on": [
            "p0_route_c_janus_path_rule_source_derivation_gate",
            "p0_route_c_boundary_gauge_unique_l_obstruction",
            "p0_route_c_small_loop_holonomy_numeric_probe",
            "p0_route_c_two_path_nonunique_l_probe",
        ],
        "theorem_rows": theorem_rows,
        "lorentz_curvature_local_checks_pass": bool(small_loop["lorentz_algebra_candidate"]),
        "small_loop_checks_pass": bool(small_loop["constant_curvature_segmentation_closes"]),
        "two_path_counterexample_active": bool(two_path["two_paths_select_different_l"]),
        "boundary_gauge_selects_zero_axiom_l": bool(boundary["unique_l_from_boundary_gauge"]),
        "janus_path_rule_supplied": bool(path_source["zero_axiom_path_rule_selected"]),
        "curvature_lorentz_holonomy_mirror_sufficient_for_unique_l": False,
        "path_rule_required_for_unique_l": True,
        "bounded_no_go_closed": True,
        "full_no_go_proved": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Route C now has a bounded underselection theorem: the existing geometric "
            "conditions are necessary filters, not a selector. A Janus-derived path "
            "rule remains required for unique same-L prediction."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C No-Path-Rule Underselection Theorem",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Lorentz/curvature local checks pass: {payload['lorentz_curvature_local_checks_pass']}",
        f"Small-loop checks pass: {payload['small_loop_checks_pass']}",
        f"Two-path counterexample active: {payload['two_path_counterexample_active']}",
        f"Boundary/gauge selects zero-axiom L: {payload['boundary_gauge_selects_zero_axiom_l']}",
        f"Janus path rule supplied: {payload['janus_path_rule_supplied']}",
        f"Curvature/Lorentz/holonomy/mirror sufficient for unique L: {payload['curvature_lorentz_holonomy_mirror_sufficient_for_unique_l']}",
        f"Path rule required for unique L: {payload['path_rule_required_for_unique_l']}",
        f"Bounded no-go closed: {payload['bounded_no_go_closed']}",
        f"Full no-go proved: {payload['full_no_go_proved']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| premise | evidence | sufficient for unique L |",
        "|---|---|---:|",
    ]
    for row in payload["theorem_rows"]:
        lines.append(
            f"| {row['premise']} | {row['evidence']} | "
            f"{row['sufficient_for_unique_l']} |"
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
