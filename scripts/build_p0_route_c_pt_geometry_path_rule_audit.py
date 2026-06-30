from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_janus_path_rule_source_derivation_gate import (
    build_payload as build_path_source,
)
from scripts.build_p0_route_c_no_path_rule_underselection_theorem import (
    build_payload as build_underselection,
)
from scripts.build_p0_route_c_two_path_nonunique_l_probe import build_payload as build_two_path
from scripts.build_p0_pt_lie_vjanus_ajanus_constraint_solver import (
    build_payload as build_pt_lie,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_pt_geometry_path_rule_audit.md")
JSON_PATH = Path("outputs/reports/p0_route_c_pt_geometry_path_rule_audit.json")


def build_payload() -> dict:
    path_source = build_path_source()
    underselection = build_underselection()
    two_path = build_two_path()
    pt_lie = build_pt_lie()
    rows = [
        {
            "pt_object": "pt_involution",
            "janus_anchor": "M26/M29/M31/X2025-bimetric orientation only",
            "constraint": "maps plus/minus sectors and reverses the relevant orientation labels",
            "selects_path_rule": False,
            "blocker": "an involution constrains endpoints and images, not a unique holonomy path family",
        },
        {
            "pt_object": "mirror_inverse_holonomy",
            "janus_anchor": "mirror symmetry rows already present in Route C",
            "constraint": "accepted transports must satisfy L_minus_to_plus = inverse(L_plus_to_minus)",
            "selects_path_rule": False,
            "blocker": "inverse consistency tests a chosen path; it does not choose between noncommuting paths",
        },
        {
            "pt_object": "extended_poincare_lie_branch",
            "janus_anchor": "p0_pt_lie_vjanus_ajanus_constraint_solver",
            "constraint": "filters parity of V_Janus/A_Janus candidate branches",
            "selects_path_rule": False,
            "blocker": "branch parity is not a covariant cross-sector path functional",
        },
        {
            "pt_object": "pt_fixed_surface_or_throat",
            "janus_anchor": "M29 one-way-wormhole/PT topology orientation",
            "constraint": "would define a transition hypersurface or boundary relation if supplied",
            "selects_path_rule": False,
            "blocker": "using a surface as selector is new boundary data unless Janus source fixes it",
        },
        {
            "pt_object": "pt_paired_geodesics",
            "janus_anchor": "M30/X2025 bimetric geodesic families",
            "constraint": "pairs sector geodesics after a map/bridge has been selected",
            "selects_path_rule": False,
            "blocker": "sector geodesics are available, but the cross-sector soldering path is still missing",
        },
        {
            "pt_object": "pt_wilson_line_candidate",
            "janus_anchor": "not published-source-derived in current ledger",
            "constraint": "could extremize a PT-invariant path action or Wilson line",
            "selects_path_rule": "conditional-extension-only",
            "blocker": "without source derivation this is an explicit new path axiom",
        },
    ]
    return {
        "description": (
            "Hard Route C audit for PT geometry as a zero-axiom selector of the "
            "cross-sector holonomy path rule."
        ),
        "status": "pt-geometry-path-rule-audit-open",
        "depends_on": [
            "p0_route_c_janus_path_rule_source_derivation_gate",
            "p0_route_c_no_path_rule_underselection_theorem",
            "p0_route_c_two_path_nonunique_l_probe",
            "p0_pt_lie_vjanus_ajanus_constraint_solver",
        ],
        "rows": rows,
        "path_source_status": path_source["status"],
        "underselection_status": underselection["status"],
        "pt_lie_status": pt_lie["status"],
        "pt_geometry_source_found": False,
        "pt_involution_filters_not_selects": True,
        "pt_mirror_inverse_constraint": True,
        "pt_lie_branch_filters_not_path_selector": True,
        "pt_path_rule_selected": False,
        "two_path_counterexample_survives_pt": bool(two_path["two_paths_select_different_l"]),
        "pt_fixed_boundary_would_be_new_axiom": True,
        "pt_wilson_line_would_be_new_axiom_without_source": True,
        "janus_cross_sector_path_selector_available": bool(
            path_source["janus_cross_sector_path_selector_available"]
        ),
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "PT geometry is a strong compatibility filter: it supports mirror "
            "inverse, sector pairing, and parity constraints. In the current source "
            "ledger it still does not select a unique same-L holonomy path. A "
            "PT-fixed path action, Wilson line, or transition surface would have to "
            "be source-derived before it can close Route C without a new axiom."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C PT Geometry Path-Rule Audit",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"PT geometry source found: {payload['pt_geometry_source_found']}",
        f"PT involution filters not selects: {payload['pt_involution_filters_not_selects']}",
        f"PT mirror inverse constraint: {payload['pt_mirror_inverse_constraint']}",
        f"PT/Lie branch filters not path selector: {payload['pt_lie_branch_filters_not_path_selector']}",
        f"PT path rule selected: {payload['pt_path_rule_selected']}",
        f"Two-path counterexample survives PT: {payload['two_path_counterexample_survives_pt']}",
        f"PT fixed boundary would be new axiom: {payload['pt_fixed_boundary_would_be_new_axiom']}",
        f"PT Wilson line would be new axiom without source: {payload['pt_wilson_line_would_be_new_axiom_without_source']}",
        f"Janus cross-sector path selector available: {payload['janus_cross_sector_path_selector_available']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| PT object | Janus anchor | constraint | selects path rule | blocker |",
        "|---|---|---|---:|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['pt_object']} | {row['janus_anchor']} | {row['constraint']} | "
            f"{row['selects_path_rule']} | {row['blocker']} |"
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
