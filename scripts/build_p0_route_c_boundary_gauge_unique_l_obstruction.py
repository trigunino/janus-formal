from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_phi_j_l_boundary_selector_probe import build_payload as build_boundary
from scripts.build_p0_route_c_path_rule_selector_matrix import build_payload as build_path_matrix


REPORT_PATH = Path("outputs/reports/p0_route_c_boundary_gauge_unique_l_obstruction.md")
JSON_PATH = Path("outputs/reports/p0_route_c_boundary_gauge_unique_l_obstruction.json")


def build_payload() -> dict:
    boundary = build_boundary()
    path_matrix = build_path_matrix()
    rows = [
        {
            "selector": "pointwise_identity_gauge",
            "can_fix_l": True,
            "janus_supplied": False,
            "accepted_zero_axiom": False,
        },
        {
            "selector": "unit_jacobian_or_tetrad_basepoint",
            "can_fix_l": True,
            "janus_supplied": False,
            "accepted_zero_axiom": False,
        },
        {
            "selector": "mirror_inverse_boundary",
            "can_fix_l": False,
            "janus_supplied": "structural only",
            "accepted_zero_axiom": False,
        },
        {
            "selector": "periodic_topology",
            "can_fix_l": False,
            "janus_supplied": "structural only",
            "accepted_zero_axiom": False,
        },
        {
            "selector": "flrw_background_time",
            "can_fix_l": "background only",
            "janus_supplied": "background only",
            "accepted_zero_axiom": False,
        },
    ]
    return {
        "description": (
            "Priority 2 obstruction: boundary/gauge data can mathematically select "
            "a representative L, but only Janus-supplied data can make it zero-axiom."
        ),
        "status": "boundary-gauge-unique-l-obstruction-open",
        "boundary_selector_status": boundary["status"],
        "path_matrix_status": path_matrix["status"],
        "rows": rows,
        "strong_boundary_selectors_exist": bool(boundary["strong_selectors_exist"]),
        "strong_boundary_selectors_source_supplied": bool(boundary["strong_selectors_source_supplied"]),
        "structural_mirror_boundary_insufficient": bool(path_matrix["structural_mirror_boundary_insufficient"]),
        "unique_l_from_boundary_gauge": False,
        "new_boundary_axiom_required_if_adopted": True,
        "flrw_background_promotion_allowed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Boundary/gauge choices can pick an L representative, but the known "
            "structural Janus conditions do not uniquely select it. A pointwise "
            "boundary/gauge choice would be a new axiom unless Janus supplies it."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C Boundary/Gauge Unique-L Obstruction",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Strong boundary selectors exist: {payload['strong_boundary_selectors_exist']}",
        f"Strong boundary selectors source supplied: {payload['strong_boundary_selectors_source_supplied']}",
        f"Structural mirror/boundary insufficient: {payload['structural_mirror_boundary_insufficient']}",
        f"Unique L from boundary/gauge: {payload['unique_l_from_boundary_gauge']}",
        f"New boundary axiom required if adopted: {payload['new_boundary_axiom_required_if_adopted']}",
        f"FLRW background promotion allowed: {payload['flrw_background_promotion_allowed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| selector | can fix L | Janus supplied | accepted zero-axiom |",
        "|---|---|---|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['selector']} | {row['can_fix_l']} | "
            f"{row['janus_supplied']} | {row['accepted_zero_axiom']} |"
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
