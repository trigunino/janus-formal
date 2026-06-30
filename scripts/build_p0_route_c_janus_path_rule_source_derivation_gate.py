from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_path_rule_selector_matrix import build_payload as build_path_matrix
from scripts.build_p0_route_c_two_path_nonunique_l_probe import build_payload as build_two_path


REPORT_PATH = Path("outputs/reports/p0_route_c_janus_path_rule_source_derivation_gate.md")
JSON_PATH = Path("outputs/reports/p0_route_c_janus_path_rule_source_derivation_gate.json")


def build_payload() -> dict:
    path_matrix = build_path_matrix()
    two_path = build_two_path()
    source_rows = [
        {
            "origin": "published_coupled_field_equations",
            "candidate_rule": "derive path family from source divergence/Bianchi rows",
            "janus_supplied": False,
            "accepted": False,
        },
        {
            "origin": "positive_geodesic_equation",
            "candidate_rule": "transport along g_plus null/geodesic congruence",
            "janus_supplied": "geodesics yes, cross-sector path selection no",
            "accepted": False,
        },
        {
            "origin": "negative_geodesic_equation",
            "candidate_rule": "transport along pulled negative-sector geodesic family",
            "janus_supplied": "geodesics yes, cross-sector path selection no",
            "accepted": False,
        },
        {
            "origin": "mirror_symmetry",
            "candidate_rule": "choose paths by plus/minus inverse holonomy",
            "janus_supplied": "structural only",
            "accepted": False,
        },
        {
            "origin": "pt_geometry",
            "candidate_rule": "choose paths by PT-fixed involution, surface, or Wilson line",
            "janus_supplied": "compatibility/filter only",
            "accepted": False,
        },
        {
            "origin": "flrw_background",
            "candidate_rule": "normal/background time transport",
            "janus_supplied": "background only",
            "accepted": False,
        },
        {
            "origin": "noether_action",
            "candidate_rule": "derive path family from an accepted action multiplier",
            "janus_supplied": False,
            "accepted": False,
        },
    ]
    return {
        "description": (
            "Priority 1 gate: audit whether a zero-axiom holonomy path rule is "
            "derivable from Janus sources rather than chosen as a boundary/path axiom."
        ),
        "status": "janus-path-rule-source-derivation-gate-open",
        "depends_on": [
            "p0_route_c_path_rule_selector_matrix",
            "p0_route_c_two_path_nonunique_l_probe",
        ],
        "source_rows": source_rows,
        "path_matrix_status": path_matrix["status"],
        "two_path_status": two_path["status"],
        "zero_axiom_path_rule_selected": False,
        "path_rule_source_derivation_closed": False,
        "all_matrix_candidates_excluded": bool(path_matrix["all_candidates_excluded_for_prediction"]),
        "two_path_nonunique_l_blocks_prediction": bool(two_path["two_paths_select_different_l"]),
        "janus_geodesics_available": True,
        "janus_cross_sector_path_selector_available": False,
        "new_path_axiom_required_if_selected_now": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Janus geodesic equations can define curves, but no inspected Janus "
            "source currently selects the cross-sector holonomy path family needed "
            "for a unique same-L transport. Selecting one now would be a new path axiom."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C Janus Path-Rule Source Derivation Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Zero-axiom path rule selected: {payload['zero_axiom_path_rule_selected']}",
        f"Path-rule source derivation closed: {payload['path_rule_source_derivation_closed']}",
        f"All matrix candidates excluded: {payload['all_matrix_candidates_excluded']}",
        f"Two-path nonunique L blocks prediction: {payload['two_path_nonunique_l_blocks_prediction']}",
        f"Janus geodesics available: {payload['janus_geodesics_available']}",
        f"Janus cross-sector path selector available: {payload['janus_cross_sector_path_selector_available']}",
        f"New path axiom required if selected now: {payload['new_path_axiom_required_if_selected_now']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| origin | candidate rule | Janus supplied | accepted |",
        "|---|---|---|---:|",
    ]
    for row in payload["source_rows"]:
        lines.append(
            f"| {row['origin']} | {row['candidate_rule']} | "
            f"{row['janus_supplied']} | {row['accepted']} |"
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
