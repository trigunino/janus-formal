from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_holonomy_path_rule_branch import build_payload as build_path_branch
from scripts.build_p0_phi_j_l_boundary_selector_probe import build_payload as build_boundary


REPORT_PATH = Path("outputs/reports/p0_route_c_path_rule_selector_matrix.md")
JSON_PATH = Path("outputs/reports/p0_route_c_path_rule_selector_matrix.json")


def build_payload() -> dict:
    path_branch = build_path_branch()
    boundary = build_boundary()
    rows = [
        {
            "rule": "positive_null_ray",
            "source_supplied": False,
            "same_l_for_k_qcross": "required",
            "loop_closed": False,
            "fixes_unique_path_family": False,
            "excluded_as_prediction": True,
        },
        {
            "rule": "matter_worldline",
            "source_supplied": False,
            "same_l_for_k_qcross": "required",
            "loop_closed": False,
            "fixes_unique_path_family": False,
            "excluded_as_prediction": True,
        },
        {
            "rule": "geodesic_congruence",
            "source_supplied": False,
            "same_l_for_k_qcross": "required",
            "loop_closed": False,
            "fixes_unique_path_family": False,
            "excluded_as_prediction": True,
        },
        {
            "rule": "hypersurface_normal",
            "source_supplied": False,
            "same_l_for_k_qcross": "required",
            "loop_closed": False,
            "fixes_unique_path_family": False,
            "excluded_as_prediction": True,
        },
        {
            "rule": "curvature_extremal_path",
            "source_supplied": False,
            "same_l_for_k_qcross": "required",
            "loop_closed": False,
            "fixes_unique_path_family": "conditional",
            "excluded_as_prediction": True,
        },
        {
            "rule": "spin_connection_autoparallel",
            "source_supplied": False,
            "same_l_for_k_qcross": "required",
            "loop_closed": False,
            "fixes_unique_path_family": "conditional",
            "excluded_as_prediction": True,
        },
        {
            "rule": "mirror_symmetric_biloop",
            "source_supplied": "structural-only",
            "same_l_for_k_qcross": "required",
            "loop_closed": False,
            "fixes_unique_path_family": False,
            "excluded_as_prediction": True,
        },
        {
            "rule": "flrw_background_normal",
            "source_supplied": "background-only",
            "same_l_for_k_qcross": "required",
            "loop_closed": False,
            "fixes_unique_path_family": False,
            "excluded_as_prediction": True,
        },
    ]
    acceptance_gate = [
        "rule is derived from Janus field equations/action/symmetry, not selected by hand",
        "same path family is used for K, Q_cross, and kinetic moments",
        "nonzero-curvature loop identities are closed",
        "segmentation and mirror inverse are proved",
        "boundary data are Janus-supplied, not pointwise gauge choices",
    ]
    return {
        "description": (
            "Route C selector matrix for holonomy path rules. It ranks candidate "
            "rules and rejects them for prediction unless Janus supplies the rule, "
            "loop closure, mirror closure, and same-L transport."
        ),
        "status": "path-rule-selector-matrix-open",
        "path_branch_status": path_branch["status"],
        "boundary_selector_status": boundary["status"],
        "rows": rows,
        "acceptance_gate": acceptance_gate,
        "candidate_rule_count": len(rows),
        "accepted_rule_count": sum(1 for row in rows if not row["excluded_as_prediction"]),
        "all_candidates_excluded_for_prediction": all(row["excluded_as_prediction"] for row in rows),
        "structural_mirror_boundary_insufficient": not bool(boundary["mirror_topology_alone_fixes_unique_map"]),
        "strong_boundary_selector_source_supplied": bool(boundary["strong_selectors_source_supplied"]),
        "path_rule_source_derived": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "No candidate path rule is accepted for prediction. The strongest "
            "geometric rules can be tested, but without Janus-supplied boundary/path "
            "data they remain hidden-axiom selectors."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C Path-Rule Selector Matrix",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Candidate rule count: {payload['candidate_rule_count']}",
        f"Accepted rule count: {payload['accepted_rule_count']}",
        f"All candidates excluded for prediction: {payload['all_candidates_excluded_for_prediction']}",
        f"Structural mirror/boundary insufficient: {payload['structural_mirror_boundary_insufficient']}",
        f"Strong boundary selector source supplied: {payload['strong_boundary_selector_source_supplied']}",
        f"Path rule source derived: {payload['path_rule_source_derived']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| rule | source supplied | same-L | loop closed | unique path family | excluded |",
        "|---|---|---|---:|---|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['rule']} | {row['source_supplied']} | {row['same_l_for_k_qcross']} | "
            f"{row['loop_closed']} | {row['fixes_unique_path_family']} | "
            f"{row['excluded_as_prediction']} |"
        )
    lines.extend(["", "## Acceptance Gate", ""])
    lines.extend(f"- {item}" for item in payload["acceptance_gate"])
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
