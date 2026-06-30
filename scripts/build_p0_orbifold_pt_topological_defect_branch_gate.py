from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_orbifold_pt_bdefect_action_filter import build_payload as build_bdefect_filter


REPORT_PATH = Path("outputs/reports/p0_orbifold_pt_topological_defect_branch_gate.md")
JSON_PATH = Path("outputs/reports/p0_orbifold_pt_topological_defect_branch_gate.json")


def build_payload() -> dict:
    bdefect = build_bdefect_filter()
    rows = [
        {
            "test": "pt_mirror_covariance",
            "result": "conditional-pass",
            "reason": "transgression can compare two PT-related solder connections without choosing an observer residual",
        },
        {
            "test": "a_pt_boundary_current",
            "result": "formal-pass",
            "reason": "delta B_top/delta A_PT gives a geometric boundary current",
        },
        {
            "test": "coefficient_selection",
            "result": "fail-open",
            "reason": "level/coupling k_top is not fixed by Janus source data",
        },
        {
            "test": "dimensional_match",
            "result": "open",
            "reason": "the correct Chern-Weil/transgression degree depends on Sigma_PT dimension",
        },
        {
            "test": "split_noether",
            "result": "open",
            "reason": "topological current alone does not prove R_plus=R_minus=0",
        },
        {
            "test": "stability",
            "result": "open",
            "reason": "topological boundary terms do not by themselves fix bulk ghost/tachyon signs",
        },
    ]
    return {
        "description": (
            "Focused gate for the topological/transgression B_defect branch, the "
            "least arbitrary defect-current candidate after PT/covariance filtering."
        ),
        "status": "orbifold-pt-topological-defect-branch-open",
        "depends_on": ["p0_orbifold_pt_bdefect_action_filter"],
        "bdefect_filter_status": bdefect["status"],
        "candidate_action": "B_top = k_top Transgression(A_PT, tau^*A_PT) on Sigma_PT",
        "candidate_current": "J_defect_top = -delta B_top/delta A_PT",
        "rows": rows,
        "topological_branch_is_best_current_candidate": True,
        "geometric_current_written": True,
        "uses_matter_moments": False,
        "uses_observational_fit": False,
        "coefficient_k_top_source_derived": False,
        "dimension_degree_fixed": False,
        "split_noether_bianchi_proved": False,
        "stability_closed": False,
        "branch_accepted": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The transgression branch is the cleanest J_defect route because it is "
            "geometric and avoids matter-moment closure. It still does not close: "
            "k_top, degree/dimension, split Noether and stability are open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Orbifold/PT Topological Defect Branch Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Candidate action: `{payload['candidate_action']}`",
        f"Candidate current: `{payload['candidate_current']}`",
        f"Topological branch is best current candidate: {payload['topological_branch_is_best_current_candidate']}",
        f"Geometric current written: {payload['geometric_current_written']}",
        f"Uses matter moments: {payload['uses_matter_moments']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Coefficient k_top source-derived: {payload['coefficient_k_top_source_derived']}",
        f"Dimension degree fixed: {payload['dimension_degree_fixed']}",
        f"Split Noether/Bianchi proved: {payload['split_noether_bianchi_proved']}",
        f"Stability closed: {payload['stability_closed']}",
        f"Branch accepted: {payload['branch_accepted']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| test | result | reason |",
        "|---|---|---|",
    ]
    for row in payload["rows"]:
        lines.append(f"| {row['test']} | {row['result']} | {row['reason']} |")
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
