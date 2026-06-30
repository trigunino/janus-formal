from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_orbifold_pt_source_current_gate import build_payload as build_source_gate


REPORT_PATH = Path("outputs/reports/p0_orbifold_pt_defect_matching_law_gate.md")
JSON_PATH = Path("outputs/reports/p0_orbifold_pt_defect_matching_law_gate.json")


def build_payload() -> dict:
    source_gate = build_source_gate()
    matching_rows = [
        {
            "condition": "pt_orbifold_identification",
            "formula": "tau^2=id and fields obey PT parity on Sigma_PT",
            "written": True,
            "source_derived": True,
            "selects_current": False,
            "blocker": "identification fixes parity, not defect tension/current",
        },
        {
            "condition": "flux_jump",
            "formula": "n_A[*F_PT]^+_- = J_defect",
            "written": True,
            "source_derived": False,
            "selects_current": False,
            "blocker": "right-hand side needs defect action or matching stress",
        },
        {
            "condition": "defect_action_variation",
            "formula": "J_defect = - delta B_defect/delta A_PT",
            "written": True,
            "source_derived": False,
            "selects_current": False,
            "blocker": "B_defect not derived from Janus/orbifold geometry",
        },
        {
            "condition": "metric_matching",
            "formula": "[h_ab]=0 and [K_ab-K h_ab]=S_ab^defect",
            "written": True,
            "source_derived": False,
            "selects_current": False,
            "blocker": "S_ab^defect is not fixed by sources",
        },
        {
            "condition": "a_pt_boundary_condition",
            "formula": "n_A *F_PT + delta B_defect/delta A_PT = 0 on Sigma_PT",
            "written": True,
            "source_derived": False,
            "selects_current": False,
            "blocker": "same missing B_defect controls the boundary law",
        },
    ]
    return {
        "description": (
            "Orbifold/PT defect matching law gate for Sigma_PT. It tests whether "
            "the fixed locus can source J_defect without free hand-selection."
        ),
        "status": "orbifold-pt-defect-matching-law-open",
        "depends_on": ["p0_orbifold_pt_source_current_gate"],
        "source_gate_status": source_gate["status"],
        "matching_rows": matching_rows,
        "sigma_pt_law_written": True,
        "pt_identification_source_derived": True,
        "flux_jump_condition_written": True,
        "defect_action_required": True,
        "defect_action_source_derived": False,
        "j_defect_formula_written": True,
        "j_defect_source_derived": False,
        "a_pt_boundary_condition_written": True,
        "a_pt_boundary_condition_closed": False,
        "metric_israel_like_matching_written": True,
        "defect_stress_source_derived": False,
        "unique_defect_current_selected": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Sigma_PT can provide the correct geometric place for J_defect. The "
            "matching form is written, but it still underselects because B_defect "
            "or S_defect is not derived. PT identification alone fixes parity, not "
            "the defect current."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Orbifold/PT Defect Matching Law Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Sigma_PT law written: {payload['sigma_pt_law_written']}",
        f"PT identification source-derived: {payload['pt_identification_source_derived']}",
        f"Flux jump condition written: {payload['flux_jump_condition_written']}",
        f"Defect action required: {payload['defect_action_required']}",
        f"Defect action source-derived: {payload['defect_action_source_derived']}",
        f"J_defect formula written: {payload['j_defect_formula_written']}",
        f"J_defect source-derived: {payload['j_defect_source_derived']}",
        f"A_PT boundary condition written: {payload['a_pt_boundary_condition_written']}",
        f"A_PT boundary condition closed: {payload['a_pt_boundary_condition_closed']}",
        f"Metric Israel-like matching written: {payload['metric_israel_like_matching_written']}",
        f"Defect stress source-derived: {payload['defect_stress_source_derived']}",
        f"Unique defect current selected: {payload['unique_defect_current_selected']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| condition | formula | written | source-derived | selects current | blocker |",
        "|---|---|---:|---:|---:|---|",
    ]
    for row in payload["matching_rows"]:
        lines.append(
            f"| {row['condition']} | `{row['formula']}` | {row['written']} | "
            f"{row['source_derived']} | {row['selects_current']} | {row['blocker']} |"
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
