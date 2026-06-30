from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_orbifold_pt_defect_matching_law_gate import (
    build_payload as build_defect_matching,
)


REPORT_PATH = Path("outputs/reports/p0_orbifold_pt_bdefect_action_filter.md")
JSON_PATH = Path("outputs/reports/p0_orbifold_pt_bdefect_action_filter.json")


def build_payload() -> dict:
    matching = build_defect_matching()
    rows = [
        {
            "candidate": "topological_boundary_term",
            "form": "B_defect = k CS(A_PT) or transgression(A_plus,A_minus)",
            "covariant": "up_to_boundary/gauge",
            "pt_compatible": True,
            "yields_j_defect": True,
            "accepted": False,
            "blocker": "level k and anomaly/boundary cancellation are not Janus-derived",
        },
        {
            "candidate": "defect_tension_geometry",
            "form": "B_defect = sqrt(|h|)(sigma + alpha [K]^2 + beta R[h])",
            "covariant": True,
            "pt_compatible": True,
            "yields_j_defect": False,
            "accepted": False,
            "blocker": "gives metric defect stress, but no A_PT current unless coupled to solder fields",
        },
        {
            "candidate": "matter_solder_boundary",
            "form": "B_defect = sqrt(|h|) Tr(A_PT P_so(T_plus L T_minus L^T))",
            "covariant": True,
            "pt_compatible": True,
            "yields_j_defect": True,
            "accepted": False,
            "blocker": "pressure/Pi/Vlasov transport and coefficient are not source-derived",
        },
        {
            "candidate": "pt_constraint_multiplier",
            "form": "B_defect = lambda (tau^* A_PT + A_PT)",
            "covariant": "conditional",
            "pt_compatible": True,
            "yields_j_defect": True,
            "accepted": False,
            "blocker": "multiplier law constrains parity but does not fix current amplitude",
        },
        {
            "candidate": "gauge_breaking_mass",
            "form": "B_defect = m^2 Tr(A_parallel^2)",
            "covariant": False,
            "pt_compatible": "branch-dependent",
            "yields_j_defect": True,
            "accepted": False,
            "blocker": "breaks solder gauge covariance unless a source-derived gauge fixing exists",
        },
        {
            "candidate": "observable_fit_boundary",
            "form": "B_defect = B[lensing/growth residual]",
            "covariant": False,
            "pt_compatible": False,
            "yields_j_defect": True,
            "accepted": False,
            "blocker": "observational fit is forbidden",
        },
    ]
    admissible = [
        row["candidate"]
        for row in rows
        if row["pt_compatible"] is True and row["covariant"] in {True, "up_to_boundary/gauge", "conditional"}
    ]
    rejected = [row["candidate"] for row in rows if row["candidate"] not in admissible]
    return {
        "description": (
            "Filter for admissible B_defect actions on Sigma_PT. It separates "
            "geometric/topological candidates from gauge-breaking or fitted choices."
        ),
        "status": "orbifold-pt-bdefect-action-filter-underselects",
        "depends_on": ["p0_orbifold_pt_defect_matching_law_gate"],
        "defect_matching_status": matching["status"],
        "rows": rows,
        "admissible_but_unaccepted": admissible,
        "rejected_candidates": rejected,
        "b_defect_forms_written": True,
        "topological_term_candidate_written": True,
        "defect_tension_candidate_written": True,
        "matter_solder_boundary_candidate_written": True,
        "fit_boundary_rejected": True,
        "unique_b_defect_selected": False,
        "b_defect_source_derived": False,
        "j_defect_selected": False,
        "underselection_reason": (
            "PT/covariance filter the form of B_defect, but coefficients, gauge "
            "completion, anomaly cancellation and matter moments remain free."
        ),
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "B_defect has plausible geometric candidates, especially topological "
            "transgression and matter-solder boundary terms. None is accepted yet: "
            "PT/covariance do not fix coefficients or source provenance."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Orbifold/PT B_defect Action Filter",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"B_defect forms written: {payload['b_defect_forms_written']}",
        f"Topological term candidate written: {payload['topological_term_candidate_written']}",
        f"Defect tension candidate written: {payload['defect_tension_candidate_written']}",
        f"Matter solder boundary candidate written: {payload['matter_solder_boundary_candidate_written']}",
        f"Fit boundary rejected: {payload['fit_boundary_rejected']}",
        f"Unique B_defect selected: {payload['unique_b_defect_selected']}",
        f"B_defect source-derived: {payload['b_defect_source_derived']}",
        f"J_defect selected: {payload['j_defect_selected']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| candidate | form | covariant | PT-compatible | yields J_defect | accepted | blocker |",
        "|---|---|---:|---:|---:|---:|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['candidate']} | `{row['form']}` | {row['covariant']} | "
            f"{row['pt_compatible']} | {row['yields_j_defect']} | "
            f"{row['accepted']} | {row['blocker']} |"
        )
    lines.extend(["", f"Underselection: {payload['underselection_reason']}", ""])
    lines.extend([f"Verdict: {payload['verdict']}", ""])
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
