from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_spath_cj_vj_nonlinear_local_no_go import (
    build_payload as build_nonlinear_no_go,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_spath_constraint_equation_classifier.md")
JSON_PATH = Path("outputs/reports/p0_route_c_spath_constraint_equation_classifier.json")


def build_payload() -> dict:
    nonlinear = build_nonlinear_no_go()
    classifier_rows = [
        {
            "constraint": "PT_parity",
            "class": "filter",
            "selects_unique": False,
            "why": "keeps parity-compatible branches but leaves arbitrary even functions",
        },
        {
            "constraint": "same_L",
            "class": "consistency_filter",
            "selects_unique": False,
            "why": "forces common bridge usage but not the bridge dynamics or F_C/F_V",
        },
        {
            "constraint": "stability",
            "class": "inequality_filter",
            "selects_unique": False,
            "why": "defines an allowed open region in jets, not a single solution",
        },
        {
            "constraint": "weak_field_sign",
            "class": "branch_filter",
            "selects_unique": False,
            "why": "rejects wrong-sign branches without fixing amplitudes",
        },
        {
            "constraint": "source_action_EL",
            "class": "missing_equation",
            "selects_unique": False,
            "why": "would be the required selector but is not derived",
        },
    ]
    return {
        "description": (
            "Classifier for whether PT, same-L, stability and related constraints "
            "are actual selection equations or only filters."
        ),
        "status": "spath-constraint-equation-classifier-open",
        "depends_on": ["p0_route_c_spath_cj_vj_nonlinear_local_no_go"],
        "nonlinear_no_go_status": nonlinear["status"],
        "classifier_rows": classifier_rows,
        "pt_is_equation": False,
        "same_l_is_equation": False,
        "stability_is_equation": False,
        "weak_field_sign_is_equation": False,
        "source_action_el_available": False,
        "all_available_constraints_are_filters": True,
        "unique_selector_available": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Available PT/same-L/stability/weak-field constraints are filters. "
            "The missing object is still a source/action Euler equation that fixes "
            "path law and C_J/V_J functional dependence."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C S_path Constraint Equation Classifier",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"PT is equation: {payload['pt_is_equation']}",
        f"Same-L is equation: {payload['same_l_is_equation']}",
        f"Stability is equation: {payload['stability_is_equation']}",
        f"Weak-field sign is equation: {payload['weak_field_sign_is_equation']}",
        f"Source/action EL available: {payload['source_action_el_available']}",
        f"All available constraints are filters: {payload['all_available_constraints_are_filters']}",
        f"Unique selector available: {payload['unique_selector_available']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| constraint | class | selects unique | why |",
        "|---|---|---:|---|",
    ]
    for row in payload["classifier_rows"]:
        lines.append(
            f"| {row['constraint']} | {row['class']} | "
            f"{row['selects_unique']} | {row['why']} |"
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
