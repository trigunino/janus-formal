from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_spath_cj_vj_invariant_filter import (
    build_payload as build_invariant_filter,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_spath_cj_vj_coefficient_underselection_gate.md")
JSON_PATH = Path("outputs/reports/p0_route_c_spath_cj_vj_coefficient_underselection_gate.json")


def build_payload() -> dict:
    invariant_filter = build_invariant_filter()
    invariant_count = int(invariant_filter["admissible_invariant_count"])
    linear_free_lower_bound = 1 + 2 * invariant_count
    constraint_rows = [
        {
            "constraint": "no_observational_fit",
            "effect": "removes observable_residual from basis",
            "fixes_coefficients": False,
            "reason": "rejects a family, does not determine remaining c_i or v_i",
        },
        {
            "constraint": "PT_mirror_parity",
            "effect": "keeps only PT-compatible invariants or pairs mirror coefficients",
            "fixes_coefficients": False,
            "reason": "surviving coefficients can still be rescaled together",
        },
        {
            "constraint": "same_l_compatibility",
            "effect": "requires all L-dependent invariants use the same bridge",
            "fixes_coefficients": False,
            "reason": "same-L is a consistency rule, not a numeric source equation",
        },
        {
            "constraint": "stability_signs",
            "effect": "requires C_0>0 and V_2>=0 on chosen branch",
            "fixes_coefficients": False,
            "reason": "inequalities bound signs/regions but do not select a unique function",
        },
        {
            "constraint": "weak_field_sign",
            "effect": "may reject wrong-sign branches",
            "fixes_coefficients": False,
            "reason": "sign anchoring is not an amplitude or nonlinear coefficient derivation",
        },
        {
            "constraint": "source_provenance",
            "effect": "would need Janus equations/action to provide coefficient equations",
            "fixes_coefficients": False,
            "reason": "no such source equation is available in the current chain",
        },
    ]
    return {
        "description": (
            "Coefficient underselection gate for C_J/V_J after the invariant filter. "
            "It distinguishes compatibility constraints from source equations."
        ),
        "status": "spath-cj-vj-coefficient-underselection-open",
        "depends_on": ["p0_route_c_spath_cj_vj_invariant_filter"],
        "admissible_invariant_count": invariant_count,
        "linear_family": "C_J=c0+sum_i c_i I_i; V_J=sum_i v_i I_i",
        "linear_family_free_coefficients_lower_bound": linear_free_lower_bound,
        "constraint_rows": constraint_rows,
        "compatibility_constraints_written": True,
        "coefficient_selection_equations_available": False,
        "all_constraints_are_filters_not_selectors": True,
        "unique_coefficient_solution_found": False,
        "stability_inequalities_replace_source_equations": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The admissible invariant basis still leaves at least the linear "
            "C_J/V_J coefficients free. PT, same-L, no-fit, weak-field signs and "
            "stability act as filters; they do not replace a Janus source equation."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C S_path C_J/V_J Coefficient Underselection Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Admissible invariant count: {payload['admissible_invariant_count']}",
        f"Linear family: `{payload['linear_family']}`",
        (
            "Linear family free coefficients lower bound: "
            f"{payload['linear_family_free_coefficients_lower_bound']}"
        ),
        f"Compatibility constraints written: {payload['compatibility_constraints_written']}",
        (
            "Coefficient selection equations available: "
            f"{payload['coefficient_selection_equations_available']}"
        ),
        f"All constraints are filters not selectors: {payload['all_constraints_are_filters_not_selectors']}",
        f"Unique coefficient solution found: {payload['unique_coefficient_solution_found']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| constraint | effect | fixes coefficients | reason |",
        "|---|---|---:|---|",
    ]
    for row in payload["constraint_rows"]:
        lines.append(
            f"| {row['constraint']} | {row['effect']} | "
            f"{row['fixes_coefficients']} | {row['reason']} |"
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
