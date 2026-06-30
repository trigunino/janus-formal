from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_orbifold_pt_topological_defect_branch_gate import (
    build_payload as build_topological_branch,
)


REPORT_PATH = Path("outputs/reports/p0_orbifold_pt_ktop_quantization_gate.md")
JSON_PATH = Path("outputs/reports/p0_orbifold_pt_ktop_quantization_gate.json")


def build_payload() -> dict:
    branch = build_topological_branch()
    rows = [
        {
            "mechanism": "large_gauge_invariance",
            "condition": "exp(i S_top) invariant under large solder-gauge transformations",
            "effect": "k_top lies in a discrete lattice",
            "fixes_unique_value": False,
            "blocker": "requires exact gauge group, normalization and defect dimension",
        },
        {
            "mechanism": "pt_orientation_parity",
            "condition": "B_top[tau^*A] = +/- B_top[A]",
            "effect": "can eliminate parity-wrong levels or signs",
            "fixes_unique_value": False,
            "blocker": "parity is a sign/branch constraint, not a level selector",
        },
        {
            "mechanism": "anomaly_inflow",
            "condition": "defect anomaly + bulk inflow = 0",
            "effect": "could fix k_top if defect anomaly polynomial is known",
            "fixes_unique_value": "conditional",
            "blocker": "no Janus defect degrees of freedom/anomaly polynomial derived",
        },
        {
            "mechanism": "minimal_integer_level",
            "condition": "choose smallest nonzero allowed k_top",
            "effect": "selects a value by minimality",
            "fixes_unique_value": False,
            "blocker": "minimality is a new axiom unless forced by source/anomaly",
        },
        {
            "mechanism": "janus_source_normalization",
            "condition": "match coefficient to published Janus field-equation source normalization",
            "effect": "would fix k_top physically",
            "fixes_unique_value": "not-available",
            "blocker": "no source equation currently ties Janus coupling to B_top",
        },
    ]
    return {
        "description": (
            "Quantization/anomaly gate for the topological defect coefficient k_top."
        ),
        "status": "orbifold-pt-ktop-quantization-gate-open",
        "depends_on": ["p0_orbifold_pt_topological_defect_branch_gate"],
        "topological_branch_status": branch["status"],
        "rows": rows,
        "k_top_quantization_condition_written": True,
        "large_gauge_can_discretize": True,
        "pt_can_filter_sign_or_parity": True,
        "anomaly_inflow_could_fix_if_anomaly_known": True,
        "defect_anomaly_polynomial_known": False,
        "gauge_group_normalization_fixed": False,
        "defect_dimension_degree_fixed": False,
        "janus_source_normalization_found": False,
        "minimal_level_choice_allowed_without_axiom": False,
        "k_top_unique_value_fixed": False,
        "k_top_source_derived": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Large-gauge/topological consistency can at best discretize k_top. "
            "A unique value would require a defect anomaly polynomial or Janus "
            "source normalization. Choosing the smallest level would be an extra axiom."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Orbifold/PT k_top Quantization Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"k_top quantization condition written: {payload['k_top_quantization_condition_written']}",
        f"Large gauge can discretize: {payload['large_gauge_can_discretize']}",
        f"PT can filter sign/parity: {payload['pt_can_filter_sign_or_parity']}",
        f"Anomaly inflow could fix if anomaly known: {payload['anomaly_inflow_could_fix_if_anomaly_known']}",
        f"Defect anomaly polynomial known: {payload['defect_anomaly_polynomial_known']}",
        f"Gauge group normalization fixed: {payload['gauge_group_normalization_fixed']}",
        f"Defect dimension degree fixed: {payload['defect_dimension_degree_fixed']}",
        f"Janus source normalization found: {payload['janus_source_normalization_found']}",
        f"Minimal level choice allowed without axiom: {payload['minimal_level_choice_allowed_without_axiom']}",
        f"k_top unique value fixed: {payload['k_top_unique_value_fixed']}",
        f"k_top source-derived: {payload['k_top_source_derived']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| mechanism | condition | effect | fixes unique value | blocker |",
        "|---|---|---|---:|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['mechanism']} | {row['condition']} | {row['effect']} | "
            f"{row['fixes_unique_value']} | {row['blocker']} |"
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
