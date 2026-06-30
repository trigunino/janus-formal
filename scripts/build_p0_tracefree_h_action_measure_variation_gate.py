from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_density_measure_closure_condition import (
    build_payload as build_density_measure_closure,
)
from scripts.build_p0_source_measure_selection_rules import (
    build_payload as build_source_measure_selection,
)


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_action_measure_variation_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_action_measure_variation_gate.json")


def build_payload() -> dict:
    density_measure = build_density_measure_closure()
    source_measure = build_source_measure_selection()
    measure_terms = [
        {
            "term": "fixed_measure",
            "variation": "delta_mu = 0",
            "allowed_if": "measure is fixed by gauge before varying H",
            "accepted": False,
        },
        {
            "term": "metric_volume_measure",
            "variation": "delta sqrt(|H|) = 1/2 sqrt(|H|) Tr(H^-1 deltaH)",
            "allowed_if": "the H action measure is the selected metric volume",
            "accepted": False,
        },
        {
            "term": "b4vol_source_measure",
            "variation": "delta_mu/mu = delta log B4vol + selected slice/lapse/J terms",
            "allowed_if": "B4vol/J/lapse branch is source-selected",
            "accepted": False,
        },
        {
            "term": "effective_absorbed_measure",
            "variation": "delta_mu already absorbed in declared rho_eff/X_TF convention",
            "allowed_if": "absorbed measure is declared and no later Q_det multiplication occurs",
            "accepted": False,
        },
    ]
    forbidden_routes = [
        "drop delta_mu without a fixed-measure proof",
        "promote determinant trace from delta_mu to trace-free S_TF",
        "mix B4vol and dust 3-volume measures in one action branch",
        "hide source selection by absorbing delta_mu into X_TF without declaration",
    ]
    return {
        "description": "Bounded P0 gate for action-measure variation terms in H_TF/Q_TF actions.",
        "status": "tracefree-h-action-measure-variation-gate-open",
        "target_channel": "H_TF/Q_TF",
        "measure_variation_closed": False,
        "fixed_measure_branch_proved": False,
        "source_measure_convention_fixed": bool(density_measure["source_convention_fixed"]),
        "source_measure_rule_accepted": source_measure["accepted_rule"],
        "delta_mu_terms_required": True,
        "delta_mu_can_source_stf": False,
        "measure_terms": measure_terms,
        "measure_terms_total": len(measure_terms),
        "measure_terms_accepted": sum(1 for row in measure_terms if row["accepted"]),
        "forbidden_routes": forbidden_routes,
        "prediction": False,
        "prediction_ready": False,
        "verdict": (
            "Action measure variation is an explicit open term. It can affect the "
            "trace equation and coefficients, but it cannot be promoted to a "
            "trace-free source without an independent STF tensor source."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Action Measure Variation Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Target channel: {payload['target_channel']}",
        f"Measure variation closed: {payload['measure_variation_closed']}",
        f"Fixed measure branch proved: {payload['fixed_measure_branch_proved']}",
        f"Source measure convention fixed: {payload['source_measure_convention_fixed']}",
        f"Source measure rule accepted: {payload['source_measure_rule_accepted']}",
        f"Delta_mu terms required: {payload['delta_mu_terms_required']}",
        f"Delta_mu can source STF: {payload['delta_mu_can_source_stf']}",
        f"Measure terms accepted: {payload['measure_terms_accepted']}/{payload['measure_terms_total']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Measure Terms",
        "",
        "| term | variation | allowed if | accepted |",
        "|---|---|---|---:|",
    ]
    for row in payload["measure_terms"]:
        lines.append(
            f"| {row['term']} | `{row['variation']}` | {row['allowed_if']} | {row['accepted']} |"
        )
    lines.extend(["", "## Forbidden Routes", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_routes"])
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
