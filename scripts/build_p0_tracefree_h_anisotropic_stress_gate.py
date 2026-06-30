from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_anisotropic_stress_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_anisotropic_stress_gate.json")


def build_payload() -> dict:
    spacetime_dimension = 4
    spatial_dimension = spacetime_dimension - 1
    spatial_stf_rank = spatial_dimension * (spatial_dimension + 1) // 2 - 1
    h_tf_rank = spacetime_dimension * (spacetime_dimension + 1) // 2 - 1
    rows = [
        {
            "object": "projector",
            "formula": "h^{mu}_{alpha}=delta^{mu}_{alpha}+u^{mu}u_{alpha}",
            "role": "chooses spatial rest frame relative to u",
            "closes_qtf": False,
        },
        {
            "object": "pressure",
            "formula": "p=(1/3)h_{alpha beta}T^{alpha beta}",
            "role": "isotropic scalar trace",
            "closes_qtf": False,
        },
        {
            "object": "anisotropic_stress",
            "formula": "Pi^{mu nu}=(h^{mu}_{alpha}h^{nu}_{beta}-(1/3)h^{mu nu}h_{alpha beta})T^{alpha beta}",
            "role": "spatial symmetric trace-free tensor",
            "closes_qtf": "partial",
        },
        {
            "object": "dust_or_perfect_fluid",
            "formula": "Pi^{mu nu}=0",
            "role": "does not source trace-free strain",
            "closes_qtf": False,
        },
    ]
    return {
        "description": "Bounded P0 gate for anisotropic stress as a trace-free H/Q_TF source candidate.",
        "status": "tracefree-h-anisotropic-stress-gate-open",
        "dimension": spacetime_dimension,
        "rank_counts": {
            "spatial_stf_pi_rank_after_u_choice": spatial_stf_rank,
            "full_4d_h_tracefree_rank": h_tf_rank,
            "unselected_4d_components_if_only_pi_spatial": h_tf_rank - spatial_stf_rank,
        },
        "rows": rows,
        "pi_tf_defined": True,
        "pi_tf_requires_congruence_u": True,
        "pi_tf_selects_full_h_tf": False,
        "dust_or_perfect_fluid_closes_qtf": False,
        "needs_janus_source_action": True,
        "needs_same_l_transport": True,
        "accepted_as_prediction_input": False,
        "prediction_ready": False,
        "guardrails": [
            "do not replace 4D H_TF by spatial Pi_TF without a source-derived u and gauge branch",
            "do not use dust or perfect fluid pressure as Q_TF source",
            "do not fit Pi_TF to cancel residuals",
        ],
        "verdict": (
            "Pi_TF is a legitimate tensor candidate, but by itself it is only a "
            "spatial trace-free source after choosing u. It cannot close the full "
            "4D H_TF/Q_TF branch unless Janus derives the congruence, same-L "
            "transport and source equation."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Anisotropic Stress Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Dimension: {payload['dimension']}",
        f"Pi_TF defined: {payload['pi_tf_defined']}",
        f"Pi_TF requires congruence u: {payload['pi_tf_requires_congruence_u']}",
        f"Pi_TF selects full H_TF: {payload['pi_tf_selects_full_h_tf']}",
        f"Dust/perfect fluid closes Q_TF: {payload['dust_or_perfect_fluid_closes_qtf']}",
        f"Needs Janus source/action: {payload['needs_janus_source_action']}",
        f"Needs same-L transport: {payload['needs_same_l_transport']}",
        f"Accepted as prediction input: {payload['accepted_as_prediction_input']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Rank Counts",
        "",
    ]
    for key, value in payload["rank_counts"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Tensor Pieces", "", "| object | formula | role | closes Q_TF |", "|---|---|---|---:|"])
    for row in payload["rows"]:
        lines.append(f"| {row['object']} | `{row['formula']}` | {row['role']} | {row['closes_qtf']} |")
    lines.extend(["", "## Guardrails", ""])
    lines.extend(f"- {item}" for item in payload["guardrails"])
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
