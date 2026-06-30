from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_source_pullback_metric_response_target.md")
JSON_PATH = Path("outputs/reports/p0_source_pullback_metric_response_target.json")


def build_payload() -> dict:
    variation_rows = [
        {
            "row": "receiver_metric_variation_fixed_phi_source",
            "formula": "delta_{g_receiver} phi^*sqrt|g_source| = 0",
            "status": "closed-under-fixed-phi-source",
        },
        {
            "row": "receiver_b4vol_response",
            "formula": "delta_{g_receiver} log B_4vol = -1/2 g_receiver^{mu nu} delta g_receiver_{mu nu}",
            "status": "closed-algebraic",
        },
        {
            "row": "source_metric_variation",
            "formula": "delta_{g_source} log phi^*sqrt|g_source| = 1/2 phi^*(g_source^{ab} delta g_source_{ab})",
            "status": "closed-algebraic-separate-variation",
        },
        {
            "row": "phi_variation",
            "formula": "delta_phi(phi^*sqrt|g_source|) = Lie_{delta phi} phi^*sqrt|g_source|",
            "status": "map-equation-not-metric-k",
        },
        {
            "row": "rho_to_variation",
            "formula": "delta_{g_receiver} rho_to = 0 if source fields and phi are fixed",
            "status": "closed-branch-assumption",
        },
        {
            "row": "pulled_action_warning",
            "formula": "if phi or source fields vary with g_receiver, extra action-dependent terms appear",
            "status": "open-action-required",
        },
    ]
    return {
        "description": "Source-pullback metric response split for B_4vol density bookkeeping.",
        "status": "receiver-metric-branch-closed-action-bridge-open",
        "variation_rows": variation_rows,
        "receiver_metric_fixed_phi_source_branch_closed": True,
        "receiver_b4vol_response_closed": True,
        "source_metric_response_separate_closed": True,
        "phi_variation_separated_from_metric_k": True,
        "rho_to_fixed_source_branch_closed": True,
        "pulled_action_bridge_closed": False,
        "full_pullback_density_response_closed": False,
        "full_dust_delta_g_t_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "For receiver metric variation at fixed phi and fixed source fields, the "
            "B_4vol response is closed. A full pulled-action variation remains open "
            "because phi/source-field dependence may add terms."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Source Pullback Metric Response Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Receiver metric fixed-phi/source branch closed: {payload['receiver_metric_fixed_phi_source_branch_closed']}",
        f"Receiver B_4vol response closed: {payload['receiver_b4vol_response_closed']}",
        f"Source metric response separate closed: {payload['source_metric_response_separate_closed']}",
        f"Phi variation separated from metric K: {payload['phi_variation_separated_from_metric_k']}",
        f"rho_to fixed-source branch closed: {payload['rho_to_fixed_source_branch_closed']}",
        f"Pulled action bridge closed: {payload['pulled_action_bridge_closed']}",
        f"Full pullback density response closed: {payload['full_pullback_density_response_closed']}",
        f"Full dust delta_g T closed: {payload['full_dust_delta_g_t_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Variation Rows",
        "",
    ]
    for row in payload["variation_rows"]:
        lines.append(f"- {row['row']}: `{row['formula']}` ({row['status']})")
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
