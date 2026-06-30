from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_dust_pullback_density_response_bridge.md")
JSON_PATH = Path("outputs/reports/p0_dust_pullback_density_response_bridge.json")


def build_payload() -> dict:
    bridge_rows = [
        {
            "row": "field_source_measure",
            "formula": "rho_eff = B_4vol rho_to, B_4vol = phi^*sqrt|g_source| / sqrt|g_receiver|",
            "status": "field-source-anchored",
        },
        {
            "row": "effective_current",
            "formula": "J_eff^mu = rho_eff u_to^mu = B_4vol rho_to u_to^mu",
            "status": "continuity-closed-for-declared-pullback",
        },
        {
            "row": "metric_response_split",
            "formula": "delta_g rho_eff = rho_to delta_g B_4vol + B_4vol delta_g rho_to",
            "status": "closed-chain-rule",
        },
        {
            "row": "receiver_measure_part",
            "formula": "delta_g log B_4vol|receiver = - delta_g log sqrt|g_receiver|",
            "status": "closed-algebraic",
        },
        {
            "row": "source_pullback_part",
            "formula": "delta_g(phi^*sqrt|g_source|) and delta_g rho_to require phi/source metric variation convention",
            "status": "open-action-required",
        },
        {
            "row": "no_double_counting",
            "formula": "if rho_eff already includes B_4vol, do not multiply Q_det/B_4vol again in K",
            "status": "required",
        },
    ]
    return {
        "description": "Bridge from pulled dust continuity to density metric response bookkeeping.",
        "status": "pullback-density-response-bridge-open",
        "bridge_rows": bridge_rows,
        "field_source_measure_anchored": True,
        "effective_current_continuity_closed": True,
        "density_response_chain_rule_closed": True,
        "receiver_measure_response_closed": True,
        "source_pullback_metric_response_closed": False,
        "source_pullback_metric_response_target_available": True,
        "no_double_counting_rule_closed": True,
        "full_pullback_density_response_closed": False,
        "full_dust_delta_g_t_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The B_4vol bookkeeping bridge is explicit. Full delta_g rho_eff still needs "
            "the source/pullback metric response of phi and source dust."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Dust Pullback Density Response Bridge",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Field source measure anchored: {payload['field_source_measure_anchored']}",
        f"Effective current continuity closed: {payload['effective_current_continuity_closed']}",
        f"Density response chain rule closed: {payload['density_response_chain_rule_closed']}",
        f"Receiver measure response closed: {payload['receiver_measure_response_closed']}",
        f"Source pullback metric response closed: {payload['source_pullback_metric_response_closed']}",
        f"Source pullback metric response target available: {payload['source_pullback_metric_response_target_available']}",
        f"No double-counting rule closed: {payload['no_double_counting_rule_closed']}",
        f"Full pullback density response closed: {payload['full_pullback_density_response_closed']}",
        f"Full dust delta_g T closed: {payload['full_dust_delta_g_t_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Bridge Rows",
        "",
    ]
    for row in payload["bridge_rows"]:
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
