from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_pulled_m_metric_response_target.md")
JSON_PATH = Path("outputs/reports/p0_pulled_m_metric_response_target.json")


def build_payload() -> dict:
    response_rows = [
        {
            "row": "definition",
            "formula": "M_{mu nu}=L_mu^a T_minus_ab L_nu^b",
            "status": "defined",
        },
        {
            "row": "chain_rule",
            "formula": "delta_g M_{mu nu}=(delta_g L_mu^a)T_ab L_nu^b + L_mu^a(delta_g T_ab)L_nu^b + L_mu^a T_ab(delta_g L_nu^b)",
            "status": "closed-algebraic",
        },
        {
            "row": "fixed_minus_source_branch",
            "formula": "delta_{g_plus} T_minus_ab=0 when minus source fields/metric and phi are fixed",
            "status": "conditional-closed",
        },
        {
            "row": "solder_metric_response",
            "formula": "delta_{g_plus} L_mu^a must preserve L^T g_plus^{-1} L = g_minus^{-1} or chosen tetrad convention",
            "status": "open-compatibility-law-required",
        },
        {
            "row": "free_l_branch",
            "formula": "if L is independent auxiliary field, delta_{g_plus} L=0 but Lorentz/tetrad compatibility is not automatic",
            "status": "conditional-not-source-derived",
        },
        {
            "row": "metric_compatible_l_branch",
            "formula": "if L is built from tetrads, delta_g L follows tetrad variation plus local Lorentz gauge",
            "status": "open-gauge-law-required",
        },
    ]
    return {
        "description": "Metric response target for M_minus_to_plus = L T_minus L^T.",
        "status": "pulled-m-chain-rule-closed-l-law-open",
        "response_rows": response_rows,
        "m_chain_rule_closed": True,
        "fixed_minus_source_branch_closed": True,
        "free_l_branch_available": True,
        "metric_compatible_l_branch_available": True,
        "l_metric_response_law_target_available": True,
        "pulled_m_symmetric_l_substitution_available": True,
        "solder_metric_response_closed": False,
        "pulled_m_metric_response_closed": False,
        "full_k_plus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "delta_g M is reduced to delta_g L plus optional minus-source response. "
            "The remaining blocker is the admissible metric response law for L."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Pulled M Metric Response Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"M chain rule closed: {payload['m_chain_rule_closed']}",
        f"Fixed minus source branch closed: {payload['fixed_minus_source_branch_closed']}",
        f"Free L branch available: {payload['free_l_branch_available']}",
        f"Metric-compatible L branch available: {payload['metric_compatible_l_branch_available']}",
        f"L metric response law target available: {payload['l_metric_response_law_target_available']}",
        f"Pulled M symmetric L substitution available: {payload['pulled_m_symmetric_l_substitution_available']}",
        f"Solder metric response closed: {payload['solder_metric_response_closed']}",
        f"Pulled M metric response closed: {payload['pulled_m_metric_response_closed']}",
        f"Full K_plus closed: {payload['full_k_plus_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Response Rows",
        "",
    ]
    for row in payload["response_rows"]:
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
