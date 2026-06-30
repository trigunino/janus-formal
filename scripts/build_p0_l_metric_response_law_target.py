from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_l_metric_response_law_target.md")
JSON_PATH = Path("outputs/reports/p0_l_metric_response_law_target.json")


def build_payload() -> dict:
    law_rows = [
        {
            "row": "compatibility_constraint",
            "formula": "L^T g_plus^{-1} L = g_minus^{-1}",
            "status": "constraint",
        },
        {
            "row": "variation_constraint",
            "formula": "(delta L)^T g^{-1} L + L^T delta(g^{-1}) L + L^T g^{-1} delta L = 0",
            "status": "closed-algebraic",
        },
        {
            "row": "symmetric_part",
            "formula": "Sym(L^{-1} delta L) = -1/2 L^{-1} delta(g^{-1}) g L",
            "status": "closed-up-to-index-convention",
        },
        {
            "row": "antisymmetric_part",
            "formula": "Anti(L^{-1} delta L)=Omega, Omega_ab=-Omega_ba",
            "status": "local-lorentz-gauge-open",
        },
        {
            "row": "free_l_rejection",
            "formula": "delta_g L=0 is admissible only if L is independent and compatibility is imposed separately",
            "status": "not-default",
        },
        {
            "row": "k_qcross_guard",
            "formula": "same L response law must be used by K transport and Q_cross optical projection",
            "status": "required",
        },
    ]
    return {
        "description": "Metric-compatible response law target for the solder/tetrad map L.",
        "status": "symmetric-l-response-closed-lorentz-gauge-open",
        "law_rows": law_rows,
        "compatibility_variation_closed": True,
        "symmetric_l_response_closed": True,
        "antisymmetric_lorentz_gauge_closed": False,
        "free_l_branch_rejected_as_default": True,
        "same_l_for_k_qcross_required": True,
        "delta_g_l_closed": False,
        "pulled_m_metric_response_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Metric compatibility fixes only the symmetric part of L^{-1}delta L. "
            "The local Lorentz gauge part remains open and must be shared by K and Q_cross."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 L Metric Response Law Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Compatibility variation closed: {payload['compatibility_variation_closed']}",
        f"Symmetric L response closed: {payload['symmetric_l_response_closed']}",
        f"Antisymmetric Lorentz gauge closed: {payload['antisymmetric_lorentz_gauge_closed']}",
        f"Free L branch rejected as default: {payload['free_l_branch_rejected_as_default']}",
        f"Same L for K/Qcross required: {payload['same_l_for_k_qcross_required']}",
        f"delta_g L closed: {payload['delta_g_l_closed']}",
        f"Pulled M metric response closed: {payload['pulled_m_metric_response_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Law Rows",
        "",
    ]
    for row in payload["law_rows"]:
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
