from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_linear_imatter_metric_variation.md")
JSON_PATH = Path("outputs/reports/p0_linear_imatter_metric_variation.json")


def build_payload() -> dict:
    variation_rows = [
        {
            "row": "plus_contract",
            "formula": "I = T_plus^{mu nu} M_minus_to_plus_{mu nu}, M_minus_to_plus = (L T_minus L^T)",
            "status": "defined",
        },
        {
            "row": "measure_variation",
            "formula": "delta sqrt(-g_plus) = -1/2 sqrt(-g_plus) g_plus_{mu nu} delta g_plus^{mu nu}",
            "status": "closed-algebraic",
        },
        {
            "row": "frozen_matter_trace",
            "formula": "delta(S_couple)|frozen = integral sqrt(-g_plus) [-1/2 g_plus_{mu nu} Phi] delta g_plus^{mu nu}",
            "status": "diagnostic-only",
        },
        {
            "row": "full_k_plus",
            "formula": "K_plus requires delta_g T_plus, delta_g L, and any metric dependence in pulled T_minus",
            "status": "open",
        },
        {
            "row": "full_k_minus",
            "formula": "K_minus requires the mirror metric response and inverse pullback convention",
            "status": "open",
        },
    ]
    return {
        "description": "Metric variation boundary for the linear I_matter candidate.",
        "status": "measure-variation-closed-full-k-open",
        "variation_rows": variation_rows,
        "measure_variation_closed": True,
        "partial_metric_variation_available": True,
        "frozen_matter_trace_is_full_k": False,
        "requires_stress_response": True,
        "requires_l_metric_dependence": True,
        "requires_pullback_metric_dependence": True,
        "stress_response_target_available": True,
        "conditional_dust_k_variation_available": True,
        "full_metric_variation_closed": False,
        "k_plus_k_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Only the volume-measure trace is closed. It cannot be used as K_plus/K_minus "
            "because the full metric response of T, L, and pullback data is still required."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Linear I_matter Metric Variation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Measure variation closed: {payload['measure_variation_closed']}",
        f"Partial metric variation available: {payload['partial_metric_variation_available']}",
        f"Frozen matter trace is full K: {payload['frozen_matter_trace_is_full_k']}",
        f"Full metric variation closed: {payload['full_metric_variation_closed']}",
        f"Stress response target available: {payload['stress_response_target_available']}",
        f"Conditional dust K variation available: {payload['conditional_dust_k_variation_available']}",
        f"K_plus/K_minus closed: {payload['k_plus_k_minus_closed']}",
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
