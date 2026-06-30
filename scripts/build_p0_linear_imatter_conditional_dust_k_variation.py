from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_linear_imatter_conditional_dust_k_variation.md")
JSON_PATH = Path("outputs/reports/p0_linear_imatter_conditional_dust_k_variation.json")


def build_payload() -> dict:
    k_rows = [
        {
            "row": "contract",
            "formula": "I = T_plus^{mu nu} M_minus_to_plus_{mu nu}",
            "status": "defined",
        },
        {
            "row": "measure_piece",
            "formula": "delta sqrt(-g_plus) gives -1/2 g_plus^{alpha beta} I delta g_plus_{alpha beta}",
            "status": "closed-algebraic",
        },
        {
            "row": "dust_tplus_piece",
            "formula": "M_{mu nu} delta_g T_plus^{mu nu} with conditional dust delta_g T_plus",
            "status": "closed-under-fixed-pullback-dust",
        },
        {
            "row": "pulled_dust_piece",
            "formula": "T_plus^{mu nu} delta_g M_minus_to_plus_{mu nu}",
            "status": "open-requires-delta-g-L-and-minus-pullback",
        },
        {
            "row": "available_k_kernel",
            "formula": "K_kernel^{alpha beta}|available = -1/2 g^{alpha beta} I + M_{mu nu} rho_plus u_plus^mu u_plus^nu (u_plus^alpha u_plus^beta - 1/2 g^{alpha beta})",
            "status": "conditional-partial",
        },
        {
            "row": "rejection",
            "formula": "available K kernel is not full K_plus until delta_g M and mirror variation are closed",
            "status": "required",
        },
    ]
    return {
        "description": "Conditional dust K-variation pieces for the linear I_matter candidate.",
        "status": "conditional-dust-k-kernel-partial",
        "k_rows": k_rows,
        "measure_piece_closed": True,
        "same_sector_dust_piece_closed_under_branch": True,
        "pulled_m_piece_closed": False,
        "pulled_m_metric_response_target_available": True,
        "delta_g_l_closed": False,
        "mirror_minus_variation_closed": False,
        "available_k_kernel_partial": True,
        "full_k_plus_closed": False,
        "full_k_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The plus same-sector dust contribution is computable under fixed-pullback "
            "assumptions, but the full K tensor still requires delta_g L, pulled M response, and mirror closure."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Linear I_matter Conditional Dust K Variation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Measure piece closed: {payload['measure_piece_closed']}",
        f"Same-sector dust piece closed under branch: {payload['same_sector_dust_piece_closed_under_branch']}",
        f"Pulled M piece closed: {payload['pulled_m_piece_closed']}",
        f"Pulled M metric response target available: {payload['pulled_m_metric_response_target_available']}",
        f"delta_g L closed: {payload['delta_g_l_closed']}",
        f"Mirror minus variation closed: {payload['mirror_minus_variation_closed']}",
        f"Available K kernel partial: {payload['available_k_kernel_partial']}",
        f"Full K_plus closed: {payload['full_k_plus_closed']}",
        f"Full K_minus closed: {payload['full_k_minus_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## K Rows",
        "",
    ]
    for row in payload["k_rows"]:
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
