from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_dust_fixed_pullback_delta_t_branch.md")
JSON_PATH = Path("outputs/reports/p0_dust_fixed_pullback_delta_t_branch.json")


def build_payload() -> dict:
    branch_rows = [
        {
            "row": "branch_assumptions",
            "formula": "phi, source metric, source dust fields fixed; rho_eff=B_4vol rho_to",
            "status": "conditional",
        },
        {
            "row": "density_response",
            "formula": "delta_g rho_eff = -1/2 rho_eff g^{alpha beta} delta g_{alpha beta}",
            "status": "closed-under-branch",
        },
        {
            "row": "normalized_transport_velocity",
            "formula": "u^mu = v_to^mu / sqrt(-g_{alpha beta} v_to^alpha v_to^beta), delta_g v_to^mu=0",
            "status": "conditional",
        },
        {
            "row": "velocity_response",
            "formula": "delta_g u^mu = 1/2 u^mu u^alpha u^beta delta g_{alpha beta}",
            "status": "closed-under-branch",
        },
        {
            "row": "dust_stress_response",
            "formula": "delta_g T^{mu nu}=rho_eff u^mu u^nu (u^alpha u^beta - 1/2 g^{alpha beta}) delta g_{alpha beta}",
            "status": "closed-under-branch",
        },
        {
            "row": "action_warning",
            "formula": "if phi/source fields vary with g, add E_phi/source-action terms before using in Janus K",
            "status": "open-action-required",
        },
    ]
    return {
        "description": "Conditional fixed-pullback branch for receiver-side dust delta_g T.",
        "status": "conditional-dust-delta-t-closed-action-open",
        "branch_rows": branch_rows,
        "fixed_phi_source_branch_closed": True,
        "density_response_closed_under_branch": True,
        "velocity_response_closed_under_branch": True,
        "dust_delta_g_t_closed_under_branch": True,
        "janus_action_delta_g_t_closed": False,
        "full_k_variation_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "A receiver-side delta_g T formula is closed only under fixed phi/source "
            "and normalized transported velocity. It is not yet the full Janus action variation."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Dust Fixed Pullback Delta T Branch",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Fixed phi/source branch closed: {payload['fixed_phi_source_branch_closed']}",
        f"Density response closed under branch: {payload['density_response_closed_under_branch']}",
        f"Velocity response closed under branch: {payload['velocity_response_closed_under_branch']}",
        f"Dust delta_g T closed under branch: {payload['dust_delta_g_t_closed_under_branch']}",
        f"Janus action delta_g T closed: {payload['janus_action_delta_g_t_closed']}",
        f"Full K variation closed: {payload['full_k_variation_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Branch Rows",
        "",
    ]
    for row in payload["branch_rows"]:
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
