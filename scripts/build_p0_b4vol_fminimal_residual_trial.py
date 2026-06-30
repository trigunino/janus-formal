from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_b4vol_fminimal_residual_trial.md")
JSON_PATH = Path("outputs/reports/p0_b4vol_fminimal_residual_trial.json")


def build_payload() -> dict:
    trial_inputs = [
        "B/J_phi/Q_det branch: field_equation_4volume_source",
        "F_alpha branch: minimal gauge with flow projections fixed",
        "same L for K_plus/K_minus and Q_cross required",
        "dust-only; pressure/Pi excluded from this trial",
    ]
    residual_rows = [
        {
            "term": "D_phi density + D log B_4vol",
            "trial_result": "absorbed into D_receiver(B_4vol rho_to u_to)",
            "status": "conditional",
        },
        {
            "term": "D_L velocity/tetrad flow projection",
            "trial_result": "cancelled by flow-projected F_alpha equations",
            "status": "conditional",
        },
        {
            "term": "transverse/off-flow F_alpha",
            "trial_result": "zero in minimal gauge unless Janus source geometry activates it",
            "status": "gauge-conditional",
        },
        {
            "term": "C_self-other u_to u_to",
            "trial_result": "must be supplied by projected EL force balance rho h Cuu",
            "status": "open",
        },
        {
            "term": "mirror plus/minus inverse consistency",
            "trial_result": "must follow from one phi/L inverse pair",
            "status": "open",
        },
    ]
    blockers = [
        "D_receiver(B_4vol rho_to u_to)=0 is not source-proved",
        "minimal-gauge F_alpha is not source-derived",
        "projected EL force balance hE=rho hCuu is not derived",
        "pressure/Pi extension is outside dust trial",
        "full R_plus/R_minus closure remains false",
    ]
    return {
        "description": "Residual trial substituting B_4vol branch and minimal-gauge F_alpha.",
        "status": "conditional-trial-open",
        "trial_inputs": trial_inputs,
        "residual_rows": residual_rows,
        "blockers": blockers,
        "b4vol_branch_selected_for_trial": True,
        "fminimal_branch_selected_for_trial": True,
        "dust_trial_reduced": True,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The trial reduces the dust residual to effective-density continuity, "
            "minimal-gauge F consistency, projected Cuu force balance, and mirror consistency. "
            "It is not a closure proof."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 B4vol + Fminimal Residual Trial",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"B4vol branch selected for trial: {payload['b4vol_branch_selected_for_trial']}",
        f"Fminimal branch selected for trial: {payload['fminimal_branch_selected_for_trial']}",
        f"Dust trial reduced: {payload['dust_trial_reduced']}",
        f"R plus closed: {payload['r_plus_closed']}",
        f"R minus closed: {payload['r_minus_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Trial Inputs",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["trial_inputs"])
    lines.extend(["", "## Residual Rows", ""])
    for row in payload["residual_rows"]:
        lines.append(f"- {row['term']}: {row['trial_result']} (status={row['status']})")
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
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
