from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_weyl_shear_source_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_weyl_shear_source_gate.json")


def build_payload() -> dict:
    diagnostics = [
        {
            "name": "electric_weyl_E_mu_nu",
            "object": "E_{mu nu}=C_{mu alpha nu beta} u^alpha u^beta",
            "trace_free": True,
            "data_role": "tidal trace-free tensor; constrains projections/orientation",
            "selects_full_h_tf_q_tf": False,
            "blocker": "needs Janus source/field equation tying E_{mu nu} to H_TF/Q_TF",
        },
        {
            "name": "congruence_shear_sigma_mu_nu",
            "object": "sigma_{mu nu}=D_{(mu}u_{nu)}-(theta/3)h_{mu nu}",
            "trace_free": True,
            "data_role": "kinematic trace-free shear; constrains flow frame/orientation",
            "selects_full_h_tf_q_tf": False,
            "blocker": "needs gauge and boundary branch before it can source H_TF/Q_TF",
        },
        {
            "name": "optical_screen_shear",
            "object": "gamma_AB / sigma_AB on the lensing screen",
            "trace_free": True,
            "projected_dimension": 2,
            "data_role": "2D projected screen observable",
            "selects_full_h_tf_q_tf": False,
            "blocker": "screen lensing is projected data, not a 4D Janus source law",
        },
    ]
    rejected_routes = [
        {
            "route": "trace_free_identity_as_source",
            "accepted": False,
            "reason": "being trace-free is a tensor type, not a source-selection law",
        },
        {
            "route": "screen_lensing_inversion_to_4d_source",
            "accepted": False,
            "reason": "2D screen shear cannot select a full 4D H_TF/Q_TF branch",
        },
        {
            "route": "residual_fit",
            "accepted": False,
            "reason": "residual fitting is not a Janus source/field equation",
        },
    ]
    return {
        "description": (
            "Bounded P0 gate for Weyl/shear as a trace-free H/Q_TF candidate."
        ),
        "status": "tracefree-h-weyl-shear-source-gate-open",
        "qtf_channel": "trace-free H / Q_TF rank-9 4D source channel",
        "candidate": "weyl_shear",
        "diagnostics": diagnostics,
        "rejected_routes": rejected_routes,
        "trace_free_diagnostics_present": True,
        "projection_orientation_constraints": True,
        "janus_source_field_equation_present": False,
        "gauge_boundary_branch_fixed": False,
        "full_h_tf_q_tf_selected": False,
        "source_selection_closed": False,
        "residual_fit_used": False,
        "physics_closed": False,
        "prediction": False,
        "prediction_ready": False,
        "guardrails": [
            "do not treat trace-free Weyl/shear data as a full H_TF/Q_TF selector",
            "do not upgrade 2D screen lensing into a 4D source law",
            "do not use residual fitting to select the missing source branch",
            "require Janus source/field equation plus gauge/boundary branch",
        ],
        "verdict": (
            "E_{mu nu}, sigma_{mu nu}, and optical screen shear are useful "
            "trace-free diagnostics. They can constrain projections and orientation, "
            "but they do not select full H_TF/Q_TF without Janus source closure."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Weyl Shear Source Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Q_TF channel: {payload['qtf_channel']}",
        f"Candidate: {payload['candidate']}",
        f"Trace-free diagnostics present: {payload['trace_free_diagnostics_present']}",
        f"Projection/orientation constraints: {payload['projection_orientation_constraints']}",
        f"Janus source/field equation present: {payload['janus_source_field_equation_present']}",
        f"Gauge/boundary branch fixed: {payload['gauge_boundary_branch_fixed']}",
        f"Full H_TF/Q_TF selected: {payload['full_h_tf_q_tf_selected']}",
        f"Residual fit used: {payload['residual_fit_used']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Diagnostics",
        "",
        "| name | trace-free | role | selects full H_TF/Q_TF | blocker |",
        "|---|---:|---|---:|---|",
    ]
    for row in payload["diagnostics"]:
        lines.append(
            f"| {row['name']} | {row['trace_free']} | {row['data_role']} | "
            f"{row['selects_full_h_tf_q_tf']} | {row['blocker']} |"
        )
    lines.extend(
        [
            "",
            "## Rejected Routes",
            "",
            "| route | accepted | reason |",
            "|---|---:|---|",
        ]
    )
    for row in payload["rejected_routes"]:
        lines.append(f"| {row['route']} | {row['accepted']} | {row['reason']} |")
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
