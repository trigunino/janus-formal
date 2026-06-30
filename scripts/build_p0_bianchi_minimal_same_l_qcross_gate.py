from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_bianchi_minimal_same_l_qcross_gate.md")
JSON_PATH = Path("outputs/reports/p0_bianchi_minimal_same_l_qcross_gate.json")


def build_payload() -> dict:
    compatibility_rows = [
        {
            "gate": "starts_after_full_connection_lift",
            "requirement": "consume the L_pm/L_mp pair solved by the full Omega lift, not a separate optical map",
            "closed": False,
        },
        {
            "gate": "mirror_inverse_pair",
            "requirement": "L_pm=L_mp^{-1} after mirror transport and sector-connection conversion",
            "closed": False,
        },
        {
            "gate": "same_l_for_k_transport",
            "requirement": "K_plus and K_minus are transported with the same L_pm/L_mp used in Q_cross",
            "closed": False,
        },
        {
            "gate": "same_null_covectors",
            "requirement": "Q_cross uses the same transported null covectors used to contract K_plus_kk and K_minus_kk",
            "closed": False,
        },
    ]
    optical_contractions = [
        {
            "name": "plus_receives_minus",
            "k_transport": "k_pm_C=L_pm^A_C k_plus_A",
            "k_contraction": "K_plus_kk=T_minus^{CD} k_pm_C k_pm_D",
            "q_cross": "Q_cross_plus=A_pm/A_plus with A_pm=(u_minus^C k_pm_C)^2",
            "kind": "geometric_optical_contraction",
            "fitted_scalar": False,
        },
        {
            "name": "minus_receives_plus",
            "k_transport": "k_mp_C=L_mp^A_C k_minus_A",
            "k_contraction": "K_minus_kk=T_plus^{CD} k_mp_C k_mp_D",
            "q_cross": "Q_cross_minus=A_mp/A_minus with A_mp=(u_plus^C k_mp_C)^2",
            "kind": "geometric_optical_contraction",
            "fitted_scalar": False,
        },
    ]
    scalar_guardrails = [
        {
            "shortcut": "independent_optical_l",
            "allowed": False,
            "reason": "an optical-only L would decouple Q_cross from Bianchi K transport",
        },
        {
            "shortcut": "posthoc_qcross",
            "allowed": False,
            "reason": "Q_cross must be computed from the transported contraction, not tuned after residual inspection",
        },
        {
            "shortcut": "qdet_absorption",
            "allowed": False,
            "reason": "Q_det is a density/volume factor and may not hide optical or mirror residuals",
        },
        {
            "shortcut": "fitted_scalar_replacement",
            "allowed": False,
            "reason": "a fitted scalar is not the geometric optical contraction A_pm/A_plus or A_mp/A_minus",
        },
    ]
    closure_requirements = [
        "full Omega_alpha lift selected, including transverse boost one-forms and spatial rotations",
        "curvature integrability for D_alpha L=Omega_alpha L closed",
        "mirror inverse row closed with L_pm=L_mp^{-1} or a source-derived mirror map",
        "K_plus/K_minus residuals checked with the same L_pm/L_mp",
        "Q_cross contractions checked with the same transported null covectors",
        "no residual absorbed into Q_det, Q_cross, B_4vol, or density convention",
    ]
    return {
        "description": (
            "Bounded P0 gate for same-L Q_cross compatibility after the "
            "Bianchi-minimal full-connection lift."
        ),
        "status": "same-l-qcross-gate-open",
        "starts_from": [
            "p0_bianchi_minimal_full_connection_lift_system",
            "p0_bianchi_minimal_mirror_inverse_attempt",
        ],
        "same_l_pm_mp_required": True,
        "same_l_as_k_transport_required": True,
        "transported_null_covectors_required": True,
        "geometric_optical_contraction_required": True,
        "fitted_scalar_allowed": False,
        "independent_optical_l_allowed": False,
        "posthoc_qcross_allowed": False,
        "qdet_absorption_allowed": False,
        "full_omega_integrability_closed": False,
        "mirror_integrability_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "compatibility_rows": compatibility_rows,
        "optical_contractions": optical_contractions,
        "scalar_guardrails": scalar_guardrails,
        "closure_requirements": closure_requirements,
        "verdict": (
            "Q_cross is admissible only as a geometric optical contraction induced "
            "by the same L_pm/L_mp and transported null covectors used for K "
            "transport. Independent optical L choices, posthoc Q_cross fitting, "
            "and Q_det absorption remain forbidden, so the gate stays open until "
            "full Omega and mirror integrability close."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Bianchi-Minimal Same-L Q_cross Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Starts from: {', '.join(payload['starts_from'])}",
        f"Same L_pm/L_mp required: {payload['same_l_pm_mp_required']}",
        f"Same L as K transport required: {payload['same_l_as_k_transport_required']}",
        f"Transported null covectors required: {payload['transported_null_covectors_required']}",
        f"Geometric optical contraction required: {payload['geometric_optical_contraction_required']}",
        f"Fitted scalar allowed: {payload['fitted_scalar_allowed']}",
        f"Independent optical L allowed: {payload['independent_optical_l_allowed']}",
        f"Posthoc Q_cross allowed: {payload['posthoc_qcross_allowed']}",
        f"Q_det absorption allowed: {payload['qdet_absorption_allowed']}",
        f"Full Omega integrability closed: {payload['full_omega_integrability_closed']}",
        f"Mirror integrability closed: {payload['mirror_integrability_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Compatibility Rows",
        "",
        "| gate | requirement | closed |",
        "|---|---|---|",
    ]
    for row in payload["compatibility_rows"]:
        lines.append(f"| {row['gate']} | {row['requirement']} | {row['closed']} |")
    lines.extend(
        [
            "",
            "## Optical Contractions",
            "",
            "| name | k transport | K contraction | Q_cross | kind | fitted scalar |",
            "|---|---|---|---|---|---|",
        ]
    )
    for row in payload["optical_contractions"]:
        lines.append(
            "| "
            f"{row['name']} | `{row['k_transport']}` | `{row['k_contraction']}` | "
            f"`{row['q_cross']}` | {row['kind']} | {row['fitted_scalar']} |"
        )
    lines.extend(["", "## Scalar Guardrails", "", "| shortcut | allowed | reason |", "|---|---|---|"])
    for row in payload["scalar_guardrails"]:
        lines.append(f"| {row['shortcut']} | {row['allowed']} | {row['reason']} |")
    lines.extend(["", "## Closure Requirements", ""])
    lines.extend(f"- {item}" for item in payload["closure_requirements"])
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
