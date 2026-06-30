from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_derivative_branch_stability_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_derivative_branch_stability_gate.json")


def build_payload() -> dict:
    required_gates = [
        "Janus source/action provenance for the derivative kinetic term",
        "boundary and gauge conditions for integration by parts and mode removal",
        "curl integrability for D Q_TF or D H_TF data",
        "same-L compatibility with the Janus transport stack",
        "mirror inverse compatibility under plus/minus exchange",
        "principal-symbol sign, ghost, and tachyon screen on reduced physical modes",
    ]
    generic_sign_conditions = [
        "reduced kinetic coefficient for Q_TF/H_TF physical modes has ghost-free sign",
        "spatial principal symbol has the declared hyperbolic/elliptic sign after gauge fixing",
        "reduced mass/Hessian eigenvalues are nonnegative on the declared background",
        "mixed derivative blocks are positive after Schur-complement or eigenvalue reduction",
    ]
    candidate_actions = [
        {
            "term": "dqtf_kinetic",
            "action_density": "D Q_TF . D Q_TF",
            "formal_stf_el_operator": "-2 P_STF(D*D Q_TF) + boundary/lower-order terms",
            "can_provide_stf_el_operator": "conditional",
            "accepted": False,
            "condition": "requires all source, integrability, transport, mirror, and stability gates",
        },
        {
            "term": "dhtf_kinetic",
            "action_density": "D H_TF . D H_TF",
            "formal_stf_el_operator": "-2 P_STF(D*D H_TF) + boundary/lower-order terms",
            "can_provide_stf_el_operator": "conditional",
            "accepted": False,
            "condition": "requires all source, integrability, transport, mirror, and stability gates",
        },
    ]
    return {
        "description": (
            "Bounded P0 source/stability gate for trace-free H/Q_TF derivative "
            "kinetic branches."
        ),
        "status": "tracefree-h-derivative-branch-stability-source-gate-open",
        "target_channel": "H_TF/Q_TF",
        "branch_class": "derivative kinetic",
        "accepted_branch_supplied": False,
        "stf_el_operator_supplied": "formal/conditional only",
        "candidate_actions": candidate_actions,
        "candidate_count": len(candidate_actions),
        "accepted_actions": [
            row["term"]
            for row in candidate_actions
            if row["accepted"] and row["can_provide_stf_el_operator"] == "accepted"
        ],
        "required_gates": required_gates,
        "requirements_closed": False,
        "janus_provenance_required": True,
        "janus_provenance_supplied": False,
        "boundary_gauge_required": True,
        "curl_integrability_required": True,
        "same_l_required": True,
        "mirror_inverse_required": True,
        "principal_symbol_screen": {
            "required": True,
            "closed": False,
            "ghost_screen": "ghost-free positive reduced kinetic symbol required",
            "tachyon_screen": "tachyon-free nonnegative reduced mass/Hessian symbol required",
            "generic_sign_conditions": generic_sign_conditions,
            "sign_conditions_necessary_not_sufficient": True,
        },
        "generic_sign_conditions_necessary": True,
        "generic_sign_conditions_sufficient": False,
        "residual_operator_allowed": False,
        "determinant_trace_allowed": False,
        "forbidden_routes": [
            "fit or declare a residual operator for the trace-free derivative source",
            "use determinant trace, log det(H), or B4vol as trace-free source data",
            "treat generic principal-symbol signs as sufficient without provenance and constraints",
        ],
        "prediction": False,
        "prediction_ready": False,
        "verdict": (
            "D Q_TF . D Q_TF and D H_TF . D H_TF remain conditional formal "
            "branches. They do not supply an accepted STF EL source until Janus "
            "provenance, boundary/gauge, curl, same-L, mirror, and stability "
            "screens all close; residual operators and determinant trace routes "
            "are forbidden."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Derivative Branch Stability/Source Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Target channel: {payload['target_channel']}",
        f"Branch class: {payload['branch_class']}",
        f"Accepted branch supplied: {payload['accepted_branch_supplied']}",
        f"STF EL operator supplied: {payload['stf_el_operator_supplied']}",
        f"Requirements closed: {payload['requirements_closed']}",
        f"Generic sign conditions necessary: {payload['generic_sign_conditions_necessary']}",
        f"Generic sign conditions sufficient: {payload['generic_sign_conditions_sufficient']}",
        f"Residual operator allowed: {payload['residual_operator_allowed']}",
        f"Determinant trace allowed: {payload['determinant_trace_allowed']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Candidate Derivative Actions",
        "",
        "| term | action density | formal STF EL operator | conditional | accepted | condition |",
        "|---|---|---|---|---:|---|",
    ]
    for row in payload["candidate_actions"]:
        lines.append(
            f"| {row['term']} | `{row['action_density']}` | "
            f"`{row['formal_stf_el_operator']}` | "
            f"{row['can_provide_stf_el_operator']} | {row['accepted']} | "
            f"{row['condition']} |"
        )
    lines.extend(["", "## Required Gates", ""])
    lines.extend(f"- {item}" for item in payload["required_gates"])
    screen = payload["principal_symbol_screen"]
    lines.extend(
        [
            "",
            "## Principal-Symbol Screen",
            "",
            f"- required: `{screen['required']}`",
            f"- closed: `{screen['closed']}`",
            f"- ghost screen: {screen['ghost_screen']}",
            f"- tachyon screen: {screen['tachyon_screen']}",
            "- generic sign conditions:",
        ]
    )
    lines.extend(f"  - `{item}`" for item in screen["generic_sign_conditions"])
    lines.append(
        f"- necessary not sufficient: `{screen['sign_conditions_necessary_not_sufficient']}`"
    )
    lines.extend(["", "## Forbidden Routes", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_routes"])
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
