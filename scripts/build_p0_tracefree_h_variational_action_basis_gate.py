from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_variational_action_basis_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_variational_action_basis_gate.json")


def build_payload() -> dict:
    acceptance_obligations = [
        "source-derived from S_Janus with variables H, L, phi, matter",
        "variation domain fixed in the symmetric trace-free H_TF/Q_TF channel",
        "boundary and gauge conditions fixed before reading the EL source",
        "same-L compatibility with the Janus stack",
        "mirror inverse compatibility under plus/minus exchange",
        "principal symbol and stability/ghost acceptance",
    ]
    candidate_terms = [
        {
            "term": "tr_qtf2",
            "class": "ultralocal invariant",
            "action_density": "Tr(Q_TF^2)",
            "could_generate": "algebraic S_TF^Janus contribution",
            "status": "conditional",
            "accepted": False,
            "reason": "not source-derived from S_Janus and has no derivative, boundary/gauge, same-L, mirror, or stability closure",
        },
        {
            "term": "tr_qtf3",
            "class": "ultralocal invariant",
            "action_density": "Tr(Q_TF^3)",
            "could_generate": "nonlinear algebraic S_TF^Janus contribution",
            "status": "conditional",
            "accepted": False,
            "reason": "not source-derived from S_Janus and has no derivative, boundary/gauge, same-L, mirror, or stability closure",
        },
        {
            "term": "dqtf_kinetic",
            "class": "derivative kinetic",
            "action_density": "D Q_TF . D Q_TF",
            "could_generate": "trace-free derivative EL operator",
            "status": "conditional",
            "accepted": False,
            "reason": "requires source/action provenance, integration by parts, gauge/boundary data, same-L, mirror, and stability closure",
        },
        {
            "term": "dhtf_kinetic",
            "class": "derivative kinetic",
            "action_density": "D H_TF . D H_TF",
            "could_generate": "trace-free derivative EL operator",
            "status": "conditional",
            "accepted": False,
            "reason": "requires source/action provenance, integration by parts, gauge/boundary data, same-L, mirror, and stability closure",
        },
        {
            "term": "qtf_pi_tf",
            "class": "linear coupling",
            "action_density": "Q_TF^{ab} Pi_TF_ab",
            "could_generate": "matter anisotropic-stress S_TF^Janus",
            "status": "conditional",
            "accepted": False,
            "reason": "Pi_TF must be derived from Janus matter variation, not inserted as a target source",
        },
        {
            "term": "qtf_weyl",
            "class": "linear coupling",
            "action_density": "Q_TF^{ab} E_ab/Weyl",
            "could_generate": "electric-Weyl/shear S_TF^Janus",
            "status": "conditional",
            "accepted": False,
            "reason": "Weyl/shear coupling needs Janus metric/optical action provenance and stability closure",
        },
        {
            "term": "qtf_phi_sigma",
            "class": "linear coupling",
            "action_density": "Q_TF^{ab} Phi_Sigma_ab",
            "could_generate": "Phi_Sigma trace-free source",
            "status": "conditional",
            "accepted": False,
            "reason": "Phi_Sigma remains unaccepted unless derived from S_Janus[H,L,phi,matter]",
        },
        {
            "term": "bf_gl_constraints",
            "class": "constraint coupling",
            "action_density": "BF/GL multipliers coupled to trace-free strain constraints",
            "could_generate": "constraint-projected S_TF^Janus",
            "status": "conditional",
            "accepted": False,
            "reason": "constraint route needs accepted Janus BF/GL provenance, gauge fixing, same-L, mirror, and stability closure",
        },
    ]
    return {
        "description": (
            "Bounded P0 basis gate for candidate variational action terms that "
            "could generate S_TF^Janus in the trace-free H/Q_TF channel."
        ),
        "status": "tracefree-h-variational-action-basis-gate-open",
        "target_channel": "S_TF^Janus for H_TF/Q_TF",
        "action_variables": ["H", "L", "phi", "matter"],
        "acceptance_rule": (
            "Every basis term remains conditional and unaccepted unless it is "
            "source-derived from S_Janus[H,L,phi,matter] with boundary/gauge, "
            "same-L, mirror, and stability obligations closed."
        ),
        "acceptance_obligations": acceptance_obligations,
        "candidate_terms": candidate_terms,
        "candidate_count": len(candidate_terms),
        "accepted_terms": [
            row["term"]
            for row in candidate_terms
            if row["accepted"] and row["status"] == "accepted"
        ],
        "requirements_closed": False,
        "any_term_accepted": False,
        "target_residual_allowed": False,
        "determinant_trace_allowed": False,
        "forbidden_routes": [
            "fit or declare a residual target for S_TF^Janus",
            "use determinant trace, log det(H), or B4vol as trace-free source data",
            "accept an action term without Janus source/action provenance",
        ],
        "prediction": False,
        "prediction_ready": False,
        "verdict": (
            "The listed variational terms are only a candidate basis. None is "
            "accepted until it is derived from the Janus action with all trace-free "
            "source obligations closed; residual targets and determinant trace "
            "routes are forbidden."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Variational Action Basis Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Target channel: {payload['target_channel']}",
        f"Action variables: `{', '.join(payload['action_variables'])}`",
        f"Requirements closed: {payload['requirements_closed']}",
        f"Any term accepted: {payload['any_term_accepted']}",
        f"Target residual allowed: {payload['target_residual_allowed']}",
        f"Determinant trace allowed: {payload['determinant_trace_allowed']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Acceptance Rule",
        "",
        payload["acceptance_rule"],
        "",
        "## Obligations",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["acceptance_obligations"])
    lines.extend(
        [
            "",
            "## Candidate Terms",
            "",
            "| term | class | action density | status | accepted | reason |",
            "|---|---|---|---|---:|---|",
        ]
    )
    for row in payload["candidate_terms"]:
        lines.append(
            f"| {row['term']} | {row['class']} | `{row['action_density']}` | "
            f"{row['status']} | {row['accepted']} | {row['reason']} |"
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
