from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_weak_congruence_variational_origin.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_weak_congruence_variational_origin.json")


def build_payload() -> dict:
    candidate_terms = [
        {
            "name": "projected_acceleration_multiplier_plus",
            "term": "lambda_plus_mu u_-to+^nu D_plus_nu u_-to+^mu",
            "target": "C_plus-minus^mu_{alpha beta} u_-to+^alpha u_-to+^beta = 0",
            "problem": "introduces a multiplier field unless lambda is derived from existing Stueckelberg variables",
        },
        {
            "name": "projected_acceleration_multiplier_minus",
            "term": "lambda_minus_a u_+to-^b D_minus_b u_+to-^a",
            "target": "C_minus-plus^a_{mu nu} u_+to-^mu u_+to-^nu = 0",
            "problem": "mirror multiplier must be inverse-map related, not independently fitted",
        },
    ]
    accepted_without_new_axiom = [
        "The term is already present after varying pulled matter with respect to phi/L.",
        "The multiplier is identified with an existing dust current or density factor.",
        "Plus and minus multipliers are mirror images from one covariant action.",
        "No new free function changes Q_cross, Q_det, or lensing normalization.",
    ]
    rejection_rules = [
        "Reject independent lambda_plus/lambda_minus fields as a new axiom.",
        "Reject any multiplier tuned to observations.",
        "Reject any route that closes dust but silently changes pressure/Pi transport.",
        "Reject if the same L is not used for K transport and Q_cross.",
    ]
    decision = {
        "minimal_variational_shape_found": True,
        "source_derived": False,
        "requires_new_multiplier_if_not_from_matter_variation": True,
        "accepted_as_final_closure": False,
        "reason": (
            "A variational origin can generate the weak congruence equation with a "
            "projected-acceleration multiplier. This is mathematically clean but not "
            "yet Janus-derived: the multiplier must come from existing pulled matter "
            "or Stueckelberg variation, otherwise it is a new constraint field."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_weak_congruence_variational_origin",
        "status": "minimal-variational-shape-conditional-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "candidate_terms": candidate_terms,
        "accepted_without_new_axiom": accepted_without_new_axiom,
        "rejection_rules": rejection_rules,
        "decision": decision,
        "next_step": (
            "Compare the multiplier shape against the actual variation of pulled dust "
            "matter under phi/L; accept only if lambda is an existing density-current "
            "object, not a newly introduced field."
        ),
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Weak Congruence Variational Origin",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Candidate Terms",
    ]
    for row in payload["candidate_terms"]:
        lines.append(f"- {row['name']}: `{row['term']}`")
        lines.append(f"  - target: `{row['target']}`")
        lines.append(f"  - problem: {row['problem']}")
    lines.extend(["", "## Accepted Without New Axiom"])
    lines.extend(f"- {item}" for item in payload["accepted_without_new_axiom"])
    lines.extend(["", "## Rejection Rules"])
    lines.extend(f"- {item}" for item in payload["rejection_rules"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Minimal variational shape found: {decision['minimal_variational_shape_found']}",
            f"Source derived: {decision['source_derived']}",
            (
                "Requires new multiplier if not from matter variation: "
                f"{decision['requires_new_multiplier_if_not_from_matter_variation']}"
            ),
            f"Accepted as final closure: {decision['accepted_as_final_closure']}",
            f"Reason: {decision['reason']}",
            "",
            f"Next step: {payload['next_step']}",
            "",
        ]
    )
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
